"""Actual imported-source fingerprint and launch-consumer contract controls."""
from __future__ import annotations

import errno
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import uuid
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts import seed_journal
from scripts.lean_slots import supervisor as production
from tests.test_lean_slots import slot_repo, downstream_repo, isolated_process_observations
from tests.test_lean_lifecycle_observation import owned


MEMBERS = {"__init__.py", "state.py", "supervisor.py", "controller.py", "cli.py",
           "proxy.py", "claude_config.py", "host_limits.py", "checkpoints.py"}


def import_package(root):
    name = "_fingerprint_fixture_" + uuid.uuid4().hex
    spec = importlib.util.spec_from_file_location(name, root / "__init__.py",
                                                submodule_search_locations=[str(root)])
    package = importlib.util.module_from_spec(spec)
    sys.modules[name] = package
    spec.loader.exec_module(package)
    module = importlib.import_module(name + ".supervisor")
    return name, module


def launcher(scripts, *, selector=False, home=False, guard=True, default=True,
             aliases=False, order="guard-first", message=None, eager_default=None):
    os_name, sys_name, path_name = ("environment", "runtime", "SourcePath") if aliases else ("os", "sys", "Path")
    imports = f"import os{' as environment' if aliases else ''}\nimport sys{' as runtime' if aliases else ''}\nfrom pathlib import Path{' as SourcePath' if aliases else ''}\n"
    body = 'ROOT = ' + path_name + '(__file__).resolve().parents[1]\n'
    if selector:
        raw = f'{path_name}({os_name}.environ.get("EXAMPLE_SHARED_ROOT", str(ROOT.parent / "shared-source")))'
        if home:
            body += f"RAW_SHARED = {raw}\nSHARED = RAW_SHARED.expanduser().resolve()\n"
        else:
            body += f"SHARED = {raw}.resolve()\n"
        body += 'SELECTED_SCRIPTS = SHARED / "scripts"\n'
    else:
        body += f"SELECTED_SCRIPTS = {path_name}({str(scripts)!r})\n"
    guard_text = ""
    if guard:
        msg = message if message is not None else 'f"Shared source unavailable: {SELECTED_SCRIPTS}"'
        guard_text = f'if not (SELECTED_SCRIPTS / "lean_slots" / "cli.py").is_file():\n    raise SystemExit({msg})\n'
    insertion = f"{sys_name}.path.insert(0, str(SELECTED_SCRIPTS))\n"
    default_text = ""
    if default:
        operand = eager_default or 'str(ROOT / "config" / "lean-slots.downstream.json")'
        default_text = f'{os_name}.environ.setdefault("LEAN_SLOT_CONFIG", {operand})\n'
    if order == "guard-first":
        body += guard_text + insertion + default_text
    else:
        body += insertion + default_text + guard_text
    return imports + body + 'from lean_slots.cli import main as entry\nif __name__ == "__main__":\n    raise SystemExit(entry())\n'


@pytest.fixture
def fp(slot_repo, tmp_path, monkeypatch, isolated_process_observations):
    ctl, repo, _ = slot_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    monkeypatch.setattr(seed_journal, "JOURNAL_DIR", tmp_path / "source-seed-journal")
    roots = []
    prefixes = []
    source = Path(production.__file__).resolve().parent
    for label in ("A", "B"):
        home = tmp_path / "homes" / label
        scripts = home / "shared-source" / "scripts"
        package = scripts / "lean_slots"
        package.mkdir(parents=True)
        for path in source.iterdir():
            if path.suffix == ".py":
                shutil.copyfile(path, package / path.name)
        prefix, module = import_package(package)
        prefixes.append(prefix)
        roots.append(SimpleNamespace(home=home, scripts=scripts, package=package, module=module))
    a, b = roots
    inv = sys.modules[a.module.Inventory.__module__].Inventory.load(ctl.inventory.source)
    sup = a.module.Supervisor(inv)
    wrapper = repo / "scripts" / "slotctl.py"
    wrapper.write_text(launcher(a.scripts))
    value = SimpleNamespace(a=a, b=b, sup=sup, ctl=ctl, repo=repo, wrapper=wrapper,
                            host=isolated_process_observations, prefixes=prefixes)
    yield value
    for name in tuple(sys.modules):
        if any(name == prefix or name.startswith(prefix + ".") for prefix in prefixes):
            sys.modules.pop(name)


def payload(fp, kind="proxy", environment=None):
    env = os.environ.copy() if environment is None else environment
    command = fp.sup.proxy_command(1) if kind == "proxy" else fp.sup.backend_command(1)
    return fp.a.module._RuntimeSourcePass(fp.sup, kind, 1, command, env).build()


def no_new_effects(fp, before=None):
    assert fp.host.launches == [] and fp.host.signals == []
    path = fp.sup.inventory.process_path("proxy", 1)
    if before is not None:
        assert path.read_bytes() == before
    else:
        assert not path.exists()


def test_fp_01_real_origin_and_complete_payload(fp):
    value = payload(fp)["sources"]
    assert set(value["shared"]["files"]) == MEMBERS
    assert value["shared"]["root"] == str(fp.a.package.resolve())
    assert value["local"] == {"absent": True}
    assert value["launcher"]["sha256"] == hashlib.sha256(fp.wrapper.read_bytes()).hexdigest()
    assert value["routing"]["selected_package"] == str(fp.a.package.resolve())
    assert fp.sup._runtime_fingerprint("proxy", 1) == fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


@pytest.mark.parametrize("member", sorted(MEMBERS))
def test_fp_02_every_shared_byte_reaches_actual_stale_consumer(fp, member):
    path = owned(fp.sup, fp.host, "proxy", 1, 840101)
    before = path.read_bytes()
    target = fp.a.package / member
    with seed_journal.seeded_mutation(target, target.read_bytes() + b"\n# independent changed source byte\n", reason="shared source consumer"):
        assert fp.sup.process_state("proxy", 1) == "stale"
        with pytest.raises(fp.a.module.SlotError, match="stale"):
            fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
        assert path.read_bytes() == before
        no_new_effects(fp, before)
    assert fp.sup.process_state("proxy", 1) == "running"


def test_fp_03_nested_add_delete_and_local_names_do_not_collide(fp):
    before = fp.sup._runtime_fingerprint("proxy", 1)
    nested = fp.a.package / "future"
    nested.mkdir()
    (nested / "__init__.py").write_text("# future initializer\n")
    extra = nested / "additional.py"
    extra.write_text("FUTURE_SOURCE = 1\n")
    changed = fp.sup._runtime_fingerprint("proxy", 1)
    assert changed != before
    value = payload(fp)["sources"]
    assert value["shared"]["files"]["future/additional.py"] == hashlib.sha256(extra.read_bytes()).hexdigest()
    extra.unlink()
    assert fp.sup._runtime_fingerprint("proxy", 1) != changed
    local = fp.repo / "scripts" / "lean_slots"
    local.mkdir()
    (local / "__init__.py").write_text("# local initialized package\n")
    (local / "state.py").write_text("LOCAL_VALUE = 2\n")
    value = payload(fp)["sources"]
    assert value["local"]["files"]["state.py"] != value["shared"]["files"]["state.py"]
    first = fp.sup._runtime_fingerprint("proxy", 1)
    (local / "state.py").write_text("LOCAL_VALUE = 3\n")
    assert fp.sup._runtime_fingerprint("proxy", 1) != first


def test_fp_04_direct_genuine_package_and_same_root_alias(fp):
    local = fp.repo / "scripts" / "lean_slots"
    shutil.copytree(fp.a.package, local)
    prefix, module = import_package(local)
    fp.prefixes.append(prefix)
    direct_state = sys.modules[module.Inventory.__module__]
    direct = module.Supervisor(direct_state.Inventory.load(fp.sup.inventory.source))
    fp.wrapper.write_text('from lean_slots.cli import main\nif __name__ == "__main__":\n    raise SystemExit(main())\n')
    assert direct._runtime_fingerprint("proxy", 1)
    actual = module._RuntimeSourcePass(direct, "proxy", 1, direct.proxy_command(1), os.environ.copy()).build()
    assert actual["sources"]["local"]["alias_of"] == "shared"
    assert actual["sources"]["local"]["files"] == actual["sources"]["shared"]["files"]


@pytest.mark.parametrize("aliases,order,message", [
    (False, "guard-first", '"literal unavailable"'),
    (True, "guard-first", 'f"Unavailable {SELECTED_SCRIPTS}"'),
    (True, "insert-first", '"literal unavailable"'),
])
@pytest.mark.parametrize("present", [None, "", "/source-defined-existing-inventory.json"])
def test_fp_05_guard_default_alias_order_and_capture_input(fp, monkeypatch, aliases, order, message, present):
    fp.wrapper.write_text(launcher(fp.a.scripts, aliases=aliases, order=order, message=message))
    if present is None:
        monkeypatch.delenv("LEAN_SLOT_CONFIG", raising=False)
    else:
        monkeypatch.setenv("LEAN_SLOT_CONFIG", present)
    original = os.environ.copy()
    value = payload(fp)["sources"]["routing"]
    default = value["inventory_default"]
    assert default["present"] is (present is not None)
    assert default["applied"] is (present is None)
    assert default["effective"] == (str(fp.repo / "config" / "lean-slots.downstream.json") if present is None else present)
    assert value["inventory_source"] == str(fp.sup.inventory.source)
    assert os.environ == original
    assert fp.sup._runtime_fingerprint("proxy", 1)


@pytest.mark.parametrize("defect", [
    "extra-call", "extra-conditional", "duplicate-insertion", "reassignment",
    "custom-import", "guard-expression", "guard-conversion", "guard-format",
    "guard-other-name", "guard-else", "default-other-key", "duplicate-default",
    "future-order", "main-other-call", "path-keywords", "selector-token",
])
def test_fp_06_unsupported_whole_templates_refuse(fp, defect):
    text = launcher(fp.a.scripts)
    if defect == "extra-call": text = text.replace("from lean_slots.cli", 'print("dynamic")\nfrom lean_slots.cli')
    elif defect == "extra-conditional": text = text.replace("from lean_slots.cli", 'if True:\n    pass\nfrom lean_slots.cli')
    elif defect == "duplicate-insertion": text = text.replace('from lean_slots.cli', 'sys.path.insert(0, str(SELECTED_SCRIPTS))\nfrom lean_slots.cli')
    elif defect == "reassignment": text = text.replace("from lean_slots.cli", "SELECTED_SCRIPTS = ROOT\nfrom lean_slots.cli")
    elif defect == "custom-import": text = text.replace("from pathlib import Path", "from unknown import Path")
    elif defect == "guard-expression": text = text.replace("{SELECTED_SCRIPTS}", "{str(SELECTED_SCRIPTS)}")
    elif defect == "guard-conversion": text = text.replace("{SELECTED_SCRIPTS}", "{SELECTED_SCRIPTS!s}")
    elif defect == "guard-format": text = text.replace("{SELECTED_SCRIPTS}", "{SELECTED_SCRIPTS:>10}")
    elif defect == "guard-other-name": text = text.replace("{SELECTED_SCRIPTS}", "{ROOT}")
    elif defect == "guard-else": text = text.replace('sys.path.insert', 'else:\n    pass\nsys.path.insert')
    elif defect == "default-other-key": text = text.replace('"LEAN_SLOT_CONFIG"', '"UNKNOWN_ENVIRONMENT"')
    elif defect == "duplicate-default": text = text.replace("from lean_slots.cli", 'os.environ.setdefault("LEAN_SLOT_CONFIG", str(ROOT))\nfrom lean_slots.cli')
    elif defect == "future-order": text = text.replace("import sys", "from __future__ import annotations\nimport sys")
    elif defect == "main-other-call": text = text.replace("SystemExit(entry())", 'SystemExit(print("dynamic"))')
    elif defect == "path-keywords": text = text.replace(".resolve()", ".resolve(strict=True)")
    elif defect == "selector-token": text = launcher(fp.a.scripts, selector=True).replace("EXAMPLE_SHARED_ROOT", "LEAN_LSP_MCP_TOKEN")
    fp.wrapper.write_text(text)
    with pytest.raises(fp.a.module.SlotError, match="runtime source"):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


@pytest.mark.parametrize("kind", ["proxy", "backend"])
@pytest.mark.parametrize("home", [False, True])
@pytest.mark.parametrize("default_present", [False, True])
def test_fp_07_actual_captured_selector_and_HOME_Popen_are_distinct(fp, monkeypatch, kind, home, default_present):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=home, aliases=True))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source" if home else str(fp.a.scripts.parent))
    monkeypatch.setenv("HOME", str(fp.a.home))
    monkeypatch.setenv("FINGERPRINT_CAPTURE_SENTINEL", "captured-A")
    if default_present:
        monkeypatch.setenv("LEAN_SLOT_CONFIG", "captured-inventory-value")
    else:
        monkeypatch.delenv("LEAN_SLOT_CONFIG", raising=False)
    expected_command = fp.sup.proxy_command(1) if kind == "proxy" else fp.sup.backend_command(1)
    expected_token = fp.sup.inventory.backend_token(1) if kind == "backend" else None
    before_environment = os.environ.copy()
    real_open = Path.open
    changed = []
    def observed_open(path, *args, **kwargs):
        handle = real_open(path, *args, **kwargs)
        if path == fp.a.package / "state.py" and not changed:
            changed.append(True)
            monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source" if home else str(fp.b.scripts.parent))
            monkeypatch.setenv("HOME", str(fp.b.home))
            monkeypatch.setenv("FINGERPRINT_CAPTURE_SENTINEL", "ambient-B")
        return handle
    monkeypatch.setattr(Path, "open", observed_open)
    intercepted = []
    actual_popen = fp.host.popen
    def popen(argv, **kwargs):
        intercepted.append({"argv": list(argv), "env": dict(kwargs["env"])})
        return actual_popen(argv, **kwargs)
    monkeypatch.setattr(subprocess, "Popen", popen)
    port = int(fp.sup.inventory.slot(1)[kind + "_port"])
    fp.sup._spawn(kind, 1, expected_command, port)
    assert changed and len(intercepted) == 1
    seen = intercepted[0]
    assert seen["argv"] == expected_command
    assert seen["env"]["EXAMPLE_SHARED_ROOT"] == before_environment["EXAMPLE_SHARED_ROOT"]
    assert seen["env"]["HOME"] == str(fp.a.home)
    assert seen["env"]["FINGERPRINT_CAPTURE_SENTINEL"] == "captured-A"
    assert ("LEAN_SLOT_CONFIG" in seen["env"]) is default_present
    if default_present:
        assert seen["env"]["LEAN_SLOT_CONFIG"] == "captured-inventory-value"
    if kind == "backend":
        assert seen["env"].get("LEAN_LSP_MCP_TOKEN") == expected_token
    record = fp.sup.inventory.process_path(kind, 1)
    original = record.read_bytes()
    assert fp.sup.process_state(kind, 1) == "unavailable"
    with pytest.raises(fp.a.module.SlotError, match="roots disagree"):
        fp.sup._spawn(kind, 1, expected_command, port)
    assert len(intercepted) == 1 and record.read_bytes() == original and not fp.host.signals


@pytest.mark.parametrize("home_value", [None, "", "relative", "~named-user", "bad\nhome", "x" * 4097])
def test_fp_08_absolute_expand_noop_has_no_HOME_dependency(fp, monkeypatch, home_value):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.a.scripts.parent))
    if home_value is None: monkeypatch.delenv("HOME", raising=False)
    else: monkeypatch.setenv("HOME", home_value)
    value = payload(fp)["sources"]["routing"]
    assert all("HOME" not in t for t in value["transforms"])
    first = fp.sup._runtime_fingerprint("proxy", 1)
    monkeypatch.setenv("HOME", str(fp.b.home))
    assert fp.sup._runtime_fingerprint("proxy", 1) == first


@pytest.mark.parametrize("invalid", ["missing", "empty", "relative", "newline", "overbound", "named", "home-file", "home-missing", "denied"])
def test_fp_09_required_HOME_refusals_prevent_pending_and_launch(fp, monkeypatch, invalid):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source")
    monkeypatch.setenv("HOME", str(fp.a.home))
    if invalid == "missing": monkeypatch.delenv("HOME")
    elif invalid == "empty": monkeypatch.setenv("HOME", "")
    elif invalid == "relative": monkeypatch.setenv("HOME", "relative")
    elif invalid == "newline": monkeypatch.setenv("HOME", "/bad\nhome")
    elif invalid == "overbound": monkeypatch.setenv("HOME", "/" + "x" * 4096)
    elif invalid == "named": monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~xshared-source")
    elif invalid == "home-file": monkeypatch.setenv("HOME", str(fp.wrapper))
    elif invalid == "home-missing": monkeypatch.setenv("HOME", str(fp.a.home / "missing"))
    elif invalid == "denied":
        original = os.stat
        def stat(path, *a, **kw):
            if Path(path) == fp.a.home: raise PermissionError(errno.EPERM, "home stat denied")
            return original(path, *a, **kw)
        monkeypatch.setattr(os, "stat", stat)
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


def test_fp_10_HOME_bare_slash_alias_and_payload(fp, monkeypatch):
    alias = fp.a.home.parent / "alias-A"
    alias.symlink_to(fp.a.home, target_is_directory=True)
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True))
    monkeypatch.setenv("HOME", str(alias))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source")
    value = payload(fp)["sources"]["routing"]
    event = next(x for x in value["transforms"] if x["branch"] == "captured-home")
    assert event == {"raw": "~/shared-source", "branch": "captured-home", "HOME_present": True,
                     "HOME": str(alias), "canonical_home": str(fp.a.home.resolve()),
                     "expanded": str(alias / "shared-source")}
    assert value["selected_package"] == str(fp.a.package.resolve())
    # Bare tilde can select a home that is itself the genuine shared repository.
    monkeypatch.setenv("HOME", str(fp.a.scripts.parent))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~")
    assert fp.sup._runtime_fingerprint("proxy", 1)


@pytest.mark.parametrize("transform", [".resolve().expanduser()", ".expanduser().expanduser().resolve()", ".expanduser('x').resolve()", ".expanduser().resolve(strict=True)"])
def test_fp_11_unsupported_HOME_transform_is_not_accepted(fp, monkeypatch, transform):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True).replace(".expanduser().resolve()", transform))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.a.scripts.parent))
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


@pytest.mark.parametrize("existing", [False, True])
def test_fp_12_default_expressions_eagerly_consume_HOME_even_if_inactive(fp, monkeypatch, existing):
    operand = 'str(Path("~/unselected-inventory.json").expanduser().resolve())'
    fp.wrapper.write_text(launcher(fp.a.scripts, eager_default=operand))
    monkeypatch.setenv("HOME", str(fp.a.home))
    if existing: monkeypatch.setenv("LEAN_SLOT_CONFIG", "existing")
    else: monkeypatch.delenv("LEAN_SLOT_CONFIG", raising=False)
    value = payload(fp)["sources"]["routing"]
    assert any(x.get("HOME") == str(fp.a.home) for x in value["transforms"])
    assert value["inventory_default"]["effective"] == ("existing" if existing else str(fp.a.home / "unselected-inventory.json"))
    monkeypatch.delenv("HOME")
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


def test_fp_13_get_fallback_is_eager_not_a_lazy_branch(fp, monkeypatch):
    text = launcher(fp.a.scripts, selector=True).replace('str(ROOT.parent / "shared-source")',
          'str(Path("~/unselected-fallback").expanduser().resolve())')
    fp.wrapper.write_text(text)
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.a.scripts.parent))
    monkeypatch.setenv("HOME", str(fp.a.home))
    assert any(x.get("HOME") == str(fp.a.home) for x in payload(fp)["sources"]["routing"]["transforms"])
    monkeypatch.delenv("HOME")
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._runtime_fingerprint("proxy", 1)


@pytest.mark.parametrize("target", ["initializer", "state", "launcher", "empty-local", "nonregular", "escape-link", "directory-cycle"])
def test_fp_14_mandatory_and_malformed_sources_refuse(fp, target):
    if target == "initializer": (fp.a.package / "__init__.py").unlink()
    elif target == "state": (fp.a.package / "state.py").unlink()
    elif target == "launcher": fp.wrapper.unlink()
    elif target == "empty-local": (fp.repo / "scripts" / "lean_slots").mkdir()
    elif target == "nonregular":
        path = fp.a.package / "not_regular.py"; path.mkdir()
    elif target == "escape-link": (fp.a.package / "foreign.py").symlink_to(fp.wrapper)
    elif target == "directory-cycle": (fp.a.package / "cycle").symlink_to(fp.a.package, target_is_directory=True)
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


@pytest.mark.parametrize("seam", ["stat", "scandir", "read", "short-read", "optional-local-stat"])
def test_fp_15_native_denial_status_retains_reservation_and_witness(fp, monkeypatch, seam):
    path = owned(fp.sup, fp.host, "proxy", 1, 840201)
    backend = owned(fp.sup, fp.host, "backend", 1, 840202)
    backend_before = backend.read_bytes()
    before = path.read_bytes()
    if seam in {"stat", "optional-local-stat"}:
        original = os.stat
        target = fp.a.package / "state.py" if seam == "stat" else fp.repo / "scripts" / "lean_slots"
        def stat(value, *args, **kwargs):
            if Path(value) == target: raise PermissionError(errno.EIO, "external stat unavailable")
            return original(value, *args, **kwargs)
        monkeypatch.setattr(os, "stat", stat)
    elif seam == "scandir":
        original = os.scandir
        def scandir(value):
            if Path(value) == fp.a.package: raise PermissionError(errno.EPERM, "external scandir denied")
            return original(value)
        monkeypatch.setattr(os, "scandir", scandir)
    else:
        original = Path.open
        def read(value, *args, **kwargs):
            if value != fp.a.package / "state.py":
                return original(value, *args, **kwargs)
            if seam == "read":
                raise PermissionError(errno.EACCES, "external read denied")
            handle = original(value, *args, **kwargs)
            class ShortRead:
                def __enter__(self):
                    handle.__enter__()
                    return self
                def __exit__(self, *args):
                    return handle.__exit__(*args)
                def read(self, bound):
                    return handle.read(bound)[:32]
            return ShortRead()
        monkeypatch.setattr(Path, "open", read)
    item = fp.sup.status()["slots"][0]
    assert item["proxy_state"] == "unavailable"
    assert item["resources"]["proxy"]["observations"]
    assert fp.sup.inventory.process_path("proxy", 1).read_bytes() == before
    assert 1 in fp.sup.capacity_census()["reserved_physical_slots"]
    assert backend.read_bytes() == backend_before
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp, before)


@pytest.mark.parametrize("change", ["edit", "add", "delete", "replace", "home-alias"])
def test_fp_16_two_full_passes_reobserve_real_drift(fp, monkeypatch, change):
    original_open = Path.open
    opens = []
    extra = fp.a.package / "future.py"
    extra.write_text("FUTURE = 1\n")
    if change == "home-alias":
        alias = fp.a.home.parent / "changing-alias"
        alias.symlink_to(fp.a.home, target_is_directory=True)
        fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True))
        monkeypatch.setenv("HOME", str(alias))
        monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source")
    if change == "home-alias":
        original_stat = os.stat
        changed_alias = []
        def switch_alias(path):
            # This injects drift in a temporary fixture; it restores no artifact.
            if Path(path) == fp.repo / "scripts" / "lean_slots" and not changed_alias:
                changed_alias.append(True)
                alias.unlink()
                alias.symlink_to(fp.b.home, target_is_directory=True)
        def stat(path, *args, **kwargs):
            try:
                observed = original_stat(path, *args, **kwargs)
            except BaseException:
                switch_alias(path)
                raise
            switch_alias(path)
            return observed
        monkeypatch.setattr(os, "stat", stat)
    def opening(path, *args, **kwargs):
        handle = original_open(path, *args, **kwargs)
        if path == fp.wrapper and change != "home-alias":
            opens.append(True)
            if len(opens) == 1:
                if change == "edit": extra.write_text("FUTURE = 2\n")
                elif change == "add": (fp.a.package / "added.py").write_text("NEW = 2\n")
                elif change == "delete": extra.unlink()
                elif change == "replace":
                    replacement = fp.a.package / "replace.tmp"; replacement.write_text("FUTURE = 1\n"); replacement.replace(extra)
        return handle
    monkeypatch.setattr(Path, "open", opening)
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


@pytest.mark.parametrize("limit", ["file", "total", "entries", "directories", "depth", "files", "AST", "path-bindings"])
def test_fp_17_declared_bounds_refuse_without_partial_digest(fp, limit):
    if limit == "file":
        (fp.a.package / "large.py").write_bytes(b"x" * (fp.a.module.MAX_JSON_BYTES + 1))
    elif limit == "total":
        for i in range(33): (fp.a.package / f"large{i}.py").write_bytes(b"x" * (1024 * 1024))
    elif limit == "entries":
        # Global budget, below the unchanged native per-directory observer bound.
        for i in range(32):
            folder = fp.a.package / f"entries{i}"
            folder.mkdir()
            for j in range(130): (folder / f"entry{j}.txt").touch()
    elif limit == "directories":
        for i in range(257): (fp.a.package / f"dir{i}").mkdir()
    elif limit == "depth":
        path = fp.a.package
        for i in range(17): path = path / f"layer{i}"; path.mkdir()
    elif limit == "files":
        for i in range(1025): (fp.a.package / f"extra{i}.py").write_text("# source\n")
    elif limit == "AST":
        fp.wrapper.write_text("\n".join(f"import os as alias{i}" for i in range(1100)) + "\n" + launcher(fp.a.scripts))
    else:
        fp.wrapper.write_text(launcher(fp.a.scripts).replace("from lean_slots.cli", "\n".join(f"X{i} = ROOT / 'part{i}'" for i in range(9)) + "\nfrom lean_slots.cli"))
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


def test_fp_18_stale_down_running_and_doctor_are_actual_distinct_consumers(fp):
    path = owned(fp.sup, fp.host, "proxy", 1, 840301)
    original = path.read_bytes()
    assert fp.sup.process_state("proxy", 1) == "running"
    target = fp.a.package / "state.py"
    with seed_journal.seeded_mutation(target, target.read_bytes() + b"\n# source changed\n", reason="doctor source consumer"):
        controller_module = sys.modules[fp.a.module.Inventory.__module__.rsplit(".", 1)[0] + ".controller"]
        ctl = controller_module.Controller(fp.sup.inventory)
        detail = " ".join(str(x) for x in ctl.doctor().get("checks", []))
        assert "stale" in detail
        assert fp.sup.process_state("proxy", 1) == "stale" and path.read_bytes() == original
    assert fp.sup.process_state("proxy", 1) == "running"
    fp.host.remove(840301)
    assert fp.sup.process_state("proxy", 1) == "down"
    assert path.read_bytes() == original and not fp.host.signals


def test_fp_19_old_config_command_auth_slot_launcher_inputs_preserved(fp):
    first = fp.sup._runtime_fingerprint("proxy", 1)
    fp.sup.inventory.raw["server"]["client_auth"] = "bearer"
    assert fp.sup._runtime_fingerprint("proxy", 1) != first
    fp.sup.inventory.raw["server"].pop("client_auth")
    assert fp.sup._runtime_fingerprint("proxy", 1) == first
    command = fp.sup.proxy_command(1) + ["declared-different-command"]
    assert fp.sup._runtime_fingerprint("proxy", 1, command) != first
    assert fp.sup._runtime_fingerprint("proxy", 2) != first
    fp.wrapper.write_text("# changed launcher bytes\n" + fp.wrapper.read_text())
    assert fp.sup._runtime_fingerprint("proxy", 1) != first


def test_fp_20_foreign_genuine_peer_origin_refuses(fp):
    name = fp.a.module.__name__.rsplit(".", 1)[0] + ".foreign"
    spec = importlib.util.spec_from_file_location(name, fp.b.package / "host_limits.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    with pytest.raises(fp.a.module.SlotError, match="roots disagree"):
        fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


@pytest.mark.parametrize("method", ["exists", "is_file"])
def test_fp_21_guard_alias_and_bounded_literal_diagnostics(fp, method):
    text = launcher(fp.a.scripts, aliases=True, message='f"Selected {ALIAS_SELECTED}"')
    text = text.replace('if not (SELECTED_SCRIPTS', 'ALIAS_SELECTED = SELECTED_SCRIPTS\nif not (SELECTED_SCRIPTS')
    text = text.replace(".is_file()", f".{method}()")
    fp.wrapper.write_text(text)
    assert fp.sup._runtime_fingerprint("proxy", 1)
    fp.wrapper.write_text(launcher(fp.a.scripts, message=repr("line one\nline two")))
    assert fp.sup._runtime_fingerprint("proxy", 1)
    fp.wrapper.write_text(launcher(fp.a.scripts, message=repr("x" * 4097)))
    with pytest.raises(fp.a.module.SlotError, match="diagnostic exceeds"):
        fp.sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


@pytest.mark.parametrize("bad", ["relative-selector", "relative-literal", "parent-chain", "parent-index", "malformed-source", "missing-cli"])
def test_fp_22_remaining_path_source_refusals(fp, monkeypatch, bad):
    if bad == "relative-selector":
        text = launcher(fp.a.scripts, selector=True)
        monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "relative/shared")
    elif bad == "relative-literal":
        text = launcher(fp.a.scripts).replace(repr(str(fp.a.scripts)), repr("relative/scripts"))
    elif bad == "parent-chain":
        text = launcher(fp.a.scripts).replace('ROOT = Path(__file__).resolve().parents[1]',
                                               'ROOT = Path(__file__).resolve().parent.parent.parent.parent.parent')
    elif bad == "parent-index":
        text = launcher(fp.a.scripts).replace('parents[1]', 'parents[5]')
    elif bad == "malformed-source":
        text = "def broken(\n"
    else:
        text = launcher(fp.a.scripts); (fp.a.package / "cli.py").unlink()
    fp.wrapper.write_text(text)
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


def test_fp_23_deterministic_native_membership_order_and_old_inputs(fp, monkeypatch):
    first = fp.sup._runtime_fingerprint("proxy", 1)
    original = os.scandir
    class ReversedEntries:
        def __init__(self, path):
            with original(path) as stream:
                self.entries = list(stream)
        def __enter__(self):
            return iter(reversed(self.entries))
        def __exit__(self, *args):
            return False
    monkeypatch.setattr(os, "scandir", ReversedEntries)
    assert fp.sup._runtime_fingerprint("proxy", 1) == first
    instructions = fp.sup.inventory.raw["server"]["instructions"]
    fp.sup.inventory.raw["server"]["instructions"] = "new declared instruction"
    assert fp.sup._runtime_fingerprint("proxy", 1) != first
    fp.sup.inventory.raw["server"]["instructions"] = instructions
    assert fp.sup._runtime_fingerprint("backend", 1) != first
    role = fp.sup.inventory.raw["repo_role"]
    fp.sup.inventory.raw["repo_role"] = "another-generic-role"
    assert fp.sup._runtime_fingerprint("proxy", 1) != first
    fp.sup.inventory.raw["repo_role"] = role
    port = fp.sup.inventory.raw["slots"]["1"]["proxy_port"]
    fp.sup.inventory.raw["slots"]["1"]["proxy_port"] = port + 50
    assert fp.sup._runtime_fingerprint("proxy", 1) != first
    fp.sup.inventory.raw["slots"]["1"]["proxy_port"] = port


def test_fp_24_actual_sourceless_import_is_not_a_source_origin(fp, tmp_path):
    import importlib.machinery
    import py_compile
    name = fp.a.module.__name__.rsplit(".", 1)[0] + ".byte_supervisor"
    target = tmp_path / "supervisor.pyc"
    py_compile.compile(str(fp.a.package / "supervisor.py"), cfile=str(target), doraise=True)
    loader = importlib.machinery.SourcelessFileLoader(name, str(target))
    spec = importlib.util.spec_from_loader(name, loader)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    loader.exec_module(module)
    sup = module.Supervisor(fp.sup.inventory)
    with pytest.raises(module.SlotError, match="origin unavailable"):
        sup._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


def test_fp_25_external_capture_unavailable_is_typed_and_readonly(fp, monkeypatch):
    path = owned(fp.sup, fp.host, "proxy", 1, 840401)
    original = path.read_bytes()
    def unavailable():
        raise RuntimeError("external environment changed during copy")
    monkeypatch.setattr(os.environ, "copy", unavailable)
    assert fp.sup.process_state("proxy", 1) == "unavailable"
    item = fp.sup.status()["slots"][0]["resources"]["proxy"]
    assert any(x["operation"] == "runtime-environment-capture" and x["error_class"] == "RuntimeError"
               for x in item["observations"])
    with pytest.raises(fp.a.module.SlotError, match="capture unavailable"):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp, original)


def test_fp_26_genuine_foreign_inventory_source_is_not_omitted(fp):
    other_state = sys.modules[fp.b.module.Inventory.__module__]
    other_inventory = other_state.Inventory.load(fp.sup.inventory.source)
    incoherent = fp.a.module.Supervisor(other_inventory)
    with pytest.raises(fp.a.module.SlotError, match="roots disagree"):
        incoherent._runtime_fingerprint("proxy", 1)
    no_new_effects(fp)


@pytest.mark.parametrize("kind", ["proxy", "backend"])
def test_fp_27_captured_HOME_prediction_ignores_ambient_B(fp, monkeypatch, kind):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True, home=True))
    monkeypatch.setenv("HOME", str(fp.a.home))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", "~/shared-source")
    capture = os.environ.copy()
    command = fp.sup.proxy_command(1) if kind == "proxy" else fp.sup.backend_command(1)
    expected = fp.sup._runtime_inputs(kind, 1, command, capture)
    monkeypatch.setenv("HOME", str(fp.b.home))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.b.scripts.parent))
    try:
        observed = fp.sup._runtime_inputs(kind, 1, command, capture)
    except fp.a.module.SlotError as exc:
        observed = ("typed-refusal", str(exc))
    # This is a real captured image/genuine A source; ambient B cannot alter its result.
    assert observed == expected
    value = payload(fp, kind, capture)["sources"]["routing"]
    assert value["selected_package"] == str(fp.a.package.resolve())
    assert next(x for x in value["transforms"] if x["branch"] == "captured-home")["HOME"] == str(fp.a.home)
    no_new_effects(fp)


def test_fp_28_slot_input_is_distinct_even_with_declared_same_command(fp):
    command = fp.sup.proxy_command(1)
    first = fp.sup._runtime_fingerprint("proxy", 1, command)
    second = fp.sup._runtime_fingerprint("proxy", 2, command)
    assert first != second
    no_new_effects(fp)


def test_fp_29_real_relative_route_cannot_inherit_parent_cwd(fp):
    relative = os.path.relpath(fp.a.scripts, Path.cwd())
    fp.wrapper.write_text(launcher(fp.a.scripts).replace(repr(str(fp.a.scripts)), repr(relative)))
    assert not Path(relative).is_absolute() and (Path.cwd() / relative).resolve() == fp.a.scripts.resolve()
    with pytest.raises(fp.a.module.SlotError):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)

def test_fp_30_selected_genuine_B_cannot_match_parent_A(fp, monkeypatch):
    fp.wrapper.write_text(launcher(fp.a.scripts, selector=True))
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.b.scripts.parent))
    assert (fp.b.package / "__init__.py").is_file() and (fp.b.package / "cli.py").is_file()
    with pytest.raises(fp.a.module.SlotError, match="roots disagree"):
        fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
    no_new_effects(fp)


@pytest.mark.parametrize("expression", ['Path("/").parents[0]', 'Path("/x").parents[3]'])
@pytest.mark.parametrize("consumer", ["status", "spawn"])
def test_fp_31_missing_parent_is_typed_and_preserves_populated_resources(fp, expression, consumer):
    path = owned(fp.sup, fp.host, "proxy", 1, 840501)
    backend = owned(fp.sup, fp.host, "backend", 1, 840502)
    before, backend_before = path.read_bytes(), backend.read_bytes()
    fp.wrapper.write_text(launcher(fp.a.scripts).replace(
        'ROOT = Path(__file__).resolve().parents[1]', 'ROOT = ' + expression))
    if consumer == "status":
        try:
            observed = fp.sup.process_state("proxy", 1)
        except IndexError as exc:
            observed = ("unexpected-index-error", str(exc))
        assert observed == "unavailable"
    else:
        try:
            fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
            observed = ("unexpected-launch", "")
        except fp.a.module.SlotError as exc:
            observed = ("typed-refusal", str(exc))
        except IndexError as exc:
            observed = ("unexpected-index-error", str(exc))
        assert observed[0] == "typed-refusal" and "parent index" in observed[1]
    item = fp.sup.status()["slots"][0]["resources"]["proxy"]
    assert item["state"] == "unavailable"
    assert any(x["operation"] == "runtime-source-template" and "parent index" in x["diagnostic_text"]
               for x in item["observations"])
    assert backend.read_bytes() == backend_before
    assert 1 in fp.sup.capacity_census()["reserved_physical_slots"]
    no_new_effects(fp, before)


@pytest.mark.parametrize("count", [1024, 1025])
def test_fp_32_loaded_origin_alias_budget_is_real_and_preserves_resources(fp, monkeypatch, count):
    path = owned(fp.sup, fp.host, "proxy", 1, 840601)
    backend = owned(fp.sup, fp.host, "backend", 1, 840602)
    before, backend_before = path.read_bytes(), backend.read_bytes()
    prefix = fp.a.module.__name__.rsplit(".", 1)[0]
    existing = sum(name == prefix or name.startswith(prefix + ".") for name in sys.modules)
    for index in range(count - existing):
        name = prefix + ".genuine_alias_" + str(index)
        spec = importlib.util.spec_from_file_location(name, fp.a.package / "host_limits.py")
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    assert sum(name == prefix or name.startswith(prefix + ".") for name in sys.modules) == count
    original_stat = os.stat
    source_stats = []
    def stat(value, *args, **kwargs):
        if Path(value).is_relative_to(fp.a.package):
            source_stats.append(str(value))
        return original_stat(value, *args, **kwargs)
    monkeypatch.setattr(os, "stat", stat)
    observed = fp.sup.process_state("proxy", 1)
    if count == 1024:
        assert observed == "running" and source_stats
    else:
        assert observed == "unavailable" and source_stats == []
        item = fp.sup.status()["slots"][0]["resources"]["proxy"]
        assert any(x["operation"] == "runtime-source-origin" and "origin count" in x["diagnostic_text"]
                   for x in item["observations"])
        with pytest.raises(fp.a.module.SlotError, match="origin count"):
            fp.sup._spawn("proxy", 1, fp.sup.proxy_command(1), 29001)
        assert source_stats == []
    assert backend.read_bytes() == backend_before
    assert 1 in fp.sup.capacity_census()["reserved_physical_slots"]
    no_new_effects(fp, before)


@pytest.mark.parametrize("expression", ['Path("/x").parents[0]', 'Path("/x/y").parents[1]'])
def test_fp_33_available_shallow_parent_keeps_actual_launch(fp, expression):
    fp.wrapper.write_text(launcher(fp.a.scripts).replace(
        'ROOT = Path(__file__).resolve().parents[1]', 'ROOT = ' + expression))
    actual = payload(fp)["sources"]["routing"]
    assert actual["inventory_default"]["default"] == "/config/lean-slots.downstream.json"
    assert actual["inventory_source"] == str(fp.sup.inventory.source)
    expected = fp.sup.proxy_command(1)
    fp.sup._spawn("proxy", 1, expected, 29001)
    assert len(fp.host.launches) == 1 and not fp.host.signals
    assert fp.sup.process_state("proxy", 1) == "running"


@pytest.mark.parametrize("kind", ["proxy", "backend"])
@pytest.mark.parametrize("populated", [False, True])
@pytest.mark.parametrize("recipe", [
    "inline-expand", "alias-expand", "inline-resolve", "alias-resolve",
    "selected-fallback-expand", "selected-fallback-resolve", "default-propagation",
    "ignored-fallback-repeat",
])
def test_fp_34_same_operand_string_provenance_refuses_actual_consumers(fp, monkeypatch, kind, populated, recipe):
    monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.a.scripts.parent))
    monkeypatch.delenv("PROVENANCE_SOURCE", raising=False)
    text = launcher(fp.a.scripts, selector=True, home=True)
    if recipe.startswith("inline"):
        suffix = ".expanduser().resolve()" if recipe.endswith("expand") else ".resolve()"
        text = text.replace('SHARED / "scripts"', 'Path(str(SHARED))' + suffix + ' / "scripts"')
    elif recipe.startswith("alias"):
        suffix = ".expanduser().resolve()" if recipe.endswith("expand") else ".resolve()"
        text = text.replace('SELECTED_SCRIPTS =', 'REWRAPPED = Path(str(SHARED))\nSELECTED_SCRIPTS =')
        text = text.replace('SHARED / "scripts"', 'REWRAPPED' + suffix + ' / "scripts"')
    elif recipe.startswith("selected-fallback"):
        suffix = ".expanduser().resolve()" if recipe.endswith("expand") else ".resolve()"
        text = text.replace('SHARED / "scripts"', 'Path(os.environ.get("PROVENANCE_SOURCE", str(SHARED)))' + suffix + ' / "scripts"')
    elif recipe == "default-propagation":
        monkeypatch.delenv("LEAN_SLOT_CONFIG", raising=False)
        text = launcher(fp.a.scripts, selector=True, home=True, default=False)
        text = text.replace('SELECTED_SCRIPTS =', 'os.environ.setdefault("LEAN_SLOT_CONFIG", str(SHARED))\nREWRAPPED = Path(os.environ.get("LEAN_SLOT_CONFIG"))\nSELECTED_SCRIPTS =')
        text = text.replace('SHARED / "scripts"', 'REWRAPPED.expanduser().resolve() / "scripts"')
    else:
        # Even an inactive default is evaluated before get sees its present selector.
        monkeypatch.setenv("PROVENANCE_SOURCE", str(fp.a.scripts.parent))
        text = text.replace('SHARED / "scripts"', 'Path(os.environ.get("PROVENANCE_SOURCE", str(Path(str(SHARED)).expanduser().resolve()))) / "scripts"')
    fp_36_refusal_effects(fp, text, kind, populated, "runtime-source-template")


@pytest.mark.parametrize("kind", ["proxy", "backend"])
@pytest.mark.parametrize("populated", [False, True])
@pytest.mark.parametrize("recipe", ["join", "str", "resolve", "expand", "alias", "selected-fallback", "ignored-default", "ignored-selector"])
def test_fp_35_cumulative_parent_recipe_refuses_actual_consumers(fp, monkeypatch, kind, populated, recipe):
    four = 'Path(__file__).resolve().parents[3]'
    expressions = {
        "join": '(' + four + ' / "child").parent',
        "str": 'Path(str(' + four + ')).parent',
        "resolve": '(' + four + ').resolve().parent',
        "expand": '(' + four + ').expanduser().resolve().parent',
        "alias": '(ROOT_PART / "child").parent',
        "selected-fallback": 'Path(os.environ.get("PROVENANCE_SOURCE", str(' + four + '))).parent',
        "ignored-default": 'Path(__file__).resolve().parents[1]',
        "ignored-selector": 'Path(__file__).resolve().parents[1]',
    }
    monkeypatch.delenv("PROVENANCE_SOURCE", raising=False)
    text = launcher(fp.a.scripts).replace('ROOT = Path(__file__).resolve().parents[1]', 'ROOT = ' + expressions[recipe])
    if recipe == "alias":
        text = text.replace('ROOT =', 'ROOT_PART = ' + four + '\nROOT =')
    elif recipe == "ignored-default":
        monkeypatch.setenv("LEAN_SLOT_CONFIG", "already-present")
        text = text.replace('str(ROOT / "config" / "lean-slots.downstream.json")', 'str((' + four + ' / "child").parent)')
    elif recipe == "ignored-selector":
        monkeypatch.setenv("PROVENANCE_SOURCE", str(fp.a.scripts))
        text = text.replace('SELECTED_SCRIPTS = Path(' + repr(str(fp.a.scripts)) + ')',
                            'SELECTED_SCRIPTS = Path(os.environ.get("PROVENANCE_SOURCE", str((' + four + ' / "child").parent)))')
    fp_36_refusal_effects(fp, text, kind, populated, "runtime-source-template")


def fp_36_refusal_effects(fp, text, kind, populated, operation):
    # All verdicts come from the genuinely imported production module and actual
    # temporary launcher; this helper only supplies independent artifact oracles.
    records = {}
    if populated:
        for member, pid in (("proxy", 840701), ("backend", 840702)):
            path = owned(fp.sup, fp.host, member, 1, pid)
            records[path] = path.read_bytes()
    fp.wrapper.write_text(text)
    command = fp.sup.proxy_command(1) if kind == "proxy" else fp.sup.backend_command(1)
    before_members = {path: path.read_bytes() for path in fp.sup.inventory.state_root.rglob("*") if path.is_file()}
    try:
        fp.sup._runtime_fingerprint(kind, 1)
        observed = "accepted"
    except fp.a.module.SlotError as exc:
        observed = "typed-refusal"
        assert any(x.state == "unavailable" and x.operation == operation for x in exc.observations)
    assert observed == "typed-refusal"
    if populated:
        assert fp.sup.process_state(kind, 1) == "unavailable"
        item = fp.sup.status()["slots"][0]["resources"][kind]
        assert item["state"] == "unavailable"
        assert any(x["operation"] == operation for x in item["observations"])
        assert 1 in fp.sup.capacity_census()["reserved_physical_slots"]
    try:
        fp.sup._spawn(kind, 1, command, int(fp.sup.inventory.slot(1)[kind + "_port"]))
        observed = "unexpected-launch"
    except fp.a.module.SlotError as exc:
        observed = "typed-refusal"
        assert any(x.state == "unavailable" and x.operation == operation for x in exc.observations)
    assert observed == "typed-refusal"
    assert {path: path.read_bytes() for path in fp.sup.inventory.state_root.rglob("*") if path.is_file()} == before_members
    assert all(path.read_bytes() == before for path, before in records.items())
    assert fp.host.launches == [] and fp.host.signals == []
    if not populated:
        assert not fp.sup.inventory.process_path(kind, 1).exists()


@pytest.mark.parametrize("kind", ["proxy", "backend"])
@pytest.mark.parametrize("recipe", ["join", "str", "resolve", "expand", "alias", "selected-fallback", "derived-expand", "fresh-selector"])
def test_fp_37_valid_provenance_recipe_preserves_actual_launch(fp, monkeypatch, kind, recipe):
    three = 'Path(__file__).resolve().parents[2]'
    expressions = {
        "join": '(' + three + ' / "child").parent',
        "str": 'Path(str(' + three + ')).parent',
        "resolve": '(' + three + ').resolve().parent',
        "expand": '(' + three + ').expanduser().resolve().parent',
        "alias": '(ROOT_PART / "child").parent',
        "selected-fallback": 'Path(os.environ.get("PROVENANCE_SOURCE", str(' + three + '))).parent',
        "derived-expand": '(' + three + ' / "child").parent.expanduser().resolve()',
        "fresh-selector": 'Path(__file__).resolve().parents[1]',
    }
    monkeypatch.delenv("PROVENANCE_SOURCE", raising=False)
    text = launcher(fp.a.scripts).replace('ROOT = Path(__file__).resolve().parents[1]', 'ROOT = ' + expressions[recipe])
    if recipe == "alias":
        text = text.replace('ROOT =', 'ROOT_PART = ' + three + '\nROOT =')
    elif recipe == "fresh-selector":
        monkeypatch.setenv("PROVENANCE_SOURCE", str(fp.a.scripts.parent))
        monkeypatch.setenv("EXAMPLE_SHARED_ROOT", str(fp.a.scripts.parent))
        text = launcher(fp.a.scripts, selector=True, home=True)
        text = text.replace('SHARED / "scripts"', 'Path(os.environ.get("PROVENANCE_SOURCE", str(SHARED))).expanduser().resolve() / "scripts"')
    fp.wrapper.write_text(text)
    expected_default = (fp.repo / "config" / "lean-slots.downstream.json" if recipe == "fresh-selector"
                        else fp.wrapper.resolve().parents[2 if recipe in {"join", "alias", "derived-expand"} else 3] / "config" / "lean-slots.downstream.json")
    routing = payload(fp, kind)["sources"]["routing"]
    assert routing["inventory_default"]["default"] == str(expected_default)
    assert routing["inventory_source"] == str(fp.sup.inventory.source)
    assert routing["selected_package"] == str(fp.a.package.resolve())
    assert isinstance(routing["inventory_default"]["default"], str)
    assert all(isinstance(x["selected"], str) and (x["fallback"] is None or isinstance(x["fallback"], str))
               for x in routing["selectors"])
    command = fp.sup.proxy_command(1) if kind == "proxy" else fp.sup.backend_command(1)
    capture = os.environ.copy()
    fp.sup._spawn(kind, 1, command, int(fp.sup.inventory.slot(1)[kind + "_port"]))
    assert len(fp.host.launches) == 1 and fp.host.signals == []
    assert fp.sup.process_state(kind, 1) == "running"
    record = fp.sup.inventory.process_path(kind, 1)
    before = record.read_bytes()
    assert fp.sup._runtime_fingerprint(kind, 1) == fp.sup._runtime_fingerprint(kind, 1)
    assert record.read_bytes() == before and os.environ == capture
