"""Every third-party module we import must be a DECLARED dependency.

WHY THIS FILE EXISTS
====================
`uv lock --upgrade` is ordinary hygiene — it is how security fixes arrive before Dependabot
files 28 alerts at once. But an upgrade may legitimately DROP a package: if nothing in
`pyproject.toml` asks for it, and the only reason it was present is that some other package
happened to depend on it, a newer release of that package removes it from the graph and it
silently disappears from the environment.

Measured 2026-08-11, the day this file was written:

  * `uv lock --upgrade` removed `pytest-timeout`. It was reachable only via `kaleido`.
    Harmless here -- nothing referenced it -- but nothing said so in advance either.
  * `scripts/provenance_dashboard.py` does `from markupsafe import escape` to HTML-escape
    reflected input. `markupsafe` was reachable only via flask / jinja2 / werkzeug /
    nbconvert. Any upgrade dropping it breaks an XSS control at import time.
  * `scripts/extract_sigma_symbolic.py` does `from tqsim import AnyonicCircuit` at module
    level. `tqsim` was neither declared NOR installed -- that script already could not run.

The first is the hazard, the second is the same hazard aimed at something load-bearing, and
the third is what the hazard looks like after it has already fired. The rule that kills all
three: **if we import it, we declare it.** Then an upgrade cannot take it away without the
resolver telling us, and `uv sync` on a clean machine installs it.

This does NOT check that a declared package is installed -- declaration is the invariant, and
an optional extra (`gpu`, `mlx`, `fermion-bag`) is deliberately not installed by default.

BLIND SPOT, stated rather than implied: a pytest plugin is activated by INSTALLATION, not by
import, so no import scan can see one. `pytest-timeout` was exactly that shape. If this repo
ever depends on plugin behaviour (a `--timeout` flag in `addopts`, a `pytest.mark.timeout`),
that plugin must be declared by hand -- nothing here will notice its absence. As of writing,
`addopts` and `markers` reference no third-party plugin.

Run: uv run python -m pytest tests/test_dependency_declaration.py -v
"""
import ast
import importlib.metadata as md
import os
import re
import sys
import tomllib
from functools import lru_cache
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
SCAN_ROOTS = ("src", "scripts", "tests")
SKIP_PARTS = {".venv", ".lake", "node_modules", "__pycache__", ".git", "worktrees"}

# Import name -> distribution name, where they differ and installed metadata cannot tell us
# (the package may legitimately be un-installed, e.g. an optional extra).
ALIASES = {
    "tqsim": "tqsim",
    "pdfminer": "pdfminer-six",
    "yaml": "pyyaml",
    "PIL": "pillow",
    "bs4": "beautifulsoup4",
    "sk_eft_rhmc": "sk-eft-rhmc",
}


# Modules that CANNOT be declared, each with the reason. This is not a convenience list --
# an entry must be a package that is genuinely unresolvable against this project's pins, and
# its consumer must fail with an actionable message rather than a bare ImportError.
UNDECLARABLE = {
    # TQSim 0.0.2 pins numpy>=1.23.4,<2.0.0; this project requires numpy>=2.0. `uv lock`
    # rejects the combination outright, so it cannot be an extra either. The one consumer,
    # scripts/extract_sigma_symbolic.py, is a one-shot σ-matrix extraction that must be run
    # in a separate numpy<2 environment; its committed output is what the repo depends on.
    "tqsim": "pins numpy<2.0, irreconcilable with this project's numpy>=2.0",
}


def _norm(name: str) -> str:
    """PEP 503 style normalization -- `pdfminer.six`, `pdfminer_six`, `pdfminer-six` agree."""
    return re.sub(r"[-_.]+", "-", name).strip().lower()


def _declared() -> set[str]:
    """Every distribution named anywhere in pyproject: main, every extra, every dep group."""
    pp = tomllib.loads((REPO / "pyproject.toml").read_text())
    out: set[str] = set()

    def add(specs):
        for s in specs:
            if isinstance(s, str):
                out.add(_norm(re.split(r"[<>=!~\[;]", s)[0]))

    add(pp["project"]["dependencies"])
    for group in pp["project"].get("optional-dependencies", {}).values():
        add(group)
    for group in pp.get("dependency-groups", {}).values():
        add(group)
    return out


def _walk_py(base: Path):
    """Yield every .py under `base`, PRUNING skip dirs as we descend.

    `rglob` would descend into .venv/ and .lake/ and filter afterwards, which costs tens of
    seconds here -- long enough to matter in the fast suite this test runs in."""
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in SKIP_PARTS]
        for fn in filenames:
            if fn.endswith(".py"):
                yield Path(dirpath) / fn


@lru_cache(maxsize=1)
def _local_module_names() -> frozenset[str]:
    """Names importable because they live in THIS repo -- `pythonpath = ["."]` plus the fact
    that scripts/ modules import each other as bare top-level names."""
    names: set[str] = set()
    for p in _walk_py(REPO):
        names.add(p.stem)
        names.add(p.parent.name)
    return frozenset(names)


def _imports() -> dict[str, set[str]]:
    """top-level imported module -> the repo files importing it."""
    found: dict[str, set[str]] = {}
    for root in SCAN_ROOTS:
        for py in _walk_py(REPO / root):
            try:
                tree = ast.parse(py.read_text(encoding="utf-8"))
            except (SyntaxError, UnicodeDecodeError):
                continue
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    mods = [a.name.split(".")[0] for a in node.names]
                elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                    mods = [node.module.split(".")[0]]
                else:
                    continue
                for m in mods:
                    found.setdefault(m, set()).add(str(py.relative_to(REPO)))
    return found


def _dist_for(module: str) -> str:
    """Best-effort import-name -> distribution-name."""
    if module in ALIASES:
        return _norm(ALIASES[module])
    try:
        owners = md.packages_distributions().get(module)
    except Exception:                                    # pragma: no cover - metadata read
        owners = None
    return _norm(owners[0]) if owners else _norm(module)


@lru_cache(maxsize=1)
def _third_party_imports_cached() -> tuple:
    """Imports that are neither stdlib nor satisfied by a file in this repo."""
    stdlib = set(sys.stdlib_module_names)
    local = _local_module_names()
    return tuple((m, tuple(sorted(f))) for m, f in _imports().items()
                 if m not in stdlib and m not in local)


def third_party_imports() -> dict[str, set[str]]:
    """Imports that are neither stdlib nor satisfied by a file in this repo."""
    return {m: set(f) for m, f in _third_party_imports_cached()}


def test_every_third_party_import_is_declared():
    """The invariant. An undeclared import works only by accident -- it is present because
    something else pulled it in, and it leaves the moment that something else stops."""
    declared = _declared()
    offenders = {
        m: sorted(files)
        for m, files in third_party_imports().items()
        if m not in UNDECLARABLE
        and _dist_for(m) not in declared
        and _norm(m) not in declared
    }
    assert not offenders, (
        "third-party module imported but NOT declared in pyproject.toml. It is in the "
        "environment only because some other package depends on it, so `uv lock --upgrade` "
        "can remove it without warning. Declare it (main deps, or an optional extra if the "
        "consumer is optional):\n  "
        + "\n  ".join(f"{m} <- {', '.join(f[:3])}" for m, f in sorted(offenders.items()))
    )


def test_scan_actually_reaches_the_codebase():
    """Seam guard. Every assertion above is vacuous if the walk finds nothing -- a moved
    directory or a tightened skip-list would turn this file green while checking zero code.
    Pin the floor to the population, not to the violations."""
    imports = third_party_imports()
    assert len(imports) >= 15, (
        f"only {len(imports)} third-party imports found across {SCAN_ROOTS} -- the scan roots "
        "or the local-module filter are wrong; this file is not checking anything"
    )
    for anchor in ("numpy", "pytest"):
        assert anchor in imports, f"{anchor!r} not seen -- the import walk is broken"


def test_undeclarable_entries_are_live_and_reasoned():
    """The exemption list is the one place this guard can be defeated, so it is itself
    guarded: an entry must still be imported somewhere (or it is stale scar tissue), and it
    must carry a reason. Without this, `UNDECLARABLE` becomes the drawer that anything
    inconvenient gets swept into."""
    imported = third_party_imports()
    stale = [m for m in UNDECLARABLE if m not in imported]
    assert not stale, (
        "UNDECLARABLE names a module nothing imports any more -- delete the entry:\n  "
        + "\n  ".join(stale))
    unreasoned = [m for m, why in UNDECLARABLE.items() if not str(why).strip()]
    assert not unreasoned, f"UNDECLARABLE entry with no stated reason: {unreasoned}"


@pytest.mark.parametrize("module, dist", [("pdfminer", "pdfminer-six"), ("yaml", "pyyaml")])
def test_alias_map_resolves_renamed_distributions(module, dist):
    """`pdfminer` resolves to the distribution `pdfminer-six`; a naive name match would report
    a false violation and train the reader to ignore this test."""
    assert _dist_for(module) == _norm(dist)
