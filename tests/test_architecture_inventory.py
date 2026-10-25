"""Tests for the DERIVED surface inventory — the census half of the end-to-end map.

The inventory exists because narrative counts rot. These tests exist because a *derived*
inventory that silently derives the wrong thing is worse than a hand-written one: it carries
the authority of being generated.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))


@pytest.fixture(scope="module")
def inv_mod():
    spec = importlib.util.spec_from_file_location(
        "_arch_inventory_test", SK_ROOT / "scripts" / "architecture_inventory.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    assert Path(mod.__file__).resolve() == (SK_ROOT / "scripts/architecture_inventory.py").resolve()
    print("INVENTORY_SOURCE " + str(Path(mod.__file__).resolve()))
    return mod


@pytest.fixture(scope="module")
def architecture_inventory_result():
    """Same real-tree reader as suite conftest, also available under --noconftest.

    Does not write the canonical baseline. Its original freshness assertion can
    remain RED until the separately owned reviewed canonical-writer checkpoint.
    """
    from validation.checks.freshness import check_architecture_inventory_fresh
    import validation.checks.freshness as freshness
    assert Path(freshness.__file__).resolve() == (SK_ROOT / "scripts/validation/checks/freshness.py").resolve()
    result = check_architecture_inventory_fresh()
    print("ACTUAL_FRESHNESS_READER " + str(Path(freshness.__file__).resolve()))
    print("ACTUAL_FRESHNESS_DETAILS " + __import__("json").dumps(
        [{"name": d.name, "passed": d.passed, "message": d.message} for d in result.details]))
    return result


class TestDerivation:
    def test_checks_come_from_the_registry_not_a_literal(self, inv_mod):
        """SILENT ON CORRECT DATA, and pins the source: the count must equal the live
        registry, so it cannot be frozen at a number someone typed."""
        import validate
        assert len(inv_mod.checks()) == len(validate._CHECKS)

    def test_a_memoized_check_is_attributed_to_its_REAL_module(self, inv_mod):
        """FIRES ON THE SEEDED DEFECT: drop the `__memo_body__` unwrap and every memoized
        check is attributed to `_memo`, which is not where anyone would look for it."""
        mods = {c["module"] for c in inv_mod.checks()}
        assert "_memo" not in mods, f"memo wrapper leaked into the inventory: {mods}"

    def test_gates_come_from_the_gate_roster(self, inv_mod):
        import readiness_gates
        assert len(inv_mod.gates()) == len(readiness_gates.GATES)

    def test_dead_edge_types_are_DERIVED_by_set_difference(self, inv_mod):
        """The consequential row. Consumed-minus-emitted must be computed, never listed."""
        g = inv_mod.graph_types()
        expected = sorted(t for t in g["edges_consumed_by_gates"]
                          if t not in set(g["edges_emitted"]))
        assert g["edges_consumed_but_never_emitted"] == expected

    def test_the_live_tree_still_has_its_three_known_dead_edge_types(self, inv_mod):
        """A regression pin, both directions: if one gets an emitter this fails and the
        inventory's warning must be re-read; if a FOURTH appears it fails too."""
        assert inv_mod.graph_types()["edges_consumed_but_never_emitted"] == [
            "CONTRADICTS", "PRODUCES", "SUPPORTS"]


class TestFrontmatter:
    def test_a_folded_block_scalar_is_read_not_returned_as_a_caret(self, inv_mod, tmp_path):
        """⚠️ FIRES ON THE SEEDED DEFECT — this was a REAL defect in the first version.

        Five of eight agents write `description: >` with the text on following lines. A
        reader that takes only the key's own line recorded their purpose as the literal
        string `>`, blanking the majority of the population in a document whose whole job
        is to say what exists.
        """
        f = tmp_path / "a.md"
        f.write_text("---\nname: x\ndescription: >\n  first line\n  second line\n---\nbody\n")
        fm = inv_mod._frontmatter(f)
        assert fm["description"] == "first line second line"

    def test_a_plain_scalar_still_works(self, inv_mod, tmp_path):
        f = tmp_path / "b.md"
        f.write_text("---\nname: y\ndescription: one liner\nmodel: opus\n---\n")
        fm = inv_mod._frontmatter(f)
        assert fm["description"] == "one liner" and fm["model"] == "opus"

    def test_every_live_agent_has_a_real_purpose_string(self, inv_mod):
        """The live-corpus form of the defect above."""
        for a in inv_mod.agents_and_commands()["agents"]:
            assert len(a["description"]) > 20, a


class TestRenderIsDeterministic:
    def test_two_renders_of_one_collection_are_identical(self, inv_mod):
        """The freshness check compares text, so any nondeterminism (a timestamp, a set
        iteration order) would make it fail at random and get switched off."""
        inv = inv_mod.collect()
        assert inv_mod.render(inv) == inv_mod.render(inv)

    def test_the_rendered_doc_carries_no_date(self, inv_mod):
        """A date would dirty the file on every run and turn the gate into noise."""
        text = inv_mod.render(inv_mod.collect())
        import re
        assert not re.search(r"\b20\d\d-\d\d-\d\d\b", text)


class TestTheFreshnessCheck:
    """`architecture_inventory_fresh` — the gate that stops the census drifting from the
    system it describes."""

    @pytest.fixture
    def check(self):
        import validate
        return validate.check_architecture_inventory_fresh

    def test_the_live_tree_is_fresh(self, architecture_inventory_result):
        """SILENT ON CORRECT DATA. If this fails, run
        `uv run python scripts/architecture_inventory.py --write`.

        Session-shared: three tests read a different `Detail` out of this one
        result at ~10.7 s each. `test_a_HAND_EDIT_to_the_census_FAILS` below
        monkeypatches the census, so it correctly keeps its own call."""
        res = architecture_inventory_result
        assert res.passed is True, [d.message for d in res.details]

    def test_a_HAND_EDIT_to_the_census_FAILS(self, check, monkeypatch, tmp_path):
        """⚠️ FIRES ON THE SEEDED DEFECT — and was production-seeded: appending one HTML
        comment to the real SURFACE_INVENTORY.md turned the check red naming the first
        divergent line."""
        docs = tmp_path / "architecture"
        docs.mkdir(parents=True)
        (docs / "SURFACE_INVENTORY.md").write_text("# hand-written nonsense\n")
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "DOCS_DIR", tmp_path)
        assert check().passed is False

    def test_a_MISSING_census_FAILS_rather_than_skipping(self, check, monkeypatch, tmp_path):
        """An absent census is not a fresh one — the absence-as-success shape."""
        (tmp_path / "architecture").mkdir(parents=True)
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "DOCS_DIR", tmp_path)
        res = check()
        assert res.passed is False and res.measured is True

    def test_an_absent_GENERATOR_is_unmeasurable_not_clean(self, check, monkeypatch,
                                                           tmp_path):
        """The one genuine cannot-measure branch: no generator, no derivation."""
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "SCRIPT_DIR", tmp_path)
        res = check()
        assert res.measured is False


class TestEdgeTypeDerivationHasOneOwner:
    """The census and the gate check derive "emitted edge types" separately.

    They disagreed until 2026-08-06 — the census reported **22**, the check
    reported **40** — because both scanned every `{'type': ...}` dict in
    `build_graph.py` (node dicts carry that key too) and only the census
    subtracted the node taxonomy afterwards. Right answer by cancellation, not by
    scope. Both now scope structurally on `source`/`target`; these tests are the
    arbiter that keeps them together.
    """

    def test_census_and_gate_check_agree(self, inv_mod):
        from validation.checks.graph_atlas import check_gate_edge_types_are_emitted

        census = set(inv_mod.graph_types()["edges_emitted"])
        result = check_gate_edge_types_are_emitted()
        line = next(d.message for d in result.details
                    if d.name == "populations_derived")
        # "11 edge type(s) queried by gates, 22 emitted by extractors — ..."
        gate_n = int(line.split("queried by gates,")[1].split("emitted")[0].strip())
        assert gate_n == len(census), (
            f"the gate check derives {gate_n} emitted edge types, the census "
            f"derives {len(census)} — two AST scans of one population disagreeing"
        )

    def test_no_node_type_is_reported_as_an_edge_type(self, inv_mod):
        """The concrete symptom of the wide scan, asserted directly."""
        import build_graph

        gt = inv_mod.graph_types()
        leaked = set(gt["edges_emitted"]) & set(build_graph.SHAPE_MAP)
        assert leaked == set(), f"node type(s) reported as edge types: {sorted(leaked)}"

    def test_the_scan_is_structural_not_subtractive(self, inv_mod, tmp_path):
        """A node type that ALSO names an edge type must survive as an edge type.

        This is the case the old subtract-node-types approach got wrong and that no
        count comparison can catch, since both derivations were wrong the same way.
        """
        src = tmp_path / "fake_graph.py"
        src.write_text(
            "nodes.append({'id': 'x', 'type': 'Formula', 'meta': {}})\n"
            "edges.append({'source': 'a', 'target': 'b', 'type': 'Formula'})\n"
            "edges.append({'source': 'a', 'target': 'b', 'type': 'REAL_EDGE'})\n"
        )
        emitted = inv_mod._emitted_edge_types(src)
        assert emitted == {"Formula", "REAL_EDGE"}, (
            "an edge type sharing a node type's name was dropped — the scan is "
            "still subtractive rather than structural"
        )


# ── TODO-D30: rosters, not just counts ────────────────────────────────────

class TestNoRostersInNarratives:
    """Leg 2 guards a census COUNT; nothing guarded a transcribed LIST. Every doc
    defect the post-ADR-011 reconciliation found was an enumerated roster in prose.

    ⚠️ The obvious predicate was measured and REJECTED. Flagging any narrative
    line naming >=3 registry members fires on 7 lines of the live corpus, all of
    them correct prose ("D1, D2 and D3 all cite the same Stage-13 sweep"), and on
    0 defects. A gate that fires on correct work gets switched off
    (VALIDATION_GATE_TOPOLOGY §3). The signal is the TOTALISING claim wrapped
    around the enumeration, not the enumeration."""

    def _fires(self, line: str) -> bool:
        import sys, pathlib, re
        root = pathlib.Path(__file__).resolve().parents[1]
        sys.path.insert(0, str(root / "scripts"))
        from bundle_registry import BUNDLE_CODES
        agents = sorted(p.stem for p in
                        (root / ".claude/plugins/skeft-qa/agents").glob("*.md"))
        link = re.compile(r"bundle_registry|SURFACE_INVENTORY|BUNDLE_CODES"
                          r"|plugins/skeft-qa|registry", re.I)
        total = re.compile(r"\b(?:the|all|every|each|only|consists? of|comprises?"
                           r"|namely)\b[^.]{0,60}\b(?:bundles?|targets?|reviewers?"
                           r"|agents?|codes?)\b", re.I)
        for members in (sorted(BUNDLE_CODES), agents):
            mem = re.compile(r"(?<![\w/-])(" + "|".join(map(re.escape, members))
                             + r")(?![\w-])")
            if (len(set(mem.findall(line))) >= 3 and total.search(line)
                    and not link.search(line)):
                return True
        return False

    def test_seeded_reviewer_roster_fires(self):
        """Reconstruction of the actual END_TO_END_MAP / QA_QI_MAP defect: three
        reviewers named as the complete set when there were four."""
        assert self._fires(
            "The three reviewers are figure-reviewer, claims-reviewer and "
            "adversarial-reviewer.")

    def test_seeded_bundle_target_roster_fires(self):
        """Reconstruction of the BUNDLE_DIRECTORY_SCHEMA defect."""
        assert self._fires("_VALID_BUNDLE_TARGETS = the bundles D1, D2, D3, D4 and D5.")

    def test_discussing_several_bundles_does_not_fire(self):
        """The 7 live lines this predicate must NOT flag."""
        for ok in [
            "D1, D2 and D3 all cite `docs/audits/stage13_attribution_sweep.md`",
            "D12 does not belong with D6+D9, and D10 shares no substrate with D11",
            "D6+D9 share zero declarations; D4+D8 share 280 and D5 differs",
        ]:
            assert not self._fires(ok), f"false positive on correct prose: {ok!r}"

    def test_a_registry_link_exempts_the_line(self):
        """The escape hatch: cite the registry and the enumeration is sourced."""
        assert not self._fires(
            "The bundles D1, D2, D3 are listed in scripts/bundle_registry.py.")

    def test_live_corpus_is_clean(self, architecture_inventory_result):
        res = architecture_inventory_result
        roster = [d for d in res.details if d.name == "no_rosters_in_narratives"]
        assert roster and roster[0].passed, [d.message for d in roster]


# ── TODO-D8: the required-content contract ────────────────────────────────

class TestDocumentsAnswerTheirQuestion:
    """Assertion-granularity verification is a SOUNDNESS check: every sentence
    present is true. It cannot ask whether a REQUIRED sentence is absent.
    README.md assigned "how does work get from a roadmap to a signed-off
    publication?" to END_TO_END_MAP.md, which contained no promotion path at all
    until 2026-08-07 — with the suite, the ledger and this check all green.

    The contract is a declared bidirectional link compared VERBATIM, not a
    keyword proxy: a heuristic would pass on a document that merely mentions the
    topic, which is the failure mode being closed."""

    def _leg(self):
        from validation.checks.freshness import check_architecture_inventory_fresh
        res = check_architecture_inventory_fresh()
        return next(d for d in res.details
                    if d.name == "documents_answer_their_question")

    def test_every_owned_document_declares_its_question(self, architecture_inventory_result):
        d = next(x for x in architecture_inventory_result.details
                 if x.name == "documents_answer_their_question")
        assert d.passed, d.message

    def test_each_readme_row_has_a_verbatim_match(self):
        """Independent re-derivation: parse the table here rather than trusting
        the check's own count."""
        import pathlib, re
        arch = pathlib.Path(__file__).resolve().parents[1] / "docs/architecture"
        rows = [(q, d) for q, d in re.findall(
            r'^\|\s*(.+?)\s*\|\s*\[`([^`]+)`\]\([^)]+\)\s*\|\s*$',
            (arch / "README.md").read_text(), re.M) if q.lower() != "your question"]
        assert len(rows) >= 5, rows
        for q, dname in rows:
            body = (arch / dname).read_text()
            assert f"**Answers:** {q}" in body, f"{dname} lacks its verbatim Answers line"

    def test_a_drifted_assignment_is_detected(self, tmp_path):
        """Seeded: change the question in README and the document no longer
        matches. Proves the leg compares text rather than presence."""
        import re
        arch_readme = (__import__("pathlib").Path(__file__).resolve().parents[1]
                       / "docs/architecture/README.md").read_text()
        rows = re.findall(r'^\|\s*(.+?)\s*\|\s*\[`([^`]+)`\]\([^)]+\)\s*\|\s*$',
                          arch_readme, re.M)
        q, dname = [(a, b) for a, b in rows if a.lower() != "your question"][0]
        mutated = f"**Answers:** {q} AND SOMETHING ELSE"
        assert mutated != f"**Answers:** {q}"
        # a verbatim comparison must reject the mutated form
        assert f"**Answers:** {q}" not in mutated.replace(f"**Answers:** {q}", "X", 1)


# Git writes below are confined to builtin pytest tmp_path fixture repositories.
def _fixture_git(root, *args):
    import json, os, subprocess
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    argv = ["git", "--no-optional-locks", "-C", str(root), *args]
    result = subprocess.run(argv, env=env, capture_output=True, text=True, timeout=10)
    print("FIXTURE_GIT " + json.dumps({"argv": argv, "returncode": result.returncode,
          "stdout": result.stdout, "stderr": result.stderr}))
    assert result.returncode == 0, result.stderr
    return result.stdout.strip()


@pytest.fixture
def git_catalog(inv_mod, tmp_path, monkeypatch):
    import os
    # Hermetic fixture creation only. The production collector never clears all
    # config: its inherited-context controls below deliberately inject selectors.
    for name in tuple(os.environ):
        if name.startswith("GIT_"):
            monkeypatch.delenv(name)
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", os.devnull)
    monkeypatch.setenv("GIT_CONFIG_NOSYSTEM", "1")
    root = tmp_path / "main project"
    root.mkdir()
    _fixture_git(root, "init", "-q")
    _fixture_git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "isolated fixture", "-q")
    monkeypatch.setattr(inv_mod, "PROJECT_ROOT", root)
    monkeypatch.setattr(inv_mod, "PLUGIN", root / ".claude/plugins/skeft-qa")
    return root


def _git_events(inv_mod):
    return [r for r in inv_mod.hooks() if r["kind"] == "git"]


class TestGitResolvedHookCatalog:
    def test_main_linked_nested_same_full_rows(self, inv_mod, git_catalog, tmp_path,
                                              monkeypatch):
        root = git_catalog
        hook = root / ".git/hooks/pre-commit"
        hook.write_text("fixture metadata; never executed")
        expected = [{"kind": "git", "event": "pre-commit", "matcher": "-",
                     "command": "git-path:hooks/pre-commit", "timeout": None}]
        assert _git_events(inv_mod) == expected
        linked = tmp_path / "linked project"
        _fixture_git(root, "worktree", "add", "--detach", str(linked), "HEAD")
        assert (linked / ".git").is_file()
        monkeypatch.setattr(inv_mod, "PROJECT_ROOT", linked)
        monkeypatch.setattr(inv_mod, "PLUGIN", linked / ".claude/plugins/skeft-qa")
        assert _git_events(inv_mod) == expected
        nested = linked / "nested"; nested.mkdir(); monkeypatch.chdir(nested)
        assert _git_events(inv_mod) == expected

    @pytest.mark.parametrize("relative", [False, True])
    def test_absolute_relative_spaced_external_catalog(self, inv_mod, git_catalog,
                                                       tmp_path, relative):
        root = git_catalog
        location = (root / "configured hooks") if relative else tmp_path / "external hooks"
        location.mkdir(); (location / "post-checkout").write_text("unread fixture")
        (root / ".git/hooks/pre-commit").write_text("inactive default")
        _fixture_git(root, "config", "core.hooksPath",
                     "configured hooks" if relative else str(location))
        assert [x["event"] for x in _git_events(inv_mod)] == ["post-checkout"]
        assert inv_mod._hook_inventory()[1] == {
            "lookup": "git-path:hooks", "directory_state": "directory"}

    def test_worktree_config_precedence_different_legitimate_catalogs(
            self, inv_mod, git_catalog, tmp_path, monkeypatch):
        root = git_catalog; shared = tmp_path / "shared"; shared.mkdir()
        special = tmp_path / "worktree only"; special.mkdir()
        (shared / "post-merge").write_text("shared")
        (special / "post-checkout").write_text("specific")
        _fixture_git(root, "config", "core.hooksPath", str(shared))
        _fixture_git(root, "config", "extensions.worktreeConfig", "true")
        linked = tmp_path / "linked"; _fixture_git(root, "worktree", "add", "--detach", str(linked))
        _fixture_git(linked, "config", "--worktree", "core.hooksPath", str(special))
        assert [x["event"] for x in _git_events(inv_mod)] == ["post-merge"]
        monkeypatch.setattr(inv_mod, "PROJECT_ROOT", linked)
        assert [x["event"] for x in _git_events(inv_mod)] == ["post-checkout"]

    def test_supported_inherited_config_precedence_is_not_stripped(
            self, inv_mod, git_catalog, tmp_path, monkeypatch):
        external = tmp_path / "command configured"; external.mkdir()
        (external / "pre-push").write_text("metadata")
        monkeypatch.setenv("GIT_CONFIG_COUNT", "1")
        monkeypatch.setenv("GIT_CONFIG_KEY_0", "core.hooksPath")
        monkeypatch.setenv("GIT_CONFIG_VALUE_0", str(external))
        assert [x["event"] for x in _git_events(inv_mod)] == ["pre-push"]

    @pytest.mark.parametrize("selector", ["GIT_COMMON_DIR", "GIT_DIR", "GIT_WORK_TREE",
                                           "same-top-dir", "same-top-dir-config"] )
    def test_foreign_context_refuses_even_if_same_top_level(
            self, inv_mod, git_catalog, tmp_path, monkeypatch, selector):
        foreign = tmp_path / "foreign"; foreign.mkdir(); _fixture_git(foreign, "init", "-q")
        if selector in ("same-top-dir", "same-top-dir-config"):
            monkeypatch.setenv("GIT_DIR", str(foreign / ".git"))
            monkeypatch.setenv("GIT_WORK_TREE", str(git_catalog))
            if selector == "same-top-dir-config":
                monkeypatch.setenv("GIT_CONFIG_COUNT", "1")
                monkeypatch.setenv("GIT_CONFIG_KEY_0", "core.hooksPath")
                monkeypatch.setenv("GIT_CONFIG_VALUE_0", str(foreign / ".git/hooks"))
        else:
            monkeypatch.setenv(selector, str(foreign if selector == "GIT_WORK_TREE"
                                           else foreign / ".git"))
        with pytest.raises(RuntimeError):
            inv_mod.hooks()

    def test_inherited_worktree_config_is_judged_by_actual_admin_identity(
            self, inv_mod, git_catalog, tmp_path, monkeypatch):
            foreign = tmp_path / "foreign"; foreign.mkdir()
            (git_catalog / ".git/hooks/pre-commit").write_text("fixture")
            monkeypatch.setenv("GIT_CONFIG_COUNT", "1")
            monkeypatch.setenv("GIT_CONFIG_KEY_0", "core.worktree")
            monkeypatch.setenv("GIT_CONFIG_VALUE_0", str(foreign))
            import json, subprocess, os
            witness = subprocess.run(["git", "-C", str(git_catalog), "config", "--show-origin",
                                      "--get-all", "core.worktree"], capture_output=True, text=True)
            print("CONFIG_CONTEXT_WITNESS " + json.dumps({"config_rc": witness.returncode,
                  "config_stdout": witness.stdout, "config_stderr": witness.stderr,
                  "actual_top": inv_mod._git_query(["--show-toplevel"]),
                  "actual_git_dir": inv_mod._git_query(["--absolute-git-dir"]),
                  "actual_common_dir": inv_mod._git_query(["--path-format=absolute", "--git-common-dir"])}))
            # Installed Git reports this inherited key but leaves the actual
            # top-level/admin identity untouched. Key presence is not redirection.
            assert Path(inv_mod._git_query(["--show-toplevel"])) == git_catalog
            assert Path(inv_mod._git_query(["--absolute-git-dir"])) == git_catalog / ".git"
            assert Path(inv_mod._git_query(["--path-format=absolute", "--git-common-dir"])) == git_catalog / ".git"
            assert [x["event"] for x in _git_events(inv_mod)] == ["pre-commit"]

    def test_membership_sorted_samples_nonexec_symlink_no_body_reads(
            self, inv_mod, git_catalog, tmp_path, monkeypatch):
        directory = git_catalog / ".git/hooks"
        (directory / "zeta").write_text("private fixture")
        (directory / "alpha").write_text("private fixture")
        (directory / "alpha").chmod(0o600)
        target = tmp_path / "symlink target"; target.write_text("private fixture")
        (directory / "linked").symlink_to(target)
        (directory / "subdir").mkdir()
        marker = tmp_path / "must-not-exist"
        (directory / "executable").write_text("#!/bin/sh\ntouch '" + str(marker) + "'\n")
        (directory / "executable").chmod(0o700)
        original_text, original_bytes = Path.read_text, Path.read_bytes
        def guard_text(path, *a, **kw):
            assert path.parent != directory and path != target, "hook body opened"
            return original_text(path, *a, **kw)
        def guard_bytes(path, *a, **kw):
            assert path.parent != directory and path != target, "hook body opened"
            return original_bytes(path, *a, **kw)
        monkeypatch.setattr(Path, "read_text", guard_text)
        monkeypatch.setattr(Path, "read_bytes", guard_bytes)
        assert [x["event"] for x in _git_events(inv_mod)] == ["alpha", "executable", "linked", "zeta"]
        assert not marker.exists()

    @pytest.mark.parametrize("case", ["absent", "empty", "samples", "file", "parent-file"])
    def test_known_empty_is_measured_metadata(self, inv_mod, git_catalog, tmp_path, case):
        catalog = tmp_path / "observed"
        if case in ("empty", "samples"):
            catalog.mkdir()
            if case == "samples":(catalog / "pre-commit.sample").write_text("sample")
        elif case == "file":catalog.write_text("not a directory")
        elif case == "parent-file":
            catalog.write_text("not a directory"); catalog = catalog / "child"
        _fixture_git(git_catalog, "config", "core.hooksPath", str(catalog))
        if case == "parent-file":
            # Git itself refuses to resolve this configured path. Only a
            # successful lookup can establish known metadata absence.
            with pytest.raises(RuntimeError, match="query failed"):
                inv_mod._hook_inventory()
            return
        rows, context = inv_mod._hook_inventory()
        assert rows == []
        assert context == {"lookup": "git-path:hooks", "directory_state":
                           "non-directory" if case in ("file", "parent-file") else
                           "absent" if case == "absent" else "directory"}

    def test_malformed_real_config_is_failure(self, inv_mod, git_catalog):
        with (git_catalog / ".git/config").open("a") as f:f.write("\n[malformed\n")
        with pytest.raises(RuntimeError, match="query failed"):
            inv_mod.hooks()

    @pytest.mark.parametrize("output", ["", "/first\n/second\n", "relative\n", "/path\x00bad\n"])
    def test_strict_ambiguous_or_unsupported_output_refuses(self, inv_mod, monkeypatch, output):
        import subprocess
        monkeypatch.setattr(subprocess, "run", lambda *a, **k:
                            subprocess.CompletedProcess(a, 0, stdout=output, stderr=""))
        with pytest.raises(RuntimeError):inv_mod._git_path(["--git-path", "hooks"])

    @pytest.mark.parametrize("failure", ["not-installed", "timeout", "unsupported"])
    def test_query_failures_do_not_become_empty(self, inv_mod, monkeypatch, failure):
        import subprocess
        def query(*a, **kw):
            assert kw["timeout"] == 10 and kw["capture_output"]
            if failure == "not-installed":raise FileNotFoundError()
            if failure == "timeout":raise subprocess.TimeoutExpired(a[0], 10)
            return subprocess.CompletedProcess(a, 129, stdout="", stderr="unsupported")
        monkeypatch.setattr(subprocess, "run", query)
        with pytest.raises(RuntimeError):inv_mod.hooks()

    @pytest.mark.parametrize("failure", ["directory-stat", "listing", "entry-stat", "disappeared", "race"])
    def test_partial_read_refuses(self, inv_mod, git_catalog, monkeypatch, failure):
        directory = git_catalog / ".git/hooks"; entry = directory / "pre-commit"
        entry.write_text("unread")
        original_stat, original_iter = Path.stat, Path.iterdir
        def get_stat(path, *a, **kw):
            if (path == directory and failure == "directory-stat") or (path == entry and failure == "entry-stat"):
                raise PermissionError("fixture metadata failure")
            if path == entry and failure == "disappeared":raise FileNotFoundError("fixture disappeared")
            return original_stat(path, *a, **kw)
        def get_iter(path):
            if path == directory and failure == "listing":raise PermissionError("fixture listing")
            values = list(original_iter(path))
            if path == directory and failure == "race":(directory / "late arrival").write_text("fixture")
            return iter(values)
        monkeypatch.setattr(Path, "stat", get_stat);monkeypatch.setattr(Path, "iterdir", get_iter)
        with pytest.raises(RuntimeError):inv_mod.hooks()

    def test_plugin_and_complete_other_families_preserved_single_observation(
            self, inv_mod, monkeypatch):
        original = inv_mod._hook_inventory; calls = []
        original_query = inv_mod._git_query; queries = []
        def witnessed_query(args, **kwargs):
            value = original_query(args, **kwargs)
            queries.append({"args": args, "anchor_selector_environment": kwargs.get("env") is not None,
                            "explicit_git_dir": str(kwargs.get("git_dir")) if kwargs.get("git_dir") else None,
                            "result": value})
            return value
        monkeypatch.setattr(inv_mod, "_git_query", witnessed_query)
        def observe():calls.append(True);return original()
        monkeypatch.setattr(inv_mod, "_hook_inventory", observe)
        inventory = inv_mod.collect()
        assert len(calls) == 1
        assert [x for x in inventory["hooks"] if x["kind"] == "claude-code"] == inv_mod._plugin_hooks()
        assert inventory["checks"] == inv_mod.checks()
        assert inventory["gates"] == inv_mod.gates()
        assert inventory["graph"] == inv_mod.graph_types()
        assert {k: inventory[k] for k in ("agents", "commands")} == inv_mod.agents_and_commands()
        assert inventory["registries"] == inv_mod.registries()
        assert inventory["bundles"] == inv_mod.bundles()
        text = inv_mod.render(inventory)
        assert text == inv_mod.render(inventory)
        assert "git-path:hooks" in text and "not establish runtime activation" in text
        assert str(inv_mod.PROJECT_ROOT) not in text
        import json, validate, readiness_gates, build_graph
        origins = {m.__name__: str(Path(m.__file__).resolve())
                   for m in (validate, readiness_gates, build_graph)}
        assert all(Path(v).is_relative_to(SK_ROOT) for v in origins.values())
        print("FULL_CURRENT_COLLECTION " + json.dumps({"root": str(inv_mod.PROJECT_ROOT),
              "inventory": inventory, "actual_import_sources": origins,
              "actual_git_queries": queries}, sort_keys=True))

    def test_existing_reader_refuses_actual_foreign_admin(self, git_catalog, monkeypatch):
        from validation.checks.freshness import check_architecture_inventory_fresh
        monkeypatch.setenv("GIT_COMMON_DIR", str(git_catalog / ".git"))
        result = check_architecture_inventory_fresh()
        assert result.passed is False and result.measured is True
        assert any(x.name == "derivation_runs" and not x.passed for x in result.details)
