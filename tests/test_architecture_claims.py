"""Executable assertions for load-bearing PROSE CLAIMS in `docs/architecture/`.

WHY THIS FILE EXISTS
--------------------
`architecture_inventory_fresh` gates two things: the derived census matches the code, and
no narrative restates a census count. A third leg, `doc_refs_resolve`, gates that every
path-like reference points at a file that exists. **None of them verifies a DESCRIPTION.**

Every error found in the 2026-08-07 accuracy pass was of exactly that shape — a sentence
whose references all resolved and whose counts were all absent, and which was false anyway:

  * "no gate or check reads `stage9_status`" — `bundle_append.py:322` reads both
  * "the four hazards ADR-009 D3 identifies" — D3 identifies five, and the fifth was live
  * "bundle Stage-13 reviews reach no gate" — they are the largest `ReviewFinding` source
  * "`--strict` is scoped by Invariant #12" — #12 governs one check, not the flag

Prose review did not catch these; only reading the code did. This file makes that reading
executable.

THE BINDING IS TWO-WAY, AND THAT IS THE WHOLE DESIGN
----------------------------------------------------
Each test does two things:

  1. asserts the claim's sentence is STILL PRESENT in the document, verbatim; and
  2. asserts the code fact that makes it true.

So editing the claim breaks the test (forcing whoever rewords it to re-verify), and changing
the code breaks the test (forcing whoever changes it to update the doc). A one-way assertion
would rot silently the moment someone rephrased the sentence — which is how the claims above
survived: they were true when written and nothing re-read them afterwards.

⚠️ **A claim asserted here must be verified by a DECIDER, never a proxy.** `grep -c
"@register_check" validate.py` returns 5 — all of them in comments; the AST returns none. A
substring proxy here would not merely fail to catch an error, it would manufacture one.

Coverage is deliberately partial: these are the load-bearing claims — the ones a reader would
act on. Adding a claim here is cheap; the cost is in choosing claims whose falsity would
mislead. See B2 in `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD`.
"""
from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
ARCH = ROOT / "docs" / "architecture"
sys.path.insert(0, str(ROOT / "scripts"))


def _claim(doc: str, sentence: str) -> None:
    """Assert the documented sentence is still there, so a reword forces re-verification."""
    text = (ARCH / doc).read_text(encoding="utf-8")
    normalized = " ".join(text.split())
    assert " ".join(sentence.split()) in normalized, (
        f"{doc} no longer contains the claim this test verifies:\n  {sentence!r}\n"
        f"If the claim was reworded, re-verify it against the code and update this test. "
        f"If it was deleted because it became false, delete this test with it.")


def _module_ast(relpath: str) -> ast.Module:
    return ast.parse((ROOT / relpath).read_text(encoding="utf-8"))


# ── VALIDATION_ARCHITECTURE.md ────────────────────────────────────────────────────────

def test_validate_py_registers_zero_checks():
    _claim("VALIDATION_ARCHITECTURE.md",
           "`scripts/validate.py` is a **framework** (zero registered checks)")
    # DECIDER: the AST. A substring scan finds `@register_check` in this file's comments.
    tree = _module_ast("scripts/validate.py")
    decorated = [
        n.name for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef)
        for d in n.decorator_list
        if (isinstance(d, ast.Call) and getattr(d.func, "id", None) == "register_check")
        or getattr(d, "id", None) == "register_check"
    ]
    assert decorated == [], f"validate.py registers checks directly: {decorated}"


def test_counts_fresh_runs_first_in_canonical_order():
    _claim("VALIDATION_ARCHITECTURE.md",
           "`counts_fresh` runs first in `_CANONICAL_ORDER`")
    import validate
    assert list(validate._CANONICAL_ORDER)[0] == "counts_fresh"


def test_adr009_d3_identifies_five_hazards():
    _claim("VALIDATION_ARCHITECTURE.md",
           "These are ADR-009 D3, which identifies **five**.")
    text = (ARCH / "VALIDATION_ARCHITECTURE.md").read_text(encoding="utf-8")
    rows = [ln for ln in text.splitlines() if ln.startswith("| **H")]
    assert len(rows) == 5, f"the hazard table has {len(rows)} rows, not five: {rows}"


def test_there_is_no_scheduled_ci_runner():
    _claim("VALIDATION_ARCHITECTURE.md",
           "There is deliberately **no scheduled runner** (verified: no `.github/workflows/`)")
    wf = ROOT / ".github" / "workflows"
    assert not wf.exists() or not any(wf.iterdir()), (
        f"{wf} now exists and is non-empty — a scheduled runner arrived and the "
        f"architecture doc still says none does")


# ── VALIDATION_GATE_TOPOLOGY.md ───────────────────────────────────────────────────────

@pytest.mark.parametrize("gate", ["NumericalFreshness", "FirstClaimVerification"])
def test_the_p2_gates_cannot_emit_blocked(gate):
    """The claim that these 'cannot block'. Verified by the states the evaluator ASSIGNS,
    not by reading its docstring — a docstring says what someone intended."""
    _claim("VALIDATION_GATE_TOPOLOGY.md",
           "have `passed` and `needs-recheck` as their only reachable")
    import readiness_gates as rg
    fn_name = next(f.__name__ for n, _p, f in rg.GATES if n == gate)
    tree = _module_ast("scripts/readiness_gates.py")
    fn = next(n for n in ast.walk(tree)
              if isinstance(n, ast.FunctionDef) and n.name == fn_name)
    states = {
        n.value.value for n in ast.walk(fn)
        if isinstance(n, ast.Assign)
        for t in n.targets
        if isinstance(t, ast.Attribute) and t.attr == "state" and isinstance(n.value, ast.Constant)
    }
    assert "blocked" not in states, (
        f"{gate} can now assign state='blocked' ({sorted(states)}), so it CAN block — "
        f"the topology table's 'can block? ❌' and READINESS_GATES' enforcement note are stale")


def test_strict_is_passed_only_by_the_submission_gate():
    """DECIDER: the gate->steps table itself. `gate_precheck` routes `--strict` through a
    `__strict__` sentinel in its per-gate step list, so the question "which gates pass
    --strict" is answered by which lists contain that sentinel — not by grepping lines."""
    _claim("VALIDATION_GATE_TOPOLOGY.md",
           "`--strict` is passed only by the submission gate")
    import gate_precheck
    table = next(v for v in vars(gate_precheck).values()
                 if isinstance(v, dict) and any(
                     isinstance(steps, list) and "__strict__" in steps for steps in v.values()))
    carriers = sorted(g for g, steps in table.items() if "__strict__" in steps)
    assert carriers == ["submission"], (
        f"gates passing --strict are {carriers}, not just ['submission'] — "
        f"VALIDATION_GATE_TOPOLOGY's flag table and its Invariant-#12 note are now wrong")


def test_the_submission_gate_ignores_p2_advisories():
    """READINESS_GATES' 'human policy vs mechanized rule' split rests on this."""
    _claim("VALIDATION_GATE_TOPOLOGY.md",
           "which counts only P1-not-passed\nand P2-`blocked`")
    src = (ROOT / "scripts" / "validation" / "checks" / "bundles_readiness.py").read_text()
    assert "p1_blocked" in src and "p2_blocked" in src, (
        "the submission gate no longer partitions blockers into p1/p2 — re-verify the "
        "policy-vs-mechanism split documented in READINESS_GATES.md")


# ── CHECK_AUTHORING_GUIDE.md ──────────────────────────────────────────────────────────

def test_memo_refuses_to_cache_a_non_measurement():
    _claim("CHECK_AUTHORING_GUIDE.md",
           "`_memo` **refuses to cache a non-measurement**")
    src = (ROOT / "scripts" / "validation" / "_memo.py").read_text(encoding="utf-8")
    assert "measured" in src, "_memo.py no longer references `measured` at all"
    tree = _module_ast("scripts/validation/_memo.py")
    guards = [
        n for n in ast.walk(tree)
        if isinstance(n, ast.Attribute) and n.attr == "measured"
    ]
    assert guards, "_memo.py does not read `.measured` — the cache can store a non-measurement"


def test_the_two_ratchet_legs_are_complements_over_one_id_set():
    """⚠️ THIS DOCUMENT ASSERTED THIS AND IT WAS FALSE. The sentence said the two legs
    partitioned the blocking population; measured, eight open blocking findings were in
    neither. Both prior wordings were true-when-written or never true, and nothing re-read
    them — which is the exact rot this file exists to stop.

    DECIDER: the check's own source, via `ast`. Leg 2 must key on the ids the aggregation
    RETURNED (`open_finding_ids`), never on the presence of an attribution field. A
    substring scan for `inferred_paper` would pass on the fixed file — the name still
    appears in the comment explaining why keying on it was wrong.
    """
    _claim("END_TO_END_MAP.md",
           "Leg 2 is keyed on the finding ids the aggregation\n  actually returned, so the "
           "two legs are complements over one id set and cover the open\n  blocking "
           "population by construction.")
    tree = _module_ast("scripts/validation/checks/bundles_readiness.py")
    fn = next(n for n in ast.walk(tree)
              if isinstance(n, ast.FunctionDef)
              and n.name == "check_bundle_stage13_claim_consistent")
    consts = {n.value for n in ast.walk(fn)
              if isinstance(n, ast.Constant) and isinstance(n.value, str)}
    assert "open_finding_ids" in consts, (
        "leg 2 no longer reads `open_finding_ids` — it is back to guessing which findings "
        "the aggregation reached instead of asking it")
    # …and it must not have gone back to the proxy. The explanatory COMMENT still says
    # `inferred_paper`; a comment is not a Constant, so this sees only real lookups.
    proxy = sorted(v for v in consts if v.startswith("inferred_"))
    assert not proxy, (
        f"the check reads {proxy} again — that attribution-field proxy is what missed the "
        f"eight pre-bundle-era findings that reach no bundle")


def test_the_ledger_writer_does_not_mint_its_own_ids():
    """⚠️ A second minter reproduces the orphan class BY CONSTRUCTION — 66 ledger records
    naming no node is what motivated the writer. DECIDER: the import graph plus the absence
    of a local definition, both via `ast`. `close_finding.py` names `mint_finding_id` in its
    own docstring, so a substring scan is satisfied by prose alone.
    """
    _claim("QA_QI_INFRASTRUCTURE_MAP.md",
           "It mints ids with the extractor's own `mint_finding_id` — a second minter "
           "would reproduce, by construction, the orphaned-record class that motivated it")
    tree = _module_ast("scripts/close_finding.py")
    modules = {a.name for n in ast.walk(tree) if isinstance(n, ast.Import)
               for a in n.names}
    assert "build_graph" in modules, (
        "close_finding.py no longer imports build_graph — it cannot be sharing the minter")
    # ASSERT THE CALL, not the name: it is `_bg.mint_finding_id(...)`, an Attribute.
    called = {c.func.attr for c in ast.walk(tree)
              if isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)}
    assert "mint_finding_id" in called, (
        "close_finding.py names the extractor's minter but never calls it")
    local = [n.name for n in ast.walk(tree)
             if isinstance(n, ast.FunctionDef) and "mint" in n.name]
    assert not local, f"close_finding.py defines its own minter(s): {local}"


def test_fix_propagation_is_the_only_evaluator_that_reads_flags():
    """The routing surface P9a builds rests on this: if a second gate read FLAGS, the
    drill-through would have to resolve blockers for it too. DECIDER: which evaluator
    functions mention the edge type at all, from the AST rather than a line grep.
    """
    _claim("QA_QI_INFRASTRUCTURE_MAP.md",
           "**`FixPropagation` is the only evaluator that reads FLAGS.** Every other gate "
           "is blind to review findings.")
    import readiness_gates as rg
    tree = _module_ast("scripts/readiness_gates.py")
    evaluators = {f.__name__ for _n, _p, f in rg.GATES}
    readers = sorted(
        n.name for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef) and n.name in evaluators
        and any(isinstance(c, ast.Constant) and c.value == "FLAGS"
                for c in ast.walk(n)))
    fix_prop = next(f.__name__ for n, _p, f in rg.GATES if n == "FixPropagation")
    assert readers == [fix_prop], (
        f"evaluators reading FLAGS are {readers}, not just [{fix_prop!r}] — a second "
        f"finding-aware gate arrived and QA_QI_INFRASTRUCTURE_MAP §3 is now wrong")


def test_the_ci_floor_counts_measurements_not_invocations():
    _claim("CHECK_AUTHORING_GUIDE.md",
           "`--ci`'s coverage floor counts *measurements, not\ninvocations*")
    # DECIDER: the AST of the `if _cfg.CI_MODE ...` block that owns the floor. A text
    # window around the constant's DEFINITION reads the wrong part of the file — the
    # definition lives in _config.py and its name appears in help strings.
    tree = _module_ast("scripts/validate.py")
    blocks = [
        n for n in ast.walk(tree)
        if isinstance(n, ast.If) and "CI_MIN_CHECKS_RUN" in ast.dump(n)
    ]
    assert blocks, "no branch reads CI_MIN_CHECKS_RUN — the coverage floor is gone"
    assert any(
        isinstance(a, ast.Attribute) and a.attr == "measured"
        for b in blocks for a in ast.walk(b)
    ), ("the coverage-floor branch no longer reads CheckResult.measured — it is counting "
        "invocations again, which is exactly what made it unfireable")


# ── CLAUDE.md rule 0 ↔ the architecture-change skill ──────────────────────────────────

def test_rule_zero_names_a_skill_that_exists():
    """Rule 0 is the claim that makes rules 1-3 fire, and it was unpinned in both
    directions: rename the skill directory or drift its `name:` and CLAUDE.md routes a
    reader to something that does not resolve, silently.

    ⚠️ MEASURED 2026-08-13: the skill lives in the repo but NOT in the loaded plugin
    cache, so `Skill(architecture-change)` fails until the operator refreshes the plugin
    and restarts. This test pins the repo side — the thing the project controls — and
    cannot see the cache, which is the known plugin-drift gap END_TO_END_MAP §3 records.
    """
    claude_md = (ROOT / "CLAUDE.md").read_text(encoding="utf-8")
    sentence = "**Invoke the `architecture-change` skill first.**"
    assert " ".join(sentence.split()) in " ".join(claude_md.split()), (
        "CLAUDE.md no longer carries rule 0. If the rule was reworded, re-verify that it "
        "still routes to the skill and update this test; if it was deleted, delete this "
        "test with it and say what replaced it.")

    skill = ROOT / ".claude/plugins/skeft-qa/skills/architecture-change/SKILL.md"
    assert skill.is_file(), f"rule 0 routes to a skill that is not on disk: {skill}"

    # DECIDER: the frontmatter `name:`, which is what the harness resolves — not the
    # directory, which can agree while the name has drifted.
    head = skill.read_text(encoding="utf-8").split("---")[1]
    names = [ln.split(":", 1)[1].strip() for ln in head.splitlines()
             if ln.startswith("name:")]
    assert names == ["architecture-change"], (
        f"the skill's frontmatter name is {names}, but CLAUDE.md rule 0 and "
        f"docs/architecture/README.md both invoke it as 'architecture-change'")


def test_the_sequence_is_rendered_identically_everywhere_it_appears():
    """The eight steps are named in three places. A reader who counts them in one and
    acts on another gets a different sequence — `terminate` was missing from two of the
    three renderings, which is how step 8 became optional in practice."""
    steps = ["orient", "measure", "specify", "review", "pilot", "plan", "ship", "terminate"]

    skill = (ROOT / ".claude/plugins/skeft-qa/skills/architecture-change/SKILL.md"
             ).read_text(encoding="utf-8")
    headings = [ln.split(".", 1)[1].strip().lower()
                for ln in skill.splitlines() if ln.startswith("### ")
                and ln[4].isdigit()]
    first_words = [h.split()[0].strip(",.:;—") for h in headings]
    assert first_words == steps, (
        f"the skill's step headings begin {first_words}, not {steps} — the headings are "
        f"the authority the other two renderings copy, so fix whichever drifted")

    for path in ("CLAUDE.md", "docs/architecture/README.md"):
        text = " ".join((ROOT / path).read_text(encoding="utf-8").split()).lower()
        rendered = [s for s in steps if s in text]
        assert rendered == steps, (
            f"{path} renders the sequence as {rendered}, missing "
            f"{[s for s in steps if s not in rendered]}")


# ── The 2026-08-13 sync-audit corrections, pinned so they cannot rot the same way ──
#
# All three sentences below were FALSE in a merged tree while every gate was green, and
# two of them were made false by the same session that wrote them. None was catchable by
# `doc_refs_resolve` (their paths all resolved) or by the counts leg (they state no count).
# Pinning is the repo's own answer to "no check verifies a prose claim", so these are
# exactly the claims that earn it: each describes a DECIDER a reader would act on.


def test_counts_json_staleness_key_is_a_hybrid_not_pure_mtime():
    """QA_QI's table recorded `counts.json` as keyed on mtime, which the count leg made
    false. The table's whole purpose is recording staleness keys, so a wrong row there is
    worse than no row: it is the place a reader goes to learn what protects the artifact."""
    _claim("QA_QI_INFRASTRUCTURE_MAP.md",
           "**value compare** on the five glob figures, mtime vs sources for `pytest_cases`")
    # DECIDER: the freshness predicate must actually call the writer's own cheap counter.
    tree = _module_ast("scripts/validation/checks/freshness.py")
    calls = [n for n in ast.walk(tree)
             if isinstance(n, ast.Call)
             and getattr(n.func, "attr", None) == "count_python_cheap"]
    assert calls, (
        "`_counts_is_stale` no longer calls `update_counts.count_python_cheap` — the doc "
        "says the key is a value compare, so either restore the call or fix the doc")
    import update_counts
    legs = set(update_counts.count_python_cheap())
    assert legs == {"python_modules", "test_files", "notebooks", "papers", "figures"}, (
        f"the cheap counter returns {sorted(legs)}; the doc says FIVE glob figures")
    assert "pytest_cases" not in legs, (
        "pytest_cases moved into the cheap counter — it costs a pytest collection, and "
        "the doc explains the split on exactly that ground")


def test_the_census_covers_three_languages_with_three_deciders():
    """Three documents scoped the census to Python after D5 added shell and D3 notebooks —
    one of them instructing a reader to 'change its docstring', which is the wrong
    instruction for a shell script or a notebook."""
    _claim("QA_QI_INFRASTRUCTURE_MAP.md",
           "answers *what is this module, script or notebook*")
    import module_census as mc
    assert set(mc.TREES) == {"src", "scripts", "notebooks"}, mc.TREES
    # DECIDER: one derivation per language, each a distinct function — not one regex.
    names = {f.name for f in ast.walk(_module_ast("scripts/module_census.py"))
             if isinstance(f, ast.FunctionDef)}
    for decider in ("_shell_header", "_notebook_first_markdown"):
        assert decider in names, (
            f"{decider} is gone — the doc claims a decider per language; a single shared "
            f"scan would reintroduce the false positive each one is bounded against")


def test_the_merge_gate_runs_the_full_suite_exactly_once():
    """VALIDATION_ARCHITECTURE described 'two agreeing `pytest -m ''` runs' for three
    commits after the duplicate was dropped. The tree-state assertion replaced it."""
    _claim("VALIDATION_ARCHITECTURE.md",
           "One `pytest -m ''` run plus `validate.py --ci --no-memo`")
    # ⚠️ DECIDER, NOT A SUBSTRING COUNT. `src.count('"-m", ""')` would also match the
    # explanatory comments above the step — this file's own docstring records a proxy of
    # exactly that shape MANUFACTURING an error. Walk the AST and count argv list literals
    # that actually carry `-m` immediately followed by the empty marker string.
    tree = _module_ast("scripts/verify_scope.py")
    full_suite_argvs = 0
    for node in ast.walk(tree):
        if not isinstance(node, ast.List):
            continue
        vals = [e.value for e in node.elts if isinstance(e, ast.Constant)]
        if "pytest" in vals:
            for a, b in zip(vals, vals[1:]):
                if a == "-m" and b == "":
                    full_suite_argvs += 1
    assert full_suite_argvs == 1, (
        f"{full_suite_argvs} argv literals run the unmarked full suite; the doc says the "
        f"merge gate runs it ONCE. If a second run was restored, say why in "
        f"VALIDATION_ARCHITECTURE §5.2 and update this test")
    names = {f.name for f in ast.walk(tree) if isinstance(f, ast.FunctionDef)}
    assert "_tree_state" in names, (
        "the before/after `git status --porcelain` assertion is gone; it is what the "
        "dropped duplicate was reaching for, and §5.2 credits it with certifying more")


def test_aristotle_proved_counts_only_run_backed_entries():
    """⚠️ 11 DRAFTS RENDER THIS MACRO AS "closed by the Aristotle automated prover".

    `aristotle_proved` was `len(ARISTOTLE_THEOREMS)`, and the registry also holds `'manual'`
    entries — theorems proved by hand, several of them BECAUSE a machine run had certified a
    weaker statement later strengthened. So the published macro overstated machine
    verification, and the 2026-08-13 statement-substance wave widened the gap from 4 to 6
    while repairing the statements it counted.

    The decider for "Aristotle closed it" is a run id, so this pins the count to that and
    not to the registry's size.
    """
    import json
    import update_counts
    from src.core.constants import ARISTOTLE_THEOREMS as A

    manual = {k for k, v in A.items() if v == "manual"}
    assert manual, (
        "no 'manual' entries — if the sentinel was renamed, this test is measuring nothing "
        "and `aristotle_proved` may silently be counting hand proofs as machine ones again")

    published = json.loads((ROOT / "docs" / "counts.json").read_text())["aristotle"]
    assert published["aristotle_proved"] == len(A) - len(manual), (
        f"aristotle_proved={published['aristotle_proved']} but the registry holds {len(A)} "
        f"entries of which {len(manual)} are manual — the macro counts hand proofs as "
        f"machine-closed in every draft that quotes it")
    assert published["aristotle_proved"] < len(A), (
        "the count equals the registry size, so the manual exclusion is not being applied")


def test_no_plugin_file_grants_a_worker_a_build_the_guard_denies():
    """Prose that instructs a worker to run a denied command is worse than silence.

    ADR-008 change-set item 3. Three plugin files carried a "narrow exception" letting a
    worker run `lake build SKEFTHawking.<Module>`; one of them additionally prescribed
    `-j4`, a flag Lake has never had, one paragraph after stating Lake has no job cap.
    `harness_worker_shell_guard.py` denies `lake build` to every subagent unconditionally,
    so the grant was unexecutable — a worker following it burns a turn on a denial.

    The decider is the guard's own denied set, not a hand-listed phrase.
    """
    import re
    import sys

    plugin = ROOT / ".claude" / "plugins" / "skeft-qa"
    sys.path.insert(0, str(plugin / "scripts"))
    try:
        import harness_worker_shell_guard as guard
    finally:
        sys.path.pop(0)

    denied = [pattern for pattern, _ in guard.DENIED]
    assert any("lake" in p and "build" in p for p in denied), (
        "the guard no longer denies `lake build` to workers; this test is measuring nothing")

    offenders = []
    for path in sorted(plugin.rglob("*.md")):
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            # Only lines that TELL a worker to run one — a line saying it is denied is fine.
            if not re.search(r"^\s*(cd .*&&\s*)?lake\s+build\b", line):
                continue
            if any(re.search(p, line) for p in denied):
                offenders.append(f"{path.relative_to(ROOT)}:{number}: {line.strip()}")
    assert not offenders, (
        "plugin prose instructs a worker to run a command the shipped guard denies:\n  "
        + "\n  ".join(offenders))


def test_no_plugin_file_prescribes_a_lake_job_cap_flag():
    """`-j4` was live in `lean-worker.md` while the same paragraph said Lake has no `-j`."""
    plugin = ROOT / ".claude" / "plugins" / "skeft-qa"
    offenders = []
    for path in sorted(plugin.rglob("*.md")):
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if re.search(r"`-j\d+`|\blake build\b[^\n]*\s-j\s*\d", line):
                offenders.append(f"{path.relative_to(ROOT)}:{number}: {line.strip()}")
    assert not offenders, (
        "plugin prose prescribes a Lake parallelism flag that does not exist:\n  "
        + "\n  ".join(offenders))


def test_the_claude_slot_endpoints_named_in_docs_are_the_ones_the_inventory_renders():
    """Docs name `mcp__skeft_wtN__*`; the renderer derives those names from the inventory.

    If an endpoint is renamed in `config/lean-slots.public.json`, every dispatch brief in the
    plugin and harness guide silently names a server that does not exist. Pinning both ways
    means the rename breaks here rather than at fan-out time.
    """
    import sys

    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        from lean_slots.claude_config import managed_servers
        from lean_slots.state import Inventory
    finally:
        sys.path.pop(0)

    rendered = set(managed_servers(Inventory.load(ROOT / "config" / "lean-slots.public.json")))
    assert rendered, "the inventory renders no slot endpoints"

    documented = set()
    sources = [
        ROOT / "docs" / "dev-loops" / "HARNESS_GUIDE.md",
        *(ROOT / ".claude" / "plugins" / "skeft-qa").rglob("*.md"),
    ]
    for path in sources:
        for match in re.finditer(r"mcp__(skeft_wt\d)__", path.read_text(encoding="utf-8")):
            documented.add(match.group(1))
    assert documented, (
        "no document names a slot endpoint — the guidance no longer tells a lead which "
        "server to hand a worker, and this test is measuring nothing")
    assert documented <= rendered, (
        f"documented endpoints {sorted(documented - rendered)} are not rendered from the "
        f"inventory, which renders {sorted(rendered)}")
