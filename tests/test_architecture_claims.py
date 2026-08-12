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
