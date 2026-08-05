"""D5 — the mutation-test obligation, made MECHANICAL. Audit finding QI-27.

ADR-009 §Context names three problems and says plainly which one did the damage:

    1. No shared-helper layer.        -> fixed by Phase 1
    2. The file exceeds one read.     -> fixed by Phase 2
    3. **No mutation-test discipline. This is the one that caused the damage.**

D5 is the answer to (3): *"a new or modified check MUST ship with a test
demonstrating BOTH directions — it FAILS on a seeded defect, and it stays SILENT
on correct data."* It shipped as **prose**. Nothing enforced it, so the suite grew
to 59 checks with, by the map's own count, ten that would fail on a seeded defect.

WHY THIS IS A CURATED REGISTRY AND NOT A SCANNER
------------------------------------------------
The obvious implementation — scan the tests for a mutation marker — does not work,
and that was **measured** before this file was written. Of the test files covering
the five Phase-3 repairs, **none** carries a mutation marker in its source: the
mutation runs are recorded in COMMIT MESSAGES and in ADR-009 §Deferred, because a
mutation is an act performed against the tree, not an artifact left in it.

A scanner would therefore have to infer "both directions" from test structure,
which is exactly the kind of proxy this project keeps getting burned by — cf.
`recurrence_reopens_closures`, whose threshold was calibrated three times against a
predicate that could not fire, and the eight shipped guards ADR-009 §Context lists.
**A registry that must be edited deliberately is honest; a scanner that guesses is
the failure mode wearing a lab coat.**

WHAT THIS FILE ENFORCES
-----------------------
1. **Every registered check is ACCOUNTED FOR** — it appears in exactly one of
   `MUTATION_VERIFIED` or `AWAITING_MUTATION_TEST`. A new check that declares
   neither fails on arrival. This is the leg that makes D5 binding: you cannot add
   a check without stating whether it is tested.
2. **The backlog may only SHRINK.** `AWAITING_CEILING` ratchets it, in the house
   idiom (`VACUOUS_STATEMENT_BASELINE`, `NATIVE_DECIDE_DECL_CLOSURE_CEILING`,
   `COUNT_LITERAL_CEILING`, `test_cannot_measure_baseline`).
3. **A `MUTATION_VERIFIED` entry cannot be fictional** — the test file it names
   must exist and must actually mention the check. That is the seam guard; without
   it, moving a name from the backlog to the verified list would be free.

⚠️ **THIS FILE DOES NOT PROVE A TEST IS GOOD.** It proves the project has made a
DECISION about every check and cannot silently add an untested one. Raising the
verified count is the real work (audit W-D); this stops the population growing
while that happens. Do not read a green run here as coverage.

MUTATION-VERIFIED 2026-08-04, both directions:
  * register a check absent from both lists -> test_every_check_is_accounted_for FAILS
  * move a name to MUTATION_VERIFIED naming a test that does not mention it
        -> test_verified_entries_name_a_real_test FAILS
  * add a name to AWAITING beyond the ceiling -> test_backlog_only_shrinks FAILS
Clean negative control: unmutated tree, all pass.
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

TESTS_DIR = SK_ROOT / "tests"


#: check name -> the test file that mutation-verifies it, and what the mutation was.
#: An entry here is a CLAIM that someone seeded a defect and watched the test fail.
#: Add one only when that has actually been done — the evidence lives in the commit.
MUTATION_VERIFIED: dict[str, tuple[str, str]] = {
    # ── ADR-009 §Deferred item 2 — the inverted submission gate ──
    "readiness_submission_gate": (
        "test_readiness_submission_gate.py",
        "11 tests / 5 mutations at the repair; pure cores `classify_readiness` and "
        "`partition_readiness` extracted so the verdict is testable against synthetic "
        "gates instead of a 15-second graph build",
    ),
    # ── ADR-009 §Deferred item 1 — the native_decide ratchet ──
    "native_decide_regression": (
        "test_native_decide_ratchet.py",
        "15 tests / 5 mutations; the metric now reads lean_deps.json directly rather "
        "than the counts.json recording of it",
    ),
    # ── ADR-009 §Deferred item 3 — the always-pass dispositions ──
    "paper_latex_compiles": (
        "test_always_pass_dispositions.py",
        "computed its verdict and discarded it; now hard-fails. D3's 2 fatal LaTeX "
        "errors were the live instance",
    ),
    "count_literals": (
        "test_always_pass_dispositions.py",
        "WARN-only against a retreating target; now a ratchet on COUNT_LITERAL_CEILING",
    ),
    "numerical_literals": (
        "test_always_pass_dispositions.py",
        "same shape; now a ratchet on NUMERICAL_LITERAL_CEILING",
    ),
    # ── Audit QI-27 W-D — the backlog, emptied module by module ──
    # reviews.py: 22 tests / 8 mutations, all caught, clean negative control. Four of the
    # eight mutate a FILTER rather than the verdict (the date rule, the same-bundle rule,
    # the section-number tie-breaker, the PASS/RESOLVED exclusion) — a suite asserting
    # only `passed is False` on one dirty fixture would have missed every one.
    "recurrence_reopens_closures": (
        "test_d5_reviews.py",
        "4 mutations: the hit counter, the date rule, the same-bundle rule and the "
        "section-number tie-breaker, each caught by a distinct leg. Synthetic findings "
        "throughout — this check's threshold was mis-calibrated three times against the "
        "live self-remediating corpus",
    ),
    "review_severity_declared": (
        "test_d5_reviews.py",
        "`n_sev < n_head` -> `n_sev < 0` caught; plus a pre-cutoff leg so the historical "
        "glyph-inference boundary cannot be silently widened into a blanket rule",
    ),
    "review_docs_mint_findings": (
        "test_d5_reviews.py",
        "2 mutations: the zero-minted verdict, and `_carries_findings` forced True — the "
        "latter is the content-scoping rule that two earlier scopings got wrong in "
        "opposite directions",
    ),
    "accepted_findings_carry_rationale": (
        "test_d5_reviews.py",
        "`len(why) < MIN_CHARS` -> False caught; all three historical field spellings "
        "(`evidence`/`rationale`/`note`) exercised, and the missing-ledger H1-silent site "
        "pinned so converting it to FAIL updates this test and the baseline together",
    ),
    # lean_substrate.py: 34 tests / 12 mutations. One MISSED on the first pass, and it
    # found a live defect (QI-28): six of nine `_LEDGER_HEDGE_RE` alternatives were
    # stems closed with `\b` and could not match an inflected form, so correct
    # bookkeeping prose would be flagged as an overclaim. The check was green and its
    # test was green while a sixth of its logic could not execute.
    "formulas": (
        "test_d5_lean_substrate.py",
        "2 mutations: the Lean-name resolution set, and `rglob` -> `glob` (the QI-01 "
        "class at this call site). Reads the check's own `mapping` literal from the AST "
        "so the fixture cannot go stale as formulas are added",
    ),
    "placeholder_not_cited": (
        "test_d5_lean_substrate.py",
        "2 mutations: the offender record, and the `_HEDGE_CLAIM_RE` conjunct — the "
        "latter is what separates an honest statement-level disclosure from an "
        "Invariant #9 overclaim. LaTeX-escaped-underscore and tex_signature legs too",
    ),
    "disclosure_consistency": (
        "test_d5_lean_substrate.py",
        "3 mutations incl. BOTH conjuncts separately, which is how QI-28 surfaced. "
        "Pins `proven` as a deliberate NON-overclaim verb so it is not tightened back in",
    ),
    "proxy_body_audit": (
        "test_d5_lean_substrate.py",
        "2 mutations: the flag, and the `reason`+`discloses` completeness rule that "
        "stops a bare whitelist entry being a free pass. Legs for lemma-scanning "
        "(finding C1), subdirectory recursion, and baseline visibility",
    ),
    "tracked_hypothesis_ledger": (
        "test_d5_lean_substrate.py",
        "`gap` -> `[]` caught; consumption-gating and the Prop-codomain exclusion "
        "exercised; the missing-lean_deps H4 divergence pinned as a known divergence",
    ),
    "tracked_hypotheses_fresh": (
        "test_d5_lean_substrate.py",
        "`if old == new` -> `if True` caught; plus a leg asserting the check does NOT "
        "write the generated doc (ADR-004 W7 M1 — a check that repairs the tree makes "
        "the drift invisible in review)",
    ),
    # physics.py: 27 new tests (test_d5_physics.py) / 10 mutations, plus 4 isolated-defect
    # legs added to the two pre-existing both-directions files after THREE
    # verdict-propagation mutations came back MISSED there — the stale fixtures are wrong
    # in four ways at once, so no single ground carried the verdict alone.
    "numerical": (
        "test_d5_physics.py",
        "`ok = rel_err <= tolerance` -> True caught; the 5% tolerance exercised on both "
        "sides (4% passes, 6% fails) so the constant is load-bearing. Reference table read "
        "from the check's own AST",
    ),
    "identities": (
        "test_d5_physics.py",
        "the identity-failure propagation caught; the acoustic-mode vanishing and the "
        "per-identity exception guard each exercised independently",
    ),
    "paper_table": (
        "test_d5_physics.py",
        "`ok = rel_err <= tolerance` -> True caught; missing-draft fails rather than skips",
    ),
    "d1_hierarchy_table": (
        "test_d1_hierarchy_table.py",
        "pre-existing stale-draft fixture PLUS QI-27 isolated-defect legs. 3 mutations; "
        "`all_pass = all_pass and ok` was MISSED until the isolated legs landed, because "
        "the historical stale draft fails on four independent grounds at once",
    ),
    "f_hierarchy_claims": (
        "test_f_hierarchy_claims.py",
        "same shape as d1: 3 mutations, with `all_pass = all_pass and ok` MISSED until a "
        "leg corrupted ONE value in an otherwise-correct draft so the anchor still matched "
        "and the verdict had to travel through the value comparison",
    ),
    "cgl_fdr": (
        "test_d5_physics.py",
        "3 mutations: the Einstein relation, the first-order BEC FDR, and the even-order "
        "noise-count pattern — each verifier wired independently",
    ),
    "physical_bounds": (
        "test_d5_physics.py",
        "the bound-failure propagation caught; negative temperature, a perturbative "
        "correction above 1, and the conditional shot-count floor each exercised",
    ),
    "cross_path_consistency": (
        "test_d5_physics.py",
        "`ok = rel_diff < 0.005` -> True caught; both comparison paths (delta_diss and "
        "decoherence) shown to move the verdict independently",
    ),
    "quantum_network": (
        "test_d5_physics.py",
        "2 mutations: the identity propagation, and `rglob` -> `glob` — this is the SIXTH "
        "QI-01 site, the one the manual grep sweep missed because its receiver is `qn_dir`",
    ),
    # lean_statements.py (24 tests / 10 mutations) + notebooks.py (19 tests / 6).
    # Two MISSED on the first pass, both fixed by strengthening the TEST, not the code:
    # a placeholder fixture typed `True` was caught by the thin-grounded rule instead
    # (so the placeholder branch was never load-bearing), and a simple-arg identity
    # wrapper never reached R-05 leg B for the same reason.
    "formula_grounding": (
        "test_d5_lean_statements.py",
        "5 mutations across dangling refs, the placeholder branch, thin-grounding and "
        "R-05 legs A/B/C. The wrapper fixture uses a COMPOUND arg deliberately: a "
        "simple-arg wrapper is caught by the thin rule first, so leg B would be untested",
    ),
    "vacuous_statement_audit": (
        "test_d5_lean_statements.py",
        "2 mutations: the hard-fail append and the baseline branch. Legs for autogen "
        "exclusion, the `_DEFINITIONAL` suffix, ground-arith staying advisory, and the "
        "compound-reflexive elision guard that prevents a false-positive class",
    ),
    "nogo_substrate_integrity": (
        "test_d5_lean_statements.py",
        "3 mutations: absent backing (Hole B), kernel-purity, and vacuity (Hole A). "
        "Also pins that `native_decide` closure entries are NOT counted as project "
        "axioms — that is ADR-002's ratchet, not a taint here",
    ),
    "notebooks": (
        "test_d5_notebooks.py",
        "2 mutations: the violation verdict and the parse-error branch. Legs prove the "
        "predicate is `def NAME(` and not the bare name, so correct notebooks that USE "
        "the physics are not flagged",
    ),
    "viz_consistency": (
        "test_d5_notebooks.py",
        "ADVISORY BY DESIGN (ADR-009 item 3), so the two directions are on the WARNING, "
        "not the verdict: 2 mutations dropping the untagged-.show() and hardcoded-hex "
        "warnings, both caught. A leg pins the advisory disposition itself",
    ),
    "notebook_exec": (
        "test_d5_notebooks.py",
        "2 mutations on the skip-cache. Legs prove a FAILED notebook is never recorded "
        "as vetted, that --force-notebooks bypasses the cache (H5), and that a src/core "
        "edit invalidates it — the last is the cache's worst possible failure",
    ),
}

#: Checks with no both-directions test yet. **This list may only shrink.**
#: Emptying it is audit workstream W-D; see
#: `docs/audits/2026-08-04-qa-qi-infrastructure/README.md` (QI-27).
AWAITING_MUTATION_TEST: frozenset[str] = frozenset({
    
    
    
    "theorems", 
    "lean_source", "lean_build", "axiom_closure_allowlist",
    "elaboration_knob_watchlist", "bundle_figure_integrity", 
    "paper_provenance",
    "parameter_provenance", "counts_fresh", "tables_fresh", "claim_clusters_fresh",
    "graph_integrity", "atlas_integrity", "atlas_hypothesis_discipline",
    "bundle_metadata_matches_graph",
    "notebook_stored_outputs_current", "readiness_verdicts_agree",
    "citation_primary_sources_present", "provenance_doi_in_registry", "bundle_consistency",
    "bundle_source_freshness", "bibitem_title_primary_source", 
    "bundle_registry_consistency", "axiom_count_prose_consistency",
    "prose_theorem_reference_coverage", "theorem_name_embedded_citations",
    "inventory_index_autogen_fresh", "lean_docstring_refs_resolve",
    "paper_toolchain_pin_drift",
})

#: The ratchet. Measured 2026-08-04. It may be LOWERED, never raised.
#: History: 54 (seeded) -> 50 (reviews.py) -> 44 (lean_substrate.py)
#: -> 35 (physics.py) -> 29 (lean_statements.py + notebooks.py).
AWAITING_CEILING = 29


def _registered() -> list[str]:
    import validate
    return [spec.name for spec in validate._CHECKS]


class TestEveryCheckIsAccountedFor:
    """The leg that makes D5 binding: a new check must DECLARE its test status."""

    def test_every_check_is_accounted_for(self):
        registered = set(_registered())
        declared = set(MUTATION_VERIFIED) | AWAITING_MUTATION_TEST

        undeclared = sorted(registered - declared)
        assert not undeclared, (
            f"{len(undeclared)} registered check(s) declare no D5 status: {undeclared}. "
            f"ADR-009 D5 requires every new or modified check to ship a test that FAILS "
            f"on a seeded defect and stays SILENT on correct data. Add it to "
            f"MUTATION_VERIFIED (naming the test, once you have actually run the "
            f"mutation) or — if you are knowingly deferring — to AWAITING_MUTATION_TEST "
            f"AND lower nothing, which will trip the ceiling and force the decision to "
            f"be explicit. Silence is the one option D5 does not allow."
        )

        stale = sorted(declared - registered)
        assert not stale, (
            f"{len(stale)} name(s) declared here are not registered checks: {stale}. "
            f"A check was renamed or removed and its D5 entry was left behind, so this "
            f"file now asserts something about nothing."
        )

    def test_the_two_lists_are_disjoint(self):
        both = sorted(set(MUTATION_VERIFIED) & AWAITING_MUTATION_TEST)
        assert not both, (
            f"{both} appear in BOTH lists. A check is either mutation-verified or it is "
            f"not; carrying it in both makes the backlog count meaningless."
        )


class TestBacklogOnlyShrinks:
    """The ratchet. Same idiom as VACUOUS_STATEMENT_BASELINE."""

    def test_backlog_only_shrinks(self):
        n = len(AWAITING_MUTATION_TEST)
        assert n <= AWAITING_CEILING, (
            f"{n} checks await a mutation test, above the frozen ceiling of "
            f"{AWAITING_CEILING}. A check was added without one. Write the test, or "
            f"raise AWAITING_CEILING in the same commit with a stated reason — which "
            f"is a decision on the record rather than a drift."
        )

    def test_the_ceiling_tracks_the_backlog(self):
        """A ceiling far above the population is headroom in which the ratchet does
        nothing — the exact defect found in `ledger_ids_resolve`, which sat at 67
        against a population of 66 and so admitted one new dangling record silently.
        """
        n = len(AWAITING_MUTATION_TEST)
        assert AWAITING_CEILING == n, (
            f"AWAITING_CEILING is {AWAITING_CEILING} but the backlog is {n}. Every unit "
            f"of slack is a check that can be added untested without failing anything. "
            f"When you remove a name from the backlog, lower the ceiling in the same "
            f"commit so the ratchet keeps biting at exactly one."
        )


class TestVerifiedEntriesAreReal:
    """A MUTATION_VERIFIED entry must point at a test that exists and mentions the
    check. Without this, promoting a name out of the backlog costs nothing."""

    def test_verified_entries_name_a_real_test(self):
        import re

        broken = []
        for check, (test_file, _why) in sorted(MUTATION_VERIFIED.items()):
            path = TESTS_DIR / test_file
            if not path.is_file():
                broken.append(f"{check}: {test_file} does not exist")
                continue
            if not re.search(rf"\b{re.escape(check)}\b", path.read_text()):
                broken.append(f"{check}: {test_file} never mentions it")
        assert not broken, (
            "MUTATION_VERIFIED entries that do not check out: " + "; ".join(broken)
            + ". An entry here is a claim that a defect was seeded and the named test "
              "failed; it must at minimum point at a test that exercises the check."
        )

    def test_every_verified_entry_records_why(self):
        thin = sorted(c for c, (_f, why) in MUTATION_VERIFIED.items() if len(why.strip()) < 30)
        assert not thin, (
            f"{thin} carry no substantive note on what the mutation was. The note is the "
            f"only durable record — the mutation itself lives in a commit message and "
            f"cannot be re-run from this file."
        )
