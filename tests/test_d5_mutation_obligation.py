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
4. **The fixture-only population is COUNTED and may only shrink** —
   `PRODUCTION_SEEDED` / `FIXTURE_ONLY_CEILING`, added 2026-08-05. See the block
   above that set for why; the short version is that (1)–(3) were all satisfied by
   four checks that could not fail in production.

⚠️ **THIS FILE DOES NOT PROVE A TEST IS GOOD.** It proves the project has made a
DECISION about every check and cannot silently add an untested one. Do not read a
green run here as coverage — read the named test.

⚠️ **NOR DOES IT PROVE A CHECK CAN FAIL.** That is a different claim and it now has
its own ratchet: 4 of 59 checks have been seen to fail against a defect written into
the real artifact they read. The other 55 have not. Obligation (4) exists because
obligations (1)–(3) read as completeness while that gap was invisible.

**STATUS 2026-08-04: THE BACKLOG IS EMPTY. All 59 registered checks are
mutation-verified, `AWAITING_MUTATION_TEST` is empty and `AWAITING_CEILING` is 0.**

That changes what this file is for. It was written to stop the untested population
GROWING while audit W-D worked it down; with the backlog at zero the ceiling now
holds the line at 100%, and the first check added without a both-directions test
fails on arrival rather than being absorbed into a backlog. Adding a name to
`AWAITING_MUTATION_TEST` is no longer a deferral — it breaks the ceiling
immediately, which is the intended cost.

⚠️ **A `MUTATION_VERIFIED` entry is a claim, and claims decay.** Each names the test
and what was mutated; the mutation runs themselves live in the commits. If you
change a check's logic, its recorded mutations no longer describe the code — re-run
them rather than trusting the entry. The seam guard below only proves the named test
EXISTS and mentions the check.

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
    "bundle_apex_resolves": (
        "test_bundle_closure.py",
        "28 tests. Production-seeded BOTH directions in the real "
        "`papers/D6/bundle_metadata.json`: a dangling `apex_theorems` entry -> FAIL naming "
        "it; the live `GaugingQEC.gaugingQEC_auxQubit_overhead_le` -> PASS with a real "
        "closure (1 apex -> 3 declarations, depth 1); reverted, back to PASS. Also mutated "
        "the production body — defeating the `UNDECLARED_APEX_CEILING` comparison fails "
        "`test_the_undeclared_count_RISING_is_a_hard_failure`, which is the assertion that "
        "keeps the check non-vacuous while no bundle has declared apexes",
    ),
    "lean_modules_in_build_graph": (
        "test_d5_lean_toolchain.py",
        "6 tests; production-seeded by deleting `import SKEFTHawking.AtlasAttr` (a true "
        "LEAF) from the real root aggregate -> red, green on restore. A non-leaf is a bad "
        "probe: a module another module imports stays transitively reachable and the check "
        "correctly stays green. Also asserts the exe-root allowlist is DERIVED from "
        "lakefile.toml by removing the declaration and requiring the verdict to flip",
    ),
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
    "bundle_tables_use_pipeline": (
        "test_d5_papers_prose.py",
        "raise the ceiling above the measured population -> the ratchet stops "
        "firing; drop a hand-written tabular into a bundle draft -> summary FAILS"),
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
        "live self-remediating corpus. QI-34 added the `name`-vs-truncated-`label` leg, "
        "both directions of the resolution-notice exemption, and a PRODUCTION probe: a "
        "real recurrence written into papers/AutomatedReviews/ turns the check red "
        "(0.857 on `name` against the 0.45 threshold, where the same pair scored "
        "exactly 0.400 against the old 0.40 — at the threshold, not above it)",
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
        "REWRITTEN under QI-31 — the check now parses the SHIPPED table. 5 code "
        "mutations CAUGHT (cell comparison -> True; verdict propagation; the "
        "empty-table, dropped-row and \\input-wiring guards), AND 3 mutations seeded "
        "in the PRODUCTION artifact itself (drifted cell / rules-with-no-rows / "
        "dropped row) each turn `validate.py --check paper_table` red",
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
    # freshness.py: 37 tests / 13 mutations. The three regenerators are QUARANTINED from
    # the characterization harness (they mutate the tree), so a real test is the only
    # protection they have ever had.
    "counts_fresh": (
        "test_d5_freshness.py",
        "3 mutations on `_counts_is_stale` incl. `rglob` -> `glob` — ADR-004 W7 M2, the "
        "ORIGINAL instance of the QI-01 class. A failed/unrunnable generator fails the "
        "check rather than reading as fresh",
    ),
    "tables_fresh": (
        "test_d5_freshness.py",
        "2 mutations incl. `min` -> `max` over output mtimes: taking the NEWEST output "
        "would let one regenerated table vouch for a stale set",
    ),
    "claim_clusters_fresh": (
        "test_d5_freshness.py",
        "2 mutations; the v1/v2 discriminator exercised so a v1 review cannot trigger "
        "regeneration it does not govern",
    ),
    "notebook_stored_outputs_current": (
        "test_d5_freshness.py",
        "6 mutations. One leg per reviewer-demonstrated bypass of an earlier version: "
        "stale figure title (round-7), moved scalar marker (round-8), base64-vs-list "
        "asymmetry (round-8), length-only digest (round-9), narrow MIME allow-list "
        "(round-10), hand-edited SVG (round-12), plus the empty-scope FAIL",
    ),
    "bundle_source_freshness": (
        "test_d5_freshness.py",
        "the `--strict` WARN->FAIL promotion caught; that is the only behaviour a bug "
        "could silently disable, and STRICT_MODE is read by attribute (H5)",
    ),
    "inventory_index_autogen_fresh": (
        "test_d5_freshness.py",
        "ADVISORY BY DESIGN (item 3), so both directions are on the WARNING. A leg pins "
        "that a raising generator can never fail the suite",
    ),
    # lean_toolchain.py: 34 tests / 14 mutations. Also CLOSES the QI-11 residue — the
    # lake-resolution block duplicated in check_lean_build and
    # check_axiom_closure_allowlist now has one owner. Deferred to W-D on purpose: it
    # changes two checks' early-return path, which ADR-009 D4 forbids mixing into a
    # mechanical pass. Only the RESOLUTION is shared; each caller keeps its own SKIP
    # message, and a test asserts the two messages stayed DIFFERENT (H4's policy line).
    "theorems": (
        "test_d5_lean_toolchain.py",
        "⚠️ REWRITTEN under QI-30 — all three of its previous legs were VACUOUS (two "
        "unreachable behind constants.py's import-time assert, one a tautology), and my "
        "first pass only pinned that the three hardcoded copies agreed. 4 mutations "
        "against the replacement, which resolves every registry key to a real Lean "
        "declaration and ratchets the 14 that do not",
    ),
    "lean_source": (
        "test_d5_lean_toolchain.py",
        "2 mutations incl. `rglob` -> `glob`; the non-recursive form hid 7,695 declared "
        "identifiers, so a spot-check name moved into a package read as NOT found",
    ),
    "lean_build": (
        "test_d5_lean_toolchain.py",
        "`ok = result.returncode == 0` -> True caught; timeout fails rather than passes; "
        "the no-lakefile SKIP is pinned as a deliberate optional-toolchain PASS (item 4)",
    ),
    "axiom_closure_allowlist": (
        "test_d5_lean_toolchain.py",
        "3 mutations incl. the `--strict` promotion (H5) and the native_decide category. "
        "The AXIOM_METADATA escape is exercised, since the rule is DISCLOSURE not ban",
    ),
    "elaboration_knob_watchlist": (
        "test_d5_lean_toolchain.py",
        "ADVISORY BY DESIGN (item 3 — kernel re-checks the term and never reads these "
        "knobs), so both directions are on the WARNING. A leg pins that maxHeartbeats is "
        "deliberately NOT watched here — Invariant #10 bans it outright elsewhere, and "
        "listing it would read as 'allowed with a warning'",
    ),
    "lean_docstring_refs_resolve": (
        "test_d5_lean_toolchain.py",
        "5 mutations incl. narrowing the block regex back to `/-- … -/`, which is the gap "
        "that hid a reference to a nonexistent declaration in a module header through "
        "five adversarial reviews. Strict-family vs advisory and the disclaimer exemption "
        "both exercised; the missing-lean_deps THIRD H4 policy (pass-with-warning) pinned",
    ),
    # graph_atlas.py: 26 tests / 11 mutations.
    "graph_integrity": (
        "test_d5_graph_atlas.py",
        "5 mutations. One leg per documented defect in its own comment history: the "
        "two-digit roster round-trip, the STRENGTHENED flags-its-own-bundle predicate "
        "(the weak version survived three reviewer mutations), the second leg for "
        "findings whose inference FAILS, the 66-vs-67 ledger baseline headroom, and BOTH "
        "exception handlers converted from fail-open to fail-closed",
    ),
    "atlas_integrity": (
        "test_d5_graph_atlas.py",
        "6 mutations across all five legs. Includes the R-07 suffixed-discharge "
        "recognition (without it, CORRECT closures report as bogus) and the "
        "phantom-vs-namespace-drift split (a stale FQN prefix is not a nonexistent "
        "target, and conflating them would make the gate unusable)",
    ),
    "atlas_hypothesis_discipline": (
        "test_d5_graph_atlas.py",
        "INFO-ONLY BY DESIGN (ADR-007 PD-2) — pinned that it never gates however bad "
        "the distribution, AND that its one `passed=False` is the exception handler, a "
        "fail-on-cannot-measure. ADR-009 Alternatives note 3 records a reconnaissance "
        "agent misreading exactly that as a contradiction",
    ),
    # papers_prose.py: 20 tests / 10 mutations (+2 on the pin-drift core).
    "paper_provenance": (
        "test_d5_papers_prose.py",
        "figure resolution (incl. the extension-append leg) and the LaTeX-comment "
        "strip that keeps cleanup records from false-positiving. ⚠️ The "
        "theorem-reference leg was DELETED under QI-32: its regex could not cross the "
        "`\\_` LaTeX escape and had matched 0 references since 2026-03-26, so the "
        "`rglob` -> `glob` mutation recorded here on 2026-08-04 was CAUGHT against a "
        "fixture using a spelling no draft contains. Lean-name resolution now belongs "
        "entirely to `prose_theorem_reference_coverage`",
    ),
    "axiom_count_prose_consistency": (
        "test_d5_papers_prose.py",
        "5 mutations on the pure core `_axiom_prose_findings`. ADR-009 item 5 holds "
        "this up as the MODEL the literal checks should reach, because it compares "
        "prose to COMPUTED TRUTH. Its value is in the exclusions, so each is a leg: "
        "historical attribution, preceding negation, per-wave deltas, word-numeral "
        "plurals, comment stripping with offsets preserved",
    ),
    "paper_toolchain_pin_drift": (
        "test_validate_toolchain_pin_drift.py",
        "ADVISORY BY DESIGN (item 3 — a stale pin in a DRAFT is a publication decision, "
        "and auto-failing would push authors toward find-and-replace). Pre-existing "
        "test of the extracted pure core `_tp_scan_lines`; mutation-verified under "
        "QI-27 — dropping the third-party exemption and widening the mathlib context "
        "are both CAUGHT",
    ),
    # prose_lean_refs.py: 12 tests / 8 mutations. Covers the step the pre-existing
    # test_validate_prose_checks.py could not: it exercises the pure cores thoroughly
    # but reaches the CHECKS only through a live-tree smoke test, so the propagation
    # from "the core found a problem" to "the check FAILS" was untested.
    "prose_theorem_reference_coverage": (
        "test_d5_prose_lean_refs.py",
        "4 mutations incl. `all(...)` -> `any(...)` on the disclaimer exemption — one "
        "disclaimed mention must not excuse a bare one elsewhere in the same draft. "
        "The missing-lean_deps FAIL (the strict side of the H4 divergence) is pinned. "
        "QI-32 added the LEGACY leg (43 non-bundle drafts, previously covered only by "
        "`paper_provenance`'s dead regex): 3 further mutations CAUGHT, plus one seeded "
        "in a PRODUCTION draft, plus a zero-headroom assertion on the live ceiling",
    ),
    "theorem_name_embedded_citations": (
        "test_d5_prose_lean_refs.py",
        "4 mutations. TWO were MISSED until the tests asserted the DETAIL as well as "
        "the verdict: the strict branch only sets how a finding RENDERS (the verdict "
        "comes from a separate line), and the no-inferable-author skip changes no "
        "verdict at all, so its emitted detail is the only observable",
    ),
    # citations.py: 25 tests / 12 mutations. THREE of the six `--strict` consumers live
    # here, which makes this module the centre of ADR-009 item 6. That item declined the
    # filed complaint but recorded a residue: five strict legs enforce concerns NO
    # ReadinessGate covers, and nothing automated passes --strict, so they run only when
    # a human does. Each strict promotion is a leg.
    "parameter_provenance": (
        "test_d5_citations.py",
        "6 mutations across coverage, LLM verification, value consistency, null-value "
        "conflicts, the --strict human-verification promotion, and the PROJECTED-tier "
        "exemption (demanding human verification of a projection would ask someone to "
        "confirm a number with no measurement behind it)",
    ),
    "provenance_doi_in_registry": (
        "test_d5_citations.py",
        "3 mutations. Pins the deliberate ASYMMETRY: an unregistered DOI is advisory "
        "(strict-gated) while an unresolvable `cited_bibkeys` entry fails in BOTH modes, "
        "because that one is an explicit reference. Case-insensitive DOI matching too",
    ),
    "citation_primary_sources_present": (
        "test_d5_citations.py",
        "the cite-regex narrowing to bare `\\cite{}` is CAUGHT — a narrowed regex "
        "silently shrinks the scanned population. inprep and pre-DOI-textbook exemptions "
        "exercised; no-drafts fails rather than passes",
    ),
    "bibitem_title_primary_source": (
        "test_d5_citations.py",
        "3 mutations. The DROP-WORD path needed its own leg: a wholly different page-1 "
        "title takes the NOT-FOUND branch, so the DROP-WORD detail's rendering was "
        "untested until a fixture reproduced the actual BLOCKER — a title matching "
        "closely but missing one word. QI-33 added 3 more, all CAUGHT (incl. reverting "
        "the strict verdict to its old NOT-FOUND-promoting form), plus a PRODUCTION "
        "probe: a real single-word drift added to CITATION_REGISTRY turns `--strict` "
        "red (8 vs the frozen ceiling 7). ⚠️ Measured limitation, from a probe that "
        "came back MISSED first: DROP-WORD only fires when the REST of the title "
        "matches page 1, so an entry already flagged NOT-FOUND absorbs further drift "
        "silently — 58 live entries are in that state",
    ),
    # bundles_readiness.py: 28 tests / 14 mutations — the LAST module. This is where
    # false green lives: five separate handlers here were converted from fail-open to
    # fail-closed, and each is a leg, because reverting one restores a check that still
    # LOOKS like it is working.
    "bundle_metadata_matches_graph": (
        "test_d5_bundles_readiness.py",
        "4 mutations. The stage13_status green-with-blockers rule is the guard whose "
        "own committed mutation record reads `PASS <-- missed` (the test existed, the "
        "guard did not). A separate leg isolates the COUNT comparison, which was not "
        "load-bearing while the green rule carried the verdict",
    ),
    "readiness_verdicts_agree": (
        "test_d5_bundles_readiness.py",
        "5 mutations incl. the REVERSE direction (heatmap GREEN while a P1 gate is "
        "blocked — live on D6) and the GLOBAL zero-gate guard, isolated with an "
        "all-GREEN roster where nothing else inspects the gate population. That empty "
        "population is the round-8 state: evaluate_all_gates renamed, every readiness "
        "check green with nothing to check",
    ),
    "bundle_consistency": (
        "test_d5_bundles_readiness.py",
        "the cross-bundle cluster scan caught; a missing index FAILS and names the "
        "command that builds it, and exact-match clusters are consistent by "
        "construction so flagging them would manufacture work",
    ),
    "bundle_registry_consistency": (
        "test_d5_bundles_readiness.py",
        "3 mutations across legs B and C. Leg C is the STRUCTURAL guard — a literal "
        "roster planted in a new scripts/*.py is detected, and a sub-threshold grouping "
        "is not. Also pins ADR-009 H2: removing the `validate`/BUNDLE_CODES consumer "
        "entry is PROHIBITED",
    ),
    "bundle_figure_integrity": (
        "test_d5_bundles_readiness.py",
        "a missing shipped PNG FAILS rather than skipping; the 8.0pt legibility floor "
        "is pinned from the AST so it cannot be quietly lowered to make a figure pass. "
        "Stage-9 round 5 found this checker had ZERO consumers repo-wide — honest but "
        "not binding",
    ),
}

#: Checks with no both-directions test yet. **EMPTY as of 2026-08-04, and it may
#: only shrink** — so adding a name here is not a deferral, it breaks the ceiling
#: immediately. That is the intended cost: with the backlog at zero there is no
#: longer a queue for an untested check to join.
#:
#: If you genuinely must defer one, raise `AWAITING_CEILING` in the same commit with
#: a stated reason. That is a decision on the record rather than a drift, which is the
#: whole point of the ratchet — but it also un-does the property this file now holds.
AWAITING_MUTATION_TEST: frozenset[str] = frozenset()

#: The ratchet. It may be LOWERED, never raised (see above).
#: History, one step per module as audit workstream W-D worked the backlog down:
#:   54 (seeded) -> 50 reviews -> 44 lean_substrate -> 35 physics
#:   -> 29 lean_statements + notebooks -> 23 freshness -> 17 lean_toolchain
#:   -> 14 graph_atlas -> 11 papers_prose -> 9 prose_lean_refs -> 5 citations
#:   -> 0 bundles_readiness.  **EMPTY.**
AWAITING_CEILING = 0


#: ══ THE SECOND OBLIGATION: was the defect seeded in a PRODUCTION artifact? ══
#:
#: Added 2026-08-05 after PR review found FOUR checks (QI-31…QI-34) carrying a
#: `MUTATION_VERIFIED` entry, a passing both-directions test, and **no ability to fail
#: in production**. Every one had been "verified" against a monkeypatched fixture that
#: used an input shape the real corpus does not contain:
#:
#:   * `paper_table` — fixture wrote a `paper_draft.tex` containing the literal string
#:     `"draft"`; the check never opened a table, and neither did the test.
#:   * `paper_provenance` — fixture wrote `\texttt{ghost_theorem}`; LaTeX writes
#:     `\texttt{ghost\_theorem}`, the one spelling the regex could not match.
#:   * `recurrence_reopens_closures` — synthetic labels scoring Jaccard 1.0 against a
#:     live corpus whose maximum was 0.375, below the threshold.
#:   * `bibitem_title_primary_source` — the strict branch was exercised by a fixture
#:     while no caller anywhere passed `--strict`.
#:
#: QI-30 stated the criterion — *a mutation caught against a patched fixture does not
#: establish that the check can fail in production* — and it was filed as residue
#: instead of applied as a sweep. This is the sweep, made mechanical: a name enters
#: `PRODUCTION_SEEDED` only when someone has written a defect into the REAL artifact
#: the check reads and watched `validate.py --check <name>` go red.
#:
#: ⚠️ Membership is DELIBERATELY conservative. An entry absent from this set is not a
#: claim that the check is broken — it is the absence of a claim that it works, which
#: is the distinction the four blockers turned on. Erring toward absent overstates the
#: remaining work; the opposite error is what produced them.
PRODUCTION_SEEDED: frozenset[str] = frozenset({
    # 2026-08-06: `apex_theorems` written into the REAL `papers/D6/bundle_metadata.json`
    # — a dangling name -> rc=1; a live theorem -> PASS with a real closure; reverted.
    "bundle_apex_resolves",
    # `import SKEFTHawking.AtlasAttr` deleted from the real `lean/SKEFTHawking.lean`
    # -> 1 orphan -> rc=1; restored, back to PASS.
    "lean_modules_in_build_graph",
    # 2026-08-05: a hand-written `\\begin{tabular}` appended to the REAL
    # `papers/D2/paper_draft.tex` -> 5 vs ceiling 4 -> rc=1; restored, back to PASS.
    "bundle_tables_use_pipeline",
    # QI-31: a drifted cell / a rules-only table / a deleted row written into
    # `papers/paper1_first_order/tables/table1_experimental_params.tex` -> rc=1 each.
    "paper_table",
    # QI-32: a new unresolved `\texttt{}` reference added to
    # `papers/paper12_polariton/paper_draft.tex` -> 82 vs ceiling 81 -> rc=1.
    "prose_theorem_reference_coverage",
    # QI-33: a real single-word title drift added to `CITATION_REGISTRY`
    # ("in the Periodically Driven") -> 8 vs ceiling 7 -> rc=1 under `--strict`.
    "bibitem_title_primary_source",
    # QI-34: a real recurrence written into `papers/AutomatedReviews/` -> 1
    # contradicted -> rc=1.
    "recurrence_reopens_closures",
})

#: The ratchet, in the same idiom as `AWAITING_CEILING`: the number of registered
#: checks NOT yet production-seeded. **It may be LOWERED, never raised.**
#:
#: 55 of 59 as of 2026-08-05. That number is the honest state of the sweep the PR
#: review's resume point lists as its top item, and it is deliberately large: it counts
#: every check for which nobody has yet demonstrated a production failure, not every
#: check that is broken. Lower it one check at a time, each with the probe recorded in
#: the commit — the same way the 54-entry `AWAITING_MUTATION_TEST` backlog went to zero.
FIXTURE_ONLY_CEILING = 55


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


class TestProductionSeedingRatchet:
    """The second obligation (2026-08-05): a check that has never been seen to fail
    against a defect in a PRODUCTION artifact is not known to be able to fail.

    This class does NOT verify that any seeding happened — nothing in a repository can,
    because a mutation is an act performed against the tree and not an artifact left in
    it (the same reason `MUTATION_VERIFIED` is a curated registry and not a scanner).
    What it enforces is that the population of un-seeded checks is COUNTED, VISIBLE and
    may only shrink. Before this existed, the number was zero-and-unstated, and four
    checks that could not fail sat inside it.
    """

    def test_production_seeded_names_are_registered_checks(self):
        """A name here must be a live check. Otherwise the ratchet can be satisfied by
        a typo — the shape `ledger_ids_resolve` shipped and `graph_integrity` had to
        find."""
        unknown = sorted(PRODUCTION_SEEDED - set(_registered()))
        assert not unknown, (
            f"PRODUCTION_SEEDED names checks that are not registered: {unknown}. "
            f"A ratchet counting names nobody runs counts nothing.")

    def test_a_production_seeded_check_is_also_mutation_verified(self):
        """Seeding a production defect is strictly stronger than the fixture-level
        obligation, so the weaker claim must already be on the record. A name that
        appeared only here would leave `MUTATION_VERIFIED` looking complete while a
        check bypassed it."""
        orphan = sorted(PRODUCTION_SEEDED - set(MUTATION_VERIFIED))
        assert not orphan, (
            f"production-seeded but not in MUTATION_VERIFIED: {orphan}")

    def test_the_fixture_only_population_only_shrinks(self):
        """The ratchet itself."""
        n = len(set(_registered()) - PRODUCTION_SEEDED)
        assert n <= FIXTURE_ONLY_CEILING, (
            f"{n} registered checks have never been seeded in a production artifact, "
            f"above the frozen ceiling of {FIXTURE_ONLY_CEILING}. A check was added "
            f"whose verification is fixture-only. Seed the defect in the real artifact "
            f"it reads and record the probe in the commit, or raise "
            f"FIXTURE_ONLY_CEILING with a stated reason — which is a decision on the "
            f"record rather than a drift.")

    def test_the_ceiling_has_ZERO_headroom(self):
        """Slack in a ratchet is the ratchet not working. Measured precedent:
        `ledger_ids_resolve` sat at 67 against a population of 66 and silently admitted
        one new dangling record; `recurrence_reopens_closures` was set above its own
        corpus maximum three times."""
        n = len(set(_registered()) - PRODUCTION_SEEDED)
        assert FIXTURE_ONLY_CEILING == n, (
            f"FIXTURE_ONLY_CEILING is {FIXTURE_ONLY_CEILING} but {n} checks are "
            f"fixture-only. When you seed one in production, LOWER the ceiling in the "
            f"same commit so the ratchet keeps biting at exactly one.")

    def test_the_four_PR_REVIEW_blockers_are_seeded(self):
        """The regression pin. These are the four that carried a MUTATION_VERIFIED
        entry, a passing both-directions test, and no ability to fail in production
        (QI-31…QI-34). Each now has a probe against the real artifact; dropping one
        from this set without recording why is how the claim would decay back."""
        expected = {"paper_table", "prose_theorem_reference_coverage",
                    "bibitem_title_primary_source", "recurrence_reopens_closures"}
        missing = sorted(expected - PRODUCTION_SEEDED)
        assert not missing, (
            f"{missing} were the PR-review merge blockers and their production probes "
            f"are recorded in commits 17bbe234 / 2dc856ec / 865db716 / 637d1184")


class TestVerifiedEntriesAreReal:
    """A MUTATION_VERIFIED entry must point at a test that exists and mentions the
    check. Without this, promoting a name out of the backlog costs nothing."""

    @staticmethod
    def _code_only(src: str) -> str:
        """Source with DOCSTRINGS REMOVED, unparsed.

        ⚠️ Why stripping them matters. This guard originally matched raw file text,
        so an entry was satisfied by the check's name appearing in a module
        docstring — and these files describe every check they cover in prose.
        Measured 2026-08-04: **3 of 59 entries were satisfied by prose alone**, and
        one of those (`axiom_count_prose_consistency`) turned out never to invoke its
        registered check at all, only a pure core. Promoting a fictional entry cost
        one line of prose; it now costs a call.
        """
        import ast

        tree = ast.parse(src)
        for node in ast.walk(tree):
            body = getattr(node, "body", None)
            if isinstance(body, list) and body and isinstance(body[0], ast.Expr) \
                    and isinstance(body[0].value, ast.Constant) \
                    and isinstance(body[0].value.value, str):
                body.pop(0)
        return ast.unparse(tree)

    def test_verified_entries_name_a_test_that_calls_the_check(self):
        """The seam guard: the named test must reference the check IN CODE.

        The reference is resolved from the live registry (`spec.func.__name__`), not
        guessed as `check_<name>` — several registered names differ from their
        function (`theorems` → `check_theorem_count`, `identities` →
        `check_formula_identities`, `formulas` → `check_formulas_to_theorems`), and a
        guard that guessed would report those as fictional while they are covered.
        """
        import re

        import validate
        func_of = {spec.name: spec.func.__name__ for spec in validate._CHECKS}

        broken = []
        for check, (test_file, _why) in sorted(MUTATION_VERIFIED.items()):
            path = TESTS_DIR / test_file
            if not path.is_file():
                broken.append(f"{check}: {test_file} does not exist")
                continue
            code = self._code_only(path.read_text())
            fn = func_of.get(check)
            if not ((fn and re.search(rf"\b{re.escape(fn)}\b", code))
                    or re.search(rf"\b{re.escape(check)}\b", code)):
                broken.append(
                    f"{check}: {test_file} never references it outside a docstring "
                    f"(looked for `{fn}` and `{check}`)")
        assert not broken, (
            "MUTATION_VERIFIED entries that do not check out: " + "; ".join(broken)
            + ". An entry here claims a defect was seeded and the named test FAILED. "
              "It must at minimum point at a test whose CODE exercises the check — a "
              "mention in prose is not coverage."
        )

    def test_every_verified_entry_records_why(self):
        thin = sorted(c for c, (_f, why) in MUTATION_VERIFIED.items() if len(why.strip()) < 30)
        assert not thin, (
            f"{thin} carry no substantive note on what the mutation was. The note is the "
            f"only durable record — the mutation itself lives in a commit message and "
            f"cannot be re-run from this file."
        )
