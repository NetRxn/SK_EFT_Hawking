---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: frontier-root-proposal-intake
model: gpt-6.1-sol
review_date: 2026-10-15
kind: targeted-infra-proposal
---

# Focused zero-headroom review

Measured against integrated primary `54b8acc11c137087ef42e08c9cf4ed6e43f20e63`; the relevant inputs are unchanged from the recorded pilot. This finding is open until the supported closure writer records verified remediation.

### 1.1 — MINOR — existing count/citation ratchets retain spare headroom

- **Severity:** minor
- **Lane:** infra
- **Location:** src/core/constants.py; tests/test_d5_citations.py — COUNT_LITERAL_CEILING and CITATION_UNDECLARED_CLASS_CEILING; existing equality-test documentation
- **Observed:** On integrated primary578d0614 the production owners measure90 recognized raw-source matches against91, and77 undeclared citations against78. Their existing equality assertions fail; both production inequality checks pass. The older publication U holds95 for the first constant and is not the application authority.
- **Expected:** Existing zero-headroom contract matches the actual current populations without broadening exemptions or detection scope.
- **Fix:** Lower only the owning primary constants91→90 and78→77; correct the citation equality-test ordinal documentation; retain existing production-seeded guards and every scientific freeze.
- **Verify:** `uv run --no-sync python -m pytest -q -p no:cacheprovider 'tests/test_ratchets_have_zero_headroom.py::TestRatchetsHaveZeroHeadroom::test_population_equals_ceiling[count_literals]' tests/test_always_pass_dispositions.py::TestCountLiteralRatchet::test_PRODUCTION_SEEDED_one_more_count_literal_fails_on_real_draft tests/test_d5_citations.py::TestExemptionIsClaimedNotInferred::test_the_undeclared_ceiling_has_ZERO_headroom tests/test_d5_citations.py::TestExemptionIsClaimedNotInferred::test_seeding_AWAY_a_declaration_turns_the_check_RED`
- **Limits:** All temporary journalled production seeds require a separately allocated exclusive candidate/interval. No actual mutant was run in this read-only proposal. The known single-digit/tie detector finding stays open; no new source-fidelity or scientific acceptance is claimed. The actual parser identity and planner routing must be checked before implementation.

## Revised pilot interpretation

The unchanged count detector recognizes90 RAW TeX-source matches. Context review labels87 as count-shaped source occurrences whose scientific truth/currentness is not independently adjudicated, two as comment-only occurrences (D9:22 and I3:31), and one as a publication-year false positive (D6:91, “Reproducing a2006 theorem…”). These labels are semantic annotations, not a new extraction predicate. The total is NOT90 confirmed false/stale census defects. The proposed ceiling remains90 because the existing check actually counts all90; changing the detector or repairing manuscript claims is outside this package. The revised P/U manifests preserve every original row/measurement, adding explicit categories/context and correcting prior blanket-debt dispositions. Original r1 inputs and the independent mandatory-revision report remain immutable.
