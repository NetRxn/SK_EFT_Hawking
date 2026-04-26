---
paper: paper22_ew_phase_transition
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-26T21:05:00Z
readiness_gates_version: 1
prior_round: 2026-04-25-2002-internal-adversarial
round: 3
---

# Adversarial Review — paper22_ew_phase_transition (Round 3)

## Summary

Round 3 closes the Round 2 BLOCKER (3.4 — paper-side propagation of
the renamed Lean theorem) and the partial-closure of 7.1 (intro / §3
unhedged "unambiguously crossover" claims). Round 2 REQUIRED 6.1
(`cubic_coeff_nonneg` disclosure) is also closed via the new §2.1
"Structure invariants" subsection. counts.tex regen is fresh
(4165 / 173 / 21), and `validate.py --check counts_fresh` passes.
The two new substantive biconditional theorems
(`first_order_iff_positive_latent_heat`, `latentHeat_zero_iff_crossover`)
are confirmed non-trivial: both use `by_contra` + `le_antisymm` /
`lt_of_le_of_ne` chains over `cubic_coeff_nonneg`, neither closes by
`rfl`. The CFH1999 fresh-fetch verification carries forward from
Round 2.

Three Round 1 / Round 2 carryforwards remain unaddressed: 1.2 (four
bibkeys with `doi_verified: None`), 7.2 ("load-bearing input to
Phase 6c.2" still appears at lines 59 and 264), 9.2 (T_c rounding
139.13 vs 139.15 still at lines 147 and 198), 3.3 (advisory only).
None of these were specified for Round 3 closure; they are tracked as
carry-forwards.

**Aggregate verdict: YELLOW.** No new BLOCKERs. No partial-BLOCKERs.
Carryforwards are draft-OK. The paper is **submission-blocked only by
the four `doi_verified: None` bibkeys** (Gate 1) — once a CrossRef
sweep flips those, paper 22 is submission-ready modulo the 7.2 / 9.2
phrasing nits.

Counts: 0 new BLOCKERs, 1 REQUIRED carryforward (1.2), 3 RECOMMENDED
carryforwards (3.3, 7.2, 9.2).

Working finding classes 1 through 8 in order. Citation cache stats:
no new fresh-fetches this round; CFH1999 round-2 record remains the
authoritative match for that bibkey.

## Findings

### 1.1 — 🟢 CLOSED (confirmed Round 2) — KLRS96 / CFH1999 attribution

- **Gate:** CitationIntegrity
- **Round 3 status:** **closed** (cumulative: closed Round 2,
  re-confirmed Round 3)
- **Evidence:** `docs/citation_verifications.jsonl:12` carries the
  Round 2 record `bibkey=CsikorFodorHeitger1999`, `verdict=match`,
  arXiv `hep-ph/9809291`, title "Endpoint of the hot electroweak
  phase transition", authors "F. Csikor, Z. Fodor, J. Heitger", DOI
  `10.1103/PhysRevLett.82.21`. Paper §1 / §3 (lines 78–85, 207–213)
  correctly split the attribution: KLRS96 for the broader 70–95 GeV
  range, CFH1999 for the refined 72.4 ± 1.7 GeV endpoint.
- **Cache:** cache-verified (Round 2 record).

### 1.2 — 🟡 REQUIRED — Four bibkeys still carry `doi_verified: None`

- **Gate:** CitationIntegrity
- **Status unchanged from Round 2** — explicitly out of scope for
  Round 3 per the closure plan ("separate citation-verification
  round").
- **Location:** `src/core/citations.py:1539, 1557, 1576, 1594`
- **Observed:** `CsikorFodorHeitger1999`, `KLRS1996`, `ButtazzoEtAl2013`,
  `ShaposhnikovWetterich2010` all `doi_verified: None`.
- **Fix:** CrossRef live-resolution sweep (separate round).
- **Impact:** Submission gate; not a Round-3 regression.

### 3.1 — 🟢 CLOSED — Lean substance + paper-side propagation (Round 2 NEW BLOCKER 3.4)

- **Gate:** LeanProofSubstance + FixPropagation
- **Round 3 status:** **closed**
- **Evidence (paper-side propagation):**
  - `paper_draft.tex:160` cites `transition_order_unfolds_to_cubic_sign`
    (the renamed theorem) framed as "definitional reduction" — matches
    the Lean docstring at `EWPhaseTransition.lean:254–259` which
    explicitly says the theorem "adds no mathematical content beyond
    unfolding the definitions".
  - `paper_draft.tex:163–169` introduces the substantive correctness-push
    framing and cites `first_order_iff_positive_latent_heat` and
    `latentHeat_zero_iff_crossover` as the actual non-trivial
    biconditionals connecting microscopic (cubic-coefficient) to
    macroscopic (latent-heat) order parameters.
  - The stale name `transition_order_from_microscopic_parameters` no
    longer appears anywhere in `paper_draft.tex`.
- **Evidence (Lean substance, re-audited):**
  - `EWPhaseTransition.lean:337–348` —
    `first_order_iff_positive_latent_heat` proof body uses
    `refine ⟨first_order_has_positive_latent_heat p, ?_⟩`,
    `by_contra h_E_npos`, `push_neg`,
    `le_antisymm h_E_npos p.cubic_coeff_nonneg`,
    `crossover_has_zero_latent_heat`, `linarith`. Non-trivial; the
    converse direction is structurally load-bearing on
    `cubic_coeff_nonneg`. Would NOT close by `rfl` / `trivial` —
    confirmed by inspection of the discharge chain.
  - `EWPhaseTransition.lean:355–365` —
    `latentHeat_zero_iff_crossover` mirror biconditional; uses
    `lt_of_le_of_ne p.cubic_coeff_nonneg (Ne.symm h_E_ne)`,
    `first_order_has_positive_latent_heat`, `linarith`. Non-trivial.

### 3.2 — 🟢 CLOSED (Round 2)

### 3.3 — 🔵 RECOMMENDED — `wave3_open_manifest_consistent` arm trivialised by `cubic_coeff_nonneg` (carryforward)

- **Gate:** LeanProofSubstance
- **Status unchanged.** Paper §5 line 297–302 still describes the
  bundled manifest; the disjunction `IsFirstOrderEW ∨ IsCrossoverEW`
  is structurally satisfied for any `EWFiniteTParams` thanks to
  `cubic_coeff_nonneg`. Advisory.

### 6.1 — 🟢 CLOSED — `cubic_coeff_nonneg` disclosure (Round 2 REQUIRED)

- **Gate:** AssumptionDisclosure
- **Round 3 status:** **closed**
- **Evidence:** New `paper_draft.tex:122–134` "Structure invariants"
  subsection discloses all four `EWFiniteTParams` positivity invariants
  (`mu_sq_pos`, `lam_pos`, `thermal_coeff_pos`, `cubic_coeff_nonneg`)
  in plain prose. The paragraph explicitly notes:
  > The non-negativity (rather than strict positivity) of $E$ is
  > load-bearing for the order classifier... All downstream substantive
  > theorems (latent-heat positivity, crossover ↔ zero latent heat)
  > consume this invariant explicitly.
  This satisfies Gate 6 for the load-bearing assumption flagged Round 2.
- **Cross-check:** `paper_draft.tex:166–169` re-references the
  non-negativity invariant inline at the introduction of the new
  biconditionals: "both of which require the structural non-negativity
  invariant `cubic_coeff_nonneg` of `EWFiniteTParams`." Disclosure
  appears twice — gate satisfied robustly.

### 7.1 — 🟢 CLOSED — Intro / §3 SM-verdict reframing (Round 2 partial-BLOCKER)

- **Gate:** NarrativeGrounding
- **Round 3 status:** **closed**
- **Evidence (intro):** `paper_draft.tex:84` now reads "the resummed
  SM transition is a crossover" (was "the SM transition is
  unambiguously a crossover" at Round 2). The "resummed" qualifier
  carries the LO-vs-loop-corrected framing into the intro. Lines
  86–89 add the explicit reframing: "The strict-LO Lean prediction in
  this paper instead encodes the un-resummed cubic coefficient and is
  reframed below as a structural reference point against which the
  resummed lattice result improves."
- **Evidence (§3):** `paper_draft.tex:214–216` now reads "the resummed
  SM is a crossover; the strict-LO prediction encoded in this paper
  diverges from the resummed lattice verdict at the documented
  threshold." The "unambiguously a crossover" phrasing has been
  removed; replaced with "resummed SM" + explicit divergence flag.
- **Cross-check (abstract):** lines 41–55 already carry the strict-LO /
  physical SM framing. Round 2 had abstract closed; Round 3 confirms
  intro and §3 now match.

### 7.2 — 🔵 RECOMMENDED — "load-bearing input to Phase 6c.2" forward-reference (carryforward)

- **Gate:** NarrativeGrounding
- **Status unchanged.** `paper_draft.tex:59` and `:264` still use
  "the load-bearing input to the future Phase 6c.2 EW-baryogenesis
  bridge theorem". No `Phase6c*.lean` artifact exists. Recommend
  rephrasing to "is intended to feed the future Phase 6c.2 EW-
  baryogenesis bridge" at both sites. Advisory.

### 9.1 — 🟢 CLOSED (confirmed Round 2 + re-audited Round 3) — counts.tex stale

- **Gate:** NumericalFreshness
- **Round 3 status:** **closed**
- **Evidence:** `docs/counts.tex:1` header timestamp
  `2026-04-25T16:02:11.298259` is post-Round-2-fix (Lean substance
  audit refactor landed). Now `\totaltheorems{4165}` (was 4118),
  `\substantivetheorems{4054}` (was 4007), `\leanmodules{173}`
  (was 172), `\papercount{21}`, `\sorrycount{0}`,
  `\axiomcount{1}`. The Round-2-to-Round-3 delta of +47 substantive
  theorems / +1 module is consistent with the announced Lean substance
  audit refactor (BHL `fierz_completeness_holds_for_bhl_dim` + falsifier;
  EW `first_order_iff_positive_latent_heat` + `latentHeat_zero_iff_crossover`;
  TPFEvasion / Z16Classification / SMGClassification / GaugingStep /
  OnsagerAlgebra structure refactors).
- **validate.py confirmation:**
  `uv run python scripts/validate.py --check counts_fresh` exits 0:
  ```
  Overall: 1/1 checks passed
  ALL CHECKS PASSED
  Archived to: docs/validation/reports/validation_20260425T210530Z.json
  ```

### 9.2 — 🔵 RECOMMENDED — T_c rounding 139.13 vs 139.15 (carryforward)

- **Gate:** NumericalFreshness
- **Status unchanged.** `paper_draft.tex:147` and `:198` still quote
  `T_c ≈ 139.13` GeV; canonical computed value 139.1535 rounds to
  139.15. Advisory.

## Round 3 net delta

- **Closed by Round 3 fixes:** 3.1 (paper-side propagation +
  re-audited Lean substance), 6.1 (cubic_coeff_nonneg disclosure),
  7.1 (intro + §3 hedging — full closure of Round 2 partial)
- **Carryforward (no regression, not in scope):** 1.2, 3.3, 7.2, 9.2
- **Newly introduced by Round 3 fixes:** **none**. The §2.1 disclosure
  paragraph reads cleanly; the §3 / abstract / intro hedging is
  consistent across the three locations; the new substantive theorem
  citations match Lean source by name and framing; counts.tex regen
  is consistent with Lean module diffs; no new bibkeys, no new tables,
  no new figures introduced. Re-scan finding classes 1–8 surfaced no
  new issues.

## Submission-readiness assessment

The paper passes Gates 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 in their
current Round-3 audit. **Submission is blocked only by Gate 1** (the
four `doi_verified: None` bibkeys at `src/core/citations.py:1539,
1557, 1576, 1594`). Once a CrossRef sweep flips those four, paper 22
is submission-ready modulo the 7.2 / 9.2 / 3.3 phrasing nits which
are RECOMMENDED-only.

## QI Candidate

None new this round. The Round 2 QI suggestion (a
`validate.py --check paper_lean_refs` cross-check that would have
caught the Round 2 NEW BLOCKER 3.4 paper-Lean rename drift) remains
relevant — Round 3 closure was driven by manual remediation; an
automated check would prevent the next iteration of this drift class.
