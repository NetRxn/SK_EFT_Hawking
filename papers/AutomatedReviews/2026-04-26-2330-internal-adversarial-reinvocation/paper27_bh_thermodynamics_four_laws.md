---
paper: paper27_bh_thermodynamics_four_laws
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-26T23:30:00Z
review_kind: re-invocation
prior_review: papers/AutomatedReviews/2026-04-26-2300-internal-adversarial/paper27_bh_thermodynamics_four_laws.md
readiness_gates_version: 1
---

# Adversarial Re-invocation — paper27_bh_thermodynamics_four_laws

## Summary

Stage 13 re-invocation against the post-strengthening state. The
strengthening pass closed most of the previous review's BLOCKERs and
REQUIREDs cleanly, including: ADWSecondLaw + FourLaws_* True
placeholders (3.1, 3.2), all four falsifier theorems
(3.3, 3.4) — now substantive non-tautological proofs anchored to
strict-monotone-decay or contradiction derivations; the
new substantive `wave3_bridge_kaul_majumdar_at_e_squared_anchor`
which actually imports Wave 3 and calls `kaulMajumdarS` (3.5);
the rename `falsifier_chi_vest_dependence` → `falsifier_alpha_ADW_dependence`
(3.7); the StrengtheningPost2026 internal-memo bibitem
removal (1.4); the GloriosoLiu2018 + CrossleyGloriosoLiu2017 used_in
+ doi_verified updates (1.5); the BH_THERMODYNAMICS_PARAMS
Schottky/JK constants residue (4.1); the stale Schottky
fig_T_H_vs_M_regime_partition.png removal (4.2); and the §8
"five mutually-independent FourLaws fields" prose overclaim (5.2).
The Lean module builds clean with 21 substantive theorems / 0 sorry
/ 0 new axioms; counts.tex matches; validate.py 22/22 PASS.

However, the re-invocation surfaces **2 NEW BLOCKERs** and **1 NEW
REQUIRED** that the strengthening pass introduced (or failed to
propagate):

- **NEW BLOCKER 1.6 — Procopio author-name drift in paper PROSE.** The
  bibitem and CITATION_REGISTRY were correctly updated to 3 authors
  (Balbinot, Fagnocchi, Fabbri), but the paper PROSE still names
  "Procopio" as a fourth author in 3 places (abstract line 40, intro
  line 80, §3.2 line 199). Lean module docstring also still has
  "Procopio" in 2 places (lines 22, 117). The fix to the bibitem
  metadata (previous BLOCKER 1.1) was incomplete — author-list
  drift remains.

- **NEW BLOCKER 5.3 — Stale `thirdLaw_Israel_BPS_conditional`
  reference.** Paper §7 line 394-396 says "We encode the third law as
  a conditional Prop `thirdLaw_Israel_BPS_conditional` in
  `FourLaws_ADWExtremality`." This Lean identifier does NOT exist in
  the post-strengthening module — it was deleted along with the other
  `True` placeholder fields. Paper-side prose drift from
  Lean-side strengthening.

- **NEW REQUIRED 5.4 — `M_c` parameter-list inconsistency.** Three
  places in the paper write `M_c(α_ADW, Λ_UV, N_f, χ_vest)` (abstract
  line 58, §1 line 105, §novelty line 511), implying χ_vest is a
  parameter of M_c. The Lean reality:
  `M_c(p) := p.N_f * p.Λ_UV / (12 π * p.α_ADW)` uses only 3 of the 4
  ADWParams fields (NOT χ_vest). Three other places in the paper
  correctly write `M_c(α_ADW, Λ_UV, N_f)` (lines 34, 157, 539, eq:Mc-default).

The previous **REQUIRED 3.5** finding's surface remediation (added
new substantive bridge `wave3_bridge_kaul_majumdar_at_e_squared_anchor`)
addresses the "phantom bridge" critique by importing Wave 3 + calling
`kaulMajumdarS` — but the original tautological theorem
`wave3_bridge_weak_nernst_holds_strong_nernst_violated` remains in
the module as a generic-positivity-propagation declaration. The
strengthening did not delete it. Severity STILL OPEN at REQUIRED
level (the new substantive bridge mitigates by being the load-bearing
claim; the old tautology is now positioned as a generic propagation
helper, but its proof body still does not reference Wave 3).

The previous **RECOMMENDED 6.1** finding (`H_RegimePartition.M_c_form_consistent`
trivially provable) is still present (the field is still in the
struct); RECOMMENDED severity, no submission impact.

Verdict: **NOT submission-ready.** Two NEW BLOCKERs (one
re-introduced as a partial fix, one introduced by the strengthening's
prose drift) keep CitationIntegrity and LeanProofSubstance gates
blocked. The strengthening pass executed faithfully on the Lean side
but did not close the loop on paper-side prose alignment.

## Re-verification of previous findings

### 1.1 — CLOSED (paper bibitem + registry) / **STILL OPEN as 1.6**
(paper prose)

- **Verification:** bibitem at `paper_draft.tex:579-582` reads
  `R.~Balbinot, S.~Fagnocchi, A.~Fabbri,` (3 authors, no Procopio).
  Registry `Balbinot2005PRD` at `citations.py:2500-2522` reads
  `'authors': 'Balbinot, R. and Fagnocchi, S. and Fabbri, A.'` —
  3 authors, `'doi_verified': True`. Both fixed correctly.
- **Status of original BLOCKER 1.1:** CLOSED at the bibitem +
  registry surface.
- **NEW BLOCKER 1.6:** the strengthening missed paper-prose mentions
  of "Procopio" — surfaces below as a new finding.

### 1.2 — CLOSED — Reall title now verbatim

- **Verification:** `paper_draft.tex:607-611` reads
  `\textit{A third law of black hole mechanics for supersymmetric
  black holes and a quasi-local mass-charge inequality}, Phys. Rev. D
  \textbf{110}, 124059 (2024). arXiv:2410.11956.` Matches registry
  exactly (`citations.py:2581-2598`).
- **Status:** CLOSED.

### 1.3 — CLOSED — Kirklin title + venue now verbatim

- **Verification:** `paper_draft.tex:639-642` reads
  `J.~Kirklin, \textit{Generalised second law beyond the
  semiclassical regime}, JHEP \textbf{07}, 192 (2025). arXiv:2412.01903.`
  Matches registry (`citations.py:2677-2693`) exactly. JHEP 07,192 (2025)
  publication record now present in bibitem.
- **Status:** CLOSED.

### 1.4 — CLOSED — `StrengtheningPost2026` removed

- **Verification:** `paper_draft.tex:644` retains a comment
  `%% Removed StrengtheningPost2026 (internal project memo, not
  externally citable). %% The four-pattern anti-vacuity audit is
  now described inline in §sec:lean.`. No `\cite{StrengtheningPost2026}`
  anywhere in source; no `\bibitem{StrengtheningPost2026}`. Registry
  has no `StrengtheningPost2026` entry. The four-pattern audit is
  inlined at §sec:lean lines 459-468.
- **Status:** CLOSED.

### 1.5 — CLOSED — Glorioso/Crossley registry hygiene

- **Verification:** `GloriosoLiu2018` (`citations.py:564-581`) now has
  `'doi_verified': True` and `used_in` includes
  `papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex`.
  `CrossleyGloriosoLiu2017` (`citations.py:2194-2213`) same:
  `'doi_verified': True` + paper27 in `used_in`.
  `GloriosoCrossleyLiu2017` (`citations.py:2599-2614`) was
  already correct (verified=True, paper27 listed).
- **Status:** CLOSED.

### 3.1 — CLOSED — `ADWSecondLaw` substantive

- **Verification:** `BHThermodynamicsFourLaws.lean:418-420`:
  ```
  structure ADWSecondLaw (b : BHData) (p : ADWParams) (entropy_div : ℝ) : Prop where
    entropy_divergence_nonneg    : 0 ≤ entropy_div
    horizon_area_link_consistent : 0 < b.A
  ```
  Two substantive fields, no `True` placeholders. The bundle now
  parameterizes over an externally-supplied `entropy_div : ℝ` and
  imposes a sign constraint on it (the load-bearing Glorioso–Liu
  Eq. (3.20) content). The `horizon_area_link_consistent` field is
  redundant with `BHData.A_pos` but the docstring explicitly names it
  as an independent consistency witness. Paper §5 line 360-370
  matches the new shape exactly.
- **Status:** CLOSED.

### 3.2 — CLOSED — `FourLaws_*` 3 substantive fields each

- **Verification:** `BHThermodynamicsFourLaws.lean:535-540`
  (`FourLaws_Schwarzschild`):
  ```
  firstLaw_smarr        : 0 < p.G_N_emerg_eval
  secondLaw_Schw        : ADWSecondLaw b p entropy_div
  evap_dT_dt_positive   : 0 < dT_dt_value
  ```
  No `True` fields. `FourLaws_ADWExtremality` (lines 567-573)
  similarly:
  ```
  firstLaw_smarr_with_substrate : 0 < p.G_N_emerg_eval ∧
                                   delta = (p.α_ADW - 1) * p.Λ_UV
  secondLaw_ADWExt              : ADWSecondLaw b p entropy_div
  evap_dT_dt_negative           : dT_dt_value < 0
  ```
  Three substantive fields each. Deferred zerothLaw_* and thirdLaw_*
  surfaced explicitly in the per-bundle docstrings (lines 528-533,
  557-565), referencing Phase 6f infrastructure dependencies.
- **Status:** CLOSED at the Lean side. Paper §8 line 425-426 prose
  also fixed: now reads "three substantive sign claims plus two
  deferred placeholder fields (`zerothLaw_*` and `thirdLaw_Israel_*`)
  that require the classical-GR infrastructure of Phase 6f
  (`Curvature.lean`, `ADMDecomposition.lean`) to encode properly".

### 3.3 — CLOSED — falsifier theorems now substantive

- **Verification:**
  - `falsifier_acoustic_decay_form` (lines 623-641) now takes
    `T_H_alt(t)` matching at `t₁` AND non-decreasing across
    `[t₁, t₂]`, concludes `T_H_alt t₂ ≠ T_H_acoustic_evolution T_H0
    τ_cool t₂`. Proof `intro h_eq_t2; ...; linarith` derives a
    contradiction via the strict-decreasing theorem. The conclusion
    is a non-equality claim (not a hypothesis-repackaging).
  - `falsifier_schwarzschild_heating` (lines 655-665) takes
    `H_RegimePartition` + `classify b p = .Schwarzschild` + observed
    non-positive `dT_dt_evap`, concludes `False` via
    `H.evap_dT_dt_above`. Genuine contradiction-derivation.
- **Status:** CLOSED. Both falsifiers now use load-bearing theorems
  (`T_H_acoustic_evolution_strict_decreasing`, `evap_dT_dt_above`)
  in their proof bodies; conclusions are non-trivial.

### 3.4 — CLOSED — `falsifier_third_law_form` substantive

- **Verification:** lines 683-700 take a
  `τ_approach : ℝ → ℝ` external function, an Israel-strong
  predicate (∀τ_max, ∃ε_th>0, ∀ε∈(0,ε_th], τ_max < τ_approach ε), a
  Kehle–Unger predicate (∃τ_max ε₀>0, ∀ε∈(0,ε₀], τ_approach ε ≤ τ_max).
  Picks `ε := min ε₀ ε_th`, applies both predicates at ε, derives
  `τ_max < τ_approach ε ≤ τ_max` ⇒ `False` via `linarith`. The proof
  uses both inputs substantively. Paper §10 lines 426-433 matches.
- **Status:** CLOSED. Real falsifier; not a vacuous disjunction.

### 3.5 — PARTIALLY CLOSED — new `wave3_bridge_kaul_majumdar_at_e_squared_anchor`
substantive; old generic `wave3_bridge_weak_nernst_holds_strong_nernst_violated`
remains a structural tautology

- **Verification:**
  - Module now imports `SKEFTHawking.BHEntropyMicroscopic` (line 3).
  - New theorem
    `wave3_bridge_kaul_majumdar_at_e_squared_anchor` (lines 754-761)
    actually calls `SKEFTHawking.BHEntropyMicroscopic.kaulMajumdarS`
    at `A = 4·G_N·exp(2)` and uses
    `kaulMajumdar_S_pos_at_e_squared` to discharge positivity. Wave 3
    is genuinely linked.
  - Old generic theorem `wave3_bridge_weak_nernst_holds_strong_nernst_violated`
    (lines 771-774) still present:
    ```
    theorem wave3_bridge_weak_nernst_holds_strong_nernst_violated
        (S_extremal : ℝ) (h_S_pos : 0 < S_extremal) :
        0 < S_extremal ∧ S_extremal ≠ 0 := by
      exact ⟨h_S_pos, ne_of_gt h_S_pos⟩
    ```
    First conjunct IS the hypothesis; second conjunct is one-step
    `ne_of_gt` from same hypothesis. The body does NOT reference
    Wave 3.
- **Status:** The substantive bridge closes the "phantom Wave 3"
  critique that was the original BLOCKER's load-bearing complaint.
  The remaining tautology is now positioned in the docstring as
  "generic positivity propagation" with the substantive anchor
  delegated to the new theorem. STILL-OPEN at REQUIRED severity per
  the original 3.5: a "bridge" theorem whose body doesn't reference
  the bridged module is structurally weak, even when re-framed as a
  helper. Recommend deletion to avoid future readers conflating the
  two declarations.

### 3.6 — STATUS UNCHANGED — `wave1_bridge_G_N_emerg_pos` is a trivial
wrapper

- **Verification:** lines 732-735 — still re-exports
  `G_N_emerg_eval_pos` with an unused `_b` parameter. Original
  RECOMMENDED severity preserved.
- **Status:** UNCHANGED, RECOMMENDED.

### 3.7 — CLOSED — falsifier renamed correctly

- **Verification:** lines 718-722 — theorem now named
  `falsifier_alpha_ADW_dependence`, conclusion
  `0 < (p.α_ADW - 1) * p.Λ_UV` uses both `α_ADW > 1` (input) and
  `p.Λ_pos` (substrate field) substantively. The χ_vest reference
  is removed. Paper §10 lines 434-441 now correctly names the
  theorem and references the historical name only as a note.
  ```
  theorem falsifier_alpha_ADW_dependence
      (p : ADWParams) (h_alpha_above_one : 1 < p.α_ADW) :
      0 < (p.α_ADW - 1) * p.Λ_UV
  ```
- **Status:** CLOSED.

### 4.1 — CLOSED — `BH_THERMODYNAMICS_PARAMS` Schottky residue removed

- **Verification:** `src/core/constants.py:2215-2254`. No
  `SCHOTTKY_T_H_PEAK_DEFAULT`, no `SCHOTTKY_FALSIFIER_TOLERANCE`, no
  Jacobson-Koike Eq. (13) attribution comment. Replaced by
  `T_H_INITIAL_DEFAULT` (line 2230) and
  `ACOUSTIC_DECAY_FALSIFIER_TOLERANCE` (line 2247), both with
  Balbinot-2005 attribution comments. The block at 2224-2229 now
  explicitly notes "Replaces the deleted SCHOTTKY_* entries from the
  initial Wave 5 ship per the post-rewrite provenance correction".
- **Status:** CLOSED.

### 4.2 — CLOSED — Stale figure removed

- **Verification:** `papers/paper27_bh_thermodynamics_four_laws/figures/`
  contains only `fig_T_H_evolution_regime_partition.png`. The pre-rewrite
  Schottky figure `fig_T_H_vs_M_regime_partition.png` is gone.
- **Status:** CLOSED.

### 5.2 — CLOSED — "Five mutually-independent FourLaws fields" overclaim removed

- **Verification:** `paper_draft.tex:467-470` reads:
  "The `FourLaws_*` bundles ship with three substantive sign claims
  plus two deferred placeholder fields (`zerothLaw_*` and
  `thirdLaw_Israel_*`) that require the classical-GR infrastructure
  of Phase 6f (`Curvature.lean`, `ADMDecomposition.lean`) to encode
  properly; this is explicitly disclosed in the per-bundle docstring."
  No instance of "five mutually-independent FourLaws fields" remains.
  (The "five mutually-independent fields" prose now applies only to
  `H_RegimePartition`, which has 5 substantive non-True fields — that's
  consistent.)
- **Status:** CLOSED.

### 5.1 — STATUS UNCHANGED — Project-original disclosure adequate
### 7.1 — STATUS UNCHANGED — counts.tex `\bhThermoTotal{21}` matches Lean (21 substantive theorems)
### 7.2 — STATUS UNCHANGED — Tables N/A
### 8.1 — STATUS UNCHANGED — No production runs claimed
### 6.1 — STATUS UNCHANGED — `H_RegimePartition.M_c_form_consistent` trivially provable; RECOMMENDED

## NEW Findings (introduced or surfaced by re-invocation)

### 1.6 — 🔴 BLOCKER — Paper PROSE still names "Procopio" as 4th Balbinot author (5 places)

- **Gate:** CitationIntegrity
- **Location:**
  - `paper_draft.tex:40` — abstract: "Balbinot, Fagnocchi,
    Fabbri, Procopio (PRD~71, 064019 (2005), arXiv:gr-qc/0405098..."
  - `paper_draft.tex:80` — §intro: "Balbinot, Fagnocchi, Fabbri,
    Procopio~\cite{Balbinot2005PRD}"
  - `paper_draft.tex:199` — §3.2: "Balbinot, Fagnocchi, Fabbri,
    Procopio~\cite{Balbinot2005PRD}"
  - `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:22` — module
    docstring: "Balbinot–Fagnocchi–Fabbri–Procopio, *Quantum Effects
    in Acoustic Black Holes: the Backreaction*, **Phys. Rev. D 71,
    064019 (2005)**"
  - `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:117` — references
    section: "**R. Balbinot, S. Fagnocchi, A. Fabbri, G.P. Procopio**,
    *Quantum Effects in Acoustic Black Holes: the Backreaction*"
- **Observed:** The bibitem at line 579-582 and the registry at
  citations.py:2500-2522 were correctly updated to 3 authors
  (Balbinot, Fagnocchi, Fabbri). But 5 prose references to the same
  paper still name "Procopio" as a 4th author. The reader sees a
  4-author attribution in the abstract and §intro and a 3-author
  attribution in the bibitem — internal inconsistency, AND an
  incorrect citation in 5 places.
- **Evidence:** `grep -n "Procopio" paper_draft.tex
  BHThermodynamicsFourLaws.lean citations.py` — see locations above.
  WebFetch on arXiv:gr-qc/0405098 in the previous review (cache-
  verified) confirmed 3 authors. The TeX archive at
  `Lit-Search/Phase-6a/primary-sources/balbinot/acusticpap.tex:57-67`
  lists exactly 3 authors.
- **Expected:** Paper PROSE references should read "Balbinot,
  Fagnocchi, Fabbri" (3 authors) consistently with the bibitem and
  registry. Lean docstrings same.
- **Fix:** 5 mechanical edits — strip ", Procopio" from the 5 prose
  references. Suggested:
  - `paper_draft.tex:40`: "Balbinot, Fagnocchi, Fabbri (PRD~71, 064019 (2005)..."
  - `paper_draft.tex:80`: "Balbinot, Fagnocchi, Fabbri~\cite{Balbinot2005PRD}"
  - `paper_draft.tex:199`: "Balbinot, Fagnocchi, Fabbri~\cite{Balbinot2005PRD}"
  - `BHThermodynamicsFourLaws.lean:22`: "Balbinot–Fagnocchi–Fabbri,"
  - `BHThermodynamicsFourLaws.lean:117`: "R. Balbinot, S. Fagnocchi, A. Fabbri,"
- **Cache:** cache-verified (previous WebFetch on arXiv:gr-qc/0405098).

### 5.3 — 🔴 BLOCKER — Stale `thirdLaw_Israel_BPS_conditional` reference

- **Gate:** LeanProofSubstance + NarrativeGrounding
- **Location:** `paper_draft.tex:394-396`
- **Observed:** "We encode the third law as a conditional Prop
  `\texttt{thirdLaw\_Israel\_BPS\_conditional}` in
  `\texttt{FourLaws\_ADWExtremality}`."
- **Evidence:** `grep "thirdLaw_Israel_BPS_conditional"
  BHThermodynamicsFourLaws.lean` returns empty (the identifier does
  NOT exist in the post-strengthening module). The strengthening
  pass deleted this field along with the other True placeholders.
  The post-strengthening `FourLaws_ADWExtremality` (lines 567-573)
  has only 3 fields: `firstLaw_smarr_with_substrate`,
  `secondLaw_ADWExt`, `evap_dT_dt_negative` — no `thirdLaw_*`.
  The Lean docstring (lines 558-565) explicitly states the third law
  is "Deferred to Phase 6f+" — but the paper §7 still claims it's
  encoded as a Prop in the bundle.
- **Expected:** Paper §7 prose should match the Lean reality. Either
  (a) re-introduce `thirdLaw_Israel_BPS_conditional` as a substantive
  field in `FourLaws_ADWExtremality`, OR (b) rewrite §7 to disclose
  the deferral consistent with the Lean docstring (e.g., "We discuss
  the third law as a deferred conditional Prop in
  `FourLaws_ADWExtremality`, to be encoded once Phase 6f.5
  `ADMDecomposition.lean` lands; the Reall BPS condition would then
  serve as the restoration hypothesis").
- **Fix:** rewrite `paper_draft.tex:394-396` to match the Lean-side
  deferral disclosure. Recommended: replace "We encode the third law
  as a conditional Prop..." with "We surface the third law as a
  deferred-encoding slot in `FourLaws_ADWExtremality`, with the
  Reall BPS condition as the restoration hypothesis once the
  Phase 6f.5 affine-time integral formalism lands. The Balbinot 2005
  $t \sim 1/T^3$ extrapolation gives the BEC-acoustic Israel-strong
  preservation prose-level."

### 5.4 — 🟡 REQUIRED — `M_c` parameter-list inconsistency (3 places)

- **Gate:** NarrativeGrounding (paper-Lean drift)
- **Location:**
  - `paper_draft.tex:58` — abstract: "$\Mc(\aADW, \Ladw, \Nf, \xivest)$
    is original to this project"
  - `paper_draft.tex:105` — §1: "the existence of a critical mass
    $\Mc(\aADW, \Ladw, \Nf, \xivest)$ separating them"
  - `paper_draft.tex:511` — §novelty: "$\Mc(\aADW, \Ladw, \Nf, \xivest)
    = (\Nf \Ladw) / (12\pi \aADW)$ ansatz is project-original"
- **Observed:** Three places imply $M_c$ depends on χ_vest. The
  formula given at line 511 explicitly expresses $M_c$ without any
  χ_vest dependence (the fourth argument is dangling).
- **Evidence:** Lean definition at
  `BHThermodynamicsFourLaws.lean:241-242`:
  `noncomputable def M_c (p : ADWParams) : ℝ :=
   p.N_f * p.Λ_UV / (12 * Real.pi * p.α_ADW)`. Uses 3 of the 4
  ADWParams fields (NOT χ_vest). The abstract eq:Mc-default at line
  157 correctly writes `\Mc(\aADW, \Ladw, \Nf)` — 3 parameters.
  Lines 34, 539 also use 3-parameter signature. So the paper is
  internally inconsistent: 3-param vs 4-param signatures coexist.
- **Expected:** `M_c` parameter list should consistently exclude
  χ_vest, matching the Lean definition.
- **Fix:** Delete the trailing ", \xivest" in 3 places: lines 58,
  105, 511.
- **Severity rationale:** REQUIRED rather than BLOCKER because the
  abstract and §intro signatures contradict the eq:Mc-default formula
  in the same paper (a reader sees both 3-param and 4-param forms);
  this is internal-inconsistency, not wrong-target. No reader will
  click through to a wrong arXiv ID, but a reader will be confused
  about whether χ_vest enters M_c or not.

## QI Candidates (carried forward and new)

The previous review's two QI suggestions remain valid and the
re-invocation surfaces a third:

1. **`validate.py --check cross_wave_bridge_imports`** (carried
   forward from previous review) — would automatically catch the
   "phantom bridge" pattern that originally triggered finding 3.5.
   The strengthening pass added the substantive bridge but did not
   delete the original tautology; this check would have flagged the
   original on first pass.

2. **PlaceholderMarker extraction over `Prop`-typed `True` fields**
   (carried forward) — the four-pattern audit caught the True
   placeholder anti-pattern in the original review only by manual
   inspection. The extractor should mechanize this.

3. **NEW: `validate.py --check paper_lean_ident_resolve`** —
   for every Lean identifier referenced by the paper (extracted via
   `\\texttt{<ident>}` in `.tex`), verify the identifier resolves to
   an actual `theorem`, `lemma`, `def`, `structure`, or field name in
   the cited Lean module. This would have flagged finding 5.3
   (`thirdLaw_Israel_BPS_conditional`) automatically. This is the
   strengthening-induced regression class — a strengthening pass that
   removes Lean theorems must propagate to paper prose, and the only
   way to enforce that mechanically is paper-side ident resolution
   against the current Lean state.

4. **NEW: `validate.py --check paper_author_consistency`** — for
   every bibkey cited in a paper, verify the prose mentions of the
   paper's authors agree with the registry entry's `'authors'` field.
   Would have flagged finding 1.6 (Procopio in prose vs not in
   bibitem). The four citation finding-classes already exist
   (wrong_target / wrong_author / wrong_title / wrong_venue) — this
   QI extends them to paper-prose audit, not just bibitem audit.

## Final remediation list (3 items must close before submission)

1. **BLOCKER 1.6** — strip ", Procopio" / "Procopio" from 5 prose
   sites (3 in paper_draft.tex, 2 in BHThermodynamicsFourLaws.lean
   docstring).
2. **BLOCKER 5.3** — rewrite paper_draft.tex:394-396 to reflect the
   Lean-side deferral, OR re-introduce `thirdLaw_Israel_BPS_conditional`
   as a substantive field. Match the Lean docstring's Phase 6f.5
   deferral language.
3. **REQUIRED 5.4** — strip ", \xivest" from M_c parameter lists in
   paper_draft.tex lines 58, 105, 511.

After these 3 mechanical edits ship, paper27 should be re-reviewed
once more (Stage 13 third pass) to verify no further drift; if clean,
submission-ready.
