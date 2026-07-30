# Phase 6EA — Kernel-Verified Photodetection Statistics: Poisson & Gaussian Discrimination Floors

## 🎯 STATUS: COMPLETE (2026-07-28; round-3 remediation closed 2026-07-29) — all three waves shipped, Stage-13 clean

> **Round-3 remediation — APPLIED AND MERGED (2026-07-29, `fb563b19`).** A third fresh-context
> adversarial pass found **zero mathematical errors**, one BLOCKER at the claims layer, and a
> punch list. All of it is applied: Waves 1–2 (see **Stage 13** below) and Wave 3.
> - **BLOCKER — the quantum bound is now EARNED, not asserted.** Wave 3 had been described as a
>   "diagonal restriction of a quantum two-state discrimination bound" while invoking no quantum
>   bound at all. Rather than narrow the sentence, the bound was built:
>   `QuantumNetwork/HelstromDiscrimination.lean` ships `IsBinaryPOVM`, `helstrom_le_povmAvgError`,
>   `helstrom_isLeast_povmAvgError`, and `quarter_sqrtFidelity_sq_le_povmAvgError` — a genuine
>   Holevo–Helstrom optimality statement over POVMs with the Fuchs–van de Graaf floor beneath it.
>   The Wave-3 claim is now backed by the theorem it names. *(The Stage-2 UNKNOWN-3 finding below —
>   that `OptimalHypothesisRate` is type-level unreachable from a Poisson-on-ℕ carrier — still
>   stands; this bound is the project's own, not a PhysLib specialization.)*
> - `folklore_missFloor_beaten_sixfold` → `folklore_missFloor_beaten_148fold` (verified present in
>   `lean_deps.json` as `SKEFTHawking.Detection.folklore_missFloor_beaten_148fold`; the old name is
>   gone). Wave 2 gained four declarations.
> - **`Detection/` migrated off the deprecated `poissonPMFReal` carrier** onto `poissonMeasure`,
>   atomically across both files via the `hasSum_poissonMeasureReal` helper; zero deprecation
>   warnings remain. Two theorem *names* still contain the dead identifier
>   (`hasSum_poissonPMFReal_mul_id`, `hasSum_poissonPMFReal_mul_descFactorial`) — deliberately kept,
>   since they are cited in frozen `papers/AutomatedReviews/` artifacts; their statements are fully
>   migrated.
> - Counts, `lean_deps.json`, `atlas_view.json` and the Inventory Index were **refreshed by the
>   post-merge gate** and are current as of `fb563b19`: `validate.py` **50/50**, 25,855 theorems.
> The dated build/validate figures in the paragraph below are the **2026-07-28 close-out record**
> and are not restated to the current gate on purpose.

Authorized 2026-07-27, closed 2026-07-28. `lake build` 10,365 jobs clean +
`lake build SKEFTHawking.ExtractDeps` 10,366 clean, **zero sorry, zero axioms**, every declaration
kernel-pure `{propext, Classical.choice, Quot.sound}`; `validate.py` **49/49**. Counts moved
25,279 → 25,460 theorems and 1,992 → 1,998 modules over the session (6EA contributes the three
`Detection/` modules below; the rest is the concurrent 6EB/6EC work).

**Shipped declarations, by wave:**

- **Wave 1 — `Detection/PoissonDiscrimination.lean` (27 decls).** `IsCountRule`, `falseAlarm`,
  `missProb`, `thresholdRule`, `affinity`; the distribution-free chain `affinity_le_binaryAffinity`
  → `binaryAffinity_sq_le_two_mul_add` → `avgError_ge_affinity_sq`; `poissonBhattacharyya_hasSum` /
  `_eq`; the headline `poisson_avgError_floor`; the exact `poisson_avgError_equalRates_eq_half`;
  the dark-baseline trio `poisson_darkBaseline_miss_floor` / `_optimum` /
  `darkBaseline_zeroFalseAlarm_load_bearing` with `falseAlarm_zero`, `isCountRule_thresholdRule`,
  `falseAlarm_thresholdRule_zero`; the ∀-quantified refutations `folklore_miss_floor_false`,
  `folklore_missFloor_beaten_148fold`, `folkloreGap_split`, `folklore_avgFloor_unsound_of_bright`,
  `brightGap_5060`, `folklore_avg_floor_unsound`, `folklore_avgFloor_unsound_factor1000`.
  *(Count basis: `lean_deps.json` lists 28 entries for the module; 27 are authored, the 28th is the
  auto-generated equation lemma `thresholdRule.eq_1`.)*
- **Wave 2 — `Detection/GaussianThreshold.lean` (40 decls after the 2026-07-29 round-3 pass; 36
  before).** Project-local `gaussianQ`, `thrErr0`, `thrErr1`; `gaussianQ_zero` / `_antitone` /
  `_neg` / `_pos` / `_le_half` / `_sub_of_le`; `gaussianPDF_moment_Ioi`; the tails
  `gaussianTail_ge_window`, `gaussianTail_mills`, `gaussianTail_chernoff` (**full `z ≥ 0`**),
  `gaussianTail_birnbaum` (stretch, closed; **unrestricted in `z` since round 3**); the rational
  bracket `gaussianQ_two_le_rational` / `_ge_rational`; `thrErr0_mono_in_sigma`,
  `thrErr1_mono_in_sigma`, `offCenter_threshold_tradeoff`, `midpoint_threshold_symmetric`;
  `avgError_ge_gaussianQ_sharp` (stretch, closed — shipped in place of the ½-constant form);
  **and the round-3 probability bridge** `gaussianReal_map_affine`, `gaussianQ_eq_measure`,
  `thrErr0_eq_measure`, `thrErr1_eq_measure`.
  *(Count basis: `lean_deps.json` listed 40 entries for the module before round 3 = 36 authored + 3
  auto-generated `.eq_1` equation lemmas for this module's three `def`s + 1 foreign
  `QuantumNetwork.avgAssignmentError.eq_1` attributed here because this module first forces it.
  Round 3 adds 4 authored theorems → **40 authored / 44 entries**. Private auxiliaries
  (`gaussianQ_two_le_add_aux`, and since round 3 `gaussianTail_birnbaum_aux`) do **not** appear in
  `lean_deps.json` and are not counted. `lean_deps.json` must be regenerated before these numbers
  can be re-checked mechanically.)*
- **Wave 3 — `Detection/ShotNoise.lean` (~18 decls).** `diagonalPSD`, `psdSqrt_diagonal`,
  `diagonalState_sqrtFidelity_eq_affinity` (S1), `binaryDist`, `binaryDensityOperator`,
  `pushforwardFidelity_eq_binaryAffinity`, `poissonFloor_le_diagonalQuantumBound` (S2, shipped as a
  sandwich); `shotPSD`, `shotPSD_eq_hawkingNoisePSD`, `shotPSD_plane_transfer`, `shotPSD_pos`;
  `hasSum_poisson_thinning` / `poisson_thinning`, `hasSum_poissonPMFReal_mul_descFactorial`,
  `poissonMean_eq`, `poissonMean_thinning`, `thinnedMean_eq_eta_mul`, `poissonVariance_eq`,
  `shotFilteredVariance_boxcar_eq_mean` / `shotFilteredVariance_ramp_gt_mean`;
  `shotGaussian_avgError_gt_leCam_floor`.

  > **Record correction (2026-07-30, record-level audit).** This list previously named
  > `shot_variance_eq_mean`, which resolves to nothing — and the shipped pair says something
  > *stronger and different*: shot variance equals the mean **only for the boxcar window**
  > (`shotFilteredVariance_boxcar_eq_mean`), and is **strictly greater** for a ramp
  > (`shotFilteredVariance_ramp_gt_mean`). The stale name asserted a window-independent identity
  > that the wave's own theorems refute, so this was a claim defect, not just a rename.

**Stage 13.** Round 1 (`2026-07-28-1839`): 2 BLOCKER + 5 MAJOR + 5 MINOR — all remediated.
Round 2 (`2026-07-28-1924`): **ZERO BLOCKER**, both round-1 blockers independently verified closed;
its 3 MAJORs + merited MINORs remediated in `1bd72ceb`. Round 3 (fresh-context, 2026-07-29): **zero
mathematical errors across all three waves** — no incorrect theorem, no missing hypothesis, no seam
mismatch, no numeric drift; every finding was again prose or looseness attached to correct
mathematics. Its calibration note — *6EA's failure mode is consistently narrative inflation around
correct mathematics* — is the standing warning for any D12 lift. Round-3 Waves 1–2 remediation
(2026-07-29):

- **I5** — the missing *probability* bridge. `gaussianQ` was an integral of a density with no
  theorem tying it to `ProbabilityTheory.gaussianReal`, while the whole downstream chain is sold as
  a floor on detector **error probability**. Shipped `gaussianQ_eq_measure` plus
  `thrErr0_eq_measure` / `thrErr1_eq_measure` (the miss branch via the reflected scale `−σ`, so no
  null-set bookkeeping) on the new composite push-forward `gaussianReal_map_affine`.
- **I3** — `thrErr1_mono_in_sigma` was `thrErr0_mono_in_sigma` at permuted arguments counted twice
  (`thrErr1 μ₁ σ t` is *definitionally* `thrErr0 t σ μ₁`). Body is now the one-term application,
  docstring marks it an orientation alias with no separate content.
- **M4/M5** — `gaussianTail_birnbaum` no longer carries `0 < z` (true at every real `z`); the two
  `mono_in_sigma` hypotheses relaxed from `<` to `≤` under the identical proof script.
- **M7/M9 — two loose constants, both from the same cause.** `folklore_missFloor_beaten_sixfold`
  claimed factor 6 against a true `e⁵ = 148.4`, and `gaussianQ_two_le_rational` gave `Q(2) ≤ 1/6`
  against a true `1/43.96`, because both discharged an exponent through `expNeg_enclosure`, whose
  Bernoulli endpoint is intrinsically that loose at `r = 2` and `r = 5`. Both re-routed through
  `Real.exp_one_gt_d9` (already used elsewhere in the family): the falsifier is now
  `folklore_missFloor_beaten_148fold` (0.3 % off truth, 25× sharper) and the bracket is
  `[1/125, 1/37]` (span 3.4, was 20.8). The "non-degenerate bracket" wording is replaced by the
  measured span.
- **Pin drift** — the Wave-2 module docstring's "no `erf`/`erfc`/Gaussian CDF at pin `5e932f97`" was
  written before the v4.32.0 bump; re-verified against the current pin `81a5d257` and updated, with
  the caveat that Mathlib's generic `ProbabilityTheory.cdf` exists but carries no Gaussian closed
  form.

**Carried, not closed (round 3).** Two items are genuinely cross-file and are deliberately *not*
done inside the Waves 1–2 edit: (i) tightening `gaussianQ_two_ge_rational` from `1/125` (35 % of
truth) to a Birnbaum-backed rational near `2.16e−2` (95 % of truth) — `1/125` is hard-coded in two
`MatchedFilter` statements, so it must land in one commit with them; (ii) the
`poissonPMFReal → poissonMeasure` deprecation migration — a **carrier** change (`Measure ℕ` vs
`ℕ → ℝ`), not a rename, and `ShotNoise.lean` passes `poissonPMFReal_nonneg` / `poissonPMFRealSum`
directly against `PoissonDiscrimination`'s `hasSum_falseAlarm` / `hasSum_missProb` /
`affinity_le_binaryAffinity` statements, so it cannot be split by file. The `Mathlib.Data.Real.Sqrt`
→ `Mathlib.Analysis.Real.Sqrt` half of that item **is** done.

**Deviations, all strengthenings** (detail in the two freeze docs' deviation tables): D7's Chernoff
closed at the full `z ≥ 0`; the D10 half-constant floor was dropped as an identity-wrapper once the
sharp form closed; `poisson_thinning`'s `η ≤ 1` and `shotPSD_plane_transfer`'s `0 ≤ η` were dropped
as non-load-bearing; the (S2) seam shipped as a sandwich rather than the frozen conjunction; D3's
`poissonTV_le_of_bhattacharyya` was demoted (off the critical path) and deliberately not shipped.

**Open, carried forward:** the prior-art novelty claim is scoped to verified evidence pending a live
multi-prover search (see the Novelty-claim note below) — a **pre-submission gate for D12**, not a
substrate gap.

---

**Originally: PLANNED (authorized 2026-07-27).** Opens the **new `6E*` thematic series** (theme: *verified device-physics metrology — detection statistics, readout noise floors, electrothermal device physics, and graphene electronic structure*), independent of the `6B*` (comp-chem/OQS → D10), `6C*` (band-theory/metamaterials → D11), and `6D*` (constant-provenance audit) series. The `6E*` series continues the repo's existing public readout-metrology arc (`ReadoutRelaxationBound`, `ThermalAssignmentFloor`, `QuantumFDTFloor`, `GrapheneNoiseFormula`) downward into the *classical detection layer* every physical readout chain bottoms out in.

**Thesis.** Every intensity-detection readout — photon counters, threshold discriminators, homodyne-style filtered-current classifiers — obeys a small set of textbook statistical floors that are routinely *cited* in device papers but have never been *kernel-checked* anywhere: the Bhattacharyya/Le Cam universal floor on Poisson discrimination, the zero-false-alarm dark-baseline optimum, and Gaussian threshold-error algebra with honest tail bounds. **(Corrected 2026-07-28, Stage-13 round 2: this sentence previously also promised "the Neyman–Pearson structure of counting tests". No Neyman–Pearson or likelihood-ratio theorem ships in this phase — the floors are symmetric Bayes/Le Cam bounds. The identical overstatement was struck from the novelty claim below; it survived here, one line above, which is the sentence most likely to be lifted into D12.)** This phase builds that layer once, exactly, in the repo's established `_enclosure` exact-rational style, so that every later device phase (6EB filtered readout, 6EC electrothermal detectors, 6EE composite readout ceilings) *consumes floors instead of re-deriving them* — and so that any experimental claim of discrimination performance can be checked against a machine-verified bound by hand. **(Scope note, 2026-07-29: as shipped, that consumption is of the Wave-2 Gaussian layer and Wave-3's `shotPSD`. 6EB and 6EC consume zero Wave-1 Poisson declarations — see the verified dependency record under Wave 1 below. Any D12 lift of this sentence must not imply the Poisson layer is load-bearing downstream; it is standalone.)**

**NOVELTY CLAIM — REFUTED AS ORIGINALLY STATED; NARROWED 2026-07-28 after a live prior-art sweep.** The original "no theorem prover has a kernel-checked … family" is **false**, and was false inside our own dependency tree:

- **Mathlib already kernel-checks a Chernoff tail bound** — `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` (`Mathlib/Probability/Moments/SubGaussian.lean:334` and `:704`, present **at our own pin**), docstring'd "Chernoff bound on the right tail of a sub-Gaussian random variable", giving `μ.real {ω | ε ≤ X ω} ≤ exp(−ε²/(2c))`. Our Stage-2 sweep missed it because it grepped for `erf`/`erfc`/Q-function — i.e. for the *object* — instead of for the *bound*. It is stated for the sub-Gaussian **class**, not instantiated at `gaussianReal`, and at `c = 1` its constant `exp(−z²/2)` is a **factor 2 weaker** than this phase's `gaussianTail_chernoff` (`½·exp(−z²/2)`), so our theorem is genuinely sharper — but it is a refinement, not a first.
- **PhysLib already kernel-checks quantum hypothesis testing** (`OptimalHypothesisRate`, with compactness/convexity/attainment/CPTP-antitonicity), so any family-level "hypothesis-testing bounds have never been kernel-checked" phrasing is dead on arrival.
- **PhysLib's own `Distance/Fidelity.lean` carries the TODO** `--Matches with classical (squared) Bhattacharyya coefficient` — the classical correspondence this phase's (S1) proves has already been *identified* as a gap by that library's authors, which strengthens the case that it is worth doing and weakens any claim that nobody had noticed it.
- **Mathlib carries the surrounding decision theory** (`avgRisk`/`bayesRisk`/`minimaxRisk`, Degenne–Luccioli 2025) with no binary specialisation and no divergence bridge; and it carries **no** Bhattacharyya/Hellinger/Rényi, **no** `erf`/`erfc`/Gaussian CDF, and **no** Poisson moment lemmas.

**⛔ TWO BLOCKING CHECKS before ANY novelty wording is lifted into D12** — both need a fetch path the in-loop egress whitelist denies, so they are operator-side:
1. **`RemyDegenne/testing-lower-bounds`** (github.com, blocked) — a live Lean project by the author who upstreams Mathlib's decision theory, whose stated scope is f-divergences *and* "error bounds for (sequential) hypothesis testing". A Bayes-binary-risk ↔ divergence lower bound there would be substantially our Le Cam floor. **Highest prior-art risk in the phase.**
2. **Isabelle/AFP `Error_Function` + the `Probability` session, and Coq `infotheo`** (isa-afp.org, github.com, coq.inria.fr — all blocked). `infotheo` formalizes information theory and is a strong candidate to already carry Bhattacharyya/Hellinger and Le Cam-type bounds. **Isabelle and Coq are currently wholly unassessed** — that is a gap in the evidence, not a finding of absence.

**The only form supported by evidence today** (hedged to knowledge, not asserted as fact): Mathlib supplies the surrounding decision theory and a sub-Gaussian Chernoff bound, and PhysLib supplies quantum hypothesis testing and fidelity; *to our knowledge* the Poisson Bhattacharyya closed form, the zero-false-alarm Poisson miss optimum, the Mills/Birnbaum–Feller Gaussian-tail sandwich, and the `ENBW·T ≥ 1/2` realizability floor are not available in any of them, and this phase contributes kernel-checked proofs of them. Strongest standalone candidates, in order: the **dark-baseline zero-false-alarm optimum**, then the **Poisson Bhattacharyya closed form** (conditional on check 2), then **`ENBW·T ≥ 1/2`** (which a reviewer may fairly call Cauchy–Schwarz with a physics label). Full report + reachability log: `docs/dev-loops/Phase6EA/LAB_NOTEBOOK.md`.

> **⚠️ GUARDRAIL — floors and screens, not detector designs.** This phase proves *statistical bounds on any detector*, stated over abstract count means and noise parameters. It makes no device claim, models no specific hardware, and asserts nothing about any experimental platform. Model identifications (which physical detector realizes which abstract parameter) are out of scope; a bound's physical *application* is always conditional on an identification made elsewhere.

> **⚠️ GUARDRAIL — state the exact bound, never a folklore form.** The folklore "miss error ≥ e^(−N_diff)" is FALSE in general (an ideal unit-threshold counter beats it whenever the baseline is bright, and it is exponentially loose as an average-error floor at bright baselines). The correct universal statement is the Le Cam/Bhattacharyya average-error floor `P_e ≥ (1/4)·exp(−(√N_a−√N_b)²)`; the exponential form `e^(−N_a)` is exact only as the zero-false-alarm miss optimum at a dark baseline. Wave 1 proves BOTH the correct floor AND the two-sided refutation of the folklore form (as `norm_num` counterexample witnesses) — the refutation is a first-class deliverable, per the repo's falsifier discipline.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping) → `SK_EFT_Hawking_Inventory_Index.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. Each wave's **Bricks** names exact project declarations (verified 2026-07-27) — read those sources **directly**.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle target D12 (authorized 2026-07-27; `PAPER_STRATEGY` §2.2 row exists).** Invariant #14 applies: write bundle-aware content from inception; paper-shaped output also reads `PAPER_STRATEGY.md` + `BUNDLE_LIFT_PROCEDURE.md`. On-disk scaffolding (`_VALID_BUNDLE_TARGETS`, `papers/D12/`) executes at **first content-lift**, not during substrate waves — do not stand it up early. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`; zero `sorry`/`native_decide` regression; any new project-local `axiom` needs explicit user sign-off + discharge plan (Invariant #15). (d) **No `maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** all numeric bounds follow the **`NumericalBounds` rational-enclosure + `norm_num`** pattern. Poisson machinery builds on Mathlib's `Probability.Distributions.Poisson` where usable — resolve UNKNOWN-1 at Stage 2 before Wave 1 statements are frozen.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** the *mathematics* (Poisson sums, exp-series identities, tail inequalities, threshold algebra) is Lean-verified; *physical identifications* (what counts as an absorbed photon, which plane a power is referred to) are the consuming phase's declared hypotheses, never smuggled into these statements. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse (exists — cite, don't re-prove):** `SKEFTHawking.QuantumNetwork.NumericalBounds.expNeg_enclosure` (`1−r ≤ e^{−r} ≤ 1/(1+r)`) — the enclosure *pattern* every rational screen here follows. ⚠ **Corrected 2026-07-29 (round 3): 6EA makes no direct call to it.** Both call sites (`folklore_missFloor_beaten_sixfold` at `r = 5`, `gaussianQ_two_le_rational` at `r = 2`) were the *cause* of the two loose constants that round 3 flagged — the Bernoulli endpoint caps the certified factor at 6 in both places — and both were re-routed through `Real.exp_one_gt_d9`. It remains this phase's style template and a live brick for `DampedTwoLevel`, `ReadoutRelaxationBound`, `ThermalAssignmentFloor` and `ETFModel`; the 6EA docstrings no longer claim a call they do not make. `SKEFTHawking.QuantumNetwork.FidelityUpperBound.classical_fvdg` (classical two-outcome Fuchs–van de Graaf identity — the TV↔Bhattacharyya bridge shape); `SKEFTHawking.LDP.CramerIID` (Chernoff-exponent machinery, for the Wave-3 seam); `SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound.avgAssignmentError_rational_floor` (the existing composed-error-floor capstone this phase generalizes below).
- **Absent → build (sweep 2026-07-27; corrected 2026-07-28 at Stage 13):** no *project* Poisson-detection statistics of any kind; no Gaussian Q-function/erfc tail bounds anywhere (Mathlib included); no Hellinger/Bhattacharyya/Le Cam bounds in Mathlib. Mathlib carries the Poisson pmf (`Probability.Distributions.Poisson.Basic`, rate `ℝ≥0`) and `Real.exp` series, and — **contrary to the original sweep** — it *does* carry an abstract decision-theoretic risk scaffold (`Probability.Decision.Risk`: `bayesRisk`/`minimaxRisk` over `Kernel`s, `ℝ≥0∞`-valued). That scaffold is not usable here (this phase needs real-valued `exp` floors over a randomized `δ : ℕ → ℝ`, and the `ℝ≥0∞` truncated arithmetic is hostile to it — the same reason `PMF` was rejected at UNKNOWN-1), but the original 'no Neyman–Pearson/likelihood-ratio structure' phrasing overstated the absence and is retracted.
- **PhysLib seam — ⛔ NOT USED (Stage-13 correction 2026-07-28).** `QuantumInfo.ResourceTheory.HypothesisTesting` (`OptimalHypothesisRate`) was scoped as the Wave-3 seam and is **type-level impossible** for this phase: it is `[Fintype d]`-bound (as is PhysLib's classical carrier `ProbDistribution α`), and Poisson lives on ℕ; it is also the *asymmetric* Neyman–Pearson value against this phase's *symmetric* Bayes/Le Cam average error. Wave 3 instead routes the seam through the `Fin 2` **pushforward**, as a diagonal restriction against the project's own fidelity substrate. **Zero `Detection.*` declarations reference `OptimalHypothesisRate`.** See `SETTLED_FORKS.md#6ea-optimalhypothesisrate-quantum-seam`.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27** per Pipeline Invariant #14; `PAPER_STRATEGY.md` §2.2). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`. Sibling boundary: D9 owns the channel/qubit-envelope layer; this phase's floors are the physical layer beneath it.

---

## Wave 1 — Poisson discrimination floors

**Goal.** The exact universal floor family for discriminating `Poisson(N_b)` vs `Poisson(N_a)` at equal priors, plus the two-sided refutation of the folklore exponential form. Verdict: reachable — finite/series algebra over Mathlib's Poisson pmf, no measure-theoretic depth required if statements are phrased over pmf sums (UNKNOWN-1).

**Why.** **Consumption record, corrected 2026-07-29 and re-verified the same day against `lean/lean_deps.json` (this bullet previously claimed Wave 1 was "the single most-consumed floor of the series" — verified FALSE).** Counting basis, stated once because the first correction mixed two of them: the figures below are **proof-term dependencies** taken from the `ExtractDeps` reverse index (`name_deps_project` ∪ `type_deps_project` ∪ `value_deps_project`), *not* textual occurrences — a docstring mention is not a consumption.

- **The headline correction stands: Wave 1 is consumed by nothing downstream.** With 6EB (`Detection/{FilterFloors,NEPAlgebra,MatchedFilter}`) and 6EC (`Electrothermal/*`) both COMPLETE, they reference **zero** Wave-1 declarations. `poisson_avgError_floor` and `poisson_darkBaseline_miss_floor` have **0** references anywhere in the tree; `poissonBhattacharyya_eq`, `avgError_ge_affinity_sq`, `IsCountRule`, `falseAlarm`, `missProb`, `affinity`, `affinity_le_binaryAffinity` and `binaryAffinity_sq_le_two_mul_add` are referenced only inside `PoissonDiscrimination.lean` + `ShotNoise.lean`.
- **What the downstream actually consumes is Wave 2**, at these dependency counts (6EB + 6EC only, excluding in-phase `ShotNoise`): `thrErr0` **6** (MatchedFilter 3, BolometricFloors 3), `thrErr1` **6** (same split), `gaussianQ` **5** (MatchedFilter 2, BolometricFloors 3), `gaussianQ_antitone` **1** (BolometricFloors), `gaussianQ_two_ge_rational` **1** (MatchedFilter; +1 in `ShotNoise`), `avgError_ge_gaussianQ_sharp` **1** (MatchedFilter). ⚠ The first pass of this correction wrote "`avgError_ge_gaussianQ_sharp` ×8, `thrErr0`/`thrErr1` ×4 each": the ×8 was a **text-grep count** (6 hits in `MatchedFilter.lean` + 2 in `BolometricFloors.lean`, nearly all docstring prose), and the ×4 undercounted. The dependency truth is that `avgError_ge_gaussianQ_sharp` has exactly **one** direct consumer — `MatchedFilter`'s budget→floor composition, which 6EC then reaches transitively — and that the *broadly* consumed Wave-2 objects are the two branch-error definitions, not the floor theorem.
- **Plus Wave 3's `shotPSD`** — 3 references, all in `Detection/NEPAlgebra` (6EB).

Wave 1 is a standalone distribution-free result with one internal consumer — genuinely novel, but not load-bearing for the series as shipped. If it is meant to be, 6EE must actually consume it and that belongs in 6EE's AC as an explicit item. It is also the sharpest example of the series' value: the folklore form is wrong in both directions, and the correct form is a two-line closed expression nobody has kernel-checked.

**Bricks.** ~~`expNeg_enclosure` (`QuantumNetwork/NumericalBounds.lean:23`)~~ — **superseded 2026-07-29**: its Bernoulli endpoint capped the quantitative falsifier at factor 6 against a true `e⁵ = 148.4`, so the wave now discharges that exponent through `Real.exp_one_gt_d9` and makes no call to it (style template only). Mathlib `poissonPMFReal` + `Real.exp_eq_tsum` — ⚠ `poissonPMFReal` is **deprecated** as of the v4.32.0 pin in favour of the `poissonMeasure` carrier; migration is cross-file (see *Carried, not closed* above). `classical_fvdg` (`QuantumNetwork/FidelityUpperBound.lean:47`) as the structural template for TV↔affinity manipulation.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Detection/PoissonDiscrimination.lean` builds 0-sorry, kernel-pure, no new axioms, with:
- [x] `poissonBhattacharyya_eq : BC(Poisson N_b, Poisson N_a) = exp (−(√N_a − √N_b)^2 / 2)` (series identity via `exp_eq_tsum`);
- [~] **DEMOTED (D3, not shipped)** `poissonTV_le_of_bhattacharyya : TV ≤ √(1 − BC^2)` specialized to Poisson pairs (or cited generic form if proved generically);
- [x] `poisson_avgError_floor : ∀ decision rule, (e₀ + e₁)/2 ≥ (1/4) · exp (−(√N_a − √N_b)^2)` — the Le Cam two-point bound, stated over arbitrary (possibly randomized) count-based decision rules;
- [x] **split into 3 decls (D4)** `poisson_darkBaseline_miss_optimum : N_b = 0 → (zero-false-alarm rules satisfy miss ≥ exp (−N_a), with equality for the count-≥-1 rule)` — stated so the zero-false-alarm hypothesis is explicit and non-droppable;
- [x] **shipped ∀-quantified, stronger than ∃ (D5)** `folklore_miss_floor_false : ∃ N_b N_a rule, miss(rule) < exp (−(N_a − N_b))` — `norm_num` witness (e.g. `N_b = 5, N_a = 10`, count-≥-1 rule, `e^{−10} < e^{−5}`);
- [x] **+ general characterization (D6)** `folklore_avg_floor_unsound : ∃ N_b N_a, (1/4)·exp(−(√N_a−√N_b)^2) > exp (−(N_a−N_b))` — `norm_num` witness (e.g. `N_b = 50, N_a = 60`: `0.158… > 4.6e−5`) showing the folklore form fails open as an average-error screen;
- [x] preemptive-strengthening checklist applied per theorem; post-wave ruthless audit logged.

## Wave 2 — Gaussian threshold discrimination algebra

**Goal.** Exact error algebra for two-Gaussian threshold classification (equal-variance case first), with honest tail enclosures replacing the un-formalized Q-function. Verdict: reachable — the Chernoff tail `Q(z) ≤ (1/2)·exp(−z²/2)` and the rational lower bounds are elementary integral estimates; exact Q-function values are NOT targeted (enclosures only, per the `_enclosure` convention).

**Why.** Filtered-current readouts classify by thresholding a (conditionally) Gaussian statistic; 6EB composes these errors with noise floors, and 6EE's ceilings need both upper AND lower tail control (a lower bound on error is a ceiling on fidelity — the load-bearing direction).

**Bricks.** ~~`expNeg_enclosure`~~ — **superseded 2026-07-29** for the same reason as Wave 1 (it capped `Q(2) ≤ 1/6` against a true `1/43.96`); the rational bracket now routes through `Real.pi_*_d*` + `Real.exp_one_*_d9`. Mathlib Gaussian integral (`integral_gaussian`); Mathlib's Gaussian *measure* `ProbabilityTheory.gaussianReal` + `gaussianReal_apply_eq_integral` / `gaussianReal_map_const_mul` / `gaussianReal_map_add_const` (added at round 3 for the probability bridge); `ReadoutRelaxationBound.avgAssignmentError_rational_floor` as the composition-shape template.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Detection/GaussianThreshold.lean` builds 0-sorry, kernel-pure, with:
- [x] **closed at the FULL `z ≥ 0` (D7 fallback not needed)** `gaussianTail_chernoff : Q z ≤ (1/2) · exp (−z^2/2)` for `z ≥ 0` (with `Q` defined as the standardized upper-tail integral);
- [x] **shipped as `gaussianTail_ge_window` + `gaussianTail_birnbaum` (D8; interval form rejected as vacuous; `birnbaum` unrestricted in `z` since round 3)** `gaussianTail_lower_enclosure` — a rational/exp lower bound on `Q z` sufficient to state error *floors* (candidate: `Q z ≥ (1/2)·(1 − z/√(2π))` on a stated interval, or the standard `z/(1+z²)·φ(z)` form; pick at Stage 2, UNKNOWN-2);
- [x] **shipped as `thrErr0/1_mono_in_sigma`** `thresholdErrors_monotone_in_sigma` — both branch errors increase with σ when the threshold lies between the means (the conservativity workhorse);
- [x] **strengthened to name the value (D9)** `midpoint_threshold_symmetric : equal σ → e₀ = e₁` and `offCenter_threshold_tradeoff` (signed monotonicity in the threshold position);
- [x] **shipped SHARP as `avgError_ge_gaussianQ_sharp`; the ½·Q(z₀) form (D10) dropped as a weaker restatement** `avg_error_ge_of_z_le : z ≤ z₀ → (e₀+e₁)/2 ≥ Q z₀`-shape floor connecting separation budgets to error floors;
- [x] **added at Stage-13 round 3 (2026-07-29), not in the original AC** — the *probability* bridge `gaussianQ_eq_measure` / `thrErr0_eq_measure` / `thrErr1_eq_measure` on `gaussianReal_map_affine`. The wave shipped `gaussianQ` as a bare density integral while every consuming statement is read as an **error-probability** floor; that reading is now a theorem against Mathlib's own `ProbabilityTheory.gaussianReal`, matching the discipline Wave 3 applied with `binaryDensityOperator`. Any future project-local "probability" definition owes the same bridge at the wave it is introduced, not two rounds later;
- [x] preemptive-strengthening + post-wave audit.

## Wave 3 — Shot-noise algebra & the quantum seam

**Goal.** The Poisson-to-spectral bridge (shot-noise PSD algebra, mean=variance scaling under thinning) and the connection of Wave-1 floors to the existing quantum discrimination corpus. Verdict: reachable; the thinning identity is finite algebra, and the quantum seam is a citation-bridge wave (consume, don't rebuild).

**Why.** 6EB needs shot-noise PSD referred across planes (Poisson thinning `η`); the quantum seam records, as theorems, that the classical floors are the commutative shadow of the Helstrom/Bhattacharyya quantum bounds already in `QuantumNetwork` — closing the arc structurally instead of leaving two disconnected bound families.

**Bricks.** `poissonBhattacharyya_eq` (Wave 1); `SKEFTHawking.QuantumNetwork.FidelityBounds` (Bhattacharyya/Fuchs–van de Graaf family); ~~`QuantumInfo.ResourceTheory.HypothesisTesting.OptimalHypothesisRate`~~ — **struck 2026-07-28 (Stage 13): not a brick, not consumed, type-level impossible for Poisson (see the corrected PhysLib-seam bullet above). Wave 3 is NOT a consumption of `HypothesisTesting`.** Shipped seam brick instead: `SKEFTHawking.QuantumNetwork.psdSqrt` + `sqrtFidelity` + `posSemidef_eq_of_mul_self_eq` on the `Fin 2` pushforward; `GrapheneNoiseFormula.johnsonNyquistPSD_pos` (PSD-convention template).

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Detection/ShotNoise.lean` builds 0-sorry, kernel-pure, with:
- [x] **pmf-level as required; `η ≤ 1` dropped as non-load-bearing (strictly stronger)** `poisson_thinning : thinning by η ∈ [0,1] maps Poisson N to Poisson (η·N)` (pmf-level identity);
- [x] **+ `shotPSD_eq_hawkingNoisePSD` making the one-sided convention a kernel-checked match** `shotPSD_def` + `shotPSD_plane_transfer : S_abs = η · S_inc`-shape reference-plane algebra with declared one-sided convention matching `GrapheneNoiseFormula`;
- [x] **SUBSTANTIVE — `poissonVariance` is the independently-computed second central moment, not `:= N`** `shot_variance_eq_mean` in the filtered-count normalization (the `N_eff` scaling used by any downstream dominance argument);
- [x] **shipped as a SANDWICH `¼·exp(…) ≤ ¼·F(ρ₀,ρ₁)² ≤ avgAssignmentError`; (S3) not attempted (type-level impossible)** `classical_floor_le_quantum_optimum`-shape bridge: the Wave-1 Poisson floor is implied by (is the diagonal restriction of) the quantum two-state discrimination bound — via the `FidelityBounds`/PhysLib hypothesis-testing seam; exact statement frozen at Stage 2 (UNKNOWN-3);
- [x] **quantitative factor 3/2, forced through `poissonBhattacharyya_eq`** at least one consuming falsifier-style witness: a concrete parameter point where the shot-inclusive Gaussian model's average error strictly exceeds the Wave-1 floor (the `norm_num` companion to the floor's non-vacuity);
- [x] preemptive-strengthening + post-wave audit; Inventory Index + counts refreshed for the new `Detection/` family.

---

## Sequencing & parallelism

Wave 1 → Wave 2 are independent (different files, disjoint substrate) — **parallelizable across two worktree slots**. Wave 3 consumes Wave 1 (Bhattacharyya identity) and is the integration wave — serialize it last. Contention: none with other active phases; the new `Detection/` directory is untouched by 6C*/6D* work. ⚠ **CORRECTED (Stage 2, lead-verified 2026-07-27): EVERY wave adds its OWN root import, in its own commit.** The original text said the root import lands in Wave 3. That is a **build defect**: `lean/lakefile.toml`'s `lean_lib` declares **no `globs`**, and `lean/SKEFTHawking.lean` is an explicit 1,878-import aggregator — so a module absent from it is **not built by `lake build` at all**, making Waves 1–2 invisible to the zero-sorry gate, `ExtractDeps`, and counts. The root is still single-writer; the orchestrator resolves the trivial import-list conflicts at merge (this is already routine).

## Phase Definition of Done

- [x] `lake build` (10,365 jobs) + `lake build SKEFTHawking.ExtractDeps` (10,366) clean; zero sorry; kernel-pure axiom set; no new project-local axioms.
- [x] `uv run python scripts/validate.py` green (**49/49**); counts + `SK_EFT_Hawking_Inventory.md` (new §2.Z) + Inventory Index refreshed with the `Detection/` family.
- [x] All three waves' AC boxes checked; per-wave post-strengthening audits logged in `docs/dev-loops/Phase6EA/LAB_NOTEBOOK.md`.
- [x] Stage-13-style adversarial pass over the statement set (vacuity/tautology hunt) — **two rounds**, closing at ZERO BLOCKER (`papers/AutomatedReviews/2026-07-28-1839-…` and `…-1924-…`).
- [x] Roadmap status updated (PLANNED → COMPLETE with dated shipped-declarations list) — see the STATUS block at the top.

## Stage-2 resolutions — LEAD SIGN-OFF 2026-07-27 (binding; supersedes the AC bullets they touch)

Full analysis: `docs/dev-loops/Phase6EA/Phase6EA_Stage2_StatementFreeze.md`. The four items below were escalated
for sign-off; all four are decided here so no wave stalls on them.

- **UNKNOWN-1 — RESOLVED.** Use Mathlib `poissonPMFReal`, with the generic Le Cam chain stated over bare
  `ℕ → ℝ`. The decisive finding is that **the randomized-rule quantifier is orthogonal to the pmf
  carrier**: a rule is `δ : ℕ → ℝ` with `δ n ∈ [0,1]` and the errors are `∑' n, p n * δ n` /
  `∑' n, q n * (1 − δ n)`, which never touches the pmf's *type*. So the roadmap's stated trap (silent
  narrowing to deterministic threshold rules) is avoided by **how the rule is quantified**, not by the
  carrier choice. `poissonPMFRealSum` carries **no positivity hypothesis**, which is what makes the
  `N_b = 0` dark-baseline item statable at all. `PMF`/`ℝ≥0∞` rejected (truncated subtraction against
  real-valued `exp` floors). Coercion discipline: `Real.sqrt (Nb : ℝ)`, never `NNReal.sqrt`.
- **UNKNOWN-2 — RESOLVED, and the roadmap's framing was wrong.** **Mathlib has no `erf`/`erfc`/
  Q-function/Gaussian CDF at pin** (declaration-level grep, zero hits), so Wave 2 *defines* `Q` locally
  and this was never a choice between library forms. The interval-restricted rational is **REJECTED**:
  it goes negative at `z > √(2π)/2 ≈ 1.2533`, so its side condition does not merely "leak into 6EE",
  it swallows 6EE's operating range. Freeze `gaussianTail_ge_window : c·φ(z+c) ≤ Q z` (`z ≥ 0`, `c > 0`)
  — global, parametric, correct exponent. The sharp `z/(1+z²)·φ(z)` is a **stretch**, and consuming
  statements must be written so substituting it needs no restatement.
- **UNKNOWN-3 — RESOLVED; the roadmap's option (b) is TYPE-LEVEL IMPOSSIBLE.** `OptimalHypothesisRate`
  takes `ρ : MState d` with `[Fintype d]`, and PhysLib's classical carrier needs `[Fintype α]` —
  **Poisson on ℕ cannot be an argument to either**. It is also the *asymmetric* Neyman–Pearson value,
  whereas Wave 1 bounds the *symmetric* Bayes/Le Cam average error, so "specialization" would be a
  category error. Route the seam through the `Fin 2` **pushforward** Wave 1 already builds, stated as a
  diagonal restriction against the project's own proven FvdG. ⚠ **Wave 3 must NOT be described as
  "first project consumption of `HypothesisTesting`"** unless that consumption actually happens — a
  claims-accuracy fix, per Stage 13.
- **Wave-1 `poissonTV_le_of_bhattacharyya` — DEMOTED to stretch.** Not a scope reduction: the Le Cam
  floor route does not pass through TV at all (Cauchy–Schwarz then elementary AM–GM), so this was an
  *assumed intermediate that turned out unnecessary*; the shipped floor is unchanged. Stating TV about
  the true Poisson pair additionally needs an MLR/positive-part argument absent from the brick list, and
  `Detection/` avoids importing the trace-norm tower. Keep it listed, with this reason.
- **Wave-2 `gaussianTail_chernoff` — ATTEMPT `z ≥ 0` FIRST; `z ≥ 0.8` is the fallback, not the target.**
  I am not signing off on narrowing the AC up front. The `z ≥ 0.8` form is provable from Mills; the full
  `z ≥ 0` constant needs a monotone-derivative argument, which is a known-shape task rather than a wall.
  Ship `z ≥ 0.8` only if `z ≥ 0` is attempted and fails, and **document the failure** if so.
- **Wave-2 threshold floor — ACCEPTED at `½·Q(z₀)` uniform over `t`,** with the sharp `Q(z₀)` as stretch.
  The factor ½ is an honest cost of uniformity in the threshold position.
- **Reuse correction:** `avgAssignmentError` already exists (`QuantumNetwork/ReadoutRelaxationBound.lean:143`)
  — Waves 1/2 consume it rather than re-defining `(e₀+e₁)/2`.
- **Witness arithmetic — VERIFIED (40-digit), and both admit stronger forms than the `∃` shape asked for.**
  W1: the undershoot is **exactly `e^{N_b}`, for every bright baseline at every `N_a`** — no `N_b < N_a`
  needed; freeze the quantitative `6·miss ≤ folklore`, discharged via `expNeg_enclosure` at `r = 5`
  (which also makes the cited brick a real call rather than a docstring reference).
  ⚠ **SUPERSEDED 2026-07-29 (Stage-13 round 3).** The parenthetical traded 25× of the certified
  constant for a brick call: `expNeg_enclosure` at `r = 5` cannot certify better than 6, while the
  true undershoot at `(N_b, N_a) = (5, 10)` is `e⁵ = 148.413`. The shipped witness is now
  `folklore_missFloor_beaten_148fold` via `Real.exp_one_gt_d9`. **Standing lesson: never let a
  brick-consumption bookkeeping goal set a certified constant.** W2: the exact
  characterization is `(N_a−N_b) − (√N_a−√N_b)² = 2√N_b(√N_a−√N_b)`, so the Le Cam floor exceeds the
  folklore form **iff `2√N_b(√N_a−√N_b) > log 4`**; the `(50,60)` witness closes by `norm_num` with no
  `Real.log` in the statement.
- **Path corrections:** the Mathlib module is `…Distributions.Poisson.Basic`; the PhysLib path is
  `QuantumInfo.ResourceTheory.HypothesisTesting`.

## Open UNKNOWNs (resolve at Stage 2 before the consuming wave freezes statements)

- **UNKNOWN-1:** phrase Wave 1 over Mathlib `PMF`/`poissonPMFReal` sums vs. a self-contained `ℕ → ℝ` pmf with proved normalization. Decide by whichever makes `poisson_avgError_floor`'s "arbitrary randomized decision rule" quantifier cleanest; the two-point bound must not silently narrow to deterministic threshold rules.
- **UNKNOWN-2:** the Gaussian lower-tail bound form (interval-restricted rational vs. `z/(1+z²)·φ(z)` global) — pick the one that composes with Wave-2's floor statements without side conditions leaking into 6EE.
- **UNKNOWN-3 — RESOLVED 2026-07-27, see the Stage-2 sign-off block above.** The seam ships as a diagonal restriction on the `Fin 2` pushforward. The `OptimalHypothesisRate` option is type-level impossible and was NOT taken; this phase performs **no** consumption of PhysLib's `HypothesisTesting`.
