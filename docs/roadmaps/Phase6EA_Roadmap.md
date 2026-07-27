# Phase 6EA — Kernel-Verified Photodetection Statistics: Poisson & Gaussian Discrimination Floors

**Status: PLANNED (authorized 2026-07-27).** Opens the **new `6E*` thematic series** (theme: *verified device-physics metrology — detection statistics, readout noise floors, electrothermal device physics, and graphene electronic structure*), independent of the `6B*` (comp-chem/OQS → D10), `6C*` (band-theory/metamaterials → D11), and `6D*` (constant-provenance audit) series. The `6E*` series continues the repo's existing public readout-metrology arc (`ReadoutRelaxationBound`, `ThermalAssignmentFloor`, `QuantumFDTFloor`, `GrapheneNoiseFormula`) downward into the *classical detection layer* every physical readout chain bottoms out in.

**Thesis.** Every intensity-detection readout — photon counters, threshold discriminators, homodyne-style filtered-current classifiers — obeys a small set of textbook statistical floors that are routinely *cited* in device papers but have never been *kernel-checked* anywhere: the Bhattacharyya/Le Cam universal floor on Poisson discrimination, the zero-false-alarm dark-baseline optimum, the Neyman–Pearson structure of counting tests, and Gaussian threshold-error algebra with honest tail bounds. This phase builds that layer once, exactly, in the repo's established `_enclosure` exact-rational style, so that every later device phase (6EB filtered readout, 6EC electrothermal detectors, 6EE composite readout ceilings) *consumes floors instead of re-deriving them* — and so that any experimental claim of discrimination performance can be checked against a machine-verified bound by hand.

Clean whitespace: no theorem prover has a kernel-checked Poisson discrimination-floor family (Bhattacharyya coefficient closed form, Le Cam two-point bound, dark-baseline exact optimum, counting-test monotone-likelihood-ratio structure) packaged as reusable metrology substrate.

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
- **Reuse (exists — cite, don't re-prove):** `SKEFTHawking.QuantumNetwork.NumericalBounds.expNeg_enclosure` (`1−r ≤ e^{−r} ≤ 1/(1+r)`) — the enclosure pattern every rational screen here follows; `SKEFTHawking.QuantumNetwork.FidelityUpperBound.classical_fvdg` (classical two-outcome Fuchs–van de Graaf identity — the TV↔Bhattacharyya bridge shape); `SKEFTHawking.LDP.CramerIID` (Chernoff-exponent machinery, for the Wave-3 seam); `SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound.avgAssignmentError_rational_floor` (the existing composed-error-floor capstone this phase generalizes below).
- **Absent → build (confirmed by sweep 2026-07-27):** no project Poisson-detection statistics of any kind; no Gaussian Q-function/erfc tail bounds; no Neyman–Pearson/likelihood-ratio structure; no Le Cam two-point bound. Mathlib carries the Poisson pmf (`Probability.Distributions.Poisson`) and `Real.exp` series but none of the discrimination bounds.
- **PhysLib seam (present, unused):** `Physlib.QuantumInfo.Finite.POVM` and `...ResourceTheory.HypothesisTesting` (`OptimalHypothesisRate`) — Wave 3 connects the classical floors to this quantum hypothesis-testing substrate rather than rebuilding it.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27** per Pipeline Invariant #14; `PAPER_STRATEGY.md` §2.2). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`. Sibling boundary: D9 owns the channel/qubit-envelope layer; this phase's floors are the physical layer beneath it.

---

## Wave 1 — Poisson discrimination floors

**Goal.** The exact universal floor family for discriminating `Poisson(N_b)` vs `Poisson(N_a)` at equal priors, plus the two-sided refutation of the folklore exponential form. Verdict: reachable — finite/series algebra over Mathlib's Poisson pmf, no measure-theoretic depth required if statements are phrased over pmf sums (UNKNOWN-1).

**Why.** This is the single most-consumed floor of the series: 6EB's filtered-readout screens, 6EC's detector composites, and 6EE's photon-budget ceilings all cite it. It is also the sharpest example of the series' value: the folklore form is wrong in both directions, and the correct form is a two-line closed expression nobody has kernel-checked.

**Bricks.** `expNeg_enclosure` (`QuantumNetwork/NumericalBounds.lean:23`); Mathlib `poissonPMFReal` + `Real.exp_eq_tsum`; `classical_fvdg` (`QuantumNetwork/FidelityUpperBound.lean:47`) as the structural template for TV↔affinity manipulation.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Detection/PoissonDiscrimination.lean` builds 0-sorry, kernel-pure, no new axioms, with:
- [ ] `poissonBhattacharyya_eq : BC(Poisson N_b, Poisson N_a) = exp (−(√N_a − √N_b)^2 / 2)` (series identity via `exp_eq_tsum`);
- [ ] `poissonTV_le_of_bhattacharyya : TV ≤ √(1 − BC^2)` specialized to Poisson pairs (or cited generic form if proved generically);
- [ ] `poisson_avgError_floor : ∀ decision rule, (e₀ + e₁)/2 ≥ (1/4) · exp (−(√N_a − √N_b)^2)` — the Le Cam two-point bound, stated over arbitrary (possibly randomized) count-based decision rules;
- [ ] `poisson_darkBaseline_miss_optimum : N_b = 0 → (zero-false-alarm rules satisfy miss ≥ exp (−N_a), with equality for the count-≥-1 rule)` — stated so the zero-false-alarm hypothesis is explicit and non-droppable;
- [ ] `folklore_miss_floor_false : ∃ N_b N_a rule, miss(rule) < exp (−(N_a − N_b))` — `norm_num` witness (e.g. `N_b = 5, N_a = 10`, count-≥-1 rule, `e^{−10} < e^{−5}`);
- [ ] `folklore_avg_floor_unsound : ∃ N_b N_a, (1/4)·exp(−(√N_a−√N_b)^2) > exp (−(N_a−N_b))` — `norm_num` witness (e.g. `N_b = 50, N_a = 60`: `0.158… > 4.6e−5`) showing the folklore form fails open as an average-error screen;
- [ ] preemptive-strengthening checklist applied per theorem; post-wave ruthless audit logged.

## Wave 2 — Gaussian threshold discrimination algebra

**Goal.** Exact error algebra for two-Gaussian threshold classification (equal-variance case first), with honest tail enclosures replacing the un-formalized Q-function. Verdict: reachable — the Chernoff tail `Q(z) ≤ (1/2)·exp(−z²/2)` and the rational lower bounds are elementary integral estimates; exact Q-function values are NOT targeted (enclosures only, per the `_enclosure` convention).

**Why.** Filtered-current readouts classify by thresholding a (conditionally) Gaussian statistic; 6EB composes these errors with noise floors, and 6EE's ceilings need both upper AND lower tail control (a lower bound on error is a ceiling on fidelity — the load-bearing direction).

**Bricks.** `expNeg_enclosure`; Mathlib Gaussian integral (`integral_gaussian`); `ReadoutRelaxationBound.avgAssignmentError_rational_floor` as the composition-shape template.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Detection/GaussianThreshold.lean` builds 0-sorry, kernel-pure, with:
- [ ] `gaussianTail_chernoff : Q z ≤ (1/2) · exp (−z^2/2)` for `z ≥ 0` (with `Q` defined as the standardized upper-tail integral);
- [ ] `gaussianTail_lower_enclosure` — a rational/exp lower bound on `Q z` sufficient to state error *floors* (candidate: `Q z ≥ (1/2)·(1 − z/√(2π))` on a stated interval, or the standard `z/(1+z²)·φ(z)` form; pick at Stage 2, UNKNOWN-2);
- [ ] `thresholdErrors_monotone_in_sigma` — both branch errors increase with σ when the threshold lies between the means (the conservativity workhorse);
- [ ] `midpoint_threshold_symmetric : equal σ → e₀ = e₁` and `offCenter_threshold_tradeoff` (signed monotonicity in the threshold position);
- [ ] `avg_error_ge_of_z_le : z ≤ z₀ → (e₀+e₁)/2 ≥ Q z₀`-shape floor connecting separation budgets to error floors;
- [ ] preemptive-strengthening + post-wave audit.

## Wave 3 — Shot-noise algebra & the quantum seam

**Goal.** The Poisson-to-spectral bridge (shot-noise PSD algebra, mean=variance scaling under thinning) and the connection of Wave-1 floors to the existing quantum discrimination corpus. Verdict: reachable; the thinning identity is finite algebra, and the quantum seam is a citation-bridge wave (consume, don't rebuild).

**Why.** 6EB needs shot-noise PSD referred across planes (Poisson thinning `η`); the quantum seam records, as theorems, that the classical floors are the commutative shadow of the Helstrom/Bhattacharyya quantum bounds already in `QuantumNetwork` — closing the arc structurally instead of leaving two disconnected bound families.

**Bricks.** `poissonBhattacharyya_eq` (Wave 1); `SKEFTHawking.QuantumNetwork.FidelityBounds` (Bhattacharyya/Fuchs–van de Graaf family); `Physlib.QuantumInfo.Finite.ResourceTheory.HypothesisTesting.OptimalHypothesisRate` (first project consumption of this PhysLib substrate); `GrapheneNoiseFormula.johnsonNyquistPSD_pos` (PSD-convention template).

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Detection/ShotNoise.lean` builds 0-sorry, kernel-pure, with:
- [ ] `poisson_thinning : thinning by η ∈ [0,1] maps Poisson N to Poisson (η·N)` (pmf-level identity);
- [ ] `shotPSD_def` + `shotPSD_plane_transfer : S_abs = η · S_inc`-shape reference-plane algebra with declared one-sided convention matching `GrapheneNoiseFormula`;
- [ ] `shot_variance_eq_mean` in the filtered-count normalization (the `N_eff` scaling used by any downstream dominance argument);
- [ ] `classical_floor_le_quantum_optimum`-shape bridge: the Wave-1 Poisson floor is implied by (is the diagonal restriction of) the quantum two-state discrimination bound — via the `FidelityBounds`/PhysLib hypothesis-testing seam; exact statement frozen at Stage 2 (UNKNOWN-3);
- [ ] at least one consuming falsifier-style witness: a concrete parameter point where the shot-inclusive Gaussian model's average error strictly exceeds the Wave-1 floor (the `norm_num` companion to the floor's non-vacuity);
- [ ] preemptive-strengthening + post-wave audit; Inventory Index + counts refreshed for the new `Detection/` family.

---

## Sequencing & parallelism

Wave 1 → Wave 2 are independent (different files, disjoint substrate) — **parallelizable across two worktree slots**. Wave 3 consumes Wave 1 (Bhattacharyya identity) and is the integration wave — serialize it last. Contention: none with other active phases; the new `Detection/` directory is untouched by 6C*/6D* work. The root `SKEFTHawking.lean` import addition lands in Wave 3 (single-writer file — coordinate with any concurrent phase's root-module edit).

## Phase Definition of Done

- [ ] `lake build` + `lake build SKEFTHawking.ExtractDeps` clean; zero sorry; kernel-pure axiom set; no new project-local axioms.
- [ ] `uv run python scripts/validate.py` green; counts + `SK_EFT_Hawking_Inventory.md` + Inventory Index refreshed with the `Detection/` family.
- [ ] All three waves' AC boxes checked; per-wave post-strengthening audits logged in the phase notebook.
- [ ] Stage-13-style adversarial pass over the statement set (vacuity/tautology hunt) — mandatory even with no paper target.
- [ ] Roadmap status updated (PLANNED → COMPLETE with dated shipped-declarations list).

## Open UNKNOWNs (resolve at Stage 2 before the consuming wave freezes statements)

- **UNKNOWN-1:** phrase Wave 1 over Mathlib `PMF`/`poissonPMFReal` sums vs. a self-contained `ℕ → ℝ` pmf with proved normalization. Decide by whichever makes `poisson_avgError_floor`'s "arbitrary randomized decision rule" quantifier cleanest; the two-point bound must not silently narrow to deterministic threshold rules.
- **UNKNOWN-2:** the Gaussian lower-tail bound form (interval-restricted rational vs. `z/(1+z²)·φ(z)` global) — pick the one that composes with Wave-2's floor statements without side conditions leaking into 6EE.
- **UNKNOWN-3:** exact shape of the classical↔quantum seam theorem (diagonal-state restriction of Helstrom vs. an `OptimalHypothesisRate` specialization) — requires reading `Physlib...HypothesisTesting` in full before freezing; first project consumption of that module.
