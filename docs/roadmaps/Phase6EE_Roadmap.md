# Phase 6EE — Kernel-Verified Two-Level Control & Composite Readout Ceilings

**Status: PLANNED (authorized 2026-07-27).** Capstone phase of the `6E*` series (*verified device-physics metrology*). Consumes 6EA (detection floors), 6EB (filtered-readout floors), 6EC (detector floors), and the existing readout-metrology corpus; 6ED feeds material-parameter seams optionally. See `Phase6EA_Roadmap.md` for the series framing.

**Thesis.** The repo already owns strong single-mechanism readout floors: `readoutDecayProb_eq_cohGamma` with its enclosure suite (relaxation), `ThermalAssignmentFloor` (thermal excitation), `avgAssignmentError_rational_floor` (their composition), the generalized-amplitude-damping channel, and the T1⊕T2 gate-fidelity family. Two layers are missing to make this a complete, state-of-the-art verified-metrology stack: (1) the *control* layer — rotating-wave reduction with an explicit error bound, projected-drive Rabi calibration algebra, and the Kramers-degeneracy protection statement, which turn "a qubit was driven" into kernel-checked rotation claims; and (2) the *composite-ceiling* layer — theorems assembling relaxation + thermal + photon-budget (6EA) + filtered-noise (6EB) + detector (6EC) floors into single end-to-end assignment-fidelity ceilings, each mechanism's hypothesis explicit, each ceiling falsifiable by `norm_num`. Together they finish the arc the `6E*` series exists for: any claimed readout performance can be screened against a machine-checked ceiling assembled from its own stated budget.

Clean whitespace: no prover has a kernel-checked RWA error bound, projected-drive calibration algebra, or an end-to-end multi-mechanism readout-fidelity ceiling.

> **⚠️ GUARDRAIL — ceilings compose under explicit independence/attribution hypotheses.** Error mechanisms do not add for free. Every composite ceiling states its attribution model (which mechanism claims which branch, what independence or worst-case-max is assumed) as explicit hypotheses. A composite that silently double-counts (conservative) is acceptable only when flagged; one that silently under-counts (fail-open) is a defect of the highest order for this phase.

> **⚠️ GUARDRAIL — RWA bounds are bounds, not the RWA.** The rotating-wave *approximation* is folklore; the deliverable is the *inequality*: the exact evolution differs from the co-rotating reduction by an explicitly bounded remainder (Bloch–Siegert scale `Ω/ω`). No theorem may assert the reduction as an equality, and every calibration statement inherits the remainder bound.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` → `SK_EFT_Hawking_Inventory_Index.md` → `Phase6EA_Roadmap.md` (series head) → `lean/SKEFTHawking/QuantumNetwork/ReadoutRelaxationBound.lean` + `ThermalAssignmentFloor.lean` + `lean/SKEFTHawking/DampedTwoLevel.lean` (the corpus this phase extends — read the sources directly). *(Path corrected 2026-07-30 by pre-arm plan-currency check: there is no `OpenSystems/` directory; `DampedTwoLevel` and `LindbladSemigroup` sit directly under `SKEFTHawking/`.)*
> 2. **Read this roadmap end-to-end**; Bricks are exact (verified 2026-07-27).
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`), per the 6EA instructions.
> 4. **Pipeline disciplines (hard gates):** (a) **bundle target D12** (authorized 2026-07-27; Invariant #14 applies — bundle-aware content from inception; scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`); (b) preemptive-strengthening + post-wave audit — this phase is the series' highest tautology risk (composition theorems degenerate into restated hypotheses if the ceiling isn't strictly sharper than its inputs; audit for that specifically); (c) kernel-purity, zero sorry, no new axioms without sign-off (#15); (d) no `maxHeartbeats` (#10).
> 5. **This phase:** matrix exponential bounds go through Mathlib's `NormedSpace.exp` and operator-norm Duhamel-type estimates (UNKNOWN-1); everything numeric follows `NumericalBounds` enclosures.

**Standing invariants:** kernel-pure; no new axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** the control/ceiling mathematics is Lean-verified; drive-Hamiltonian and mechanism-attribution identifications are consumer-side hypotheses. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse:** `SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound` (`readoutDecayProb_eq_cohGamma`, `readoutDecayProb_enclosure`, `avgAssignmentError_rational_floor`) — the existing composition capstone this phase generalizes; `ThermalAssignmentFloor` (`thermalExcitedPop`, `half_one_sub_tanh`); `SKEFTHawking.DampedTwoLevel` + `SKEFTHawking.LindbladSemigroup` (**note: no `OpenSystems.` namespace segment** — corrected 2026-07-30); `QuantumNetwork.GeneralizedAmpDamp` (thermal T1 channel) + `CoherenceFidelity` (T1⊕T2 fidelity closed forms) + `NamedChannels`; 6EA/6EB/6EC outputs per their roadmaps — **all four 6E predecessors are now COMPLETE** (6ED closed 2026-07-30), so every floor this phase composes is available.
- **Absent → build:** RWA remainder bound; projected-drive/Rabi calibration algebra; Kramers-degeneracy statement; the multi-mechanism composite ceilings. *(Re-verified 2026-07-30: `rotatingWave`/`Rabi` are genuinely absent.)*

> **⚠️ GUARDRAIL — Kramers must be BUILT FROM SCRATCH. The prior guardrail's premise was false; it is retracted.** *(Retracted 2026-07-30 after reading `MajoranaKramers.lean` in source rather than by name.)*
>
> The earlier instruction read "reuse its `Θ`-algebra rather than rebuilding it". **There is no `Θ`-algebra in `MajoranaKramers` to reuse.** Verified directly in source:
> - `kramers_anticommutation (j2_a a_j2 : ℝ) (h : j2_a + a_j2 = 0) : j2_a = -a_j2 := by linarith` — two REALS. The docstring claims `{J₂, A} = 0` for the fermion matrix; the statement is `eq_neg_of_add_eq_zero_left` on ℝ. No matrix, no `J₂`, no anticommutator.
> - `kramers_pfaffian_definite_sign (pf1 pf2 : ℝ) (h_kramers : ∀ (a : ℝ), a = a) …  : pf1 * pf2 ≥ 0 := by positivity` — the Kramers hypothesis is a **self-admitted placeholder** (`-- Kramers condition placeholder`, vacuously true); the docstring claims the Wei et al. PRL 116 Pfaffian-sign theorem; the statement is `mul_nonneg`.
>
> **Calibration of the finding.** These theorems are *true* and are NOT "vacuous statements" in the detector's sense — `validate.py --check vacuous_statement_audit` PASSES and does not flag them, correctly, because they are genuine real-arithmetic implications. The defect is a **name/docstring ↔ statement mismatch**: the names and docstrings assert matrix/Pfaffian/antiunitary content the statements do not contain. Neither appears in `VACUOUS_STATEMENT_BASELINE` or any other disclosure registry, so the debt is currently invisible to every gate.
>
> **Consequence for this phase:** the Wave-2 Kramers statement is genuinely new substrate and must be built from first principles — an antiunitary `Θ` with `Θ² = -1` and a real degeneracy conclusion. Nothing may be cited as "reused" from `MajoranaKramers`.
>
> **Owed elsewhere (out of 6EE scope, flagged not fixed):** `MajoranaKramers` needs either honest renaming/disclosure or real substrate. Building genuine Kramers here creates the substrate those lemmas could later be re-pointed at.
- **Mathlib/PhysLib:** `NormedSpace.exp` for matrix exponentials; PhysLib `QuantumInfo.Finite.Qubit` (qubit-specific helpers, consumed already via bridge modules).

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27**; `PAPER_STRATEGY.md` §2.2; this phase supplies layers (iv) control and (v) composite ceilings). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`.

---

## Wave 1 — Rotating-wave reduction with explicit remainder

**Goal.** For the driven two-level Hamiltonian `H(t) = (ω₀/2)σ_z + Ω·cos(ωt+φ)·O_drive`, the co-rotating reduction at resonance with an operator-norm remainder bound of Bloch–Siegert scale. Verdict: reachable-with-care — a Duhamel/averaging estimate on 2×2 matrices; the spike is picking the estimate route (UNKNOWN-1) before freezing constants.

**Why.** Every control claim in any two-level platform routes through the RWA; the explicit inequality version is the series' most broadly citable control theorem.

**Bricks.** Mathlib `NormedSpace.exp`; `DampedTwoLevel` (ODE-verification pattern); PhysLib `Qubit`.
**Additional in-repo bricks (added 2026-07-29, post-v4.32-bump substrate re-scan).** The project
already owns a 37-declaration matrix-exponential corpus that this Bricks list predates and that
UNKNOWN-1 should cost out before spiking either route from scratch:
`MatrixBCHCubicMathlibPR` (4 decls — order-2/cubic Baker–Campbell–Hausdorff; BCH is the direct tool
for bounding `exp(A)·exp(B)` against `exp(A+B)`, which is the RWA remainder's exact shape),
`MatrixExpLocalHomeomorphMathlibPR` (14), `FKLW/GenericSUdMatrixMercatorLog` (19 — concrete-radius
matrix log). All three are kernel-pure and Mathlib-PR-packaged. A second candidate route is PhysLib
`Mathematics/Resolvent.lean` (new at pin `c4843367`): `norm_resolvent_le` (‖resolvent z t‖ ≤ |z.im|⁻¹),
`contDiff_resolvent`, `iteratedDeriv_resolvent`, `norm_iteratedDeriv_resolvent_le`,
`hasTemperateGrowth_resolvent` — a resolvent-estimate path to the same bound.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Control/RotatingWave.lean` builds 0-sorry, kernel-pure, with:
- [ ] `rwaReduction_def` — the co-rotating effective Hamiltonian in the interaction picture (definition, convention-explicit);
- [ ] `rwa_remainder_bound : ‖U_exact(T) − U_rwa(T)‖ ≤ C·(Ω/ω)·(1 + Ω·T)`-shape inequality with explicit `C` (exact shape frozen after the UNKNOWN-1 spike; the deliverable is ANY honest explicit-constant bound of Bloch–Siegert scale, not the optimal one);
- [ ] `rwa_rotation_angle : θ = (m/2)·Ω·T` for the co-rotating propagator with projected drive element `m = |⟨0|O_drive|1⟩|` — the calibration identity at the RWA level;
- [ ] `norm_num` witnesses: a parameter point where the remainder bound is small (validity) and one where it is order-unity (honest failure);
- [ ] preemptive-strengthening + post-wave audit.

## Wave 2 — Projected-drive calibration algebra & Kramers protection

**Goal.** The calibration layer: signed projected drive elements, duration/phase calibration identities (transverse and longitudinal), matrix-element-suppression algebra, and the Kramers-degeneracy statement for time-reversal-protected doublets. Verdict: reachable — finite-dimensional algebra; the Kramers statement is a clean antiunitary-symmetry theorem (UNKNOWN-2 for its best Mathlib formulation).

**Why.** Calibration identities are where control claims silently break (magnitude-vs-sign, suppressed matrix elements); making them signed, exact theorems closes that class. Kramers degeneracy is the textbook protection statement for any doublet-encoded system.

**Bricks.** Wave 1; `blochPauli` spectral core (`Topological.BlochBundle`, if the doublet statement uses it); PhysLib `Qubit`.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Control/DriveCalibration.lean` builds 0-sorry, kernel-pure, with:
- [ ] `projectedDriveElement_def` (signed complex `⟨0|O|1⟩` and longitudinal `(⟨0|O|0⟩−⟨1|O|1⟩)/2`) + `calibrated_duration_transverse : T = 2θ/(m·Ω)` and the longitudinal dual — both SIGNED, with fail-conditions (`m = 0`, sign-inverted target) as explicit hypotheses, not absorbed magnitudes;
- [ ] `envelope_phase_alignment : achieved axis phase = φ + arg⟨0|O|1⟩` (the phase-calibration identity);
- [ ] `matrixElement_suppression : ‖⟨0|O|1⟩‖ ≤ ‖O‖`-shape bound + a strict-suppression witness (a concrete frame where `m ≪ ‖O‖` — the physics that makes naive `θ = Ω·T` calibration wrong);
- [ ] `kramers_degeneracy : time-reversal antiunitary with T² = −1 → every eigenvalue of a T-symmetric Hamiltonian is (at least) doubly degenerate` (finite-dimensional statement; formulation per UNKNOWN-2);
- [ ] preemptive-strengthening + post-wave audit.

## Wave 3 — Composite readout ceilings

**Goal.** The capstone: end-to-end assignment-fidelity ceilings assembling relaxation (existing), thermal (existing), photon-budget (6EA), filtered-noise/matched-filter (6EB), and detector (6EC) floors, under explicit attribution hypotheses; each ceiling with `norm_num` non-vacuity witnesses on both sides. Verdict: reachable — the mechanism floors all exist by this point; the work is honest composition (the guardrail's independence/attribution discipline) and sharpness witnesses.

**Why.** This is the theorem family the whole series exists to enable: a single machine-checked inequality per readout class, from stated physical budget to fidelity ceiling.

**Bricks.** `avgAssignmentError_rational_floor` + `readoutDecayProb_enclosure` + `thermalExcitedPop` (existing); 6EA `poisson_avgError_floor` + Gaussian floors; 6EB `error_floor_from_budget`; 6EC `bolometer_error_floor`; `GeneralizedAmpDamp` + `CoherenceFidelity` for the channel-level statements.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/Control/CompositeReadoutCeilings.lean` builds 0-sorry, kernel-pure, with:
- [ ] `relaxation_thermal_ceiling` — the existing pairwise composition re-stated in the phase's uniform ceiling format (cite `avgAssignmentError_rational_floor`; no re-proof) as the format anchor;
- [ ] `photon_budget_ceiling : F ≤ 1 − (1/2)·(1/4)·exp(−(√N_a−√N_b)²)`-shape ceiling from the 6EA floor, attribution hypotheses explicit;
- [ ] `filtered_readout_ceiling` — 6EB budget floor composed to a fidelity ceiling for any admissible-filter threshold readout;
- [ ] `detector_chain_ceiling` — the 6EC bolometric floor composed end-to-end (the deepest chain: detector NEP → filter → Gaussian error → fidelity);
- [ ] `combined_ceiling_max` — mechanisms combine at least as `F ≤ 1 − max(individual floors)/2`-shape (worst-mechanism form, always sound) plus the strictly-sharper additive form under stated independence hypotheses, with the difference between the two forms itself witnessed;
- [ ] per-ceiling `norm_num` witness pairs: a budget point where the ceiling bites (claim above it = refuted) and one where it doesn't (non-triviality both ways);
- [ ] root-module import + Inventory/counts refresh; series-close notes recorded in this roadmap.
- [ ] preemptive-strengthening + post-wave audit (tautology hunt per the instructions blockquote — mandatory emphasis).

---

## Sequencing & parallelism

Wave 1 → Wave 2 serialize (calibration consumes the RWA identity); Wave 3 consumes everything and closes the series. Wave 1 may start once 6EA Wave 2 exists (it needs nothing from 6EB/6EC); **Wave 3 is the series barrier** — do not start it before 6EB Wave 3 and 6EC Wave 3 ship, or its AC list degrades to the mechanisms available (record the descope explicitly if the operator orders an early close). 6ED is an optional seam (material-parameter instantiations of the ceilings), never a blocker.

## Phase Definition of Done

- [ ] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms.
- [ ] `validate.py` green; Inventory + Index refreshed with the `Control/` family.
- [ ] Adversarial statement audit logged — composite-tautology hunt is the priority class.
- [ ] Roadmap status updated with dated shipped-declarations list; `6E*` series-close summary recorded here (what shipped across 6EA–6EE, what remains deferred).

## Open UNKNOWNs

- **UNKNOWN-1:** the RWA remainder route — direct Duhamel estimate on the interaction-picture generator (elementary, likely loose constant) vs. first-order averaging lemma (sharper, more machinery). Spike both to statement level before freezing Wave 1's AC constant shape.
  **→ Spike a THIRD route first (added 2026-07-29): in-repo BCH.** `MatrixBCHCubicMathlibPR` already
  proves the cubic BCH remainder for matrices, and the RWA bound is structurally a BCH remainder
  (`‖exp(A)exp(B) − exp(A+B)‖` at Bloch–Siegert scale `Ω/ω`). If it applies, Wave 1 reduces to
  instantiating an existing kernel-pure theorem instead of building a Duhamel or averaging estimate.
  Cost to check: one `lean_hover_info` on the BCH statement + one dimensional-analysis pass against
  the target shape. Do this before either planned spike — if it lands, both are moot; if it doesn't,
  the two original routes stand unchanged and ~15 minutes were spent.
  (PhysLib `Mathematics/Resolvent.lean` is a fourth route — see the Wave-1 Bricks note.)
- **UNKNOWN-2:** Kramers-degeneracy formulation — Mathlib's antiunitary/`LinearIsometryEquiv` conjugate-linear machinery vs. an explicit 2n×2n real-form statement. Check `lean_leansearch`/`lean_loogle` for existing quaternionic-structure results first; do not rebuild what Mathlib has.
- **UNKNOWN-3:** whether the additive combined ceiling's independence hypotheses can be stated channel-theoretically (via `GeneralizedAmpDamp` composition) rather than probabilistically — prefer the channel route if `CoherenceFidelity`'s composition pattern extends; it keeps the phase inside the existing corpus's idiom.
