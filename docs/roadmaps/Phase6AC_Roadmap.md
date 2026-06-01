# Phase 6AC — Verified Quantum-Network Substrate III (secret-key rate + multipartite + teleportation)

**Status:** OPEN (2026-06-01). Bundle-target **D6 §6**. Builds on **Phase 6AA** (DONE, Stage-13 GREEN) and **Phase 6AB** (DONE, Stage-13 GREEN). Extends the fidelity-envelope substrate with the *operational* network metrics: the BB84 secret-key rate, the multipartite (GHZ-vs-W) distillation comparison, and the Horodecki teleportation fidelity.

**Inherited (do NOT re-litigate):** pin v4.29.1/5e932f97; native-build on bare Mathlib (no LQI/native_decide/LeanCert); Bell-diagonal/Werner real-parameter representation (no density matrices/traceNorm/diamond-norm); model-independent FIDELITY target; Pauli-error basis; dB-primitive attenuation. **Stage-9 wiring (root import + counts regen) is part of shipping each wave.** **Leak:** never write the hyphenated private-sibling-repo directory name in public files (literal pre-commit grep); no oracle/harness/cert/product framing.

## Wave catalog
| Wave | Content | Status |
|---|---|---|
| **W1** | BB84 secret-key rate: `binEntropyBit` (bits renormalization of Mathlib nats `binEntropy`) + `bb84KeyRate r(e)=1−2h₂(e)`; perfect-channel `r(0)=1`; **crossover proven not hardcoded** — `bb84KeyRate_pos_iff_binEntropy_lt` (positive ⇔ `binEntropy e < log 2/2`), `bb84KeyRate_strictAntiOn` (rate ↓ in error), `bb84_crossover_exists` (IVT: `e*∈(0,1/2)` with `r(e*)=0`), `bb84KeyRate_pos_iff_lt_crossover` (positive ⇔ `e<e*`), and `bb84_positiveKey_fidelity_threshold` (network: positive key ⇔ `F_e2e > 1−e*`) | ✅ DONE (`SecretKeyRate.lean`, kernel-pure {propext,Classical.choice,Quot.sound}) |
| **W2** | Multipartite GHZ-vs-W random-party rate: GHZ₃ rate + Fortescue–Lo Thm 3.5 (`W₃ rate ≥ GHZ₃`, strict under loss); composes with shipped `fortescueLoYield` | ⏳ PENDING |
| **W3** | Teleportation (PROBE-GATED): Mathlib Haar lemma `∫_{S²}(⟨ψ|σ_k|ψ⟩)²dμ=1/3`? If tractable → Horodecki `f_avg=(2F+1)/3` + `F>1/2` utility threshold. If hard → algebraic skeleton + Haar fact as a TRACKED HYPOTHESIS (Prop arg), NOT a project axiom | ⏳ PENDING |
| **W4** | Packaging: D6 §6 + preprint extended with W1–W3 + fresh-context Stage-13 → FULLY CLEAN | ⏳ PENDING |

## Decisions (pinned at phase open)
- **Bits vs nats.** Mathlib's `Real.binEntropy` is in *nats* (natural log): `binEntropy p = p·log p⁻¹ + (1−p)·log(1−p)⁻¹`, with `binEntropy_two_inv : binEntropy 2⁻¹ = log 2`. The Shor–Preskill formula `r=1−2h₂(e)` uses *bits*, so define `binEntropyBit p := binEntropy p / log 2` (then `h₂(1/2)=1`, `r(0)=1`). The crossover `r(e*)=0 ⟺ h₂(e*)=1/2 ⟺ binEntropy e* = log 2/2`.
- **Crossover not hardcoded.** Existence of `e*` via `intermediate_value_Icc'` on the continuous, strictly-decreasing rate (`bb84KeyRate_continuous` + `binEntropy_strictMonoOn`); uniqueness on `[0,1/2]` from `bb84KeyRate_strictAntiOn`. The decimal `≈0.11` is never asserted — it is the implicit root of `h₂(e)=1/2`.
- **Useful-half restriction.** `binEntropy` is symmetric about `1/2`, so `r(e)` has a spurious positive branch for `e→1`. The network positive-key threshold is stated under `1/2 ≤ F_e2e` (QBER `∈[0,1/2]`) to select the physical branch.

## Invariants (Phase 6AC)
- Kernel-pure `{propext, Classical.choice, Quot.sound}`; zero sorry; zero new project-local axioms (W3 Haar = tracked hypothesis if needed, not an axiom); no `maxHeartbeats`.
- Substrate self-contained under `SKEFTHawking.QuantumNetwork.*`; no external QI dependency.
- Preemptive-strengthening checklist applied before each theorem statement.

## Progress log
- **W1 — DONE** (`SecretKeyRate.lean`, kernel-pure): 9 declarations (`binEntropyBit`, `log_two_pos`, `binEntropyBit_two_inv`, `bb84KeyRate`, `bb84KeyRate_zero`, `bb84KeyRate_two_inv`, `bb84KeyRate_pos_iff_binEntropy_lt`, `bb84KeyRate_strictAntiOn`, `bb84KeyRate_continuous`, `bb84_crossover_exists`, `bb84KeyRate_pos_iff_lt_crossover`, `bb84_positiveKey_fidelity_threshold`). Root-imported into `SKEFTHawking.lean`; counts regenerated (Stage-9).
