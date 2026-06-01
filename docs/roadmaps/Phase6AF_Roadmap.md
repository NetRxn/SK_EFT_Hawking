# Phase 6AF — Strengthen the deferred 6AE analytic core (trace-distance metric → diamond norm)

**Status:** OPEN (2026-06-01). Bundle-target **D6 §6**. Closes the analytic frontier deferred by Phase 6AE (DONE) — the trace-norm triangle, mixed-state distinguishability (Uhlmann fidelity + Fuchs–van de Graaf), CPTP contractivity (data processing), and the diamond norm. This fully unblocks arbitrary-state certification. User greenlit full 6AF-1→5 via autonomous `/goal`, research risk accepted.

**Inherited (do NOT re-litigate):** pin v4.29.1/`5e932f97`; CONCRETE finite-dim route on `Matrix (Fin n) (Fin n) ℂ` (no Stinespring); `open scoped ComplexOrder` (+ `Matrix.Norms.L2Operator`/`MatrixOrder` where the C*-structure is needed). Kernel-pure `{propext, Classical.choice, Quot.sound}`; **NO sorry, NO new project-local axiom** (fence intractable steps as documented deferred lemmas with the precise blocker); no `maxHeartbeats`; Stage-9 per wave (root-import + ExtractDeps + update_counts); leak discipline; preemptive-strengthening checklist before each theorem (load-bearing statements, no tautologies).

## Build-on (shipped 6AE substrate — use by name)
`QuantumNetwork/MixedState.lean`: `IsDensityOperator`, `traceNorm A = ∑√eig(AᴴA)` (via `traceNormOf` on the PSD witness), `traceDist = ½‖ρ−σ‖₁`, structural lemmas; **`trace_cfc`** (`(hM.cfc f).trace = ∑(f(eig):ℂ)`), **`isHermitian_mul_self_eq_cfc_sq`**, **`map_eigenvalues_conjTranspose_mul_self`**, **`traceNorm_posSemidef`** (PSD⟹‖A‖₁=tr A — the linchpin), `traceNorm_density_eq_one`. `QuantumNetwork/DiamondNorm.lean`: `partialTrace` + `trace_partialTrace`, `choiMatrix`.

## TOEHOLDS (the FKLW spectral arsenal — the unlock; verify each via lean-lsp before use)
- `FKLW/GenericSUdDecreasingSortPartialSums.lean` — `partial_sums_nonneg_of_decreasing_traceless` (non-increasing + traceless ⟹ partial sums ≥0): the **Ky-Fan / majorization seed** for the Hermitian trace-norm triangle.
- `FKLW/GenericSUdSpectralLift.lean`, `GenericSUdHermitianDischargeFull.lean` — extract `H = U·diag(a)·Uᴴ` + lift through unitary conjugation: the **polar-decomposition substrate**.
- `FKLW/GenericSUdEigenvalueLinftyBound.lean` — Gershgorin `|λ(A)| ≤ ‖A‖_op`.
- `FKLW/GenericSUdTraceNorm.lean` — row-sum domination / norm-via-`Finset.sup` template.
- `FKLW/SpecialUnitaryTopology.lean` — `specialUnitaryGroup_isCompact` (sup-attainment); `SpecialUnitaryPathConnected.lean` — live `CStarMatrix`/`CStarAlgebra` instance on matrices.
- `DKMBootstrap/LinearFunctionals.lean` — convex/dual-cone closure (`ProperCone`/`PointedCone`) for sup-of-linear-functionals.
- `RTReplicaTrickOnMTC.lean` — sup-attainment witness pattern. `BHEntropyMicroscopic.lean` — entropy-of-state analytic style.

## Wave sequence (dependency-ordered; ship each kernel-pure, Stage-9 wired)
| Wave | Content | Toehold | Risk |
|---|---|---|---|
| **6AF-1** | **Hermitian trace-norm triangle** `‖A+B‖₁≤‖A‖₁+‖B‖₁` (A,B Hermitian) ⟹ `traceDist` genuine metric (triangle) + `traceDist ρ σ ∈ [0,1]` for density operators. Route: `‖H‖₁ = ∑|λ| = sup over Hermitian U, −I≤U≤I, of tr(HU)` (achieved at `sign(H)` via cfc), OR Ky-Fan partial sums. | FKLW `partial_sums_nonneg_of_decreasing_traceless` + spectral lift | **days — do FIRST, de-risk** |
| **6AF-2** | Operator `|A|` (`cfc √ (AᴴA)`) + **polar decomposition** `A=U|A|`; general trace-norm triangle; von Neumann trace inequality `|tr(AB)|≤∑σᵢ(A)σᵢ(B)` if needed for the dual char | FKLW spectral lift + `trace_cfc`/`map_eigenvalues_…` | ~1 wk |
| **6AF-3** | **Uhlmann fidelity** `F(ρ,σ)=(tr√(√ρ σ √ρ))²` + **Fuchs–van de Graaf** `1−F ≤ D ≤ √(1−F²)` (quantitative, both bounds) | `cfc √` of operator products | ~1 wk |
| **6AF-4** | CPTP channel (instantiate `CompletelyPositiveMap` on `CStarMatrix`/`Matrix` + trace-preservation) + **trace-distance CONTRACTIVITY** `D(Φρ,Φσ)≤D(ρ,σ)` (data processing) | FKLW C*-bridge + 6AF-2 | **hardest — 1–2 wk, genuine risk** |
| **6AF-5** | **`diamondNorm`** `‖Φ‖_◇ = sup_ρ ‖(Φ⊗id)ρ‖₁`: tensor channel `Φ⊗id`, bounded sup (compactness), norm axioms, submultiplicativity, Choi characterization | FKLW compactness + RTReplicaTrick sup-attainment + `choiMatrix` | ~1–2 wk |

**OUT:** infinite-dim / von Neumann algebra generality; SDP solver; private/product content; demand/GTM.

**DONE:** 6AF-1→5 proven (trace-distance metric + bounds, fidelity + FvdG, CPTP contractivity, diamond norm + properties) OR any genuinely-intractable step fenced as a documented deferred lemma with the precise blocker; all modules kernel-pure + root-imported + counts regenerated; D6 §6 + preprint extended (compile-clean); fresh-context Stage-13 FULLY CLEAN.

## Progress log
- **6AF-1 (in progress) — reduction shipped** (`MixedState.lean`, kernel-pure): `traceNorm_hermitian` (`‖H‖₁ = ∑|eigᵢ|`, via the shipped `map_eigenvalues_conjTranspose_mul_self` + `Real.sqrt_sq_eq_abs`); `eigPosSum hA := ∑ max(eigᵢ,0)`; **`traceNorm_hermitian_eq`** (`‖H‖₁ = 2·eigPosSum − tr H`, from `|x|=2max(x,0)−x`). This **reduces the Hermitian trace-norm triangle to subadditivity of `eigPosSum`**. Counts 770 mod / 10079 thm / 0 axiom / 0 sorry. REMAINING for 6AF-1: `eigPosSum` subadditivity `eigPosSum(A+B) ≤ eigPosSum A + eigPosSum B` — route: positive-eigenprojection `P_H := cfc (indicator>0) H` gives **achievement** `eigPosSum H = tr_re(P_H·H)` (via cfc multiplicativity + `trace_cfc`, since `indicator·id = max(·,0)` on the spectrum) and the **bound** `tr_re(P·H) ≤ eigPosSum H` for any projection P (via spectral theorem: `tr(PH)=∑λᵢpᵢ`, `pᵢ=diag(UᴴPU)∈[0,1]`, so `∑λᵢpᵢ ≤ ∑λᵢ⁺`). Then triangle = subadditivity + trace-additivity via `traceNorm_hermitian_eq`; then `traceDist` metric + `∈[0,1]`.
