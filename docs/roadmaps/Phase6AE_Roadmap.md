# Phase 6AE — General mixed-state / channel layer + diamond norm

**Status:** OPEN (2026-06-01). Bundle-target **D6 §6**. The deliberately-deferred "arbitrary-state certification" layer (out-of-scope through 6AD; demand-gated). Greenlit by the user with "build A then attempt B" and explicit acceptance of research risk. Builds the general density-matrix / quantum-channel substrate that the Bell-diagonal/Werner substrate (6AA–6AD) intentionally avoided.

**Inherited:** pin v4.29.1/5e932f97; kernel-pure `{propext, Classical.choice, Quot.sound}`; **zero sorry, zero new project-local axioms** (deep theorems we cannot close are *documented as deferred*, never sorried or axiomatized); no `maxHeartbeats`; Stage-9 per wave; leak discipline.

## Route decision (from the 6AE scouting probe, 2026-06-01)
Mathlib at pin **has**: `Matrix.IsHermitian.eigenvalues` + `spectral_theorem` + `trace_eq_sum_eigenvalues` (`Analysis/Matrix/Spectrum.lean`); `PosSemidef`/`PosDef` + `eigenvalues_nonneg` + `posSemidef_conjTranspose_mul_self` (`Analysis/Matrix/PosDef.lean`); `IsHermitian.cfc` operator functional calculus incl. sqrt (`HermitianFunctionalCalculus.lean`); `CompletelyPositiveMap`/`CStarMatrix`/`PositiveLinearMap`/GNS (`CStarAlgebra/`); Rayleigh/variational eigenvalues (`InnerProductSpace/Rayleigh.lean`); `Analysis/Convex/Cone/` duality.
Mathlib at pin **lacks** (all net-new): Stinespring dilation, Choi/Jamiołkowski, diamond/CB norm, trace norm/Schatten, partial trace, SDP framework.
⟹ **Concrete finite-dimensional route** on `Matrix (Fin n) (Fin n) ℂ` (no abstract C*-algebra detour, no Stinespring): trace norm = `∑ √eigenvalues(AᴴA)`; diamond norm via the explicit Choi matrix + stabilized sup.

## Wave catalog
| Wave | Content | Risk |
|---|---|---|
| **6AE-A** | `MixedState.lean`: `IsDensityOperator`, `traceNorm`, `traceDist` (metric + `[0,1]`), Uhlmann `fidelity` + Fuchs–van de Graaf, CPTP channel + **trace-distance contractivity** (data processing) | low foundation / **trace-norm triangle + contractivity = hard core** |
| **6AE-B** | `DiamondNorm.lean`: explicit `partialTrace`, `choiMatrix`, `diamondNorm` (stabilized sup) + norm axioms + submultiplicativity + Choi characterization | **research core** (no Stinespring/Choi/SDP in-library) |

**Discipline for the hard core:** ship the cleanly-provable foundation first; attempt triangle/contractivity/diamond-sup with the variational + cone substrate; if a theorem genuinely won't close in budget, record it as a *documented deferred lemma* in this roadmap (not a sorry, not an axiom) and ship everything that doesn't depend on it.

## Progress log
- **6AE-A increment 1 (foundation) — DONE** (`MixedState.lean`, kernel-pure): `IsDensityOperator` (PSD ∧ trace 1); `traceNormOf` (factored on the PSD witness — proof-irrelevant) + `traceNormOf_congr` (matrix-equality ⟹ equal trace norm) + `traceNormOf_nonneg`; `traceNorm A := traceNormOf (posSemidef_conjTranspose_mul_self A) = ∑√eigenvalues(AᴴA)`; `traceNorm_nonneg`, `traceNorm_neg` (AᴴA = (−A)ᴴ(−A)), `traceNorm_zero`; `traceDist ρ σ := ½‖ρ−σ‖₁`; `traceDist_nonneg`, `traceDist_comm`, `traceDist_self`. Root-imported; counts 769 mod / 10065 thm / 0 axiom / 0 sorry. Built on `Analysis/Matrix/{Spectrum,PosDef}` + `open scoped ComplexOrder`.

### Active research frontier (6AE-A remainder + 6AE-B) — documented, NOT sorried/axiomatized
The deep theorems require wiring Mathlib's **CFC `abs`/`sqrt`** (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean`) to the eigenvalue-sum trace norm, plus the variational (`InnerProductSpace/Rayleigh.lean`) and cone-duality (`Analysis/Convex/Cone/`) substrate. Confirmed multi-session research, sequenced:
1. **Bridge** `traceNorm (PosSemidef A) = A.trace.re` — linchpin. **Workhorse PROVEN** (`trace_cfc`: `(hM.cfc f).trace = ∑ (f(eigenvalues i):ℂ)`, kernel-pure, via the `trace_eq_zero_iff` template — unitary-conjugation trace-invariance + `trace_diagonal`). Two routes to finish, both blocked off-the-shelf: (a) `traceNorm A = (trace (CFC.abs A)).re` + `CFC.abs_of_nonneg` — BLOCKED: `NonUnitalContinuousFunctionalCalculus ℝ (Matrix _ _ ℂ) IsSelfAdjoint` does not synthesize even with `open scoped Matrix.Norms.L2Operator` (Mathlib instance gap); (b) concrete via `trace_cfc` only — reduces to `eigenvalues(AᴴA) i = (eigenvalues A i)²` for PSD A, needs an **antitone-sort-uniqueness** lemma (squaring preserves order on the nonneg PSD spectrum; derive `AᴴA = U·D²·Uᴴ` from `spectral_theorem` then uniqueness of sorted eigenvalues). **Route (b) is the active next attempt** — avoids the CFC instance entirely. Blocker documented in `MixedState.lean`.
2. **`traceNorm` of density = 1** + `traceDist ρ σ ∈ [0,1]` (needs bridge + triangle).
3. **Trace-norm triangle inequality** `‖A+B‖₁ ≤ ‖A‖₁+‖B‖₁` — the hard core; via the dual/variational characterization `‖A‖₁ = sup_{‖U‖≤1}|tr(UᴴA)|`.
4. **Uhlmann fidelity + Fuchs–van de Graaf** (`cfc sqrt`).
5. **CPTP contractivity** `D(Φρ,Φσ) ≤ D(ρ,σ)` (data processing) — instantiate `CompletelyPositiveMap` on `CStarMatrix`/`Matrix`.
6. **6AE-B**: explicit `partialTrace`, `choiMatrix`, `diamondNorm` (stabilized sup) + norm axioms + Choi characterization.

**Status:** foundation shipped and verified; the frontier is the genuine research effort the 6AE scoping flagged (A′ research-grade). Held for a dedicated multi-session push rather than rushed (no overclaim; correctness over expediency).
