import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.MixedState

/-!
# Channel structure for the diamond norm (Phase 6AE-B)

The concrete finite-dimensional infrastructure underlying the diamond norm:
the **partial trace** and the **Choi matrix**, built explicitly on
`Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ` (no Stinespring, no abstract C*).

* `partialTrace M` traces out the second tensor factor: `(∑ k, M (i,k) (j,k))`.
* `choiMatrix Φ` is the Choi/Jamiołkowski matrix of a linear map `Φ` on matrices.

These are independent of the trace-norm *metric* theory (they do not use the
triangle inequality), so they are proven here; the diamond norm's analytic
properties are documented as the deferred frontier below.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {m n : ℕ}

/-- **Partial trace** over the second tensor factor:
`(partialTrace M) i j = ∑ k, M (i,k) (j,k)`. -/
noncomputable def partialTrace (M : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ k, M (i, k) (j, k)

/-- The partial trace is linear (additive). -/
theorem partialTrace_add (M N : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    partialTrace (M + N) = partialTrace M + partialTrace N := by
  ext i j
  simp only [partialTrace, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]

/-- **The partial trace preserves the full trace**: `tr(partialTrace M) = tr M`. -/
theorem trace_partialTrace (M : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (partialTrace M).trace = M.trace := by
  simp only [partialTrace, Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type]

/-- The partial trace maps the zero matrix to zero. -/
@[simp] theorem partialTrace_zero :
    partialTrace (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 0 := by
  ext i j; simp [partialTrace]

/-- **Choi/Jamiołkowski matrix** of a linear map `Φ` on `n × n` matrices:
`choiMatrix Φ (i,k) (j,l) = Φ (E_{ij}) k l`, where `E_{ij}` is the standard basis
matrix. Encodes `Φ` as a single `n² × n²` matrix (channel–state duality). -/
noncomputable def choiMatrix (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The Choi matrix of the zero map is zero. -/
@[simp] theorem choiMatrix_zero :
    choiMatrix (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  ext p q; simp [choiMatrix]

/-
## DEFERRED FRONTIER (6AE-A steps 3–5 + 6AE-B diamond-norm properties)

These rest on analytic machinery that Mathlib at our pin (v4.29.1/`5e932f97`) does
NOT provide, verified absent by direct grep 2026-06-01: **no von Neumann trace
inequality, no Ky Fan inequality, no matrix polar decomposition, no Schatten/nuclear
norm**. Building them from scratch is a multi-week formalization, beyond this phase's
budget; fenced honestly (no sorry, no axiom) per the phase discipline.

* **Step 3 — trace-norm triangle** `‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁`. Standard route is the dual
  characterization `‖A‖₁ = sup_{‖U‖≤1} |tr(UᴴA)|`, which needs polar decomposition +
  the von Neumann trace inequality (both absent). For the Hermitian case (sufficient
  for `traceDist`), a spectral-theorem route via `‖H‖₁ = sup_{−I ≤ U ≤ I} tr(HU)` is
  plausible on the shipped `spectral_theorem` substrate but still a multi-lemma build.
* **Step 2 (remainder) — `traceDist ρ σ ∈ [0,1]` upper bound** and the metric triangle:
  depend on Step 3.
* **Step 4 — Uhlmann fidelity + Fuchs–van de Graaf**: need `cfc √` of operator products
  and the FvdG inequalities (analytic).
* **Step 5 — CPTP contractivity** `D(Φρ,Φσ) ≤ D(ρ,σ)` (data processing): needs Step 3 +
  Kraus/Stinespring-style contractivity.
* **Step 6 — `diamondNorm`** `‖Φ‖_◇ = sup_ρ ‖(Φ⊗id)ρ‖₁` and its norm axioms /
  submultiplicativity / Choi characterization: the *sup* needs boundedness +
  the tensor channel `Φ⊗id`, and the norm axioms rest on Step 3. The concrete
  `partialTrace` and `choiMatrix` above are the channel–state-duality substrate it
  builds on.

PROVEN so far (6AE-A): `traceNorm`/`traceDist` + structural properties;
`traceNorm_posSemidef` (the PSD→trace bridge, step 1 linchpin); `traceNorm_density_eq_one`.
-/

end SKEFTHawking.QuantumNetwork
