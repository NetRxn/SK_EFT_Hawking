import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.MixedState
import SKEFTHawking.QuantumNetwork.CPTPChannel

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
## STATUS (updated 2026-06-01 after Phase 6AF)

Most of the analytic frontier that 6AE deferred has since been PROVEN in Phase 6AF — the
6AE blocker note ("no von Neumann / Ky Fan / polar / Schatten") was bypassed by a
positive-part + Hermitian-dilation + charpoly route that needs none of them:

* **Step 3 — trace-norm triangle**: ✅ DONE (`MixedState.traceNorm_hermitian_triangle`,
  and the *general* non-Hermitian `traceNorm_triangle` via the Hermitian dilation).
* **Step 2 — `traceDist ∈ [0,1]` + metric triangle**: ✅ DONE (`traceDist_triangle`,
  `traceDist_mem_Icc`).
* **Step 4 — Uhlmann fidelity**: ✅ FOUNDATION DONE (`sqrtFidelity`/`fidelity`, `=1` on the
  diagonal, symmetric, Uhlmann form verified). `F ≤ 1` (`sqrtFidelity_le_one`) and the
  Fuchs–van de Graaf **lower** bound `1−F ≤ D` (`one_sub_sqrtFidelity_le_traceDist`) are now PROVEN
  (Phase 6AF-7, `FidelityBounds.lean`); only the FvdG **upper** bound `D ≤ √(1−F²)` remains fenced
  (Uhlmann purification, grep-verified absent).
* **Step 5 — CPTP contractivity** `D(Φρ,Φσ) ≤ D(ρ,σ)`: ✅ DONE (`CPTPChannel.lean`,
  `traceDist_krausMap_le`).
* **Step 6 — `diamondNorm`** `‖Φ‖_◇ = sup_ρ ‖(Φ⊗id)ρ‖₁`: the **Choi positivity**
  half of the channel–state duality is proven below (`choiMatrix_krausMap_posSemidef`).
  The full diamond *norm* (the supremum over states + its boundedness/attainment, the
  tensor channel `Φ⊗id` over the product index, and the norm axioms) remains the
  DEFERRED FRONTIER — see the dedicated note after the Choi theorem below.
-/

/-- **Choi positivity (channel–state duality, 6AF-5)**: the Choi matrix of a Kraus channel
`Φ(ρ) = ∑ₖ Kₖ ρ Kₖᴴ` is positive semidefinite. This is the "easy" (⟹) direction of Choi's
theorem — complete positivity implies a PSD Choi matrix — proven concretely: the Choi matrix
is `∑ₖ wₖ wₖᴴ` with `wₖ(p) = Kₖ(p.2, p.1)`, a sum of rank-one PSD outer products. -/
theorem choiMatrix_krausMap_posSemidef (K : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (choiMatrix (krausMap K)).PosSemidef := by
  have key : choiMatrix (krausMap K)
      = ∑ k, (Matrix.of fun (p : Fin n × Fin n) (_ : Fin 1) => K k p.2 p.1)
          * (Matrix.of fun (p : Fin n × Fin n) (_ : Fin 1) => K k p.2 p.1)ᴴ := by
    ext p q
    simp only [choiMatrix, krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_self_mul_conjTranspose _

/-
## STATUS — the diamond norm (updated 2026-06-01, Phase 6AF-6)

`choiMatrix_krausMap_posSemidef` above gives the channel–state-duality positivity. The diamond
norm itself has since been BUILT in `DiamondNormSup.lean`, in its operational trace-distance form
`diamondDist Φ₁ Φ₂ = sup_ρ D((Φ₁⊗id)ρ, (Φ₂⊗id)ρ) = ½‖Φ₁−Φ₂‖_◇`:

* the two earlier blockers dissolved — the **tensor channel `Φ⊗id`** is now a CPTP Kraus channel
  (`isKrausChannel_tensorKraus`, via the Kronecker mixed-product lemmas), and the **product-index**
  obstruction vanished once the trace-norm / CPTP theory was generalized from `Fin n` to an
  arbitrary `[Fintype ι][DecidableEq ι]` (Phase 6AF-6a), instantiated here at `Fin n × Fin n`;
* the **supremum** is well-defined via `Real.sSup` from **boundedness alone** (every term is in
  `[0,1]` since the stabilized outputs are density operators) — attainment is *not* needed to
  define it or to prove its properties: `diamondDist` is proven nonnegative, `≤ 1`, symmetric,
  and zero on the diagonal.

Since then (Phase 6AF-7/8, 2026-06-02) the **triangle inequality** (`diamondDist_triangle`, in
`DiamondNormSup.lean`) and **attainment** of the sup (`exists_diamondDist_eq`, in
`DiamondNormAttainment.lean`, via trace-norm continuity + compactness of the density set + EVT)
are both PROVEN — so `diamondDist` is a genuine `[0,1]`-valued metric whose supremum is a maximum.
The **Choi-SDP / Watrous duality** characterization — the full primal=dual SDP identity
`diamondDist_eq_choiSDP` — is now PROVEN unconditionally and kernel-pure (Phase 6AI,
`DiamondSDPDuality.lean`, via the geometric Hahn–Banach / conic Farkas lemma
`geometric_hahn_banach_compact_closed`); the former "convex-duality substrate absent at pin" fence
was stale (Mathlib v4.29.1 ships conic Farkas). No documented-deferred QI-analytic item remains. The
**primal (one-sided) lower bound** is PROVEN in `DiamondNormChoi.lean`
(`diamondDist_ge_maxEntangled`): `le_diamondDist` evaluated at the maximally-entangled (Choi)
feasible point gives `diamondDist Φ₁ Φ₂ ≥ D((Φ₁⊗id)Ω, (Φ₂⊗id)Ω)` with no SDP duality. (Its
quantitative Choi-matrix form `≥ (1/2n)·‖J(Φ₁)−J(Φ₂)‖₁` would additionally need the identity
`(Φ⊗id)Ω = (1/n)·choiMatrix(Φ)` — an optional refinement, not shipped.)
-/

end SKEFTHawking.QuantumNetwork
