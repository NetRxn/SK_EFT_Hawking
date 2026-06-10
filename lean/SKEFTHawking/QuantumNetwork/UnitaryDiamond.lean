import SKEFTHawking.QuantumNetwork.DiamondNormSup
import SKEFTHawking.QuantumNetwork.KroneckerOpNorm
import SKEFTHawking.QuantumNetwork.OpNormHolder
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Unitary operator-norm → diamond bound (Phase 6AP, Wave 3)

The Aharonov–Kitaev–Nisan-style conversion from gate-synthesis error to worst-case channel
error: for unitary channels `Φ_U(ρ) = UρUᴴ`, `Φ_V(ρ) = VρVᴴ`,

  `diamondDist Φ_U Φ_V ≤ ‖U − V‖_op`

in this project's `½‖·‖_◇` diamond-distance convention (equivalently `‖Φ_U − Φ_V‖_◇ ≤
2‖U − V‖_op`; AKN 1998, Watrous *TQI* §3.3 exercise class). This converts a compiled-gate
operator-norm error (e.g. a Clifford+T synthesis bound) into a certified diamond figure.

**Sharpness caveat (stated, not silently claimed):** the bound is NOT sharp under global
phase — `U` and `e^{iθ}U` generate the SAME channel (`diamondDist = 0`,
`diamondDist_unitary_smul_phase`) while `‖U − e^{iθ}U‖_op > 0`. The known tightening
optimizes the phase (`min_θ ‖U − e^{iθ}V‖`); it is documented here and deliberately not
shipped as part of this wave.

## Substrate

* The general trace-norm toolbox is transferred from the PhysLib dependency through the
  identification `traceNorm_eq_physlib` (both norms are the sum of singular values):
  subadditivity `traceNorm_add_le` and the two Hölder bounds
  `traceNorm_mul_le_l2opNorm` / `traceNorm_mul_le_traceNorm_l2opNorm`.
* The telescope is proven for arbitrary CONTRACTIONS (`‖A‖, ‖B‖ ≤ 1`), strictly stronger
  than the unitary case: `traceNorm_conj_diff_le`.
* The ancilla register is handled by `KroneckerOpNorm.l2_opNorm_kronecker_one_le` (W2).

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The two trace norms agree (sum of singular values) -/

private lemma eigenvalues_congr {M N : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hN : N.IsHermitian) (h : M = N) : hM.eigenvalues = hN.eigenvalues := by
  subst h; rfl

/-- **The project trace norm coincides with the PhysLib trace norm** — both are the sum of
singular values `∑ √eigenvalues(AᴴA)` (`Matrix.traceNorm_eq_sum_singularValues` on the
PhysLib side). This single identification imports PhysLib's general trace-norm toolbox
(subadditivity, Hölder) for the diamond-distance layer. -/
theorem traceNorm_eq_physlib (A : Matrix ι ι ℂ) : traceNorm A = Matrix.traceNorm A := by
  rw [Matrix.traceNorm_eq_sum_singularValues]
  unfold traceNorm traceNormOf singularValues
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact congrFun (eigenvalues_congr _ _ (by rw [Matrix.conjTranspose_conjTranspose])) i

/-- **Trace-norm subadditivity (general matrices):** `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`
(via PhysLib `Matrix.traceNorm_add_le` through `traceNorm_eq_physlib`). -/
theorem traceNorm_add_le (A B : Matrix ι ι ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  simp only [traceNorm_eq_physlib]
  exact Matrix.traceNorm_add_le A B

/-- **Hölder (op-left):** `‖A·B‖₁ ≤ ‖A‖_op · ‖B‖₁`
(PhysLib `Matrix.traceNorm_mul_le_opNorm_traceNorm`). -/
theorem traceNorm_mul_le_l2opNorm (A B : Matrix ι ι ℂ) :
    traceNorm (A * B) ≤ ‖A‖ * traceNorm B := by
  simp only [traceNorm_eq_physlib]
  exact Matrix.traceNorm_mul_le_opNorm_traceNorm A B

/-- **Hölder (op-right):** `‖A·B‖₁ ≤ ‖A‖₁ · ‖B‖_op`
(PhysLib `Matrix.traceNorm_mul_le_traceNorm_opNorm`). -/
theorem traceNorm_mul_le_traceNorm_l2opNorm (A B : Matrix ι ι ℂ) :
    traceNorm (A * B) ≤ traceNorm A * ‖B‖ := by
  simp only [traceNorm_eq_physlib]
  exact Matrix.traceNorm_mul_le_traceNorm_opNorm A B

/-! ## §2. Unitaries are operator-norm contractions -/

/-- A unitary matrix has L²-operator norm at most `1` (via the Loewner contraction
criterion `opNorm_le_one_of_mul_conjTranspose_le_one` with `U·Uᴴ = 1`). -/
theorem l2_opNorm_le_one_of_unitary [Nonempty ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : ‖U‖ ≤ 1 := by
  apply opNorm_le_one_of_mul_conjTranspose_le_one
  have h : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.mp hU)
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [h, sub_self]
  exact Matrix.PosSemidef.zero

/-! ## §3. The contraction telescope -/

/-- **Conjugation-difference telescope (contraction form).** For operator-norm contractions
`A, B` (`‖A‖, ‖B‖ ≤ 1`) and any matrix `ρ`:

  `‖AρAᴴ − BρBᴴ‖₁ ≤ 2·‖A − B‖_op·‖ρ‖₁`

via the add–subtract split `AρAᴴ − BρBᴴ = (A−B)ρAᴴ + Bρ(A−B)ᴴ`, subadditivity, and the
two Hölder bounds. Strictly stronger than the unitary case (any Kraus contraction works). -/
theorem traceNorm_conj_diff_le {A B : Matrix ι ι ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (ρ : Matrix ι ι ℂ) :
    traceNorm (A * ρ * Aᴴ - B * ρ * Bᴴ) ≤ 2 * ‖A - B‖ * traceNorm ρ := by
  have hsplit : A * ρ * Aᴴ - B * ρ * Bᴴ
      = (A - B) * (ρ * Aᴴ) + (B * ρ) * (A - B)ᴴ := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have hAH : ‖Aᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]; exact hA
  have hABH : ‖(A - B)ᴴ‖ = ‖A - B‖ := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
  have hρnn : 0 ≤ traceNorm ρ := traceNorm_nonneg ρ
  have hABnn : 0 ≤ ‖A - B‖ := norm_nonneg _
  -- first term: ‖(A−B)·(ρAᴴ)‖₁ ≤ ‖A−B‖·‖ρAᴴ‖₁ ≤ ‖A−B‖·‖ρ‖₁·‖Aᴴ‖ ≤ ‖A−B‖·‖ρ‖₁
  have h₁ : traceNorm ((A - B) * (ρ * Aᴴ)) ≤ ‖A - B‖ * traceNorm ρ := by
    calc traceNorm ((A - B) * (ρ * Aᴴ))
        ≤ ‖A - B‖ * traceNorm (ρ * Aᴴ) := traceNorm_mul_le_l2opNorm _ _
      _ ≤ ‖A - B‖ * (traceNorm ρ * ‖Aᴴ‖) := by
          exact mul_le_mul_of_nonneg_left (traceNorm_mul_le_traceNorm_l2opNorm _ _) hABnn
      _ ≤ ‖A - B‖ * (traceNorm ρ * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hABnn
          exact mul_le_mul_of_nonneg_left hAH hρnn
      _ = ‖A - B‖ * traceNorm ρ := by ring
  -- second term: ‖(Bρ)·(A−B)ᴴ‖₁ ≤ ‖Bρ‖₁·‖A−B‖ ≤ ‖B‖·‖ρ‖₁·‖A−B‖ ≤ ‖ρ‖₁·‖A−B‖
  have h₂ : traceNorm ((B * ρ) * (A - B)ᴴ) ≤ ‖A - B‖ * traceNorm ρ := by
    calc traceNorm ((B * ρ) * (A - B)ᴴ)
        ≤ traceNorm (B * ρ) * ‖(A - B)ᴴ‖ := traceNorm_mul_le_traceNorm_l2opNorm _ _
      _ = traceNorm (B * ρ) * ‖A - B‖ := by rw [hABH]
      _ ≤ (‖B‖ * traceNorm ρ) * ‖A - B‖ := by
          exact mul_le_mul_of_nonneg_right (traceNorm_mul_le_l2opNorm _ _) hABnn
      _ ≤ (1 * traceNorm ρ) * ‖A - B‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hABnn
          exact mul_le_mul_of_nonneg_right hB hρnn
      _ = ‖A - B‖ * traceNorm ρ := by ring
  calc traceNorm (A * ρ * Aᴴ - B * ρ * Bᴴ)
      = traceNorm ((A - B) * (ρ * Aᴴ) + (B * ρ) * (A - B)ᴴ) := by rw [hsplit]
    _ ≤ traceNorm ((A - B) * (ρ * Aᴴ)) + traceNorm ((B * ρ) * (A - B)ᴴ) :=
        traceNorm_add_le _ _
    _ ≤ ‖A - B‖ * traceNorm ρ + ‖A - B‖ * traceNorm ρ := add_le_add h₁ h₂
    _ = 2 * ‖A - B‖ * traceNorm ρ := by ring

/-! ## §4. The diamond AKN bound for unitary Kraus channels -/

variable {n : ℕ}

/-- The single-operator Kraus family of a unitary conjugation `ρ ↦ UρUᴴ`. -/
noncomputable def unitaryKraus (U : Matrix (Fin n) (Fin n) ℂ) :
    Fin 1 → Matrix (Fin n) (Fin n) ℂ :=
  fun _ => U

/-- A unitary's single-operator Kraus family is a CPTP channel (`UᴴU = 1`). -/
theorem isKrausChannel_unitaryKraus {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : IsKrausChannel (unitaryKraus U) := by
  unfold IsKrausChannel unitaryKraus
  rw [Fin.sum_univ_one]
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

/-- The stabilized action of the unitary Kraus family: `(Φ_U ⊗ id)ρ = (U⊗I)ρ(U⊗I)ᴴ`. -/
theorem krausMap_tensorKraus_unitaryKraus (U : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    krausMap (tensorKraus (unitaryKraus U)) ρ
      = (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  unfold krausMap tensorKraus unitaryKraus
  rw [Fin.sum_univ_one]

/-- **The diamond AKN bound** (Aharonov–Kitaev–Nisan 1998, in the `½‖·‖_◇` diamond-distance
convention): for unitaries `U, V`,

  `diamondDist Φ_U Φ_V ≤ ‖U − V‖_op`

(equivalently `‖Φ_U − Φ_V‖_◇ ≤ 2‖U − V‖_op`). Pointwise over every stabilized input the
contraction telescope gives `D((Φ_U⊗id)ρ, (Φ_V⊗id)ρ) ≤ ‖(U−V)⊗I‖_op ≤ ‖U−V‖_op` (W2
Kronecker bound), and the supremum preserves the bound. Converts a compiled-gate
operator-norm error into a certified worst-case channel error. NOT phase-sharp — see
`diamondDist_unitary_smul_phase`. -/
theorem diamondDist_unitaryKraus_le [NeZero n] {U V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    diamondDist (unitaryKraus U) (unitaryKraus V) ≤ ‖U - V‖ := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  apply Real.sSup_le _ (norm_nonneg _)
  rintro d ⟨ρ, hρ, rfl⟩
  rw [krausMap_tensorKraus_unitaryKraus, krausMap_tensorKraus_unitaryKraus]
  set A := U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hAdef
  set B := V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hBdef
  have hAB : A - B = (U - V) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hAdef, hBdef]
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [sub_mul]
  have hA1 : ‖A‖ ≤ 1 :=
    (KroneckerOpNorm.l2_opNorm_kronecker_one_le U).trans (l2_opNorm_le_one_of_unitary hU)
  have hB1 : ‖B‖ ≤ 1 :=
    (KroneckerOpNorm.l2_opNorm_kronecker_one_le V).trans (l2_opNorm_le_one_of_unitary hV)
  have hABop : ‖A - B‖ ≤ ‖U - V‖ := by
    rw [hAB]; exact KroneckerOpNorm.l2_opNorm_kronecker_one_le (U - V)
  have htele := traceNorm_conj_diff_le hA1 hB1 ρ
  have hρ1 : traceNorm ρ = 1 := traceNorm_density_eq_one hρ
  rw [hρ1, mul_one] at htele
  unfold traceDist
  have hABnn : 0 ≤ ‖A - B‖ := norm_nonneg _
  nlinarith [htele, hABop]

/-! ## §5. Phase non-sharpness (the honest caveat, as a theorem) -/

/-- **Global phase yields the SAME channel:** for `|c| = 1`, the Kraus conjugations of `c•U`
and `U` agree pointwise — `(c•U)ρ(c•U)ᴴ = (c·c̄)•(UρUᴴ) = UρUᴴ`. -/
theorem krausMap_tensorKraus_smul_phase {c : ℂ} (hc : ‖c‖ = 1)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    krausMap (tensorKraus (unitaryKraus (c • U))) ρ
      = krausMap (tensorKraus (unitaryKraus U)) ρ := by
  rw [krausMap_tensorKraus_unitaryKraus, krausMap_tensorKraus_unitaryKraus]
  rw [Matrix.smul_kronecker, Matrix.conjTranspose_smul]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : Complex.normSq c = 1 := by
    rw [← Complex.sq_norm, hc]; norm_num
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, h2]; norm_cast
  rw [hcc, one_smul]

/-- **The AKN bound is NOT sharp under global phase:** `c•U` (`|c| = 1`) and `U` are at
diamond distance ZERO — they are the same channel — while `‖c•U − U‖_op` is generically
positive (e.g. `c = −1`: `‖−U−U‖ = 2‖U‖`). The known tightening optimizes the global phase;
it is documented, not silently claimed, and the un-optimized bound above remains sound. -/
theorem diamondDist_unitary_smul_phase {c : ℂ} (hc : ‖c‖ = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    diamondDist (unitaryKraus (c • U)) (unitaryKraus U) = 0 := by
  unfold diamondDist
  have hset : {d | ∃ ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator ρ ∧
      d = traceDist (krausMap (tensorKraus (unitaryKraus (c • U))) ρ)
        (krausMap (tensorKraus (unitaryKraus U)) ρ)}
      = {d | ∃ ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator ρ ∧
      d = traceDist (krausMap (tensorKraus (unitaryKraus U)) ρ)
        (krausMap (tensorKraus (unitaryKraus U)) ρ)} := by
    refine Set.ext fun d => ⟨?_, ?_⟩ <;> rintro ⟨ρ, hρ, rfl⟩ <;>
      exact ⟨ρ, hρ, by rw [krausMap_tensorKraus_smul_phase hc]⟩
  rw [hset]
  have := diamondDist_self (unitaryKraus U)
  unfold diamondDist at this
  exact this

end SKEFTHawking.QuantumNetwork
