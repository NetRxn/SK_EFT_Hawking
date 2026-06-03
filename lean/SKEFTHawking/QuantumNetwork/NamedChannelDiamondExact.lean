import SKEFTHawking.QuantumNetwork.DiamondNormDual
import SKEFTHawking.QuantumNetwork.NamedChannels

/-!
# Exact diamond distance for named channels via the optimal dual witness (Phase 6AG, Ask 1 exact)
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- A `γ`-scaled real rank-one outer product `p q ↦ γ·s(p)·s(q)` is PSD for `γ ≥ 0`
(it is `A·Aᴴ` for the single column `A p _ = √γ·s(p)`). -/
theorem posSemidef_smul_outer {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ℝ} (hγ : 0 ≤ γ)
    (s : ι → ℝ) : (Matrix.of fun p q => (γ : ℂ) * (s p : ℂ) * (s q : ℂ)).PosSemidef := by
  set A : Matrix ι (Fin 1) ℂ := Matrix.of fun p _ => (Real.sqrt γ : ℂ) * (s p : ℂ) with hA
  have hAA : A * Aᴴ = Matrix.of fun p q => (γ : ℂ) * (s p : ℂ) * (s q : ℂ) := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hA, Matrix.of_apply,
      Fin.sum_univ_one, Complex.star_def, map_mul, Complex.conj_ofReal]
    rw [show (Real.sqrt γ : ℂ) * (s p : ℂ) * ((Real.sqrt γ : ℂ) * (s q : ℂ))
        = ((Real.sqrt γ * Real.sqrt γ : ℝ) : ℂ) * (s p : ℂ) * (s q : ℂ) by push_cast; ring,
      Real.mul_self_sqrt hγ]
  rw [← hAA]; exact Matrix.posSemidef_self_mul_conjTranspose A

/-- The Bloch vector of the optimal dephasing witness: `e₀₀ − e₁₁`. -/
def sDeph : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0

/-- The optimal dual witness for the dephasing channel difference: `γ·v vᵀ` with `v = e₀₀ − e₁₁`. -/
noncomputable def dephasingWitness (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => (γ : ℂ) * (sDeph p : ℂ) * (sDeph q : ℂ)

theorem dephasingWitness_posSemidef {γ : ℝ} (hγ : 0 ≤ γ) : (dephasingWitness γ).PosSemidef :=
  posSemidef_smul_outer hγ sDeph

/-- `ptrace₂ (dephasingWitness γ) = γ·1`. -/
theorem ptrace2_dephasingWitness (γ : ℝ) :
    ptrace2 (dephasingWitness γ) = (γ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, dephasingWitness, sDeph, Matrix.smul_apply, Fin.sum_univ_two]

/-- `W − C ≥ 0`: the witness dominates the Choi difference in the Loewner order. `W − C = γ·v' v'ᵀ`
with `v' = e₀₀ + e₁₁`. -/
theorem dephasingWitness_sub_choi_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (dephasingWitness γ - (choiMatrix (krausMap (dephasingKraus γ))
      - choiMatrix (krausMap (idKrausPad 1 2)))).PosSemidef := by
  rw [dephasing_choi_diff h0 h1]
  have heq : dephasingWitness γ - (γ : ℂ) • dephasingChoiBase
      = Matrix.of fun p q => (γ : ℂ)
          * ((if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0 : ℝ) : ℂ)
          * ((if q = (0, 0) then 1 else if q = (1, 1) then 1 else 0 : ℝ) : ℂ) := by
    ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp only [Matrix.sub_apply, dephasingWitness, Matrix.of_apply, sDeph, Matrix.smul_apply,
        smul_eq_mul, dephasingChoiBase, Prod.mk.injEq, Fin.isValue] <;>
      norm_num <;> ring
  rw [heq]
  exact posSemidef_smul_outer h0 (fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0)

/-- **Exact dephasing diamond distance:** `diamondDist (dephasingKraus γ) (id) = γ` for
`0 ≤ γ ≤ 1`. Lower bound `diamondDist_dephasing_ge`; upper bound `diamondDist_le_dual_witness` at
the optimal witness `dephasingWitness γ` (with `‖ptrace₂ W‖ = ‖γ·1‖ = γ`). The two-sided envelope
is closed — the first exact diamond distance for a named channel, with no twirl machinery. -/
theorem diamondDist_dephasing_eq {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    diamondDist (dephasingKraus γ) (idKrausPad 1 2) = γ := by
  refine le_antisymm ?_ (diamondDist_dephasing_ge h0 h1)
  have hub := diamondDist_le_dual_witness (isKrausChannel_dephasingKraus h0 h1)
    (isKrausChannel_idKrausPad 1 2) (dephasingWitness_posSemidef h0)
    (dephasingWitness_sub_choi_posSemidef h0 h1)
  rwa [ptrace2_dephasingWitness, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg h0] at hub

/-! ## Depolarizing channel: exact diamond distance `= p` -/

/-- Bloch indicators for the two off-diagonal `+2/3` eigenvectors `e₀₁, e₁₀`. -/
def s01Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 1) then 1 else 0
def s10Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (1, 0) then 1 else 0

/-- The optimal dual witness for depolarizing: the positive part `C₊ = (2p/3)·P₊`, written as the
sum of the three rank-one projectors onto the `+2/3` eigenspace `{e₀₁, e₁₀, (e₀₀−e₁₁)/√2}`. -/
noncomputable def depolarizingWitness (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (Matrix.of fun a b => ((2 * p / 3 : ℝ) : ℂ) * (s01Dep a : ℂ) * (s01Dep b : ℂ))
  + (Matrix.of fun a b => ((2 * p / 3 : ℝ) : ℂ) * (s10Dep a : ℂ) * (s10Dep b : ℂ))
  + (Matrix.of fun a b => ((p / 3 : ℝ) : ℂ) * (sDeph a : ℂ) * (sDeph b : ℂ))

theorem depolarizingWitness_posSemidef {p : ℝ} (hp : 0 ≤ p) : (depolarizingWitness p).PosSemidef := by
  have h23 : (0 : ℝ) ≤ 2 * p / 3 := by linarith
  have h3 : (0 : ℝ) ≤ p / 3 := by linarith
  exact ((posSemidef_smul_outer h23 s01Dep).add (posSemidef_smul_outer h23 s10Dep)).add
    (posSemidef_smul_outer h3 sDeph)

theorem ptrace2_depolarizingWitness (p : ℝ) :
    ptrace2 (depolarizingWitness p) = (p : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, depolarizingWitness, s01Dep, s10Dep, sDeph, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two] <;> ring

theorem depolarizingWitness_sub_choi_posSemidef {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (depolarizingWitness p - (choiMatrix (krausMap (depolarizingKraus p))
      - choiMatrix (krausMap (idKrausPad 3 2)))).PosSemidef := by
  rw [depolarizing_choi_diff h0 h1]
  have heq : depolarizingWitness p - (p : ℂ) • depolarizingChoiBase
      = Matrix.of fun a b => (p : ℂ)
          * ((if a = (0, 0) then 1 else if a = (1, 1) then 1 else 0 : ℝ) : ℂ)
          * ((if b = (0, 0) then 1 else if b = (1, 1) then 1 else 0 : ℝ) : ℂ) := by
    ext q r; obtain ⟨a, y⟩ := q; obtain ⟨b, y'⟩ := r
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp only [depolarizingWitness, s01Dep, s10Dep, sDeph, depolarizingChoiBase, Matrix.sub_apply,
        Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq,
        Fin.isValue] <;>
      norm_num <;> ring
  rw [heq]
  exact posSemidef_smul_outer h0 (fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0)

/-- **Exact depolarizing diamond distance:** `diamondDist (depolarizingKraus p) (id) = p` for
`0 ≤ p ≤ 1`. Lower bound `diamondDist_depolarizing_ge`; upper bound at the positive-part dual
witness (`ptrace₂ W = p·1`). Two-sided exact value for the second named channel. -/
theorem diamondDist_depolarizing_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    diamondDist (depolarizingKraus p) (idKrausPad 3 2) = p := by
  refine le_antisymm ?_ (diamondDist_depolarizing_ge h0 h1)
  have hub := diamondDist_le_dual_witness (isKrausChannel_depolarizingKraus h0 h1)
    (isKrausChannel_idKrausPad 3 2) (depolarizingWitness_posSemidef h0)
    (depolarizingWitness_sub_choi_posSemidef h0 h1)
  rwa [ptrace2_depolarizingWitness, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg h0] at hub

/-! ## Amplitude-damping channel: two-sided bracket (non-covariant, clean upper bound) -/

/-- Standard-basis indicators at `(0,0)` and `(1,1)`. -/
def s00Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 0) then 1 else 0
def s11Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (1, 1) then 1 else 0

/-- A dual witness for amplitude damping (not optimal, but clean): `γ·|e₀₁⟩⟨e₀₁| + γ·|e₁₀⟩⟨e₁₀| +
(1−√(1−γ))·|v⟩⟨v|` with `v = e₀₀−e₁₁`. Gives `W − C` diagonal-PSD and `ptrace₂ W` scalar. -/
noncomputable def ampDampWitness (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (Matrix.of fun a b => (γ : ℂ) * (s01Dep a : ℂ) * (s01Dep b : ℂ))
  + (Matrix.of fun a b => (γ : ℂ) * (s10Dep a : ℂ) * (s10Dep b : ℂ))
  + (Matrix.of fun a b => ((1 - Real.sqrt (1 - γ) : ℝ) : ℂ) * (sDeph a : ℂ) * (sDeph b : ℂ))

theorem one_sub_sqrt_nonneg {γ : ℝ} (h0 : 0 ≤ γ) : (0 : ℝ) ≤ 1 - Real.sqrt (1 - γ) := by
  have hle : Real.sqrt (1 - γ) ≤ 1 :=
    calc Real.sqrt (1 - γ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  linarith

theorem ampDampWitness_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) : (ampDampWitness γ).PosSemidef :=
  ((posSemidef_smul_outer h0 s01Dep).add (posSemidef_smul_outer h0 s10Dep)).add
    (posSemidef_smul_outer (one_sub_sqrt_nonneg h0) sDeph)

theorem ptrace2_ampDampWitness (γ : ℝ) :
    ptrace2 (ampDampWitness γ)
      = ((γ + (1 - Real.sqrt (1 - γ)) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, ampDampWitness, s01Dep, s10Dep, sDeph, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two] <;> push_cast <;> ring

theorem ampDampWitness_sub_choi_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (ampDampWitness γ - (choiMatrix (krausMap (ampDampKraus γ))
      - choiMatrix (krausMap (idKrausPad 1 2)))).PosSemidef := by
  rw [ampDamp_choi_diff h0 h1]
  have heq : ampDampWitness γ - ampDampChoiDiff γ
      = (Matrix.of fun a b => ((1 - Real.sqrt (1 - γ) : ℝ) : ℂ) * (s00Dep a : ℂ) * (s00Dep b : ℂ))
        + (Matrix.of fun a b => (γ : ℂ) * (s01Dep a : ℂ) * (s01Dep b : ℂ))
        + (Matrix.of fun a b => ((1 - Real.sqrt (1 - γ) + γ : ℝ) : ℂ)
            * (s11Dep a : ℂ) * (s11Dep b : ℂ)) := by
    ext q r; obtain ⟨a, y⟩ := q; obtain ⟨b, y'⟩ := r
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp [ampDampWitness, ampDampChoiDiff, s00Dep, s01Dep, s10Dep, s11Dep, sDeph,
        Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, Prod.mk.injEq] <;>
      push_cast <;> ring
  rw [heq]
  exact ((posSemidef_smul_outer (one_sub_sqrt_nonneg h0) s00Dep).add
      (posSemidef_smul_outer h0 s01Dep)).add
    (posSemidef_smul_outer (by have := one_sub_sqrt_nonneg h0; linarith) s11Dep)

/-- **Amplitude-damping two-sided diamond bracket:** `γ/2 ≤ diamondDist (ampDampKraus γ) (id) ≤
γ + 1 − √(1−γ)` for `0 ≤ γ ≤ 1`. The upper bound (the direction the channel is benchmarked in)
comes from `diamondDist_le_dual_witness` at a clean — non-optimal — dual witness; amplitude damping
is not Pauli-covariant so the Choi input is not optimal and the bracket is not tight (exact value
needs the `√(1−γ)`-dependent eigenvector witness). -/
theorem diamondDist_ampDamp_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    diamondDist (ampDampKraus γ) (idKrausPad 1 2) ≤ γ + 1 - Real.sqrt (1 - γ) := by
  have hub := diamondDist_le_dual_witness (isKrausChannel_ampDampKraus h0 h1)
    (isKrausChannel_idKrausPad 1 2) (ampDampWitness_posSemidef h0)
    (ampDampWitness_sub_choi_posSemidef h0 h1)
  rw [ptrace2_ampDampWitness, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by have := one_sub_sqrt_nonneg h0; linarith)] at hub
  linarith

/-! ## Amplitude damping: EXACT diamond distance `= γ` (product-state worst case)

Amplitude damping is *not* Pauli-covariant, so the maximally entangled (Choi) input is not optimal
and the `diamondDist_ampDamp_le` bracket is loose. The true worst-case input is the **unentangled
product state** `|1⟩⟨1| ⊗ |1⟩⟨1|`: on it the output–input difference is the real-diagonal matrix
`γ·E_{(0,1)} − γ·E_{(1,1)}` with trace norm `2γ`, giving `traceDist = γ`. The matching upper bound
uses the optimal **diagonal** witness `γ·E_{(0,0)} + γ·E_{(1,0)}` — cleaner than the loose
`ampDampWitness` — whose `ptrace₂ = γ·1`, and `W − C ⪰ 0` because the residual `{(0,0),(1,1)}`
block `[[γ, t],[t, γ]]` (`t = 1 − √(1−γ)`) is PSD since `γ ≥ t` (equivalently `√(1−γ)·(1−√(1−γ)) ≥ 0`).
This upgrades the two-sided bracket to the **exact** value `γ`, the third named channel closed exactly
(after dephasing and depolarizing) with no twirl or SDP-duality machinery. -/

/-- The amplitude-damping worst-case input: the product state `|1⟩⟨1| ⊗ |1⟩⟨1|`. -/
noncomputable def ampDampInput : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = (1, 1) then 1 else 0)

theorem ampDampInput_isDensityOperator : IsDensityOperator ampDampInput := by
  refine ⟨Matrix.posSemidef_diagonal_iff.mpr fun i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [ampDampInput, Matrix.trace_diagonal]

/-- The output–input difference on `ampDampInput`: `γ·E_{(0,1)} − γ·E_{(1,1)}`. -/
noncomputable def ampDampOutDiff (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = (0, 1) then (γ : ℂ) else if i = (1, 1) then -(γ : ℂ) else 0)

/-- The PSD square root `|Δ|` of the output difference: `γ·E_{(0,1)} + γ·E_{(1,1)}`. -/
noncomputable def ampDampOutAbs (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = (0, 1) then (γ : ℂ) else if i = (1, 1) then (γ : ℂ) else 0)

/-- The stabilized output difference on the product input collapses to the diagonal `γ·E_{(0,1)} −
γ·E_{(1,1)}` (the single populated Choi column `(1, ·)` filtered through the `(1,1)` input). -/
theorem ampDamp_out_diff {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    krausMap (tensorKraus (ampDampKraus γ)) ampDampInput
      - krausMap (tensorKraus (idKrausPad 1 2)) ampDampInput = ampDampOutDiff γ := by
  ext p q; obtain ⟨y, α⟩ := p; obtain ⟨y', β⟩ := q
  rw [Matrix.sub_apply, krausMap_tensorKraus_apply, krausMap_tensorKraus_apply]
  have hC : ∀ a b : Fin 2,
      choiMatrix (krausMap (ampDampKraus γ)) (a, y) (b, y') * ampDampInput (a, α) (b, β)
        - choiMatrix (krausMap (idKrausPad 1 2)) (a, y) (b, y') * ampDampInput (a, α) (b, β)
        = ampDampChoiDiff γ (a, y) (b, y') * ampDampInput (a, α) (b, β) := by
    intro a b
    rw [← sub_mul, ← Matrix.sub_apply,
      congrFun (congrFun (ampDamp_choi_diff h0 h1) (a, y)) (b, y')]
  simp_rw [← Finset.sum_sub_distrib, hC]
  fin_cases y <;> fin_cases α <;> fin_cases y' <;> fin_cases β <;>
    simp [ampDampChoiDiff, ampDampInput, ampDampOutDiff, Matrix.diagonal_apply, Prod.ext_iff]

theorem traceNorm_ampDampOutDiff {γ : ℝ} (h0 : 0 ≤ γ) :
    traceNorm (ampDampOutDiff γ) = 2 * γ := by
  have habs : absOp (ampDampOutDiff γ) = ampDampOutAbs γ := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
      (Matrix.posSemidef_diagonal_iff.mpr fun i => ?_) ?_
    · fin_cases i <;> simp <;> exact h0
    · rw [absOp_mul_self]
      ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
      fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
        simp [ampDampOutAbs, ampDampOutDiff, Matrix.mul_apply, Matrix.diagonal_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]
  rw [traceNorm_eq_trace_absOp, habs, ampDampOutAbs, Matrix.trace_diagonal, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Prod.mk.injEq, Complex.add_re]
  norm_num
  ring

/-- The **optimal** amplitude-damping dual witness: the diagonal `γ·E_{(0,0)} + γ·E_{(1,0)}`. -/
noncomputable def ampDampWitnessOpt (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = (0, 0) then (γ : ℂ) else if i = (1, 0) then (γ : ℂ) else 0)

theorem ampDampWitnessOpt_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) : (ampDampWitnessOpt γ).PosSemidef := by
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> simp <;> exact h0

theorem ptrace2_ampDampWitnessOpt (γ : ℝ) :
    ptrace2 (ampDampWitnessOpt γ) = (γ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, ampDampWitnessOpt, Matrix.smul_apply]

theorem ampDampWitnessOpt_sub_choi_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (ampDampWitnessOpt γ - (choiMatrix (krausMap (ampDampKraus γ))
      - choiMatrix (krausMap (idKrausPad 1 2)))).PosSemidef := by
  rw [ampDamp_choi_diff h0 h1]
  have heq : ampDampWitnessOpt γ - ampDampChoiDiff γ
      = (Matrix.of fun a b => ((1 - Real.sqrt (1 - γ) : ℝ) : ℂ)
          * ((if a = (0, 0) then 1 else if a = (1, 1) then 1 else 0 : ℝ) : ℂ)
          * ((if b = (0, 0) then 1 else if b = (1, 1) then 1 else 0 : ℝ) : ℂ))
        + (Matrix.of fun a b => ((γ - (1 - Real.sqrt (1 - γ)) : ℝ) : ℂ)
            * (s00Dep a : ℂ) * (s00Dep b : ℂ))
        + (Matrix.of fun a b => ((γ - (1 - Real.sqrt (1 - γ)) : ℝ) : ℂ)
            * (s11Dep a : ℂ) * (s11Dep b : ℂ)) := by
    ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp [ampDampWitnessOpt, ampDampChoiDiff, s00Dep, s11Dep,
        Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, Prod.ext_iff]
  rw [heq]
  have ht : (0 : ℝ) ≤ 1 - Real.sqrt (1 - γ) := one_sub_sqrt_nonneg h0
  have htγ : (0 : ℝ) ≤ γ - (1 - Real.sqrt (1 - γ)) := by
    have hw0 : (0 : ℝ) ≤ Real.sqrt (1 - γ) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (1 - γ) * Real.sqrt (1 - γ) = 1 - γ :=
      Real.mul_self_sqrt (by linarith)
    nlinarith [mul_nonneg hw0 ht, hsq]
  exact ((posSemidef_smul_outer ht (fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0)).add
      (posSemidef_smul_outer htγ s00Dep)).add (posSemidef_smul_outer htγ s11Dep)

/-- **Exact amplitude-damping diamond distance:** `diamondDist (ampDampKraus γ) (id) = γ` for
`0 ≤ γ ≤ 1`. Upper bound via the optimal diagonal dual witness (`ptrace₂ W = γ·1`); matching lower
bound via the product input `|1⟩⟨1|⊗|1⟩⟨1|` (`traceDist = ½·2γ = γ`). This is sharp — the loose
`diamondDist_ampDamp_le` bracket `γ ≤ ◇ ≤ γ+1−√(1−γ)` collapses to the exact value `γ`. -/
theorem diamondDist_ampDamp_eq {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    diamondDist (ampDampKraus γ) (idKrausPad 1 2) = γ := by
  refine le_antisymm ?_ ?_
  · have hub := diamondDist_le_dual_witness (isKrausChannel_ampDampKraus h0 h1)
      (isKrausChannel_idKrausPad 1 2) (ampDampWitnessOpt_posSemidef h0)
      (ampDampWitnessOpt_sub_choi_posSemidef h0 h1)
    rwa [ptrace2_ampDampWitnessOpt, norm_smul, norm_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h0] at hub
  · have hlb := le_diamondDist (isKrausChannel_ampDampKraus h0 h1) (isKrausChannel_idKrausPad 1 2)
      ampDampInput_isDensityOperator
    rw [traceDist, ampDamp_out_diff h0 h1, traceNorm_ampDampOutDiff h0] at hlb
    linarith

end SKEFTHawking.QuantumNetwork
