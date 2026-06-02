import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
import SKEFTHawking.QuantumNetwork.HaarPauli

/-!
# Named single-qubit noise channels (Phase 6AG, Ask 1)

Operators benchmark gates against *named* noise models — depolarizing, dephasing,
amplitude-damping. This file defines their Kraus representations and proves each is a CPTP
channel (`IsKrausChannel`), the substrate for certifying diamond-norm bounds against these models.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

theorem pauliZ_conjTranspose : pauliZᴴ = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ]

theorem pauliZ_mul_self : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Single-qubit **dephasing channel** Kraus operators `{√(1−γ)·I, √γ·Z}`. -/
noncomputable def dephasingKraus (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (Real.sqrt (1 - γ) : ℂ) • 1
  | 1 => (Real.sqrt γ : ℂ) • pauliZ

/-- The dephasing channel is CPTP for `0 ≤ γ ≤ 1`. -/
theorem isKrausChannel_dephasingKraus {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsKrausChannel (dephasingKraus γ) := by
  have e0 : (dephasingKraus γ 0)ᴴ * (dephasingKraus γ 0) = ((1 - γ : ℝ) : ℂ) • 1 := by
    show ((Real.sqrt (1 - γ) : ℂ) • 1)ᴴ * ((Real.sqrt (1 - γ) : ℂ) • 1) = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_smul, Matrix.one_mul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by linarith)]
  have e1 : (dephasingKraus γ 1)ᴴ * (dephasingKraus γ 1) = ((γ : ℝ) : ℂ) • 1 := by
    show ((Real.sqrt γ : ℂ) • pauliZ)ᴴ * ((Real.sqrt γ : ℂ) • pauliZ) = _
    rw [Matrix.conjTranspose_smul, smul_mul_smul, pauliZ_conjTranspose, pauliZ_mul_self,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  unfold IsKrausChannel
  rw [Fin.sum_univ_two, e0, e1, ← add_smul, ← Complex.ofReal_add,
    show (1 - γ + γ : ℝ) = 1 by ring, Complex.ofReal_one, one_smul]

/-- Single-qubit **amplitude-damping channel** Kraus operators
`{[[1,0],[0,√(1−γ)]], [[0,√γ],[0,0]]}`. -/
noncomputable def ampDampKraus (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)]
  | 1 => !![0, (Real.sqrt γ : ℂ); 0, 0]

/-- The amplitude-damping channel is CPTP for `0 ≤ γ ≤ 1`. -/
theorem isKrausChannel_ampDampKraus {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsKrausChannel (ampDampKraus γ) := by
  unfold IsKrausChannel
  rw [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ampDampKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0, Real.mul_self_sqrt (show (0:ℝ) ≤ 1 - γ by linarith)]

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]

theorem pauliY_conjTranspose : pauliYᴴ = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY]

theorem pauliX_mul_self : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_mul_self : pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Single-qubit **depolarizing channel** Kraus operators `{√(1−p)·I, √(p/3)·X, √(p/3)·Y, √(p/3)·Z}`
(error probability `p` split equally over the three Paulis). -/
noncomputable def depolarizingKraus (p : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (Real.sqrt (1 - p) : ℂ) • 1
  | 1 => (Real.sqrt (p / 3) : ℂ) • pauliX
  | 2 => (Real.sqrt (p / 3) : ℂ) • pauliY
  | 3 => (Real.sqrt (p / 3) : ℂ) • pauliZ

/-- The depolarizing channel is CPTP for `0 ≤ p ≤ 1`. -/
theorem isKrausChannel_depolarizingKraus {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsKrausChannel (depolarizingKraus p) := by
  have hp3 : (0 : ℝ) ≤ p / 3 := by linarith
  have key : ∀ (c : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ), Pᴴ = P → P * P = 1 →
      ((c : ℂ) • P)ᴴ * ((c : ℂ) • P) = ((c * c : ℝ) : ℂ) • 1 := by
    intro c P hPh hPP
    rw [Matrix.conjTranspose_smul, smul_mul_smul, hPh, hPP, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
  have e0 : (depolarizingKraus p 0)ᴴ * (depolarizingKraus p 0) = ((1 - p : ℝ) : ℂ) • 1 := by
    show ((Real.sqrt (1 - p) : ℂ) • 1)ᴴ * ((Real.sqrt (1 - p) : ℂ) • 1) = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_smul, Matrix.one_mul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by linarith)]
  have e1 : (depolarizingKraus p 1)ᴴ * (depolarizingKraus p 1) = ((p / 3 : ℝ) : ℂ) • 1 := by
    rw [show depolarizingKraus p 1 = (Real.sqrt (p / 3) : ℂ) • pauliX from rfl,
      key _ _ pauliX_conjTranspose pauliX_mul_self, Real.mul_self_sqrt hp3]
  have e2 : (depolarizingKraus p 2)ᴴ * (depolarizingKraus p 2) = ((p / 3 : ℝ) : ℂ) • 1 := by
    rw [show depolarizingKraus p 2 = (Real.sqrt (p / 3) : ℂ) • pauliY from rfl,
      key _ _ pauliY_conjTranspose pauliY_mul_self, Real.mul_self_sqrt hp3]
  have e3 : (depolarizingKraus p 3)ᴴ * (depolarizingKraus p 3) = ((p / 3 : ℝ) : ℂ) • 1 := by
    rw [show depolarizingKraus p 3 = (Real.sqrt (p / 3) : ℂ) • pauliZ from rfl,
      key _ _ pauliZ_conjTranspose pauliZ_mul_self, Real.mul_self_sqrt hp3]
  unfold IsKrausChannel
  rw [Fin.sum_univ_four, e0, e1, e2, e3, ← add_smul, ← add_smul, ← add_smul,
    ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add,
    show (1 - p + p / 3 + p / 3 + p / 3 : ℝ) = 1 by ring, Complex.ofReal_one, one_smul]

/-- The **identity channel** with `m+1` Kraus operators (`I` plus `m` zeros), padded so its Kraus
count can be matched to a named channel's for `diamondDist`. -/
noncomputable def idKrausPad (m n : ℕ) : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ :=
  fun i => if i = 0 then 1 else 0

theorem isKrausChannel_idKrausPad (m n : ℕ) : IsKrausChannel (idKrausPad m n) := by
  unfold IsKrausChannel idKrausPad
  rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem krausMap_idKrausPad (m n : ℕ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    krausMap (idKrausPad m n) ρ = ρ := by
  unfold krausMap idKrausPad
  rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The (γ-independent) structure matrix of the dephasing Choi difference: `−2` at the two
off-diagonal coherence positions `((0,0),(1,1))` and `((1,1),(0,0))`, zero elsewhere. -/
noncomputable def dephasingChoiBase : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if (p = (0, 0) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 0)) then -2 else 0

/-- The Choi difference of the dephasing channel and the identity is `γ · dephasingChoiBase`. -/
theorem dephasing_choi_diff {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    choiMatrix (krausMap (dephasingKraus γ)) - choiMatrix (krausMap (idKrausPad 1 2))
      = (γ : ℂ) • dephasingChoiBase := by
  ext p q
  obtain ⟨a, y⟩ := p
  obtain ⟨b, y'⟩ := q
  simp only [Matrix.sub_apply, choiMatrix_krausMap_apply, Fin.sum_univ_two, dephasingKraus,
    idKrausPad, dephasingChoiBase, Matrix.smul_apply, Matrix.one_apply, pauliZ, smul_eq_mul]
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h0,
      Real.mul_self_sqrt (show (0:ℝ) ≤ 1 - γ by linarith)] <;>
    ring_nf

/-- `B²` for `B = dephasingChoiBase`: the diagonal matrix with `4` at `(0,0)` and `(1,1)`. -/
noncomputable def dephasingChoiDiag : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if (p = (0, 0) ∧ q = (0, 0)) ∨ (p = (1, 1) ∧ q = (1, 1)) then 4 else 0

theorem dephasingChoiBase_conjTranspose : dephasingChoiBaseᴴ = dephasingChoiBase := by
  ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [dephasingChoiBase, Matrix.conjTranspose_apply]

theorem dephasingChoiBase_mul_self :
    dephasingChoiBase * dephasingChoiBase = dephasingChoiDiag := by
  ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [dephasingChoiBase, dephasingChoiDiag, Matrix.mul_apply] <;> ring_nf

theorem dephasingChoiDiag_mul_self : dephasingChoiDiag * dephasingChoiDiag = (4 : ℂ) • dephasingChoiDiag := by
  ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [dephasingChoiDiag, Matrix.mul_apply, Matrix.smul_apply]

theorem dephasingChoiDiag_trace : dephasingChoiDiag.trace = 8 := by
  simp [Matrix.trace, Matrix.diag_apply, dephasingChoiDiag, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

/-- **`traceNorm dephasingChoiBase = 4`** — its singular values are `2, 2, 0, 0`. -/
theorem traceNorm_dephasingChoiBase : traceNorm dephasingChoiBase = 4 := by
  have hBh := dephasingChoiBase_conjTranspose
  have hDpsd : dephasingChoiDiag.PosSemidef := by
    rw [← dephasingChoiBase_mul_self]; nth_rewrite 1 [← hBh]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hc : (0 : ℂ) ≤ (1 / 2 : ℂ) := by rw [Complex.le_def]; norm_num
  have habs : absOp dephasingChoiBase = (1 / 2 : ℂ) • dephasingChoiDiag := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) (hDpsd.smul hc) ?_
    rw [absOp_mul_self, hBh, dephasingChoiBase_mul_self, smul_mul_smul,
      dephasingChoiDiag_mul_self, smul_smul, show ((1 / 2 : ℂ) * (1 / 2) * 4) = 1 by norm_num,
      one_smul]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_smul, dephasingChoiDiag_trace, smul_eq_mul]
  norm_num

/-- **Dephasing channel diamond-distance lower bound:** `diamondDist (dephasingKraus γ) (id) ≥ γ`
for `0 ≤ γ ≤ 1`, obtained from the quantitative Choi trace-norm lower bound
(`diamondDist_ge_choi_traceNorm`) since `‖J(Φ_γ) − J(id)‖₁ = 4γ`. The bound is tight — `γ` is the exact
diamond distance because the maximally-entangled (Choi) input is optimal for this Pauli-covariant
channel — but only the lower bound `≥ γ` is formalized here (Choi-input optimality is not). -/
theorem diamondDist_dephasing_ge {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    γ ≤ diamondDist (dephasingKraus γ) (idKrausPad 1 2) := by
  have hbound := diamondDist_ge_choi_traceNorm
    (isKrausChannel_dephasingKraus h0 h1) (isKrausChannel_idKrausPad 1 2)
  rw [dephasing_choi_diff h0 h1, traceNorm_smul_nonneg h0, traceNorm_dephasingChoiBase] at hbound
  calc γ = (1 : ℝ) / (2 * (2 : ℕ)) * (γ * 4) := by push_cast; ring
    _ ≤ _ := hbound

/-- The (`p`-independent) structure matrix of the depolarizing Choi difference. Entry at
`((a,y),(b,y'))` equals `−4/3·[y=a ∧ y'=b] + 2/3·[a=b ∧ y=y']`; its eigenvalues are
`{2/3, 2/3, 2/3, −2}`. -/
noncomputable def depolarizingChoiBase : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun r c => (if r.2 = r.1 ∧ c.2 = c.1 then (-(4 : ℂ) / 3) else 0)
              + (if r.1 = c.1 ∧ r.2 = c.2 then ((2 : ℂ) / 3) else 0)

/-- The Choi difference of the depolarizing channel and the identity is `p · depolarizingChoiBase`. -/
theorem depolarizing_choi_diff {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    choiMatrix (krausMap (depolarizingKraus p)) - choiMatrix (krausMap (idKrausPad 3 2))
      = (p : ℂ) • depolarizingChoiBase := by
  have hss : Real.sqrt (p / 3) * Real.sqrt (p / 3) = p / 3 :=
    Real.mul_self_sqrt (by linarith)
  have htt : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p :=
    Real.mul_self_sqrt (by linarith)
  have hs2 : (↑(Real.sqrt (p / 3)) : ℂ) ^ 2 = (↑p : ℂ) / 3 := by
    rw [sq, ← Complex.ofReal_mul, hss]; push_cast; ring
  ext r c
  obtain ⟨a, y⟩ := r
  obtain ⟨b, y'⟩ := c
  simp only [Matrix.sub_apply, choiMatrix_krausMap_apply, Fin.sum_univ_four, depolarizingKraus,
    idKrausPad, depolarizingChoiBase, Matrix.smul_apply, Matrix.one_apply, pauliX, pauliY, pauliZ,
    smul_eq_mul]
  set s := Real.sqrt (p / 3)
  set t := Real.sqrt (1 - p)
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul, hss, htt, Complex.conj_I,
      Fin.sum_univ_four, Matrix.zero_apply] <;>
    ring_nf <;>
    simp only [hs2, Complex.I_sq] <;>
    ring_nf

theorem depolarizingChoiBase_conjTranspose : depolarizingChoiBaseᴴ = depolarizingChoiBase := by
  ext r c; obtain ⟨a, y⟩ := r; obtain ⟨b, y'⟩ := c
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [depolarizingChoiBase, Matrix.conjTranspose_apply]

/-- The candidate for `|B|`: `1 − ½B`. Its square equals `B²` (minimal polynomial
`B² = (4/3)(1 − B)`), so by PSD-square uniqueness it is `absOp B`. -/
theorem depolarizing_candidate_mul_self :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (1 / 2 : ℂ) • depolarizingChoiBase) *
        ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (1 / 2 : ℂ) • depolarizingChoiBase)
      = depolarizingChoiBase * depolarizingChoiBase := by
  ext r c; obtain ⟨a, y⟩ := r; obtain ⟨b, y'⟩ := c
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [depolarizingChoiBase, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, smul_eq_mul] <;> norm_num

/-- PSD-exhibiting form of the candidate: `1 − ½B = ½·1 + (3/8)·BᴴB`, a sum of two PSD matrices. -/
theorem depolarizing_candidate_psd_form :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (1 / 2 : ℂ) • depolarizingChoiBase
      = (1 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (3 / 8 : ℂ) • (depolarizingChoiBaseᴴ * depolarizingChoiBase) := by
  rw [depolarizingChoiBase_conjTranspose]
  ext r c; obtain ⟨a, y⟩ := r; obtain ⟨b, y'⟩ := c
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [depolarizingChoiBase, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, smul_eq_mul] <;> norm_num

theorem depolarizingChoiBase_trace : depolarizingChoiBase.trace = 0 := by
  simp [Matrix.trace, Matrix.diag_apply, depolarizingChoiBase, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

/-- **`traceNorm depolarizingChoiBase = 4`** — its singular values are `2/3, 2/3, 2/3, 2`. -/
theorem traceNorm_depolarizingChoiBase : traceNorm depolarizingChoiBase = 4 := by
  have hc12 : (0 : ℂ) ≤ (1 / 2 : ℂ) := by rw [Complex.le_def]; norm_num
  have hc38 : (0 : ℂ) ≤ (3 / 8 : ℂ) := by rw [Complex.le_def]; norm_num
  have hQpsd : ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
      (1 / 2 : ℂ) • depolarizingChoiBase).PosSemidef := by
    rw [depolarizing_candidate_psd_form]
    exact (Matrix.PosSemidef.one.smul hc12).add
      ((Matrix.posSemidef_conjTranspose_mul_self _).smul hc38)
  have habs : absOp depolarizingChoiBase =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (1 / 2 : ℂ) • depolarizingChoiBase := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) hQpsd ?_
    rw [absOp_mul_self, depolarizingChoiBase_conjTranspose, depolarizing_candidate_mul_self]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_sub, Matrix.trace_smul,
    depolarizingChoiBase_trace, Matrix.trace_one, smul_zero, sub_zero]
  simp

/-- **Depolarizing channel diamond-distance lower bound:** `diamondDist (depolarizingKraus p) (id) ≥ p`
for `0 ≤ p ≤ 1`, via the Choi trace-norm lower bound (`diamondDist_ge_choi_traceNorm`) since
`‖J(Φ_p) − J(id)‖₁ = 4p`. The bound is tight — `p` is in fact the exact diamond distance because the
maximally-entangled input is optimal for this Pauli-covariant channel — but only the lower bound `≥ p`
is formalized here (the matching upper bound / Choi-input optimality is not). -/
theorem diamondDist_depolarizing_ge {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    p ≤ diamondDist (depolarizingKraus p) (idKrausPad 3 2) := by
  have hbound := diamondDist_ge_choi_traceNorm
    (isKrausChannel_depolarizingKraus h0 h1) (isKrausChannel_idKrausPad 3 2)
  rw [depolarizing_choi_diff h0 h1, traceNorm_smul_nonneg h0, traceNorm_depolarizingChoiBase] at hbound
  calc p = (1 : ℝ) / (2 * (2 : ℕ)) * (p * 4) := by push_cast; ring
    _ ≤ _ := hbound

/-- Choi difference matrix of the amplitude-damping channel and the identity. Unlike the Pauli
channels this is **not** a scalar multiple of a `γ`-independent matrix (the entries `√(1−γ)−1` are
nonlinear in `γ`), reflecting that amplitude damping is not Pauli-covariant — so the
maximally-entangled (Choi) input is not optimal and Candidate B gives a lower bound, not the exact
diamond distance. -/
noncomputable def ampDampChoiDiff (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun r c =>
    if (r = (0, 0) ∧ c = (1, 1)) ∨ (r = (1, 1) ∧ c = (0, 0)) then ((Real.sqrt (1 - γ) : ℂ) - 1)
    else if r = (1, 1) ∧ c = (1, 1) then (-(γ : ℂ))
    else if r = (1, 0) ∧ c = (1, 0) then (γ : ℂ)
    else 0

theorem ampDamp_choi_diff {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    choiMatrix (krausMap (ampDampKraus γ)) - choiMatrix (krausMap (idKrausPad 1 2))
      = ampDampChoiDiff γ := by
  ext r c
  obtain ⟨a, y⟩ := r
  obtain ⟨b, y'⟩ := c
  simp only [Matrix.sub_apply, choiMatrix_krausMap_apply, Fin.sum_univ_two, ampDampKraus,
    idKrausPad, ampDampChoiDiff]
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 - γ by linarith), Real.mul_self_sqrt h0]

theorem ampDampChoiDiff_isHermitian {γ : ℝ} : (ampDampChoiDiff γ).IsHermitian := by
  ext r c; obtain ⟨a, y⟩ := r; obtain ⟨b, y'⟩ := c
  fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
    simp [ampDampChoiDiff, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- Diagonal Loewner contraction `−1 ≤ R ≤ 1` aligned with the two `±γ` diagonal entries of the
amplitude-damping Choi difference: `+1` at `(1,0)` (where the entry is `+γ`) and `−1` at `(1,1)`
(where it is `−γ`), so `Re tr(Δ·R) = 2γ`. -/
noncomputable def ampDampTestR : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = (1, 0) then 1 else if i = (1, 1) then -1 else 0)

theorem ampDampTestR_one_sub_posSemidef :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - ampDampTestR).PosSemidef := by
  rw [ampDampTestR, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> simp <;> rw [Complex.le_def] <;> norm_num

theorem ampDampTestR_one_add_posSemidef :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + ampDampTestR).PosSemidef := by
  rw [ampDampTestR, ← Matrix.diagonal_one, Matrix.diagonal_add]
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> simp <;> rw [Complex.le_def] <;> norm_num

theorem ampDamp_trace_diff_mul_R {γ : ℝ} :
    ((ampDampChoiDiff γ * ampDampTestR).trace).re = 2 * γ := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ampDampChoiDiff, ampDampTestR,
    Matrix.diagonal, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- **`2γ ≤ traceNorm(amp-damp Choi difference)`** via the Hermitian dual-norm keystone with the
diagonal contraction `ampDampTestR`. -/
theorem two_mul_le_traceNorm_ampDampChoiDiff {γ : ℝ} :
    2 * γ ≤ traceNorm (ampDampChoiDiff γ) := by
  have h := re_trace_mul_le_traceNorm_hermitian (ampDampChoiDiff_isHermitian (γ := γ))
    ampDampTestR_one_sub_posSemidef ampDampTestR_one_add_posSemidef
  rwa [ampDamp_trace_diff_mul_R] at h

/-- **Amplitude-damping channel diamond-distance lower bound:**
`diamondDist (ampDampKraus γ) (id) ≥ γ/2` for `0 ≤ γ ≤ 1`. Amplitude damping is not Pauli-covariant,
so the Choi (maximally-entangled) input is not optimal; this is the certified lower bound from the
quantitative Choi trace-norm bound (`diamondDist_ge_choi_traceNorm`) since `‖J(Φ_γ) − J(id)‖₁ ≥ 2γ`
(exhibited by a diagonal Loewner contraction aligned with the `±γ` diagonal Choi entries). -/
theorem diamondDist_ampDamp_ge {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    γ / 2 ≤ diamondDist (ampDampKraus γ) (idKrausPad 1 2) := by
  have hbound := diamondDist_ge_choi_traceNorm
    (isKrausChannel_ampDampKraus h0 h1) (isKrausChannel_idKrausPad 1 2)
  rw [ampDamp_choi_diff h0 h1] at hbound
  have htn := two_mul_le_traceNorm_ampDampChoiDiff (γ := γ)
  calc γ / 2 = (1 : ℝ) / (2 * (2 : ℕ)) * (2 * γ) := by push_cast; ring
    _ ≤ (1 : ℝ) / (2 * (2 : ℕ)) * traceNorm (ampDampChoiDiff γ) := by
        apply mul_le_mul_of_nonneg_left htn; positivity
    _ ≤ _ := hbound

end SKEFTHawking.QuantumNetwork
