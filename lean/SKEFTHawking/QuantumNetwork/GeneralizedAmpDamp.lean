import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact

/-!
# Generalized (thermal) amplitude-damping diamond distance (Phase 6AK, Wave 6AK.4)

The **generalized amplitude-damping (GAD)** channel models qubit relaxation toward a finite-temperature
bath with excited-state population `N ∈ [0,1]` and damping `γ ∈ [0,1]`. Its four Kraus operators are
the `√(1−N)`-weighted amplitude-damping pair (de-excitation `|1⟩→|0⟩`) together with the
`√N`-weighted transpose pair (excitation `|0⟩→|1⟩`):

`E₀=√(1−N)[[1,0],[0,√(1−γ)]]`, `E₁=√(1−N)[[0,√γ],[0,0]]`,
`E₂=√N[[√(1−γ),0],[0,1]]`,   `E₃=√N[[0,0],[√γ,0]]`.

`N = 0` recovers ordinary amplitude damping. Unlike the Pauli channels, GAD is *not* Pauli-covariant,
so its diamond distance to the identity has no one-line closed form; we give a kernel-pure **two-sided
bracket**. The lower bound `(1−N)γ` is *exact and achievable*: on the unentangled excited product input
`|1⟩⟨1|⊗|1⟩⟨1|` the output–input difference is the real diagonal `(1−N)γ·(E_{(0,1)}−E_{(1,1)})` with
trace norm `2(1−N)γ`, so `traceDist = (1−N)γ` — the thermal de-excitation flux. The upper bound is the
trivial CPTP channel-distance cap `1` (the exact value needs the `√(1−γ)`-dependent eigenvector witness,
as for amplitude damping).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

/-- **Generalized (thermal) amplitude-damping** Kraus operators with damping `γ` and bath
excited-state population `N`. -/
noncomputable def genAmpDampKraus (γ N : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (Real.sqrt (1 - N) : ℂ) • !![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)]
  | 1 => (Real.sqrt (1 - N) : ℂ) • !![0, (Real.sqrt γ : ℂ); 0, 0]
  | 2 => (Real.sqrt N : ℂ) • !![(Real.sqrt (1 - γ) : ℂ), 0; 0, 1]
  | 3 => (Real.sqrt N : ℂ) • !![0, 0; (Real.sqrt γ : ℂ), 0]

/-- The generalized amplitude-damping channel is CPTP for `0 ≤ γ ≤ 1`, `0 ≤ N ≤ 1`. -/
theorem isKrausChannel_genAmpDampKraus {γ N : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hN0 : 0 ≤ N)
    (hN1 : N ≤ 1) : IsKrausChannel (genAmpDampKraus γ N) := by
  have h1N : (0 : ℝ) ≤ 1 - N := by linarith
  have h1γ : (0 : ℝ) ≤ 1 - γ := by linarith
  have key : ∀ (c : ℝ), 0 ≤ c → ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      ((Real.sqrt c : ℂ) • M)ᴴ * ((Real.sqrt c : ℂ) • M) = (c : ℂ) • (Mᴴ * M) := by
    intro c hc M
    rw [Matrix.conjTranspose_smul, smul_mul_smul, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have e0 : (genAmpDampKraus γ N 0)ᴴ * genAmpDampKraus γ N 0
      = ((1 - N : ℝ) : ℂ) • !![1, 0; 0, ((1 - γ : ℝ) : ℂ)] := by
    rw [show genAmpDampKraus γ N 0 = (Real.sqrt (1 - N) : ℂ) • !![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)]
        from rfl, key (1 - N) h1N]
    congr 1; ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
        Real.mul_self_sqrt h1γ]
  have e1 : (genAmpDampKraus γ N 1)ᴴ * genAmpDampKraus γ N 1
      = ((1 - N : ℝ) : ℂ) • !![0, 0; 0, (γ : ℂ)] := by
    rw [show genAmpDampKraus γ N 1 = (Real.sqrt (1 - N) : ℂ) • !![0, (Real.sqrt γ : ℂ); 0, 0]
        from rfl, key (1 - N) h1N]
    congr 1; ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hγ0]
  have e2 : (genAmpDampKraus γ N 2)ᴴ * genAmpDampKraus γ N 2
      = (N : ℂ) • !![((1 - γ : ℝ) : ℂ), 0; 0, 1] := by
    rw [show genAmpDampKraus γ N 2 = (Real.sqrt N : ℂ) • !![(Real.sqrt (1 - γ) : ℂ), 0; 0, 1]
        from rfl, key N hN0]
    congr 1; ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
        Real.mul_self_sqrt h1γ]
  have e3 : (genAmpDampKraus γ N 3)ᴴ * genAmpDampKraus γ N 3 = (N : ℂ) • !![(γ : ℂ), 0; 0, 0] := by
    rw [show genAmpDampKraus γ N 3 = (Real.sqrt N : ℂ) • !![0, 0; (Real.sqrt γ : ℂ), 0]
        from rfl, key N hN0]
    congr 1; ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hγ0]
  unfold IsKrausChannel
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.add_apply, smul_eq_mul] <;> ring

/-! ## Two-sided diamond-distance bracket -/

/-- The Choi matrix of GAD on the populated `(1,·)(1,·)` block — i.e. `GAD(|1⟩⟨1|)`: diagonal with
`(1-N)γ` at `(0,0)` (the de-excitation flux to `|0⟩`) and `1-(1-N)γ` at `(1,1)`. -/
theorem genAmpDamp_choi_excited {γ N : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hN0 : 0 ≤ N) (hN1 : N ≤ 1)
    (y y' : Fin 2) :
    choiMatrix (krausMap (genAmpDampKraus γ N)) (1, y) (1, y')
      = if y = 0 ∧ y' = 0 then (((1 - N) * γ : ℝ) : ℂ)
        else if y = 1 ∧ y' = 1 then ((1 - (1 - N) * γ : ℝ) : ℂ) else 0 := by
  have h1N : (0 : ℝ) ≤ 1 - N := by linarith
  have h1γ : (0 : ℝ) ≤ 1 - γ := by linarith
  have ent : ∀ a b : Fin 2,
      choiMatrix (krausMap (genAmpDampKraus γ N)) (1, a) (1, b)
        = ∑ k, genAmpDampKraus γ N k a 1 * (starRingEnd ℂ) (genAmpDampKraus γ N k b 1) :=
    fun a b => by rw [choiMatrix_krausMap_apply]
  have c00 : choiMatrix (krausMap (genAmpDampKraus γ N)) (1, 0) (1, 0) = (((1 - N) * γ : ℝ) : ℂ) := by
    rw [ent]
    simp only [genAmpDampKraus, Fin.sum_univ_four, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, map_mul,
      Complex.conj_ofReal, map_zero, mul_zero, zero_mul, add_zero, zero_add]
    rw [mul_mul_mul_comm]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt h1N, Real.mul_self_sqrt hγ0]
  have c11 : choiMatrix (krausMap (genAmpDampKraus γ N)) (1, 1) (1, 1)
      = ((1 - (1 - N) * γ : ℝ) : ℂ) := by
    rw [ent]
    simp only [genAmpDampKraus, Fin.sum_univ_four, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, map_mul,
      Complex.conj_ofReal, map_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
    rw [mul_mul_mul_comm]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt h1N, Real.mul_self_sqrt h1γ,
      Real.mul_self_sqrt hN0]
    push_cast; ring
  have c01 : choiMatrix (krausMap (genAmpDampKraus γ N)) (1, 0) (1, 1) = 0 := by
    rw [ent]
    simp [genAmpDampKraus, Fin.sum_univ_four, Matrix.smul_apply, Matrix.of_apply]
  have c10 : choiMatrix (krausMap (genAmpDampKraus γ N)) (1, 1) (1, 0) = 0 := by
    rw [ent]
    simp [genAmpDampKraus, Fin.sum_univ_four, Matrix.smul_apply, Matrix.of_apply]
  fin_cases y <;> fin_cases y' <;>
    simp only [Fin.zero_eta, Fin.mk_one, c00, c01, c10, c11, and_self, and_true, true_and,
      and_false, false_and, if_true, if_false, Fin.reduceEq, reduceIte]

/-- The output–input difference on the excited product input collapses to the amplitude-damping
diagonal at the **thermal de-excitation flux** `(1-N)γ`: `krausMap(GAD⊗id)|1⟩⟨1|⊗|1⟩⟨1| − |1⟩⟨1|⊗|1⟩⟨1|
= ampDampOutDiff((1-N)γ)`. -/
theorem genAmpDamp_out_diff {γ N : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    krausMap (tensorKraus (genAmpDampKraus γ N)) ampDampInput
        - krausMap (tensorKraus (idKrausPad 3 2)) ampDampInput
      = ampDampOutDiff ((1 - N) * γ) := by
  ext p q; obtain ⟨y, α⟩ := p; obtain ⟨y', β⟩ := q
  rw [Matrix.sub_apply, krausMap_tensorKraus_apply, krausMap_tensorKraus_apply]
  have hcollapse : ∀ (J : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      (∑ a, ∑ b, J (a, y) (b, y') * ampDampInput (a, α) (b, β))
        = J (1, y) (1, y') * ampDampInput (1, α) (1, β) := by
    intro J
    simp only [Fin.sum_univ_two, ampDampInput, Matrix.diagonal_apply, Prod.ext_iff]
    fin_cases α <;> fin_cases β <;> simp
  rw [hcollapse, hcollapse, genAmpDamp_choi_excited hγ0 hγ1 hN0 hN1]
  have hid : choiMatrix (krausMap (idKrausPad 3 2)) (1, y) (1, y')
      = if y = 1 ∧ y' = 1 then (1 : ℂ) else 0 := by
    rw [choiMatrix_krausMap_apply]
    fin_cases y <;> fin_cases y' <;>
      simp [krausMap, idKrausPad, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [hid]
  simp only [ampDampInput, Matrix.diagonal_apply, Prod.ext_iff, ampDampOutDiff, Matrix.diagonal_apply]
  fin_cases y <;> fin_cases α <;> fin_cases y' <;> fin_cases β <;> push_cast <;> simp

/-- **Generalized (thermal) amplitude-damping two-sided diamond bracket:**
`(1−N)γ ≤ diamondDist (genAmpDampKraus γ N) (id) ≤ 1`. The lower bound is the exact achievable thermal
de-excitation flux (worst-case unentangled excited input); the upper bound is the trivial CPTP
channel-distance cap (GAD is not covariant, so the exact value needs the `√(1−γ)`-dependent eigenvector
witness, as for amplitude damping). For `N = 0` the lower bound recovers the amplitude-damping value
`γ`. -/
theorem diamondDist_genAmpDamp_bracket {γ N : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hN0 : 0 ≤ N)
    (hN1 : N ≤ 1) :
    (1 - N) * γ ≤ diamondDist (genAmpDampKraus γ N) (idKrausPad 3 2) ∧
      diamondDist (genAmpDampKraus γ N) (idKrausPad 3 2) ≤ 1 := by
  refine ⟨?_, diamondDist_le_one (isKrausChannel_genAmpDampKraus hγ0 hγ1 hN0 hN1)
    (isKrausChannel_idKrausPad 3 2)⟩
  have hflux : (0 : ℝ) ≤ (1 - N) * γ := mul_nonneg (by linarith) hγ0
  have hlb := le_diamondDist (isKrausChannel_genAmpDampKraus hγ0 hγ1 hN0 hN1)
    (isKrausChannel_idKrausPad 3 2) ampDampInput_isDensityOperator
  rw [traceDist, genAmpDamp_out_diff hγ0 hγ1 hN0 hN1, traceNorm_ampDampOutDiff hflux] at hlb
  linarith

end SKEFTHawking.QuantumNetwork
