import SKEFTHawking.QuantumNetwork.KroneckerEntropy
import SKEFTHawking.QuantumNetwork.QuantumKlein
import Mathlib.Analysis.Matrix.Order

/-!
# Subadditivity of the von Neumann entropy and mutual information (Phase 6AL, Wave 3, item C)

The headline quantum-information result of this phase:

* **Subadditivity** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` for a bipartite density operator with full-rank
  marginals, and
* **Mutual information nonnegativity** `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB) ≥ 0`.

The proof is Klein's inequality applied to the product reference `σ = ρ_A ⊗ ρ_B`. The reusable
upstream-infrastructure lemma is the **operator log of a tensor product**

`log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ 1 + 1 ⊗ log ρ_B`  (full-rank `ρ_A, ρ_B`).

`cfc_kronecker` is absent from Mathlib, and the analytic `CFC.log`/`exp` machinery is unavailable on
matrices (the operator-norm topology is not defeq to the entrywise one used by the eigenbasis CFC
instance). We therefore build the identity from the eigenbasis form: the missing brick `cfc_diagonal`
(`cfc f (diagonal (↑∘a)) = diagonal (↑∘f∘a)`, built here via `cfcHom` uniqueness — every function is
continuous on the finite matrix spectrum) plus the kronecker decomposition `ρ ⊗ σ = V (diag d) Vᴴ`
(`KroneckerEntropy.lean`) and `StarAlgHomClass.map_cfc` for the basis-change automorphism. The full-rank
hypothesis is essential — `log(λμ) = log λ + log μ` only for `λ, μ > 0`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A real diagonal matrix is Hermitian. -/
theorem isHermitian_diagonal_ofReal (a : ι → ℝ) :
    (Matrix.diagonal (fun i => (a i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [Complex.conj_ofReal]

/-- Each real diagonal entry lies in the real spectrum of the diagonal matrix. -/
theorem mem_spectrum_diagonal_ofReal (a : ι → ℝ) (i : ι) :
    a i ∈ spectrum ℝ (Matrix.diagonal (fun j => (a j : ℂ))) := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_sub, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_diagonal] at hu
  refine hu.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
  simp [Pi.algebraMap_apply]

/-- **Continuous functional calculus of a real diagonal matrix is diagonal:**
`cfc f (diagonal (i ↦ ↑(a i))) = diagonal (i ↦ ↑(f (a i)))`. Built via `cfcHom` uniqueness: the
diagonal-application star homomorphism `g ↦ diagonal (i ↦ ↑(g (a i)))` is continuous and sends the
identity to the matrix, so it equals `cfcHom`. -/
theorem cfc_diagonal (f : ℝ → ℝ) (a : ι → ℝ) :
    cfc f (Matrix.diagonal (fun i => (a i : ℂ)))
      = Matrix.diagonal (fun i => ((f (a i) : ℝ) : ℂ)) := by
  set D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (a i : ℂ)) with hDdef
  have hD : IsSelfAdjoint D := isHermitian_diagonal_ofReal a
  -- the candidate star-algebra hom `Φ : C(spectrum ℝ D, ℝ) →⋆ₐ[ℝ] Matrix ι ι ℂ`
  let Φ : C(spectrum ℝ D, ℝ) →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    { toFun := fun g => Matrix.diagonal
        (fun i => ((g ⟨a i, mem_spectrum_diagonal_ofReal a i⟩ : ℝ) : ℂ))
      map_one' := by simp
      map_mul' := fun g h => by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1; funext i; simp only [ContinuousMap.mul_apply]; push_cast; ring
      map_zero' := by simp
      map_add' := fun g h => by
        rw [Matrix.diagonal_add]
        congr 1; funext i; simp only [ContinuousMap.add_apply]; push_cast; ring
      commutes' := fun r => by
        rw [Matrix.algebraMap_eq_diagonal]; congr 1
      map_star' := fun g => by
        rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
        congr 1; funext i; simp [Complex.conj_ofReal] }
  have hΦcont : Continuous Φ := by
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    exact Complex.continuous_ofReal.comp (continuous_eval_const _)
  have hΦid : Φ ((ContinuousMap.id ℝ).restrict (spectrum ℝ D)) = D := rfl
  have hf : ContinuousOn f (spectrum ℝ D) := Matrix.finite_real_spectrum.continuousOn f
  rw [cfc_apply (ha := hD) (hf := hf), cfcHom_eq_of_continuous_of_map_id hD Φ hΦcont hΦid]
  rfl

/-- The matrix logarithm depends only on the matrix, not the Hermitian-ness proof. -/
theorem matrixLog_irrel {A : Matrix ι ι ℂ} (h1 h2 : A.IsHermitian) : matrixLog h1 = matrixLog h2 :=
  (Matrix.IsHermitian.cfc_eq h1 Real.log).symm.trans (Matrix.IsHermitian.cfc_eq h2 Real.log)

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The kronecker product of two unitary matrices is unitary. -/
noncomputable def kronUnitary (U : ↥(unitary (Matrix m m ℂ))) (V : ↥(unitary (Matrix n n ℂ))) :
    ↥(unitary (Matrix (m × n) (m × n) ℂ)) :=
  ⟨(↑U : Matrix m m ℂ) ⊗ₖ (↑V : Matrix n n ℂ), by
    rw [Unitary.mem_iff]
    have hsU := Unitary.mem_iff.mp U.2
    have hsV := Unitary.mem_iff.mp V.2
    have hstar : star ((↑U : Matrix m m ℂ) ⊗ₖ (↑V : Matrix n n ℂ))
        = (star (↑U : Matrix m m ℂ)) ⊗ₖ (star (↑V : Matrix n n ℂ)) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    refine ⟨?_, ?_⟩
    · rw [hstar, ← Matrix.mul_kronecker_mul, hsU.1, hsV.1, Matrix.one_kronecker_one]
    · rw [hstar, ← Matrix.mul_kronecker_mul, hsU.2, hsV.2, Matrix.one_kronecker_one]⟩

@[simp] theorem kronUnitary_coe (U : ↥(unitary (Matrix m m ℂ))) (V : ↥(unitary (Matrix n n ℂ))) :
    (↑(kronUnitary U V) : Matrix (m × n) (m × n) ℂ) = (↑U : Matrix m m ℂ) ⊗ₖ (↑V : Matrix n n ℂ) :=
  rfl

/-- **Unitary conjugation commutes with the kronecker product:**
`(U X Uᴴ) ⊗ (V Y Vᴴ) = (U ⊗ V) (X ⊗ Y) (U ⊗ V)ᴴ`. -/
theorem conjStarAlgAut_kronecker (U : ↥(unitary (Matrix m m ℂ)))
    (V : ↥(unitary (Matrix n n ℂ))) (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U X) ⊗ₖ (Unitary.conjStarAlgAut ℂ _ V Y)
      = Unitary.conjStarAlgAut ℂ _ (kronUnitary U V) (X ⊗ₖ Y) := by
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply,
    kronUnitary_coe]
  have hstar : star ((↑U : Matrix m m ℂ) ⊗ₖ (↑V : Matrix n n ℂ))
      = (star (↑U : Matrix m m ℂ)) ⊗ₖ (star (↑V : Matrix n n ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  rw [hstar, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- **Operator logarithm of a tensor product** `log(ρ ⊗ σ) = log ρ ⊗ 1 + 1 ⊗ log σ` for full-rank
(positive-definite) `ρ, σ`. The reusable upstream-infrastructure lemma. -/
theorem matrixLog_kronecker {ρ : Matrix m m ℂ} {σ : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    matrixLog (isHermitian_kronecker hρ.1 hσ.1)
      = matrixLog hρ.1 ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ matrixLog hσ.1 := by
  set Uρ := hρ.1.eigenvectorUnitary with hUρ
  set Uσ := hσ.1.eigenvectorUnitary with hUσ
  set Vu := kronUnitary Uρ Uσ with hVu
  set pρ := hρ.1.eigenvalues with hpρ
  set pσ := hσ.1.eigenvalues with hpσ
  have hφcont : Continuous (Unitary.conjStarAlgAut ℂ (Matrix (m × n) (m × n) ℂ) Vu) := by
    have hfun : (⇑(Unitary.conjStarAlgAut ℂ (Matrix (m × n) (m × n) ℂ) Vu))
        = fun X => (↑Vu : Matrix (m × n) (m × n) ℂ) * X * star (↑Vu : Matrix (m × n) (m × n) ℂ) := by
      funext X; rw [Unitary.conjStarAlgAut_apply]
    rw [hfun]
    exact (continuous_const.mul continuous_id).mul continuous_const
  -- LHS = conjStarAlgAut Vu (diagonal of log(pρ·pσ))
  have hL : matrixLog (isHermitian_kronecker hρ.1 hσ.1)
      = Unitary.conjStarAlgAut ℂ _ Vu
          (Matrix.diagonal (fun ij : m × n => ((Real.log (pρ ij.1 * pσ ij.2) : ℝ) : ℂ))) := by
    have hAB : ρ ⊗ₖ σ = Unitary.conjStarAlgAut ℂ _ Vu
        (Matrix.diagonal (RCLike.ofReal ∘ pρ) ⊗ₖ Matrix.diagonal (RCLike.ofReal ∘ pσ)) := by
      rw [hVu]
      conv_lhs => rw [hρ.1.spectral_theorem, hσ.1.spectral_theorem]
      exact conjStarAlgAut_kronecker Uρ Uσ _ _
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ pρ) ⊗ₖ Matrix.diagonal (RCLike.ofReal ∘ pσ)
        = Matrix.diagonal (fun ij : m × n => ((pρ ij.1 * pσ ij.2 : ℝ) : ℂ)) := by
      rw [Matrix.diagonal_kronecker_diagonal]
      congr 1; funext ij
      simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_mul]
    rw [matrixLog, ← Matrix.IsHermitian.cfc_eq, hAB, hdiag,
      ← StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ _ Vu) Real.log
        (Matrix.diagonal (fun ij : m × n => ((pρ ij.1 * pσ ij.2 : ℝ) : ℂ)))
        (hf := Matrix.finite_real_spectrum.continuousOn Real.log) (hφ := hφcont)
        (ha := isHermitian_diagonal_ofReal _)
        (hφa := by rw [← hdiag, ← hAB]; exact isHermitian_kronecker hρ.1 hσ.1)]
    congr 1
    exact cfc_diagonal Real.log (fun ij : m × n => pρ ij.1 * pσ ij.2)
  -- RHS term 1: matrixLog ρ ⊗ 1 = conjStarAlgAut Vu (diagonal of log pρ)
  have hR1 : matrixLog hρ.1 ⊗ₖ (1 : Matrix n n ℂ)
      = Unitary.conjStarAlgAut ℂ _ Vu
          (Matrix.diagonal (fun ij : m × n => ((Real.log (pρ ij.1) : ℝ) : ℂ))) := by
    have e1 : (1 : Matrix n n ℂ) = Unitary.conjStarAlgAut ℂ _ Uσ (1 : Matrix n n ℂ) := (map_one _).symm
    have hlog : matrixLog hρ.1
        = Unitary.conjStarAlgAut ℂ _ Uρ (Matrix.diagonal (RCLike.ofReal ∘ Real.log ∘ pρ)) := rfl
    have hk : Matrix.diagonal (RCLike.ofReal ∘ Real.log ∘ pρ) ⊗ₖ (1 : Matrix n n ℂ)
        = Matrix.diagonal (fun ij : m × n => ((Real.log (pρ ij.1) : ℝ) : ℂ)) := by
      rw [show (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.diagonal_kronecker_diagonal]
      congr 1; funext ij
      simp only [Function.comp_apply, mul_one, RCLike.ofReal_eq_complex_ofReal]
    rw [hlog, e1, hVu, conjStarAlgAut_kronecker, hk]
  -- RHS term 2: 1 ⊗ matrixLog σ = conjStarAlgAut Vu (diagonal of log pσ)
  have hR2 : (1 : Matrix m m ℂ) ⊗ₖ matrixLog hσ.1
      = Unitary.conjStarAlgAut ℂ _ Vu
          (Matrix.diagonal (fun ij : m × n => ((Real.log (pσ ij.2) : ℝ) : ℂ))) := by
    have e1 : (1 : Matrix m m ℂ) = Unitary.conjStarAlgAut ℂ _ Uρ (1 : Matrix m m ℂ) := (map_one _).symm
    have hlog : matrixLog hσ.1
        = Unitary.conjStarAlgAut ℂ _ Uσ (Matrix.diagonal (RCLike.ofReal ∘ Real.log ∘ pσ)) := rfl
    have hk : (1 : Matrix m m ℂ) ⊗ₖ Matrix.diagonal (RCLike.ofReal ∘ Real.log ∘ pσ)
        = Matrix.diagonal (fun ij : m × n => ((Real.log (pσ ij.2) : ℝ) : ℂ)) := by
      rw [show (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.diagonal_kronecker_diagonal]
      congr 1; funext ij
      simp only [Function.comp_apply, one_mul, RCLike.ofReal_eq_complex_ofReal]
    rw [hlog, e1, hVu, conjStarAlgAut_kronecker, hk]
  rw [hL, hR1, hR2, ← map_add]
  congr 1
  rw [Matrix.diagonal_add]
  congr 1; funext ij
  rw [← Complex.ofReal_add,
    ← Real.log_mul (ne_of_gt (hρ.eigenvalues_pos ij.1)) (ne_of_gt (hσ.eigenvalues_pos ij.2))]

/-- **Subadditivity of the von Neumann entropy** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` for a bipartite density
operator `ρ_AB` with full-rank marginals `ρ_A, ρ_B`. The marginals are characterised by the
partial-trace pairings `hmA`/`hmB` (`tr(ρ_AB · (G ⊗ 1)) = tr(ρ_A · G)` and the `1 ⊗ H` analogue).
Klein's inequality applied to the product reference `ρ_A ⊗ ρ_B`, expanded via `matrixLog_kronecker`. -/
theorem vonNeumannEntropy_subadditive {ρAB : Matrix (m × n) (m × n) ℂ}
    {ρA : Matrix m m ℂ} {ρB : Matrix n n ℂ} (hAB : IsDensityOperator ρAB)
    (hA : ρA.PosDef) (hB : ρB.PosDef) (hAtr : ρA.trace = 1) (hBtr : ρB.trace = 1)
    (hmA : ∀ G : Matrix m m ℂ, (ρAB * (G ⊗ₖ (1 : Matrix n n ℂ))).trace = (ρA * G).trace)
    (hmB : ∀ H : Matrix n n ℂ, (ρAB * ((1 : Matrix m m ℂ) ⊗ₖ H)).trace = (ρB * H).trace) :
    vonNeumannEntropy hAB.1.isHermitian ≤ vonNeumannEntropy hA.1 + vonNeumannEntropy hB.1 := by
  have hσ : (ρA ⊗ₖ ρB).PosDef := hA.kronecker hB
  have hσtr : (ρA ⊗ₖ ρB).trace = 1 := by rw [Matrix.trace_kronecker, hAtr, hBtr, one_mul]
  have hklein := relativeEntropy_nonneg hAB hσ hσtr
  have hlog : matrixLog hσ.1
      = matrixLog hA.1 ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ matrixLog hB.1 := by
    rw [matrixLog_irrel hσ.1 (isHermitian_kronecker hA.1 hB.1)]
    exact matrixLog_kronecker hA hB
  have key : relativeEntropy hAB.1.isHermitian hσ.1
      = -vonNeumannEntropy hAB.1.isHermitian
        + (vonNeumannEntropy hA.1 + vonNeumannEntropy hB.1) := by
    rw [relativeEntropy, re_trace_mul_matrixLog hAB.1.isHermitian, hlog, mul_add, Matrix.trace_add,
      hmA (matrixLog hA.1), hmB (matrixLog hB.1), Complex.add_re,
      re_trace_mul_matrixLog hA.1, re_trace_mul_matrixLog hB.1]
    ring
  rw [key] at hklein
  linarith

/-- **Quantum mutual information is nonnegative:** `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB) ≥ 0` for a
bipartite density operator with full-rank marginals. Immediate from subadditivity. -/
theorem mutualInformation_nonneg {ρAB : Matrix (m × n) (m × n) ℂ}
    {ρA : Matrix m m ℂ} {ρB : Matrix n n ℂ} (hAB : IsDensityOperator ρAB)
    (hA : ρA.PosDef) (hB : ρB.PosDef) (hAtr : ρA.trace = 1) (hBtr : ρB.trace = 1)
    (hmA : ∀ G : Matrix m m ℂ, (ρAB * (G ⊗ₖ (1 : Matrix n n ℂ))).trace = (ρA * G).trace)
    (hmB : ∀ H : Matrix n n ℂ, (ρAB * ((1 : Matrix m m ℂ) ⊗ₖ H)).trace = (ρB * H).trace) :
    0 ≤ vonNeumannEntropy hA.1 + vonNeumannEntropy hB.1 - vonNeumannEntropy hAB.1.isHermitian := by
  linarith [vonNeumannEntropy_subadditive hAB hA hB hAtr hBtr hmA hmB]

end SKEFTHawking.QuantumNetwork
