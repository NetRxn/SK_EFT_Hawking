import SKEFTHawking.QuantumNetwork.VonNeumannEntropy
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Eigenvalues of a Kronecker product and von Neumann entropy additivity (Phase 6AK, Wave FU-8)

Mathlib v4.29.1 has **no** lemma giving the eigenvalues of a Kronecker product `A ⊗ B` as the products
`λᵢ μⱼ` of the factor eigenvalues — this is the missing infrastructure that blocks von Neumann entropy
additivity `S(ρ ⊗ σ) = S(ρ) + S(σ)`. We build it here, mirroring the repo's charpoly-matching technique
already used for `map_eigenvalues_conjTranspose_mul_self` (`MixedState.lean`):

1. `charpoly_kronecker_eq` — `(A ⊗ B).charpoly = ∏ᵢⱼ (X − λᵢμⱼ)`. Proof: diagonalise each factor by its
   eigenvector unitary (`spectral_theorem`), combine with `mul_kronecker_mul` to write
   `A ⊗ B = V · diag(λᵢμⱼ) · V⁻¹` for the unitary `V = U_A ⊗ U_B`, and use the conjugation-invariance of
   the characteristic polynomial (`charpoly_units_conj`) together with `charpoly_diagonal`.
2. `map_eigenvalues_kronecker` — the **eigenvalue multiset** of `A ⊗ B` equals `{λᵢ μⱼ}` (match charpoly
   roots through `roots_charpoly_eq_eigenvalues`, exactly as the squared-eigenvalue lemma does).
3. `sum_negMulLog_eigenvalues_kronecker` — `∑ₖ g(eigₖ(A⊗B)) = ∑ᵢⱼ g(λᵢμⱼ)` for `g = negMulLog`.
4. `vonNeumannEntropy_kronecker_add` — `S(ρ ⊗ σ) = S(ρ) + S(σ)`, via `Real.negMulLog_mul` and the
   density-operator normalisations `∑ᵢ pᵢ = ∑ⱼ qⱼ = 1`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem isHermitian_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  show (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- **Characteristic polynomial of a Kronecker product of Hermitians:**
`(A ⊗ B).charpoly = ∏ᵢⱼ (X − λᵢ μⱼ)`. -/
theorem charpoly_kronecker_eq {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).charpoly = ∏ ij : m × n, (Polynomial.X - Polynomial.C
      ((RCLike.ofReal (hA.eigenvalues ij.1) : ℂ) * (RCLike.ofReal (hB.eigenvalues ij.2) : ℂ))) := by
  set UA := hA.eigenvectorUnitary with hUA
  set UB := hB.eigenvectorUnitary with hUB
  set V : Matrix (m × n) (m × n) ℂ := (↑UA : Matrix m m ℂ) ⊗ₖ (↑UB : Matrix n n ℂ) with hV
  set W : Matrix (m × n) (m × n) ℂ :=
    (↑(star UA) : Matrix m m ℂ) ⊗ₖ (↑(star UB) : Matrix n n ℂ) with hW
  set d : (m × n) → ℂ := fun ij =>
    (RCLike.ofReal ∘ hA.eigenvalues) ij.1 * (RCLike.ofReal ∘ hB.eigenvalues) ij.2 with hd
  have hVW : V * W = 1 := by
    rw [hV, hW, ← Matrix.mul_kronecker_mul, Unitary.coe_mul_star_self, Unitary.coe_mul_star_self,
      Matrix.one_kronecker_one]
  have hWV : W * V = 1 := by
    rw [hV, hW, ← Matrix.mul_kronecker_mul]
    simp only [Unitary.coe_star]
    rw [Unitary.coe_star_mul_self, Unitary.coe_star_mul_self, Matrix.one_kronecker_one]
  let u : (Matrix (m × n) (m × n) ℂ)ˣ := ⟨V, W, hVW, hWV⟩
  have hdecomp : A ⊗ₖ B = u.val * Matrix.diagonal d * u⁻¹.val := by
    show A ⊗ₖ B = V * Matrix.diagonal d * W
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal]
    rfl
  rw [hdecomp, charpoly_units_conj, Matrix.charpoly_diagonal]
  simp only [hd, Function.comp_apply]

/-- **Eigenvalue multiset of a Kronecker product:** the eigenvalues of `A ⊗ B` are the products
`{λᵢ μⱼ}` of the factor eigenvalues. -/
theorem map_eigenvalues_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A ⊗ₖ B).IsHermitian) :
    Multiset.map hAB.eigenvalues Finset.univ.val
      = Multiset.map (fun ij : m × n => hA.eigenvalues ij.1 * hB.eigenvalues ij.2)
          Finset.univ.val := by
  have hofReal : Function.Injective (RCLike.ofReal : ℝ → ℂ) := Complex.ofReal_injective
  apply Multiset.map_injective hofReal
  rw [Multiset.map_map, Multiset.map_map, ← hAB.roots_charpoly_eq_eigenvalues,
    charpoly_kronecker_eq hA hB, Finset.prod_eq_multiset_prod,
    show (fun ij : m × n => Polynomial.X - Polynomial.C
          ((RCLike.ofReal (hA.eigenvalues ij.1) : ℂ) * (RCLike.ofReal (hB.eigenvalues ij.2) : ℂ)))
        = (fun a : ℂ => Polynomial.X - Polynomial.C a)
          ∘ (fun ij : m × n => (RCLike.ofReal (hA.eigenvalues ij.1) : ℂ)
              * (RCLike.ofReal (hB.eigenvalues ij.2) : ℂ)) from rfl,
    ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
  refine Multiset.map_congr rfl fun ij _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **Sum of a function over the eigenvalues of a Kronecker product** equals the double sum over the
products of factor eigenvalues (stated for `negMulLog`, the von Neumann entropy summand). -/
theorem sum_negMulLog_eigenvalues_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A ⊗ₖ B).IsHermitian) :
    ∑ k, Real.negMulLog (hAB.eigenvalues k)
      = ∑ ij : m × n, Real.negMulLog (hA.eigenvalues ij.1 * hB.eigenvalues ij.2) := by
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum,
    show (fun k => Real.negMulLog (hAB.eigenvalues k)) = Real.negMulLog ∘ hAB.eigenvalues from rfl,
    show (fun ij : m × n => Real.negMulLog (hA.eigenvalues ij.1 * hB.eigenvalues ij.2))
        = Real.negMulLog ∘ (fun ij : m × n => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) from rfl,
    ← Multiset.map_map, ← Multiset.map_map, map_eigenvalues_kronecker hA hB hAB]

/-- **Additivity of the von Neumann entropy under tensor products:** `S(ρ ⊗ σ) = S(ρ) + S(σ)`. The
eigenvalues of `ρ ⊗ σ` are the products `pᵢ qⱼ`, and `negMulLog(pᵢqⱼ) = qⱼ negMulLog(pᵢ) + pᵢ negMulLog(qⱼ)`
(`Real.negMulLog_mul`); summing and using `∑ᵢ pᵢ = ∑ⱼ qⱼ = 1` gives the result. -/
theorem vonNeumannEntropy_kronecker_add {ρ : Matrix m m ℂ} {σ : Matrix n n ℂ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    vonNeumannEntropy (isHermitian_kronecker hρ.1.isHermitian hσ.1.isHermitian)
      = vonNeumannEntropy hρ.1.isHermitian + vonNeumannEntropy hσ.1.isHermitian := by
  rw [vonNeumannEntropy, sum_negMulLog_eigenvalues_kronecker hρ.1.isHermitian hσ.1.isHermitian,
    Fintype.sum_prod_type]
  have hkey : ∀ i, ∑ j, Real.negMulLog (hρ.1.isHermitian.eigenvalues i * hσ.1.isHermitian.eigenvalues j)
      = (∑ j, hσ.1.isHermitian.eigenvalues j) * Real.negMulLog (hρ.1.isHermitian.eigenvalues i)
        + hρ.1.isHermitian.eigenvalues i * ∑ j, Real.negMulLog (hσ.1.isHermitian.eigenvalues j) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Real.negMulLog_mul _ _
  rw [Finset.sum_congr rfl fun i _ => hkey i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_eigenvalues_density hσ, sum_eigenvalues_density hρ, one_mul, one_mul,
    vonNeumannEntropy, vonNeumannEntropy]

end SKEFTHawking.QuantumNetwork
