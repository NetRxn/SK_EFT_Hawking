/-
# Phase 5q.H close-out — THE CANONICAL DISJOINT-UNION INTERSECTION FORM (σ-additivity's provable form)

The #161 assessment (`PinPlusKTSpinSigmaStockElement` report-notes; `PinPlusKTSpinSigmaStock` §2):
`InterMatrixBlockAtom prov a` over an ARBITRARY disclosed bundle `a` is NOT provable — `a`'s `fc`/`B`
fields on the disjoint union `p ⊔ q` have no tie to the `⊔`-structure. The provable form CONSTRUCTS the
canonical sum bundle first, then the block-congruence follows.

This module builds, for two closed spin 4-manifolds `M = A`, `N = B` (`TopCat`), the **canonical
integral fundamental class and `H²`-basis on `M ⊔ N`** and proves the intersection matrix is
BLOCK-DIAGONAL:

    interMatrix (M ⊔ N)  =  blockDiag (interMatrix M) (interMatrix N)    (`interMatrix_disjointSum_eq_blockDiag`)

exactly — feeding `latticeSig_blockDiag` to fire **σ-additivity** on the canonical construction:

    σ(M ⊔ N)  =  σ(M) + σ(N)                                             (`latticeSig_interMatrix_disjointSum`)

## The three ingredients (all provable — the cross-vanishing is not a wall)

* **`intFundClassSum`** — `[M ⊔ N] = [M] ⊕ [N]`: the sum's evaluation functional is `⟨·,[M]⟩∘inl* +
  ⟨·,[N]⟩∘inr*` via the two inclusion pullbacks.
* **`intH2BasisSum`** — the block `H²`-basis: `H²(M ⊔ N;ℤ) ≃ₗ H²(M;ℤ) × H²(N;ℤ)` (the integral
  disjoint-sum equiv `cohomologyDisjointSumEquivInt`) transports the product basis of the two pieces.
* **the integral cup cross-vanishing** — for `a` an `M`-block class and `b` an `N`-block class,
  `⟨a ∪ b, [M ⊔ N]⟩ = 0`. This is NOT a wall: it is the pullback multiplicativity of the integral cup
  (`cohomologyPullbackInt_cupH24`, ALREADY on main), which gives the form-splitting
  `interFormInt (M⊔N) α β = interFormInt M (inl*α)(inl*β) + interFormInt N (inr*α)(inr*β)`
  (`interFormInt_disjointSum`); the block basis sends `M`-classes to `(inl*·) = ·, (inr*·) = 0` and
  vice versa, so the cross entries vanish by `map_zero`.

**Dimension discipline.** `A`, `B` closed spin 4-manifolds; `⊔` = the disjoint union (the carrier's
add-op substrate); integral (co)homology degrees 2 and 4; the form on `H²`.

**Fence** `synthetic-grade-ker-bot-nogo`: the sum fundamental class and block basis are constructed by
genuine integral (co)homology (the ported disjoint-sum equiv), not a fabricated grade. The `⊔` here is a
genuine disjoint union — the legitimate domain of the split engine, distinct from the banned
partition/pair-class routes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyDisjointSumInt
import SKEFTHawking.SingularCohomologyFunctorialityInt
import SKEFTHawking.IntersectionMatrixInt
import SKEFTHawking.SpinSigmaGenerator

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.SingularCohomologyDisjointSumInt
  (cohomologyDisjointSumEquivInt cohomologyDisjointSumEquivInt_apply)
open SKEFTHawking.SingularCohomologyDisjointSum (sumSpace inlMap inrMap)
open SKEFTHawking.SpinSigmaRoute (blockDiag blockDiag_def latticeSig_blockDiag)

variable (A B : TopCat)

/-! ## §1. The canonical sum fundamental class and the form-splitting -/

/-- **The canonical integral fundamental class of `M ⊔ N`**, `[M ⊔ N] = [M] ⊕ [N]`. Its evaluation
functional on `H⁴(M ⊔ N;ℤ)` is `⟨·, [M]⟩ ∘ inl* + ⟨·, [N]⟩ ∘ inr*`, the two inclusion pullbacks composed
with the pieces' fundamental-class evaluations. -/
noncomputable def intFundClassSum (fcA : IntFundamentalClass A) (fcB : IntFundamentalClass B) :
    IntFundamentalClass (sumSpace A B) where
  eval := fcA.eval ∘ₗ cohomologyPullbackInt (inlMap A B) 4
    + fcB.eval ∘ₗ cohomologyPullbackInt (inrMap A B) 4

@[simp] theorem intFundClassSum_eval (fcA : IntFundamentalClass A) (fcB : IntFundamentalClass B) :
    (intFundClassSum A B fcA fcB).eval
      = fcA.eval ∘ₗ cohomologyPullbackInt (inlMap A B) 4
        + fcB.eval ∘ₗ cohomologyPullbackInt (inrMap A B) 4 := rfl

/-- **The form-splitting for the canonical sum class** (the integral cup cross-vanishing, packaged):
`interFormInt (M ⊔ N) α β = interFormInt M (inl*α)(inl*β) + interFormInt N (inr*α)(inr*β)`. Immediate
from cup-pullback multiplicativity (`cohomologyPullbackInt_cupH24`). The cross-vanishing is then a
corollary: if `inr*α = 0` then the `N`-summand drops by `map_zero`. -/
theorem interFormInt_disjointSum (fcA : IntFundamentalClass A) (fcB : IntFundamentalClass B)
    (α β : Cohomology (sumSpace A B) 2) :
    interFormInt (intFundClassSum A B fcA fcB) α β
      = interFormInt fcA (cohomologyPullbackInt (inlMap A B) 2 α)
          (cohomologyPullbackInt (inlMap A B) 2 β)
        + interFormInt fcB (cohomologyPullbackInt (inrMap A B) 2 α)
          (cohomologyPullbackInt (inrMap A B) 2 β) := by
  rw [interFormInt_apply, interFormInt_apply, interFormInt_apply, intFundClassSum_eval,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    cohomologyPullbackInt_cupH24, cohomologyPullbackInt_cupH24]

/-! ## §2. The block `H²`-basis on `M ⊔ N` -/

/-- **The canonical block `H²`-basis of `M ⊔ N`.** Rank `b₂(M) + b₂(N)`; the basis transports the
product basis `B_M ⊕ B_N` of `H²(M;ℤ) × H²(N;ℤ)` back through the integral disjoint-sum equiv
`cohomologyDisjointSumEquivInt`, reindexed to `Fin (b₂(M) + b₂(N))` by `finSumFinEquiv`. -/
noncomputable def intH2BasisSum (BA : IntH2Basis A) (BB : IntH2Basis B) :
    IntH2Basis (sumSpace A B) where
  rank := BA.rank + BB.rank
  basis := ((BA.basis.prod BB.basis).map (cohomologyDisjointSumEquivInt A B 2).symm).reindex
    finSumFinEquiv

@[simp] theorem intH2BasisSum_rank (BA : IntH2Basis A) (BB : IntH2Basis B) :
    (intH2BasisSum A B BA BB).rank = BA.rank + BB.rank := rfl

/-- The block basis vector at index `k` is the equiv-transport of the product basis vector at
`finSumFinEquiv.symm k`. -/
theorem intH2BasisSum_basis_apply (BA : IntH2Basis A) (BB : IntH2Basis B)
    (k : Fin (BA.rank + BB.rank)) :
    (intH2BasisSum A B BA BB).basis k
      = (cohomologyDisjointSumEquivInt A B 2).symm ((BA.basis.prod BB.basis) (finSumFinEquiv.symm k)) := by
  show ((((BA.basis.prod BB.basis).map (cohomologyDisjointSumEquivInt A B 2).symm).reindex
    finSumFinEquiv) k) = _
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply]

/-- **`inl*` of the equiv-transported product class is its first component** — the `M`-restriction of
`e⁻¹ v` reads off `v.1`. From `e (e⁻¹ v) = v` and `e = (inl*, inr*)`. -/
theorem cohomologyPullbackInt_inl_equivSymm (v : Cohomology A 2 × Cohomology B 2) :
    cohomologyPullbackInt (inlMap A B) 2 ((cohomologyDisjointSumEquivInt A B 2).symm v) = v.1 := by
  have h := (cohomologyDisjointSumEquivInt A B 2).apply_symm_apply v
  rw [cohomologyDisjointSumEquivInt_apply] at h
  exact congrArg Prod.fst h

/-- **`inr*` of the equiv-transported product class is its second component**. -/
theorem cohomologyPullbackInt_inr_equivSymm (v : Cohomology A 2 × Cohomology B 2) :
    cohomologyPullbackInt (inrMap A B) 2 ((cohomologyDisjointSumEquivInt A B 2).symm v) = v.2 := by
  have h := (cohomologyDisjointSumEquivInt A B 2).apply_symm_apply v
  rw [cohomologyDisjointSumEquivInt_apply] at h
  exact congrArg Prod.snd h

/-! ## §3. The block-congruence (exact equality) and σ-additivity -/

/-- **THE CANONICAL DISJOINT-UNION INTERSECTION MATRIX IS BLOCK-DIAGONAL** (exact matrix equality):

    interMatrix (intFundClassSum) (intH2BasisSum)  =  blockDiag (interMatrix M) (interMatrix N).

The block structure is the form-splitting (`interFormInt_disjointSum`) evaluated on the block basis:
the `M`-block vectors restrict to `(inl*·) = ·`, `(inr*·) = 0` and the `N`-block vectors vice versa
(`cohomologyPullbackInt_inl/inr_equivSymm` + `Basis.prod` components), so the diagonal blocks are the
pieces' matrices and the off-diagonal (cross) entries vanish by `map_zero` — the integral cup
cross-vanishing, realized. -/
theorem interMatrix_disjointSum_eq_blockDiag (fcA : IntFundamentalClass A)
    (fcB : IntFundamentalClass B) (BA : IntH2Basis A) (BB : IntH2Basis B) :
    interMatrix (intFundClassSum A B fcA fcB) (intH2BasisSum A B BA BB)
      = blockDiag (interMatrix fcA BA) (interMatrix fcB BB) := by
  ext k l
  rw [interMatrix_apply, intH2BasisSum_basis_apply, intH2BasisSum_basis_apply,
    interFormInt_disjointSum, cohomologyPullbackInt_inl_equivSymm, cohomologyPullbackInt_inl_equivSymm,
    cohomologyPullbackInt_inr_equivSymm, cohomologyPullbackInt_inr_equivSymm, blockDiag_def,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  set s := finSumFinEquiv.symm k with hs
  set t := finSumFinEquiv.symm l with ht
  rcases s with i | i <;> rcases t with j | j <;>
    simp only [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, interMatrix_apply, map_zero,
      LinearMap.zero_apply, Matrix.zero_apply, add_zero, zero_add]

/-- **σ-ADDITIVITY OF THE CANONICAL DISJOINT-UNION SIGNATURE** (the visible corollary):

    σ(M ⊔ N)  =  σ(M) + σ(N),

for the canonical sum construction, given each piece's intersection form is even unimodular (the Wu /
Poincaré-duality per-piece obligations). This is the provable form of the σ-descent additivity input
`hadd` (`PinPlusKTSpinSigmaStock.sigAdditivity_atoms_of_blockCongr`): the disjoint-union intersection
matrix is block-diagonal (`interMatrix_disjointSum_eq_blockDiag`), and `latticeSig` is block-additive on
even-unimodular blocks. So the σ-descent's additivity plumbing is discharged for the canonical bundle;
only the deep bordism-invariance half `hbord` remains. -/
theorem latticeSig_interMatrix_disjointSum (fcA : IntFundamentalClass A)
    (fcB : IntFundamentalClass B) (BA : IntH2Basis A) (BB : IntH2Basis B)
    (heuA : IsEvenUnimodular (interMatrix fcA BA)) (heuB : IsEvenUnimodular (interMatrix fcB BB)) :
    latticeSig (interMatrix (intFundClassSum A B fcA fcB) (intH2BasisSum A B BA BB))
      = latticeSig (interMatrix fcA BA) + latticeSig (interMatrix fcB BB) := by
  rw [interMatrix_disjointSum_eq_blockDiag]
  exact latticeSig_blockDiag _ _ heuA heuB

end SKEFTHawking.SingularCohomologyInt
