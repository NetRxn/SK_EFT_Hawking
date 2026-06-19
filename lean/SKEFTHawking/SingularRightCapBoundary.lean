import Mathlib
import SKEFTHawking.SingularCapChainIncl

/-!
# Phase 5q.F (PD6f-c4-R3a) — the right-cap chain-map property for a cocycle
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularCapChainIncl

namespace SKEFTHawking.SingularRightCapBoundary

/-- The right cap of a cast basis simplex factors through `frontBig`/`backBig`: for `σ : simplex(k+l+1)`
and the degree cast `h : k+l+1 = k+1+l`, `(h ▸ σ) ⌢ʳ b = b(backBig σ) • [frontBig σ]`. -/
theorem rcapBasis_cast {X : TopCat} {k l : ℕ} (b : SingularCochain X l)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + l + 1)))) (s : ZMod 2)
    (h : k + l + 1 = k + 1 + l) :
    rcap (k := k + 1) b (h ▸ Finsupp.single σ s)
      = s • (b (backBig σ) • Finsupp.single (frontBig σ) (1 : ZMod 2)) := by
  rw [singularChain_single_cast σ s h, rcap_single_smul, rcapBasis, frontFace_cast σ h,
    backFace_cast σ h]

/-- Per-simplex right-cap Alexander–Whitney boundary split, mirror of `cap_leibniz_single` with
front/back swapped: for `σ : simplex(k+l+1)` and the cast `h : k+l+1 = k+1+l`,
`∂((h ▸ σ) ⌢ʳ b) = (δb)(backSmall σ) • [frontSmall σ] + (∂σ) ⌢ʳ b`. -/
theorem rcap_leibniz_single {X : TopCat} {k l : ℕ} (b : SingularCochain X l)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + l + 1))))
    (h : k + l + 1 = k + 1 + l) :
    chainBoundary X k (rcap (k := k + 1) b (h ▸ Finsupp.single σ 1))
      = coboundary X l b (backSmall σ) • Finsupp.single (frontSmall σ) 1
        + rcap (k := k) b (boundaryBasis X (k + l) σ) := by
  -- LHS: `∂(σ ⌢ʳ b)` = `b(backBig σ) • ∂[frontBig σ]`, peeling the last front-face term.
  have hL : chainBoundary X k (rcap (k := k + 1) b (h ▸ Finsupp.single σ 1))
      = b (backBig σ) • (∑ j : Fin (k + 1), Finsupp.single (face j.castSucc (frontBig σ)) (1 : ZMod 2))
        + b (backBig σ) • Finsupp.single (frontSmall σ) 1 := by
    rw [rcapBasis_cast b σ 1 h, one_smul, map_smul, chainBoundary_single, boundaryBasis,
      Fin.sum_univ_castSucc, face_last_frontBig, smul_add]
  -- The back-coboundary term peels its first face into the diagonal `b(backBig σ)•[frontSmall σ]`.
  have hcobound : coboundary X l b (backSmall σ) • Finsupp.single (frontSmall σ) (1 : ZMod 2)
      = (∑ j : Fin (l + 1),
          b (face j.succ (backSmall σ)) • Finsupp.single (frontSmall σ) (1 : ZMod 2))
        + b (backBig σ) • Finsupp.single (frontSmall σ) (1 : ZMod 2) := by
    rw [coboundary_apply, Fin.sum_univ_succ, face_zero_backSmall, add_smul, Finset.sum_smul, add_comm]
  -- `∂σ ⌢ʳ b` splits `Fin (k+l+2)` at `k`: the `i ≤ k` faces keep `[frontBig σ]`-interior faces with
  -- `b(backBig σ)`; the `i > k` faces keep `[frontSmall σ]` with the interior back coboundary faces.
  have hk : k + 1 + (l + 1) = k + l + 2 := by omega
  have hrcap : rcap (k := k) b (boundaryBasis X (k + l) σ)
      = (∑ j : Fin (k + 1),
            b (backBig σ) • Finsupp.single (face j.castSucc (frontBig σ)) (1 : ZMod 2))
        + (∑ l' : Fin (l + 1),
            b (face l'.succ (backSmall σ)) • Finsupp.single (frontSmall σ) (1 : ZMod 2)) := by
    have hsum : rcap (k := k) b (boundaryBasis X (k + l) σ)
        = ∑ i : Fin (k + l + 2), rcapBasis b (face i σ) := by
      rw [boundaryBasis, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [rcap_single_smul, one_smul])
    rw [hsum, ← Equiv.sum_comp (finCongr hk) (fun i => rcapBasis b (face i σ)), Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      have hle : (finCongr hk (Fin.castAdd (l + 1) j)).val ≤ k := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]; omega
      rw [rcapBasis, frontFace_face_of_le σ _ hle, backFace_face_of_le σ _ hle]
      have hidx : (⟨(finCongr hk (Fin.castAdd (l + 1) j)).val, by omega⟩ : Fin (k + 2))
          = j.castSucc := by
        apply Fin.ext; simp [Fin.val_castSucc]
      rw [hidx]
    · refine Finset.sum_congr rfl (fun l' _ => ?_)
      have hgt : k < (finCongr hk (Fin.natAdd (k + 1) l')).val := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [rcapBasis, frontFace_face_of_gt σ _ hgt, backFace_face_of_gt σ _ hgt]
      have hidx : (⟨(finCongr hk (Fin.natAdd (k + 1) l')).val - k, by have := l'.isLt; omega⟩ : Fin (l + 2))
          = l'.succ := by
        apply Fin.ext; simp only [Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [hidx]
  -- The two `∑_{j≥1}` back-coboundary sums (from `hcobound`'s `δb` and `hrcap`'s `i>k` faces) coincide
  -- and cancel over ℤ/2; what remains is the front sum + the diagonal.
  have hBB : (∑ j : Fin (l + 1), b (face j.succ (backSmall σ)) • Finsupp.single (frontSmall σ) (1 : ZMod 2))
        + (∑ j : Fin (l + 1), b (face j.succ (backSmall σ)) • Finsupp.single (frontSmall σ) (1 : ZMod 2))
      = 0 := by rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [hL, hrcap, hcobound,
    add_comm (∑ j : Fin (l + 1), b (face j.succ (backSmall σ)) • Finsupp.single (frontSmall σ) (1 : ZMod 2))
      (b (backBig σ) • Finsupp.single (frontSmall σ) (1 : ZMod 2)),
    Finset.smul_sum, add_add_add_comm, add_assoc, hBB, add_zero, add_comm]

/-- **A cocycle right-caps to a chain map** (mod 2): if `b` is a cocycle (`δb = 0`) then
`∂(b ⌢ʳ c) = b ⌢ʳ (∂c)` for every `(k+l+1)`-chain `c` — i.e. the right cap `b ⌢ʳ ·` intertwines the
chain boundaries. The right-cap mirror of `cap_cocycle_chainMap`: this is the descent fact that makes
`b ⌢ʳ ·` well-defined on homology for a cocycle `b` (used to extract the *left* cup factor in a Kronecker
pairing on homology, `kronecker_cup_rcap`). The left `rcap` reads its `(k+l+1)`-chain at the AW split
`(k+1)+l` (`= k+l+1` propositionally; the `cast` is the right-cap counterpart of the degree shift the
cup Leibniz absorbs via `frontBig`/`backBig`). Proved by `Finsupp.induction_linear` reducing to the
cast-free basis split `rcap_leibniz_single`, with the `coboundary b` diagonal term killed by `hb`. -/
theorem rcap_cocycle_chainMap {X : TopCat} {k l : ℕ} (b : SingularCochain X l)
    (hb : coboundaryₗ X l b = 0) (c : SingularChain X (k + l + 1)) :
    chainBoundary X k (rcap (k := k + 1) b ((by omega : k + l + 1 = k + 1 + l) ▸ c))
      = rcap (k := k) b (chainBoundary X (k + l) c) := by
  have h : k + l + 1 = k + 1 + l := by omega
  induction c using Finsupp.induction_linear with
  | zero => rw [singularChain_cast_zero h]; simp
  | add c d hc hd =>
      rw [singularChain_cast_add c d h, map_add, map_add, map_add, map_add, hc, hd]
  | single σ s =>
      have hs : (h ▸ Finsupp.single σ s : SingularChain X (k + 1 + l))
          = s • (h ▸ Finsupp.single σ 1 : SingularChain X (k + 1 + l)) := by
        rw [singularChain_single_cast σ s h, singularChain_single_cast σ 1 h, Finsupp.smul_single,
          smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, rcap_leibniz_single, chainBoundary_single_smul, map_smul, smul_add]
      have hδ : coboundary X l b (backSmall σ) = 0 := congrFun hb (backSmall σ)
      rw [hδ, zero_smul, smul_zero, zero_add]

end SKEFTHawking.SingularRightCapBoundary
