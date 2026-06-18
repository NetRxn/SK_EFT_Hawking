import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularConvexRadialBase
import SKEFTHawking.SingularLocalHomologyColimit
import SKEFTHawking.SingularBallCover

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4i) — `goodCompact` for the empty set and finite convex unions

Two assembly lemmas toward Hatcher 3.27 step 3 (an arbitrary compact `K ⊆ ℝⁿ` is `goodCompact`):

* **`goodCompact_empty`** (any `X`): the empty set is `goodCompact n` because `Hᵢ(X | ∅) = Hᵢ(X, X) = 0`
  — `subspaceChains (∅ᶜ) = ⊤`, so the relative chain module (hence the relative homology) is the zero
  module. This closes the empty-intersection branch that `goodCompact_biUnion` opens when the cover's
  balls are pairwise disjoint.

* **`goodCompact_biUnion_convex`** (Euclidean): a finite union `⋃ i∈s, B i` of convex compact sets is
  `goodCompact (m+2)`. Runs `SingularGoodCompact.goodCompact_biUnion`; every nonempty sub-intersection
  `⋂ i∈t, B i` is convex (intersection of convex) and compact (closed subset of one of the `B i`), so
  `SingularConvexRadialBase.goodCompact_convexCompact` (brick 4g) applies when it is nonempty and
  `goodCompact_empty` when it is empty.

These feed the colimit step-3 assembly (`vanishAbove`/`determinedByPoints` for an arbitrary Euclidean
compact) over the finite closed-ball cover (`SingularBallCover.exists_finite_closedBall_cover`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularGoodCompactEuclidean

variable {X : TopCat}

/-! ## `goodCompact_empty` -/

/-- `subspaceChains (∅ᶜ) = ⊤`: every chain's support simplices land in `∅ᶜ = univ`. -/
theorem subspaceChains_compl_empty_eq_top (n : ℕ) :
    subspaceChains (∅ᶜ : Set ↑X) n = ⊤ := by
  refine eq_top_iff.2 (fun c _ => mem_subspaceChains_of_support (fun τ _ x _ => ?_))
  exact Set.notMem_empty x

/-- The relative chain module of the pair `(X, X)` is the zero module. -/
instance relativeChain_compl_empty_subsingleton (n : ℕ) :
    Subsingleton (RelativeChain (∅ᶜ : Set ↑X) n) := by
  rw [RelativeChain, subspaceChains_compl_empty_eq_top]
  infer_instance

/-- `Hᵢ(X | ∅) = Hᵢ(X, X) = 0`: every relative-homology class of the pair `(X, X)` is zero. -/
theorem relativeHomology_compl_empty_eq_zero (n : ℕ) (x : RelativeHomology (∅ᶜ : Set ↑X) n) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show z = 0 from Subsingleton.elim z 0]
  exact Submodule.Quotient.mk_zero _

/-- **The empty set is `goodCompact`** (any `X`, any `n`): both halves hold because the relevant
relative-homology module `Hᵢ(X | ∅) = Hᵢ(X, X)` is the zero module. The empty-intersection branch of
the `goodCompact_biUnion` finite-union induction. -/
theorem goodCompact_empty (n : ℕ) :
    SKEFTHawking.SingularGoodCompact.goodCompact (X := X) n (∅ : Set ↑X) := by
  refine ⟨fun i _ x => relativeHomology_compl_empty_eq_zero i x, fun α _ => ?_⟩
  exact relativeHomology_compl_empty_eq_zero n α

/-! ## `goodCompact_biUnion_convex` -/

/-- **A finite union of convex compact sets is `goodCompact`** (Hatcher 3.27 step 2, all-dimensional):
for a nonempty finite family `B i` (`i ∈ s`) of convex compact subsets of `ℝⁿ` (`n = m+2`), the union
`⋃ i∈s, B i` is `goodCompact (m+2)`. Every nonempty sub-intersection is convex compact
(`goodCompact_convexCompact`, brick 4g); the empty ones use `goodCompact_empty`. -/
theorem goodCompact_biUnion_convex {m : ℕ} {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (B : ι → Set (EuclideanSpace ℝ (Fin (m + 2))))
    (hconv : ∀ i ∈ s, Convex ℝ (B i)) (hcomp : ∀ i ∈ s, IsCompact (B i)) :
    SKEFTHawking.SingularGoodCompact.goodCompact
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) (⋃ i ∈ s, B i) := by
  classical
  -- Provide `X := Eucl (m+2)` explicitly to `goodCompact_biUnion`: it sidesteps the `isDefEq`
  -- heartbeat wall the coercion `Set (EuclideanSpace …) ≟ Set ↑(Eucl …)` triggers under the
  -- `goodCompact` Prop when `X` is a metavariable.
  exact SingularGoodCompact.goodCompact_biUnion (X := SingularEuclideanAcyclic.Eucl (m + 2)) hs B
    (fun t ht htne => by
      obtain ⟨j, hj⟩ := htne
      -- Each nonempty sub-intersection is convex (intersection of convex), closed (intersection of
      -- the compact-hence-closed `B i`), and compact (closed subset of `B j`, `j ∈ t`).
      have hconvI : Convex ℝ (⋂ i ∈ t, B i) :=
        convex_iInter (fun i => convex_iInter (fun hi => hconv i (ht hi)))
      have hclosedI : IsClosed (⋂ i ∈ t, B i) :=
        isClosed_biInter (fun i hi => (hcomp i (ht hi)).isClosed)
      have hcompI : IsCompact (⋂ i ∈ t, B i) :=
        (hcomp j (ht hj)).of_isClosed_subset hclosedI (Set.biInter_subset_of_mem hj)
      refine ⟨hclosedI, ?_⟩
      by_cases hne : (⋂ i ∈ t, B i).Nonempty
      · obtain ⟨O, hO⟩ := hne
        exact SingularConvexRadialBase.goodCompact_convexCompact hconvI hcompI hO
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact goodCompact_empty (m + 2))

/-! ## Step 3 (a) — `vanishAbove` for an arbitrary Euclidean compact -/

/-- **`vanishAbove (m+2) K` for an arbitrary compact `K ⊆ ℝⁿ`** (Hatcher 3.27 step 3, the high-degree
half): `Hᵢ(ℝⁿ | K) = 0` for `i > m+2`. A class `α` factors through `Hᵢ(ℝⁿ | C)` for a compact
neighbourhood `C ⊇ K` (the colimit surjectivity `exists_factor_through_compact`, brick 4e); covering
`K` by finitely many closed balls inside `interior C` yields a convex-compact-union `C'` with
`K ⊆ C' ⊆ C` and `Hᵢ(ℝⁿ | C') = 0` (brick 4i), so the image of `α`'s representative in `Hᵢ(ℝⁿ | C')`
vanishes and `α = 0` (`relIncl_trans`). -/
theorem vanishAbove_eucl_compact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hK : IsCompact K) :
    vanishAbove (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact (goodCompact_empty (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2)).1
  · intro i hi α
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨C, hCcomp, hKC, β, hβ⟩ :=
      SingularLocalHomologyColimit.exists_factor_through_compact
        (X := SingularEuclideanAcyclic.Eucl (m + 2)) hK α
    obtain ⟨s, r, hs, hsK, hrpos, hcov, hsub⟩ :=
      SingularBallCover.exists_finite_closedBall_cover hK isOpen_interior hKC hKne
    have hgoodC' : SKEFTHawking.SingularGoodCompact.goodCompact
        (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) (⋃ c ∈ s, Metric.closedBall c (r c)) :=
      goodCompact_biUnion_convex hs (fun c => Metric.closedBall c (r c))
        (fun c _ => convex_closedBall c (r c)) (fun c _ => isCompact_closedBall c (r c))
    have hC'C : (⋃ c ∈ s, Metric.closedBall c (r c)) ⊆ C :=
      Set.iUnion₂_subset (fun c hc => (hsub c hc).trans interior_subset)
    have hCC' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
        ⊆ (⋃ c ∈ s, Metric.closedBall c (r c))ᶜ := Set.compl_subset_compl.mpr hC'C
    have hC'K : ((⋃ c ∈ s, Metric.closedBall c (r c))ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
        ⊆ Kᶜ := Set.compl_subset_compl.mpr hcov
    have hβ'0 : relIncl hCC' (k + 1) β = 0 := hgoodC'.1 (k + 1) hi _
    calc α = relIncl _ (k + 1) β := hβ.symm
      _ = relIncl hC'K (k + 1) (relIncl hCC' (k + 1) β) := (relIncl_trans hCC' hC'K (k + 1) β).symm
      _ = relIncl hC'K (k + 1) 0 := by rw [hβ'0]
      _ = 0 := map_zero _

end SKEFTHawking.SingularGoodCompactEuclidean
