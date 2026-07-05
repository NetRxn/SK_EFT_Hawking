import Mathlib
import SKEFTHawking.SingularIntFundamentalClassExist
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularGoodCompactUnionInt

/-!
# Phase 5q.H · E1 brick 18f — the Mayer–Vietoris MIDDLE of the oriented ℤ fundamental-class induction

The union / finite-union steps of the ℤ chart-cover construction of the oriented fundamental class `[M]`
(Hatcher 3.27(b), oriented version). The direct integral mirror of the mod-2
`SingularFundamentalClass.hasFundClass_union` / `hasFundClass_biUnion`, with the `x + x = 0` collapse
(`ZModModule.add_self`) replaced by the honest ℤ `sub_self`.

The framework `SingularIntFundamentalClassExist.hasOrientedFundClassInt orient K` fixes a **single global**
orientation section `orient : M → ℤ`. Hence in the union step the two witnesses `αA` (for `A`), `αB` (for
`B`) restrict to the SAME oriented local generator `orientedLocalGenerator x (orient x)` at every
`x ∈ A ∩ B`, so the MV **difference** `Σ(αA, αB) = relInclInt αA − relInclInt αB` restricts to `0` there;
by `determinedByPointsInt (A ∩ B)` it vanishes, so `(αA, αB) ∈ ker (relMvHomSumInt) = im (relMvHomDiagInt)`
(`relMvInt_exact_middle'`), and the glued preimage restricts to the oriented generator everywhere. No
orientation-coherence obstruction arises — `orient` is fixed.

* `hasOrientedFundClassInt_union` — the MV union step (`U = Aᶜ`, `V = Bᶜ`).
* `hasOrientedFundClassInt_biUnion` — the finite-union induction (`Finset.Nonempty.cons_induction`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt
  (relMvHomDiagInt relMvHomSumInt relMvInt_exact_middle')
open SKEFTHawking.IntOrientationSection
  (orientedLocalGenerator restrictToPointInt relInclInt relInclInt_trans)
open SKEFTHawking.SingularIntFundamentalClassExist
  (hasOrientedFundClassInt restrictsToOrientedGeneratorInt)

namespace SKEFTHawking.SingularIntFundClassUnionInt

variable {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **A `relInclInt` over a set equality is injective** (left-inverted by its reverse, from
`relInclInt_roundtrip`). Used to inject `Σ(αA, αB) ∈ Hₙ(M | Aᶜ∪Bᶜ)` across the de Morgan identity
`Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ` into `Hₙ(M | A∩B)` where `determinedByPointsInt` applies. -/
theorem relInclInt_injective_of_setEq {X : TopCat} {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S) (n : ℕ) :
    Function.Injective (relInclInt hST n) :=
  Function.LeftInverse.injective
    (fun p => SKEFTHawking.SingularGoodCompactUnionInt.relInclInt_roundtrip hST hTS n p)

/-- **The Mayer–Vietoris union step of the oriented ℤ existence induction** (Hatcher 3.27(b), oriented):
if `A`, `B` are closed, `A ∩ B` is determined-by-points, and both `A`, `B` have an oriented fundamental
class w.r.t. the *same* section `orient`, then so does `A ∪ B`. The two classes `αA`, `αB` restrict to the
same oriented generator at each point of `A ∩ B`, so the MV difference `Σ(αA, αB)` restricts to `0` there;
hence `Σ(αA, αB) = 0` (via `determinedByPointsInt`), so `(αA, αB) ∈ im (relMvHomDiagInt)`
(`relMvInt_exact_middle'`), and the preimage `v`, pushed to `Hₙ(M | (A∪B)ᶜ)`, restricts to the oriented
generator everywhere. -/
theorem hasOrientedFundClassInt_union (orient : M → ℤ) {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B)
    (hDAB : SKEFTHawking.SingularGoodCompactInt.determinedByPointsInt (X := TopCat.of M) 4 (A ∩ B))
    (hfA : hasOrientedFundClassInt orient A) (hfB : hasOrientedFundClassInt orient B) :
    hasOrientedFundClassInt orient (A ∪ B) := by
  obtain ⟨αA, hαA⟩ := hfA
  obtain ⟨αB, hαB⟩ := hfB
  have hge : (Aᶜ ∩ Bᶜ : Set ↑(TopCat.of M)) ⊆ (A ∪ B)ᶜ := (Set.compl_union A B).ge
  have hUVsub : (Aᶜ ∪ Bᶜ : Set ↑(TopCat.of M)) ⊆ (A ∩ B)ᶜ := (Set.compl_inter A B).ge
  have hVUsub : ((A ∩ B)ᶜ : Set ↑(TopCat.of M)) ⊆ (Aᶜ ∪ Bᶜ) := (Set.compl_inter A B).le
  -- `Σ(αA, αB) = 0`: transport into `Hₙ(M | A∩B)` and apply `determinedByPointsInt`; at each `y` the two
  -- restrictions equal the *same* oriented generator, so their ℤ difference vanishes.
  have hsum0 : relMvHomSumInt (M := TopCat.of M) Aᶜ Bᶜ 4 (αA, αB) = 0 := by
    apply relInclInt_injective_of_setEq hUVsub hVUsub 4
    rw [map_zero]
    refine hDAB _ (fun y hy => ?_)
    have keyA : restrictToPointInt hy 4
        (relInclInt hUVsub 4 (relInclInt Set.subset_union_left 4 αA))
        = restrictToPointInt hy.1 4 αA := by
      show relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) 4
          (relInclInt hUVsub 4 (relInclInt Set.subset_union_left 4 αA))
        = relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy.1)) 4 αA
      rw [relInclInt_trans, relInclInt_trans]
    have keyB : restrictToPointInt hy 4
        (relInclInt hUVsub 4 (relInclInt Set.subset_union_right 4 αB))
        = restrictToPointInt hy.2 4 αB := by
      show relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) 4
          (relInclInt hUVsub 4 (relInclInt Set.subset_union_right 4 αB))
        = relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy.2)) 4 αB
      rw [relInclInt_trans, relInclInt_trans]
    have hsumeq : relMvHomSumInt (M := TopCat.of M) Aᶜ Bᶜ 4 (αA, αB)
        = relInclInt Set.subset_union_left 4 αA - relInclInt Set.subset_union_right 4 αB := by
      show relInclInt Set.subset_union_left 4 αA + (-relInclInt Set.subset_union_right 4) αB
        = relInclInt Set.subset_union_left 4 αA - relInclInt Set.subset_union_right 4 αB
      rw [LinearMap.neg_apply, ← sub_eq_add_neg]
    rw [hsumeq, map_sub, map_sub, keyA, keyB, hαA y hy.1, hαB y hy.2, sub_self]
  -- exactness: `(αA, αB) = relMvHomDiagInt v` for some `v ∈ Hₙ(M | Aᶜ∩Bᶜ)`.
  obtain ⟨v, hv⟩ :=
    ((relMvInt_exact_middle' (M := TopCat.of M) Aᶜ Bᶜ hA.isOpen_compl hB.isOpen_compl 3)
      (αA, αB)).mp hsum0
  have hvA : relInclInt Set.inter_subset_left 4 v = αA := congrArg Prod.fst hv
  have hvB : relInclInt Set.inter_subset_right 4 v = αB := congrArg Prod.snd hv
  refine ⟨relInclInt hge 4 v, fun x hx => ?_⟩
  rcases hx with hxA | hxB
  · -- `restrictToPointInt hx (relInclInt hge v) = restrictToPointInt (x∈A) αA = oriented generator`
    rw [show restrictToPointInt (Set.mem_union_left B hxA) 4 (relInclInt hge 4 v)
        = restrictToPointInt hxA 4 αA from ?_]
    · exact hαA x hxA
    · show relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
          (Set.mem_union_left B hxA))) 4 (relInclInt hge 4 v)
        = relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxA)) 4 αA
      rw [← hvA, relInclInt_trans, relInclInt_trans]
  · rw [show restrictToPointInt (Set.mem_union_right A hxB) 4 (relInclInt hge 4 v)
        = restrictToPointInt hxB 4 αB from ?_]
    · exact hαB x hxB
    · show relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
          (Set.mem_union_right A hxB))) 4 (relInclInt hge 4 v)
        = relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxB)) 4 αB
      rw [← hvB, relInclInt_trans, relInclInt_trans]

/-- **Finite-union existence** (Hatcher 3.27(b), oriented ℤ): for a nonempty finite family `K i` (`i ∈ s`)
each with an oriented fundamental class (same section `orient`), all of whose nonempty sub-intersections
`⋂ i∈t, K i` are closed and `goodCompactInt`, the union `⋃ i∈s, K i` has an oriented fundamental class.
Induction on `s` via `hasOrientedFundClassInt_union`, mirroring the mod-2 `hasFundClass_biUnion`; the union
step's `determinedByPointsInt (A ∩ B)` comes from `goodCompactInt (K a ∩ ⋃ K i) = goodCompactInt (⋃ (K a ∩
K i))` supplied by `goodCompactInt_biUnion` over the sub-intersection family. -/
theorem hasOrientedFundClassInt_biUnion (orient : M → ℤ) {ι : Type*} [DecidableEq ι] :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set M),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧
           SKEFTHawking.SingularGoodCompactInt.goodCompactInt (X := TopCat.of M) 4 (⋂ i ∈ t, K i)) →
      (∀ i ∈ s, hasOrientedFundClassInt orient (K i)) →
      hasOrientedFundClassInt orient (⋃ i ∈ s, K i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro K _hgc hfc
      simpa using hfc a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
      intro K hgc hfc
      have hUnion : (⋃ i ∈ Finset.cons a s ha, K i) = K a ∪ ⋃ i ∈ s, K i := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨i, rfl | hi, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hUnion]
      have hKa := hgc {a} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_self a s))
        (Finset.singleton_nonempty a)
      have hKac : IsClosed (K a) := by simpa using hKa.1
      have hBc : IsClosed (⋃ i ∈ s, K i) := by
        refine Set.Finite.isClosed_biUnion s.finite_toSet (fun i hi => ?_)
        have := hgc {i} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_of_mem hi))
          (Finset.singleton_nonempty i)
        simpa using this.1
      have hfKa : hasOrientedFundClassInt orient (K a) := hfc a (Finset.mem_cons_self a s)
      have hfB : hasOrientedFundClassInt orient (⋃ i ∈ s, K i) :=
        ih K (fun t ht htne => hgc t (ht.trans (Finset.subset_cons ha)) htne)
          (fun i hi => hfc i (Finset.mem_cons_of_mem hi))
      have hdist : K a ∩ (⋃ i ∈ s, K i) = ⋃ i ∈ s, (K a ∩ K i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨hxa, i, hi, hx⟩; exact ⟨i, hi, hxa, hx⟩
        · rintro ⟨i, hi, hxa, hx⟩; exact ⟨hxa, i, hi, hx⟩
      have hgcInter : SKEFTHawking.SingularGoodCompactInt.goodCompactInt (X := TopCat.of M) 4
          (K a ∩ (⋃ i ∈ s, K i)) := by
        rw [hdist]
        refine SKEFTHawking.SingularGoodCompactUnionInt.goodCompactInt_biUnion (X := TopCat.of M) hs
          (fun i => K a ∩ K i) (fun t ht htne => ?_)
        have heq : (⋂ i ∈ t, (K a ∩ K i)) = ⋂ i ∈ insert a t, K i := by
          obtain ⟨j, hj⟩ := htne
          ext x
          simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
          constructor
          · rintro h i (rfl | hi)
            · exact (h j hj).1
            · exact (h i hi).2
          · intro h
            exact fun i hi => ⟨h a (Or.inl rfl), h i (Or.inr hi)⟩
        rw [heq]
        exact hgc (insert a t)
          (Finset.insert_subset (Finset.mem_cons_self a s) (ht.trans (Finset.subset_cons ha)))
          (Finset.insert_nonempty a t)
      exact hasOrientedFundClassInt_union orient hKac hBc hgcInter.2 hfKa hfB

end SKEFTHawking.SingularIntFundClassUnionInt
