import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularRelativeMV

/-!
# Phase 5q.F (w₂-foundation) — the finite-union closure of the "good compact" property (Hatcher 3.27)

This module assembles the two halves of the Hatcher 3.27 compactness property — the high-degree
vanishing `vanishAbove n K` (`Hᵢ(M|K) = 0` for `i > n`) and the degree-`n` determined-by-points
property `determinedByPoints n K` — into a single predicate `goodCompact n K`, and proves it is
closed under finite unions.

The load-bearing new content is `determinedByPoints_union`: the (b)-half Mayer–Vietoris induction
step. Given `determinedByPoints n A`, `determinedByPoints n B` and the *vanishing* of `Hₙ₊₁(M|A∩B)`
(the inductive hypothesis, supplied here as `vanishAbove n (A∩B)`), a class in `Hₙ(M|A∪B)` that
restricts to `0` at every point of `A∪B` is `0`. The argument runs through the relative MV diagonal
`relMvHomDiag Aᶜ Bᶜ n : Hₙ(M|A∪B) → Hₙ(M|A) ⊕ Hₙ(M|B)`, which is injective once `Hₙ₊₁(M|A∩B) = 0`
(`relMvHomDiag_injective_of_acyclic`); both components vanish by `determinedByPoints A`/`B` applied
through `restrictToPoint_relIncl`, so the class is `0`.

`goodCompact_biUnion` then runs the finite-union induction exactly as `vanishAbove_biUnion`, with
`goodCompact_union` in the cons step.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.SingularGoodCompact

variable {X : TopCat}

/-- **The (b)-half MV induction step** (Hatcher 3.27): if `A`, `B` are closed and both are
determined-by-points in degree `n`, and `Hₙ₊₁(M|A∩B) = 0` (`vanishAbove n (A∩B)`), then `A∪B` is
determined-by-points in degree `n`. -/
theorem determinedByPoints_union {n : ℕ} {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hDA : determinedByPoints n A) (hDB : determinedByPoints n B)
    (hVAB : vanishAbove n (A ∩ B)) : determinedByPoints n (A ∪ B) := by
  intro α hα
  -- Injectivity of the MV diagonal `Hₙ(M|A∪B) → Hₙ(M|A) ⊕ Hₙ(M|B)`, available once `Hₙ₊₁(M|A∩B)=0`.
  have hAcyc : ∀ x : RelativeHomology (Aᶜ ∪ Bᶜ) (n + 1), x = 0 := by
    rw [← Set.compl_inter]
    exact hVAB (n + 1) (by omega)
  have hinj := relMvHomDiag_injective_of_acyclic
    (X := X) hA.isOpen_compl hB.isOpen_compl n hAcyc
  -- Move `α` into the diagonal's domain `Hₙ(M | Aᶜ ∩ Bᶜ)` via the *cast-free* inclusion-of-pairs
  -- map for the de Morgan equality `(A∪B)ᶜ ⊆ Aᶜ ∩ Bᶜ` (which holds as `(A∪B)ᶜ = Aᶜ ∩ Bᶜ`).
  have hle : (A ∪ B)ᶜ ⊆ Aᶜ ∩ Bᶜ := (Set.compl_union A B).le
  have hge : Aᶜ ∩ Bᶜ ⊆ (A ∪ B)ᶜ := (Set.compl_union A B).ge
  have hsubA : (A ∪ B)ᶜ ⊆ Aᶜ := Set.compl_subset_compl.mpr Set.subset_union_left
  have hsubB : (A ∪ B)ᶜ ⊆ Bᶜ := Set.compl_subset_compl.mpr Set.subset_union_right
  -- The two MV components of `relIncl hle n α` vanish — they are the restrictions to `Aᶜ`/`Bᶜ`,
  -- which are `0` by `determinedByPoints A`/`B` via `restrictToPoint_relIncl` and `hα`.
  have hzero : relMvHomDiag Aᶜ Bᶜ n (relIncl hle n α) = 0 := by
    apply Prod.ext
    · show relIncl Set.inter_subset_left n (relIncl hle n α) = 0
      rw [relIncl_trans]
      refine hDA _ (fun y hy => ?_)
      rw [restrictToPoint_relIncl Set.subset_union_left hy n α]
      exact hα y (Set.mem_union_left B hy)
    · show relIncl Set.inter_subset_right n (relIncl hle n α) = 0
      rw [relIncl_trans]
      refine hDB _ (fun y hy => ?_)
      rw [restrictToPoint_relIncl Set.subset_union_right hy n α]
      exact hα y (Set.mem_union_right A hy)
  -- Injectivity of the diagonal forces `relIncl hle n α = 0`; the reverse inclusion `relIncl hge n`
  -- then recovers `α = 0` (the two inclusions compose to the identity on `Hₙ(M | (A∪B)ᶜ)`).
  have hle0 : relIncl hle n α = 0 := hinj (by rw [hzero, map_zero])
  have hback : relIncl hge n (relIncl hle n α) = α := by
    rw [relIncl_trans, relIncl, RelativeHomology.map_id]
    rfl
  rw [hle0, map_zero] at hback
  exact hback.symm

/-- **The combined Hatcher-3.27 "good compact" property**: both the high-degree vanishing
`Hᵢ(M|K) = 0` (`i > n`) and the degree-`n` determined-by-points property. -/
def goodCompact (n : ℕ) (K : Set ↑X) : Prop :=
  vanishAbove n K ∧ determinedByPoints n K

/-- **`goodCompact` is closed under union**: combine `vanishAbove_union` and
`determinedByPoints_union` (the latter using `hgAB.1 : vanishAbove n (A∩B)`). -/
theorem goodCompact_union {n : ℕ} {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hgA : goodCompact n A) (hgB : goodCompact n B) (hgAB : goodCompact n (A ∩ B)) :
    goodCompact n (A ∪ B) :=
  ⟨vanishAbove_union hA hB hgA.1 hgB.1 hgAB.1,
   determinedByPoints_union hA hB hgA.2 hgB.2 hgAB.1⟩

/-- **Finite-union good-compactness** (Hatcher 3.27): for a nonempty finite family `K i` (`i ∈ s`)
all of whose nonempty sub-intersections `⋂ i∈t, K i` (`∅ ≠ t ⊆ s`) are closed and `goodCompact n`,
the union `⋃ i∈s, K i` is `goodCompact n`. Induction on `s` via `goodCompact_union`, mirroring
`vanishAbove_biUnion`. -/
theorem goodCompact_biUnion {ι : Type*} [DecidableEq ι] {n : ℕ} :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set ↑X),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧ goodCompact n (⋂ i ∈ t, K i)) →
      goodCompact n (⋃ i ∈ s, K i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro K hsub
      simpa using (hsub {a} (Finset.Subset.refl _) (Finset.singleton_nonempty a)).2
  | cons a s ha hs ih =>
      intro K hsub
      have hKa := hsub {a} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_self a s))
        (Finset.singleton_nonempty a)
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
      have hKac : IsClosed (K a) := by simpa using hKa.1
      have hKav : goodCompact n (K a) := by simpa using hKa.2
      refine goodCompact_union hKac ?_ hKav ?_ ?_
      · refine Set.Finite.isClosed_biUnion s.finite_toSet (fun i hi => ?_)
        have := hsub {i} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_of_mem hi))
          (Finset.singleton_nonempty i)
        simpa using this.1
      · exact ih K (fun t ht htne => hsub t (ht.trans (Finset.subset_cons ha)) htne)
      · have hdist : K a ∩ (⋃ i ∈ s, K i) = ⋃ i ∈ s, (K a ∩ K i) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
          constructor
          · rintro ⟨hxa, i, hi, hx⟩; exact ⟨i, hi, hxa, hx⟩
          · rintro ⟨i, hi, hxa, hx⟩; exact ⟨hxa, i, hi, hx⟩
        rw [hdist]
        refine ih (fun i => K a ∩ K i) (fun t ht htne => ?_)
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
        exact hsub (insert a t)
          (Finset.insert_subset (Finset.mem_cons_self a s) (ht.trans (Finset.subset_cons ha)))
          (Finset.insert_nonempty a t)

end SKEFTHawking.SingularGoodCompact
