import Mathlib
import SKEFTHawking.SingularGoodCompactInt
import SKEFTHawking.SingularRelativeMVConnectingInt

/-!
# The integral finite-union closure of the "good compact" property (Hatcher 3.27, ℤ) — brick 18d

The ℤ analog of the mod-2 `SingularGoodCompact` finite-union closure. Assembles the union step of the
Hatcher 3.27 compactness induction over ℤ:

* `determinedByPointsInt_union` — the (b)-half MV induction step: given `determinedByPointsInt n A`,
  `determinedByPointsInt n B`, and the *vanishing* of `Hₙ₊₁(M|A∩B; ℤ)` (supplied as
  `vanishAboveInt n (A∩B)`), a class in `Hₙ(M|A∪B; ℤ)` restricting to `0` at every point of `A∪B` is
  `0`. Runs through the integral relative MV diagonal `relMvHomDiagInt Aᶜ Bᶜ n`, injective once
  `Hₙ₊₁(M|A∩B) = 0` (`relMvHomDiagInt_injective_of_acyclic`, brick 18c); both components vanish by
  `determinedByPointsInt A`/`B` via `restrictToPointInt_relInclInt`.

* `vanishAboveInt_union` — the (a)-half: `Hᵢ(M|K)=0` propagation, from the MV injectivity + vanishing
  target (the ℤ mirror of `vanishAbove_union` / `relInter_acyclic_of_acyclic`).

* `goodCompactInt_union` / `goodCompactInt_biUnion` — the finite-union closure, mirroring
  `goodCompact_union` / `goodCompact_biUnion`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt)
open SKEFTHawking.SingularGoodCompactInt

namespace SKEFTHawking.SingularGoodCompactUnionInt

variable {X : TopCat}

/-- **`relInclInt` of the diagonal `SingularRelativeMVInt.relInclInt` agrees with the point
`IntOrientationSection.relInclInt`.** Both are `RelHomologyInt.map id`, hence definitionally equal;
this bridge lets the MV diagonal components be read off as point-restriction inclusions. -/
theorem mvRelInclInt_eq_relInclInt {S T : Set ↑X} (h : S ⊆ T) (n : ℕ)
    (α : RelHomologyInt S n) :
    SKEFTHawking.SingularRelativeMVInt.relInclInt h n α = relInclInt h n α := rfl

/-- **Round-trip identity**: `relInclInt` over `S ⊆ T` then `T ⊆ S` (when the two sets are equal) is the
identity. Used to recover `α` from its image in `Hₙ(M | Aᶜ∩Bᶜ)` (`(A∪B)ᶜ = Aᶜ∩Bᶜ`). -/
theorem relInclInt_roundtrip {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S) (n : ℕ)
    (α : RelHomologyInt S n) :
    relInclInt hTS n (relInclInt hST n α) = α := by
  rw [relInclInt_trans]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  show relInclInt (hST.trans hTS) n (RelHomologyInt.mk S n z) = RelHomologyInt.mk S n z
  rw [show RelHomologyInt.mk S n z = Submodule.Quotient.mk z from rfl, relInclInt, RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  rw [relMapChainInt_id]

/-- **The (b)-half MV induction step** (Hatcher 3.27, ℤ): if `A`, `B` are closed and both are
determined-by-points in degree `n`, and `Hₙ₊₁(M|A∩B; ℤ) = 0` (`vanishAboveInt n (A∩B)`), then `A∪B` is
determined-by-points in degree `n`. -/
theorem determinedByPointsInt_union {n : ℕ} {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hDA : determinedByPointsInt n A) (hDB : determinedByPointsInt n B)
    (hVAB : vanishAboveInt n (A ∩ B)) : determinedByPointsInt n (A ∪ B) := by
  intro α hα
  -- Injectivity of the MV diagonal, available once `Hₙ₊₁(M|A∩B) = 0`.
  have hAcyc : ∀ x : RelHomologyInt (Aᶜ ∪ Bᶜ) (n + 1), x = 0 := by
    rw [← Set.compl_inter]
    exact hVAB (n + 1) (by omega)
  have hinj := SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt_injective_of_acyclic
    (M := X) hA.isOpen_compl hB.isOpen_compl n hAcyc
  have hle : (A ∪ B)ᶜ ⊆ Aᶜ ∩ Bᶜ := (Set.compl_union A B).le
  have hge : Aᶜ ∩ Bᶜ ⊆ (A ∪ B)ᶜ := (Set.compl_union A B).ge
  have hsubA : (A ∪ B)ᶜ ⊆ Aᶜ := Set.compl_subset_compl.mpr Set.subset_union_left
  have hsubB : (A ∪ B)ᶜ ⊆ Bᶜ := Set.compl_subset_compl.mpr Set.subset_union_right
  -- The two MV components of `relInclInt hle n α` vanish.
  have hzero : SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt Aᶜ Bᶜ n (relInclInt hle n α) = 0 := by
    apply Prod.ext
    · show SKEFTHawking.SingularRelativeMVInt.relInclInt Set.inter_subset_left n
        (relInclInt hle n α) = 0
      rw [mvRelInclInt_eq_relInclInt, relInclInt_trans]
      refine hDA _ (fun y hy => ?_)
      rw [restrictToPointInt_relInclInt Set.subset_union_left hy n α]
      exact hα y (Set.mem_union_left B hy)
    · show SKEFTHawking.SingularRelativeMVInt.relInclInt Set.inter_subset_right n
        (relInclInt hle n α) = 0
      rw [mvRelInclInt_eq_relInclInt, relInclInt_trans]
      refine hDB _ (fun y hy => ?_)
      rw [restrictToPointInt_relInclInt Set.subset_union_right hy n α]
      exact hα y (Set.mem_union_right A hy)
  -- Injectivity forces `relInclInt hle n α = 0`; the round-trip recovers `α = 0`.
  have hle0 : relInclInt hle n α = 0 := hinj (by rw [hzero, map_zero])
  have hback : relInclInt hge n (relInclInt hle n α) = α := relInclInt_roundtrip hle hge n α
  rw [hle0, map_zero] at hback
  exact hback.symm

/-- **Integral MV vanishing propagation**: if both `Hₖ₊₁(M | A) = 0` and `Hₖ₊₁(M | B) = 0`, and
`Hₖ₊₂(M | A∩B) = 0`, then `Hₖ₊₁(M | A∪B) = 0`. In the `U = M∖A`, `V = M∖B` form: `Hₖ₊₁(M, U∩V) = 0`
follows because `relMvHomDiagInt` is injective (gluing) and its target vanishes. -/
theorem relInterInt_acyclic_of_acyclic {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B) (k : ℕ)
    (hUV : ∀ x : RelHomologyInt (Aᶜ ∪ Bᶜ) (k + 1 + 1), x = 0)
    (hU' : ∀ x : RelHomologyInt (Aᶜ) (k + 1), x = 0)
    (hV' : ∀ x : RelHomologyInt (Bᶜ) (k + 1), x = 0) :
    ∀ x : RelHomologyInt (Aᶜ ∩ Bᶜ) (k + 1), x = 0 := by
  intro x
  have hinj := SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt_injective_of_acyclic
    (M := X) hA.isOpen_compl hB.isOpen_compl (k + 1) hUV
  refine (injective_iff_map_eq_zero _).mp hinj x ?_
  exact Prod.ext (hU' _) (hV' _)

/-- **Integral vanishing is closed under union**: `vanishAboveInt n A`, `vanishAboveInt n B`,
`vanishAboveInt n (A∩B)` imply `vanishAboveInt n (A∪B)`. -/
theorem vanishAboveInt_union {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B) {n : ℕ}
    (hVA : vanishAboveInt n A) (hVB : vanishAboveInt n B) (hVAB : vanishAboveInt n (A ∩ B)) :
    vanishAboveInt n (A ∪ B) := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Set.compl_union]
  refine relInterInt_acyclic_of_acyclic hA hB k ?_ ?_ ?_
  · rw [← Set.compl_inter]; exact hVAB (k + 1 + 1) (by omega)
  · exact hVA (k + 1) (by omega)
  · exact hVB (k + 1) (by omega)

/-- **`goodCompactInt` is closed under union**: combine `vanishAboveInt_union` and
`determinedByPointsInt_union` (the latter using `hgAB.1 : vanishAboveInt n (A∩B)`). -/
theorem goodCompactInt_union {n : ℕ} {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hgA : goodCompactInt n A) (hgB : goodCompactInt n B) (hgAB : goodCompactInt n (A ∩ B)) :
    goodCompactInt n (A ∪ B) :=
  ⟨vanishAboveInt_union hA hB hgA.1 hgB.1 hgAB.1,
   determinedByPointsInt_union hA hB hgA.2 hgB.2 hgAB.1⟩

/-- **Finite-union integral good-compactness** (Hatcher 3.27, ℤ): for a nonempty finite family `K i`
(`i ∈ s`) all of whose nonempty sub-intersections `⋂ i∈t, K i` (`∅ ≠ t ⊆ s`) are closed and
`goodCompactInt n`, the union `⋃ i∈s, K i` is `goodCompactInt n`. Induction on `s` via
`goodCompactInt_union`. -/
theorem goodCompactInt_biUnion {ι : Type*} [DecidableEq ι] {n : ℕ} :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set ↑X),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧ goodCompactInt n (⋂ i ∈ t, K i)) →
      goodCompactInt n (⋃ i ∈ s, K i) := by
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
      have hKav : goodCompactInt n (K a) := by simpa using hKa.2
      refine goodCompactInt_union hKac ?_ hKav ?_ ?_
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

end SKEFTHawking.SingularGoodCompactUnionInt
