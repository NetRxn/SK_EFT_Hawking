/-
# Phase 5q.H (E1 CSC-PD tower) — `hfree` union step + finite-union assembly (Kaplansky-freeness)

The top relative homology `H₄(M|K;ℤ)` of a good-compact is FREE, assembled inductively over a finite
chart cover. The MV diagonal `relMvHomDiagInt Aᶜ Bᶜ 4 : H₄(M|A∪B) → H₄(M|A) × H₄(M|B)` is INJECTIVE once
`H₅(M|A∩B) = 0` (`vanishAboveInt 4 (A∩B)` — the good-compact high-degree vanishing), so `H₄(M|A∪B)`
embeds as a submodule of the free product `H₄(M|A) × H₄(M|B)` and is therefore FREE by Kaplansky
(`free_submodule_of_free`, arbitrary rank — NO finite-generation needed). This propagates freeness through
`goodCompactInt_biUnion` verbatim, reducing `hfree` to the base-case freeness of the cover atoms.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularTopHomologyFreeInt
import SKEFTHawking.SingularGoodCompactUnionInt
import SKEFTHawking.FreeSubmoduleOfFreeInt

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularGoodCompactInt

namespace SKEFTHawking.SingularTopHomologyFreeUnionInt

variable {X : TopCat}

/-- **The `hfree` union step (Kaplansky-freeness)**: for closed `A`, `B` with `H₄(M|A;ℤ)`, `H₄(M|B;ℤ)`
free and `H₅(M|A∩B;ℤ) = 0`, the union top-homology `H₄(M|A∪B;ℤ)` is free. The integral relative MV
diagonal `relMvHomDiagInt Aᶜ Bᶜ 4` is injective once `H₅(M|A∩B)=0`, embedding `H₄(M|A∪B)` into the free
product `H₄(M|A) × H₄(M|B)`; a submodule of a free ℤ-module is free (Kaplansky, arbitrary rank). -/
theorem free_relHom_union {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hVint : ∀ x : RelHomologyInt (Aᶜ ∪ Bᶜ) (4 + 1), x = 0)
    (hfA : Module.Free ℤ (RelHomologyInt Aᶜ 4))
    (hfB : Module.Free ℤ (RelHomologyInt Bᶜ 4)) :
    Module.Free ℤ (RelHomologyInt (Aᶜ ∩ Bᶜ) 4) := by
  haveI := hfA; haveI := hfB
  have hinj := SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt_injective_of_acyclic
    (M := X) hA.isOpen_compl hB.isOpen_compl 4 hVint
  haveI : Module.Free ℤ
      (LinearMap.range (SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt Aᶜ Bᶜ 4)) :=
    SKEFTHawking.FreeSubmoduleInt.free_submodule_of_free _
  exact Module.Free.of_equiv
    (LinearEquiv.ofInjective (SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt Aᶜ Bᶜ 4) hinj).symm

/-- **`hfree` finite-union assembly (Kaplansky-freeness)**: for a nonempty finite family `K i` (`i ∈ s`)
all of whose nonempty sub-intersections `⋂ i∈t, K i` are closed and `goodCompactInt 4`, and each atom
`K i` has `H₄(M|K i;ℤ)` free, the union `H₄(M | ⋃ i∈s, K i; ℤ)` is free. Induction on `s` via
`free_relHom_union`, mirroring `goodCompactInt_biUnion` — the good-compact sub-intersections supply the
`H₅(M|A∩B)=0` vanishings the union step needs. -/
theorem free_relHom_biUnion {ι : Type*} [DecidableEq ι] :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set ↑X),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧ goodCompactInt 4 (⋂ i ∈ t, K i)) →
      (∀ i ∈ s, Module.Free ℤ (RelHomologyInt (K i)ᶜ 4)) →
      Module.Free ℤ (RelHomologyInt (⋃ i ∈ s, K i)ᶜ 4) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro K hgc hfg
      have hUnion : (⋃ i ∈ ({a} : Finset ι), K i) = K a := by simp
      rw [hUnion]
      exact hfg a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
      intro K hgc hfg
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
      -- `K a` is closed and free; the rest-union is free by IH; their intersection is good-compact.
      have hKa := hgc {a} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_self a s))
        (Finset.singleton_nonempty a)
      have hKac : IsClosed (K a) := by simpa using hKa.1
      have hUnionClosed : IsClosed (⋃ i ∈ s, K i) := by
        refine Set.Finite.isClosed_biUnion s.finite_toSet (fun i hi => ?_)
        have := hgc {i} (Finset.singleton_subset_iff.mpr (Finset.mem_cons_of_mem hi))
          (Finset.singleton_nonempty i)
        simpa using this.1
      have hfreeKa : Module.Free ℤ (RelHomologyInt (K a)ᶜ 4) :=
        hfg a (Finset.mem_cons_self a s)
      have hfreeUnion : Module.Free ℤ (RelHomologyInt (⋃ i ∈ s, K i)ᶜ 4) :=
        ih K (fun t ht htne => hgc t (ht.trans (Finset.subset_cons ha)) htne)
          (fun i hi => hfg i (Finset.mem_cons_of_mem hi))
      -- Good-compactness of `K a ∩ ⋃ i∈s, K i = ⋃ i∈s, (K a ∩ K i)` (mirrors `goodCompactInt_biUnion`).
      have hdist : K a ∩ (⋃ i ∈ s, K i) = ⋃ i ∈ s, (K a ∩ K i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨hxa, i, hi, hx⟩; exact ⟨i, hi, hxa, hx⟩
        · rintro ⟨i, hi, hxa, hx⟩; exact ⟨hxa, i, hi, hx⟩
      have hgcInter : goodCompactInt 4 (K a ∩ ⋃ i ∈ s, K i) := by
        rw [hdist]
        refine SKEFTHawking.SingularGoodCompactUnionInt.goodCompactInt_biUnion hs
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
      -- The `H₅(M|A∩B)=0` the union step needs, in the `Aᶜ ∪ Bᶜ` form.
      have hVint : ∀ x : RelHomologyInt ((K a)ᶜ ∪ (⋃ i ∈ s, K i)ᶜ) (4 + 1), x = 0 := by
        rw [← Set.compl_inter]
        exact hgcInter.1 (4 + 1) (by omega)
      rw [hUnion, Set.compl_union]
      exact free_relHom_union hKac hUnionClosed hVint hfreeKa hfreeUnion

end SKEFTHawking.SingularTopHomologyFreeUnionInt
