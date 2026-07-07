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
import SKEFTHawking.SingularIntFundClassChartBall

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularGoodCompactInt

namespace SKEFTHawking.SingularTopHomologyFreeUnionInt

/-- **The `hfree` base case (chart ball)**: for a closed-ball chart neighbourhood
`K = (chartAt y₀).symm '' B̄(chartAt y₀·y₀, r)` (`0 ≤ r`, `B̄ ⊆ target`), the top relative homology
`H₄(M|K;ℤ)` is free. It is `≃+ ℤ` (`perEquivInt` — the chart-ball restriction is bijective at the
centre), hence free over ℤ. The atom-freeness the finite-union assembly `free_relHom_biUnion` consumes. -/
theorem free_relHom_chartBall {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (y₀ : M) {r : ℝ} (hr : 0 ≤ r)
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).target) :
    Module.Free ℤ (RelHomologyInt (X := TopCat.of M)
      ((chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r)ᶜ 4) := by
  have hy₀K : y₀ ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r :=
    ⟨chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀, Metric.mem_closedBall_self hr,
      (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).left_inv (mem_chart_source _ y₀)⟩
  exact Module.Free.of_equiv
    (SKEFTHawking.SingularIntFundClassChartBall.perEquivInt y₀ hrsub hy₀K).toIntLinearEquiv.symm

/-- **The dischargeable ball-freeness hypothesis** `HballFreeInt m M`: `H_{m+2}(M | closed chart-ball)`
is free for every closed chart-ball. Threaded through the CSC-PD tower in place of the FALSE
`∀-compact-S` `hfree` (freeness fails for wild compacts — a submodule of a product `∏ ℤ` need not be
free), because the tower only ever needs freeness at the good-compact cofinal `K'` = a finite union of
chart-balls. At `m = 2` (the 4-manifold) it is the THEOREM `free_relHom_chartBall` (`hballFreeInt_dim4`),
so the tower's freeness input is discharged unconditionally rather than posited. -/
def HballFreeInt (m : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] : Prop :=
  ∀ (y₀ : M) (ρ : ℝ), 0 ≤ ρ →
    Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) ρ
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).target →
    Module.Free ℤ (RelHomologyInt (X := TopCat.of M)
      ((chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) ρ)ᶜ (m + 2))

/-- **`HballFreeInt` is a theorem at `m = 2`** (the 4-manifold, `Fin 4`): every closed chart-ball has
free top relative homology, by `free_relHom_chartBall`. This discharges the tower's freeness hypothesis
unconditionally at the only dimension that matters for the 16-convergence. -/
theorem hballFreeInt_dim4 {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] : HballFreeInt 2 M :=
  fun y₀ _ρ hρ hsub => free_relHom_chartBall y₀ hρ hsub

variable {X : TopCat}

/-- **The `hfree` union step (Kaplansky-freeness)**: for closed `A`, `B` with `Hₙ(M|A;ℤ)`, `Hₙ(M|B;ℤ)`
free and `Hₙ₊₁(M|A∩B;ℤ) = 0`, the union homology `Hₙ(M|A∪B;ℤ)` is free. The integral relative MV
diagonal `relMvHomDiagInt Aᶜ Bᶜ n` is injective once `Hₙ₊₁(M|A∩B)=0`, embedding `Hₙ(M|A∪B)` into the free
product `Hₙ(M|A) × Hₙ(M|B)`; a submodule of a free ℤ-module is free (Kaplansky, arbitrary rank). -/
theorem free_relHom_union {n : ℕ} {A B : Set ↑X} (hA : IsClosed A) (hB : IsClosed B)
    (hVint : ∀ x : RelHomologyInt (Aᶜ ∪ Bᶜ) (n + 1), x = 0)
    (hfA : Module.Free ℤ (RelHomologyInt Aᶜ n))
    (hfB : Module.Free ℤ (RelHomologyInt Bᶜ n)) :
    Module.Free ℤ (RelHomologyInt (Aᶜ ∩ Bᶜ) n) := by
  haveI := hfA; haveI := hfB
  have hinj := SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt_injective_of_acyclic
    (M := X) hA.isOpen_compl hB.isOpen_compl n hVint
  haveI : Module.Free ℤ
      (LinearMap.range (SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt Aᶜ Bᶜ n)) :=
    SKEFTHawking.FreeSubmoduleInt.free_submodule_of_free _
  exact Module.Free.of_equiv
    (LinearEquiv.ofInjective (SKEFTHawking.SingularRelativeMVInt.relMvHomDiagInt Aᶜ Bᶜ n) hinj).symm

/-- **`hfree` finite-union assembly (Kaplansky-freeness)**: for a nonempty finite family `K i` (`i ∈ s`)
all of whose nonempty sub-intersections `⋂ i∈t, K i` are closed and `goodCompactInt n`, and each atom
`K i` has `Hₙ(M|K i;ℤ)` free, the union `Hₙ(M | ⋃ i∈s, K i; ℤ)` is free. Induction on `s` via
`free_relHom_union`, mirroring `goodCompactInt_biUnion` — the good-compact sub-intersections supply the
`Hₙ₊₁(M|A∩B)=0` vanishings the union step needs. -/
theorem free_relHom_biUnion {ι : Type*} [DecidableEq ι] {n : ℕ} :
    ∀ {s : Finset ι}, s.Nonempty → ∀ (K : ι → Set ↑X),
      (∀ t : Finset ι, t ⊆ s → t.Nonempty →
         IsClosed (⋂ i ∈ t, K i) ∧ goodCompactInt n (⋂ i ∈ t, K i)) →
      (∀ i ∈ s, Module.Free ℤ (RelHomologyInt (K i)ᶜ n)) →
      Module.Free ℤ (RelHomologyInt (⋃ i ∈ s, K i)ᶜ n) := by
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
      have hfreeKa : Module.Free ℤ (RelHomologyInt (K a)ᶜ n) :=
        hfg a (Finset.mem_cons_self a s)
      have hfreeUnion : Module.Free ℤ (RelHomologyInt (⋃ i ∈ s, K i)ᶜ n) :=
        ih K (fun t ht htne => hgc t (ht.trans (Finset.subset_cons ha)) htne)
          (fun i hi => hfg i (Finset.mem_cons_of_mem hi))
      -- Good-compactness of `K a ∩ ⋃ i∈s, K i = ⋃ i∈s, (K a ∩ K i)` (mirrors `goodCompactInt_biUnion`).
      have hdist : K a ∩ (⋃ i ∈ s, K i) = ⋃ i ∈ s, (K a ∩ K i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨hxa, i, hi, hx⟩; exact ⟨i, hi, hxa, hx⟩
        · rintro ⟨i, hi, hxa, hx⟩; exact ⟨hxa, i, hi, hx⟩
      have hgcInter : goodCompactInt n (K a ∩ ⋃ i ∈ s, K i) := by
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
      have hVint : ∀ x : RelHomologyInt ((K a)ᶜ ∪ (⋃ i ∈ s, K i)ᶜ) (n + 1), x = 0 := by
        rw [← Set.compl_inter]
        exact hgcInter.1 (n + 1) (by omega)
      rw [hUnion, Set.compl_union]
      exact free_relHom_union hKac hUnionClosed hVint hfreeKa hfreeUnion

end SKEFTHawking.SingularTopHomologyFreeUnionInt
