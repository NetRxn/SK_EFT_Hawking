/-
# Phase 5q.F — disjoint-union additivity of singular ℤ/2 cohomology (toward ξ_Pin⁺'s `sumStr`)

The faithful Pin⁺ `TangentialData`'s `sumStr` combines structures `σ ∈ H¹(s)`, `τ ∈ H¹(t)` into
`H¹(s ⊔ t)`; that needs the additivity `H¹(A ⊔ B) ≅ H¹(A) × H¹(B)`. The geometric heart is that a
singular simplex of `A ⊕ B` — a continuous map from the (convex, hence preconnected) standard simplex —
factors through `Sum.inl` or `Sum.inr`. This module builds that factoring, giving the simplex-level
decomposition `(toSSet (A ⊕ B))ₙ ≃ (toSSet A)ₙ ⊕ (toSSet B)ₙ`.
-/
import SKEFTHawking.SingularCohomologyFunctorial

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite Topology

/-- **A continuous map from a preconnected space to a sum factors through one inclusion.** The range is
preconnected and contained in the disjoint clopen sets `range inl`, `range inr`, so it lies in one. -/
theorem continuous_to_sum_factor {D α β : Type*} [TopologicalSpace D] [PreconnectedSpace D]
    [TopologicalSpace α] [TopologicalSpace β] (f : C(D, α ⊕ β)) :
    (Set.range f ⊆ Set.range (Sum.inl : α → α ⊕ β)) ∨
      (Set.range f ⊆ Set.range (Sum.inr : β → α ⊕ β)) := by
  have hpc : IsPreconnected (Set.range f) := isPreconnected_range f.continuous
  refine hpc.subset_or_subset isOpen_range_inl isOpen_range_inr ?_ ?_
  · rw [Set.disjoint_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    exact (Sum.inr_ne_inl hb).elim
  · rintro x -
    rcases x with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

/-- The continuous `α`-factor of `f : C(D, α ⊕ β)` whose range lies in `range inl`: `inl ∘ g = f`. -/
noncomputable def factorLeft {D α β : Type*} [TopologicalSpace D] [TopologicalSpace α]
    [TopologicalSpace β] (f : C(D, α ⊕ β)) (h : Set.range f ⊆ Set.range (Sum.inl : α → α ⊕ β)) :
    C(D, α) where
  toFun d := (Equiv.ofInjective _ Sum.inl_injective).symm ⟨f d, h ⟨d, rfl⟩⟩
  continuous_toFun := by
    rw [(Topology.IsEmbedding.inl (X := α) (Y := β)).continuous_iff]
    refine f.continuous.congr (fun d => ?_)
    have := (Equiv.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective).apply_symm_apply
      ⟨f d, h ⟨d, rfl⟩⟩
    exact (congrArg Subtype.val this).symm

@[simp] theorem inl_factorLeft {D α β : Type*} [TopologicalSpace D] [TopologicalSpace α]
    [TopologicalSpace β] (f : C(D, α ⊕ β)) (h : Set.range f ⊆ Set.range (Sum.inl : α → α ⊕ β))
    (d : D) : Sum.inl (factorLeft f h d) = f d := by
  have := (Equiv.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective).apply_symm_apply
    ⟨f d, h ⟨d, rfl⟩⟩
  exact congrArg Subtype.val this

/-- The continuous `β`-factor of `f : C(D, α ⊕ β)` whose range lies in `range inr`: `inr ∘ g = f`. -/
noncomputable def factorRight {D α β : Type*} [TopologicalSpace D] [TopologicalSpace α]
    [TopologicalSpace β] (f : C(D, α ⊕ β)) (h : Set.range f ⊆ Set.range (Sum.inr : β → α ⊕ β)) :
    C(D, β) where
  toFun d := (Equiv.ofInjective _ Sum.inr_injective).symm ⟨f d, h ⟨d, rfl⟩⟩
  continuous_toFun := by
    rw [(Topology.IsEmbedding.inr (X := α) (Y := β)).continuous_iff]
    refine f.continuous.congr (fun d => ?_)
    have := (Equiv.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective).apply_symm_apply
      ⟨f d, h ⟨d, rfl⟩⟩
    exact (congrArg Subtype.val this).symm

@[simp] theorem inr_factorRight {D α β : Type*} [TopologicalSpace D] [TopologicalSpace α]
    [TopologicalSpace β] (f : C(D, α ⊕ β)) (h : Set.range f ⊆ Set.range (Sum.inr : β → α ⊕ β))
    (d : D) : Sum.inr (factorRight f h d) = f d := by
  have := (Equiv.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective).apply_symm_apply
    ⟨f d, h ⟨d, rfl⟩⟩
  exact congrArg Subtype.val this

end SKEFTHawking.SingularCohomologyMod2
