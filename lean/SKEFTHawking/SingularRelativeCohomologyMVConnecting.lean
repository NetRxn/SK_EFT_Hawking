import Mathlib
import SKEFTHawking.SingularRelativeKroneckerEquiv
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularRelativeCohomologyMV
import SKEFTHawking.SingularDualityMVAdjoint
import SKEFTHawking.SingularUniversalCoeff

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-b2) — the relative cohomology MV connecting map

The connecting map of the relative cohomology Mayer–Vietoris long exact sequence
  `Hᵏ(M|A∩B) --δ--> Hᵏ⁺¹(M|A∪B)`
is built by **`dualMap`-conjugation** of the *homology* MV connecting map
`SingularRelativeMV.relMvDelta : Hₖ₊₁(M|A∪B) → Hₖ(M|A∩B)` through the perfect Kronecker pairing
`SingularRelativeKroneckerEquiv.relKroneckerHEquiv` (`Hᵏ(M,S) ≃ (Hₖ(M,S))^*`, finite-dim-free over `ℤ/2`):
  `δ := relKroneckerHEquiv(U∪V)⁻¹ ∘ (relMvDelta)^* ∘ relKroneckerHEquiv(U∩V)`.
This sidesteps the contravariant small-simplices/excision program that a direct cochain-level connecting
map would need (`SingularRelativeCohomologyMVExact` note) — the homology connecting map already exists.

The defining property is the **adjunction** `⟨δ ω, w⟩_{U∪V} = ⟨ω, relMvDelta w⟩_{U∩V}` (`relKroneckerH`
pairing), which holds essentially by construction and is the only interface the cohomology-MV exactness
transfer uses. Completes the top row of the Poincaré-duality `5`-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularRelativeCohomologyMV SKEFTHawking.SingularRelativeKroneckerEquiv
  SKEFTHawking.SingularRelativeCohomologyRestrict SKEFTHawking.SingularDualityAdjoint
  SKEFTHawking.SingularDualityMVAdjoint SKEFTHawking.SingularUniversalCoeff
  SKEFTHawking.SingularRelativeUC SKEFTHawking.SingularRelativeUCSurj

namespace SKEFTHawking.SingularRelativeCohomologyMVConnecting

variable {M : TopCat}

/-- **The relative cohomology MV connecting map** `δ : Hᵏ(M|A∩B) → Hᵏ⁺¹(M|A∪B)` (`k = N+1`), the
`dualMap`-conjugate of the homology connecting `relMvDelta` through the perfect Kronecker pairing. -/
noncomputable def relCohomMvConnecting (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ) :
    RelativeCohomology (U ∩ V) (N + 1) →ₗ[ZMod 2] RelativeCohomology (U ∪ V) (N + 2) :=
  (relKroneckerHEquiv (U ∪ V) (N + 1)).symm.toLinearMap ∘ₗ
    (relMvDelta U V hU hV (N + 1)).dualMap ∘ₗ
    (relKroneckerHEquiv (U ∩ V) N).toLinearMap

/-- **The defining adjunction of the cohomology MV connecting map**:
`⟨δ ω, w⟩_{U∪V} = ⟨ω, relMvDelta w⟩_{U∩V}`. The sole interface to `relCohomMvConnecting` used downstream
(exactness transfer + cap-naturality). -/
theorem relKroneckerH_relCohomMvConnecting (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (ω : RelativeCohomology (U ∩ V) (N + 1)) (w : RelativeHomology (U ∪ V) (N + 2)) :
    relKroneckerH (U ∪ V) (relCohomMvConnecting U V hU hV N ω) w
      = relKroneckerH (U ∩ V) ω (relMvDelta U V hU hV (N + 1) w) := by
  rw [relCohomMvConnecting, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, relKroneckerH_symm, LinearMap.dualMap_apply, relKroneckerHEquiv_apply]

/-! ## The cochain-complex conditions (`δ∘Σ = 0`, `Δ∘δ = 0`) -/

/-- **`δ ∘ Σ = 0`**: the cohomology MV connecting map kills the image of the MV sum. Dual to the homology
`relMvHomDiag ∘ relMvDelta = 0`: `⟨δ(Σ(α,β)), w⟩ = ⟨α,(relMvHomDiag(δ_hom w)).1⟩ + ⟨β,…⟩ = 0`. -/
theorem relCohomMvConnecting_relCohomMvSum (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ}
    (α : RelativeCohomology U (N + 1)) (β : RelativeCohomology V (N + 1)) :
    relCohomMvConnecting U V hU hV N (relCohomMvSum U V (N + 1) (α, β)) = 0 := by
  refine relCohomology_eq_zero_of_relKroneckerH (U ∪ V) _ (fun w => ?_)
  rw [relKroneckerH_relCohomMvConnecting, relKroneckerH_relCohomMvSum]
  have h0 : relMvHomDiag U V (N + 1) (relMvDelta U V hU hV (N + 1) w) = 0 :=
    (relMv_exact_connecting' U V hU hV (N + 1) _).mpr ⟨w, rfl⟩
  have h1 : relIncl Set.inter_subset_left (N + 1) (relMvDelta U V hU hV (N + 1) w) = 0 := by
    have := congrArg Prod.fst h0; simpa [relMvHomDiag] using this
  have h2 : relIncl Set.inter_subset_right (N + 1) (relMvDelta U V hU hV (N + 1) w) = 0 := by
    have := congrArg Prod.snd h0; simpa [relMvHomDiag] using this
  rw [h1, h2, map_zero, map_zero, add_zero]

/-- **`Δ ∘ δ = 0`**: the cohomology MV diagonal kills the image of the connecting map. Dual to the homology
`relMvDelta ∘ relMvHomSum = 0` (`relMv_exact_sum'`): each restriction of `δω` pairs to `0`. -/
theorem relCohomMvDiag_relCohomMvConnecting (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ}
    (ω : RelativeCohomology (U ∩ V) (N + 1)) :
    relCohomMvDiag U V (N + 2) (relCohomMvConnecting U V hU hV N ω) = 0 := by
  rw [relCohomMvDiag_apply, Prod.mk_eq_zero]
  constructor
  · refine relCohomology_eq_zero_of_relKroneckerH U _ (fun x => ?_)
    rw [relKroneckerH_relCohomRestrict', relKroneckerH_relCohomMvConnecting]
    have hsum : relIncl Set.subset_union_left (N + 2) x = relMvHomSum U V (N + 2) (x, 0) := by
      rw [relMvHomSum, LinearMap.coprod_apply, map_zero, add_zero]
    rw [hsum, show relMvDelta U V hU hV (N + 1) (relMvHomSum U V (N + 2) (x, 0)) = 0 from
      (relMv_exact_sum' U V hU hV (N + 1) _).mpr ⟨(x, 0), rfl⟩, map_zero]
  · refine relCohomology_eq_zero_of_relKroneckerH V _ (fun y => ?_)
    rw [relKroneckerH_relCohomRestrict', relKroneckerH_relCohomMvConnecting]
    have hsum : relIncl Set.subset_union_right (N + 2) y = relMvHomSum U V (N + 2) (0, y) := by
      rw [relMvHomSum, LinearMap.coprod_apply, map_zero, zero_add]
    rw [hsum, show relMvDelta U V hU hV (N + 1) (relMvHomSum U V (N + 2) (0, y)) = 0 from
      (relMv_exact_sum' U V hU hV (N + 1) _).mpr ⟨(0, y), rfl⟩, map_zero]

/-! ## Cohomology MV exactness at `Hᵏ(M|A∩B)` (`range Σ = ker δ`) -/

/-- **Relative cohomology MV exactness at `Hᵏ(M|A∩B)`** (`k = N+1`): `range Σ = ker δ`, by duality-transfer
of `SingularRelativeMV.relMv_exact_connecting'`. The diag-term exactness of the cohomology MV LES. -/
theorem relCohomMv_exact_sum (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (relCohomMvSum U V (N + 1)) (relCohomMvConnecting U V hU hV N) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun η hη => ?_) ?_
  · -- ker δ ⊆ range Σ
    rw [LinearMap.mem_ker] at hη
    have hker : LinearMap.ker (relMvHomDiag U V (N + 1))
        ≤ LinearMap.ker (relKroneckerH (U ∩ V) η) := by
      intro c hc
      rw [LinearMap.mem_ker] at hc ⊢
      obtain ⟨w, rfl⟩ := (relMv_exact_connecting' U V hU hV (N + 1) c).mp hc
      rw [← relKroneckerH_relCohomMvConnecting, hη, map_zero, LinearMap.zero_apply]
    obtain ⟨g, hg⟩ :=
      exists_factor_of_ker_le_ker (relMvHomDiag U V (N + 1)) (relKroneckerH (U ∩ V) η) hker
    obtain ⟨α, hα⟩ := relKroneckerH_surjective_field U
      (g ∘ₗ LinearMap.inl (ZMod 2) (RelativeHomology U (N + 1)) (RelativeHomology V (N + 1)))
    obtain ⟨β, hβ⟩ := relKroneckerH_surjective_field V
      (g ∘ₗ LinearMap.inr (ZMod 2) (RelativeHomology U (N + 1)) (RelativeHomology V (N + 1)))
    have hsplit : ∀ (a : RelativeHomology U (N + 1)) (b : RelativeHomology V (N + 1)),
        relKroneckerH U α a + relKroneckerH V β b = g (a, b) := by
      intro a b
      rw [hα, hβ, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
      congr 1
      apply Prod.ext <;> simp
    refine ⟨(α, β), ?_⟩
    refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (U ∩ V)
      (relCohomMvSum U V (N + 1) (α, β) - η) (fun c => ?_))
    rw [map_sub, LinearMap.sub_apply, relKroneckerH_relCohomMvSum, hsplit,
      show (relIncl Set.inter_subset_left (N + 1) c, relIncl Set.inter_subset_right (N + 1) c)
        = relMvHomDiag U V (N + 1) c from rfl,
      show g (relMvHomDiag U V (N + 1) c) = relKroneckerH (U ∩ V) η c from LinearMap.congr_fun hg c,
      sub_self]
  · -- range Σ ⊆ ker δ
    rintro p ⟨q, rfl⟩
    obtain ⟨α, β⟩ := q
    rw [LinearMap.mem_ker, relCohomMvConnecting_relCohomMvSum]

/-! ## Cohomology MV exactness at `Hᵏ⁺¹(M|A∪B)` (`range δ = ker Δ`) -/

/-- **Relative cohomology MV exactness at `Hᵏ⁺¹(M|A∪B)`** (`k = N+1`): `range δ = ker Δ`, by
duality-transfer of `SingularRelativeMV.relMv_exact_sum'`. The union-term exactness of the cohomology MV
LES — with `relCohomMv_exact_middle` and `relCohomMv_exact_sum`, the full top row of the PD `5`-lemma. -/
theorem relCohomMv_exact_connecting (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (relCohomMvConnecting U V hU hV N) (relCohomMvDiag U V (N + 2)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun ζ hζ => ?_) ?_
  · -- ker Δ ⊆ range δ
    rw [LinearMap.mem_ker, relCohomMvDiag_apply, Prod.mk_eq_zero] at hζ
    obtain ⟨hresU, hresV⟩ := hζ
    have hζU : ∀ x, relKroneckerH (U ∪ V) ζ (relIncl Set.subset_union_left (N + 2) x) = 0 := by
      intro x
      rw [← relKroneckerH_relCohomRestrict', hresU, map_zero, LinearMap.zero_apply]
    have hζV : ∀ y, relKroneckerH (U ∪ V) ζ (relIncl Set.subset_union_right (N + 2) y) = 0 := by
      intro y
      rw [← relKroneckerH_relCohomRestrict', hresV, map_zero, LinearMap.zero_apply]
    have hker : LinearMap.ker (relMvDelta U V hU hV (N + 1))
        ≤ LinearMap.ker (relKroneckerH (U ∪ V) ζ) := by
      intro w hw
      rw [LinearMap.mem_ker] at hw ⊢
      obtain ⟨⟨x, y⟩, rfl⟩ := (relMv_exact_sum' U V hU hV (N + 1) w).mp hw
      rw [relMvHomSum, LinearMap.coprod_apply, map_add, hζU x, hζV y, add_zero]
    obtain ⟨ψ, hψ⟩ :=
      exists_factor_of_ker_le_ker (relMvDelta U V hU hV (N + 1)) (relKroneckerH (U ∪ V) ζ) hker
    obtain ⟨ω, hω⟩ := relKroneckerH_surjective_field (U ∩ V) ψ
    refine ⟨ω, ?_⟩
    refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (U ∪ V)
      (relCohomMvConnecting U V hU hV N ω - ζ) (fun w => ?_))
    rw [map_sub, LinearMap.sub_apply, relKroneckerH_relCohomMvConnecting, hω,
      show ψ (relMvDelta U V hU hV (N + 1) w) = relKroneckerH (U ∪ V) ζ w
        from LinearMap.congr_fun hψ w, sub_self]
  · -- range δ ⊆ ker Δ
    rintro p ⟨ω, rfl⟩
    rw [LinearMap.mem_ker, relCohomMvDiag_relCohomMvConnecting]

end SKEFTHawking.SingularRelativeCohomologyMVConnecting
