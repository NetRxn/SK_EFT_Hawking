import Mathlib
import SKEFTHawking.SingularCSCOpenMonotone

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6d-ii) — the compactly-supported cohomology MV maps

The maps of the compactly-supported-cohomology Mayer–Vietoris sequence for opens `U`, `V`,
  `Hᵏ_c(U∩V) --Δ--> Hᵏ_c(U) ⊕ Hᵏ_c(V) --Σ--> Hᵏ_c(U∪V)`,
built from the open-monotone (extension-by-zero) maps `cscOpenMonotone`:
* `Δ = (mono_{U∩V⊆U}, mono_{U∩V⊆V})` (the diagonal of restrictions);
* `Σ = mono_{U⊆U∪V}∘fst − mono_{V⊆U∪V}∘snd` (the difference).
The composite `Σ ∘ Δ = 0` is immediate from functoriality (`cscOpenMonotone_comp`): both terms equal
`mono_{U∩V⊆U∪V}` and cancel. This is the `⊇`-half / the chain-complex condition of the colim-MV; the
substantive **middle exactness** (`ker Σ ⊆ range Δ`) is built separately (the duality `5`-lemma's top row).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularCSCOpenMonotone

namespace SKEFTHawking.SingularCSCMayerVietoris

variable {M : TopCat}

/-- **The MV diagonal** `Δ : Hᵏ_c(U∩V) → Hᵏ_c(U) ⊕ Hᵏ_c(V)`, the pair of extension-by-zero maps from the
intersection. -/
noncomputable def cscMvDiag (U V : Set ↑M) (k : ℕ) :
    CompactlySupportedCohomologyOpen (U ∩ V) k →ₗ[ZMod 2]
      CompactlySupportedCohomologyOpen U k × CompactlySupportedCohomologyOpen V k :=
  (cscOpenMonotone Set.inter_subset_left k).prod (cscOpenMonotone Set.inter_subset_right k)

/-- **The MV difference** `Σ : Hᵏ_c(U) ⊕ Hᵏ_c(V) → Hᵏ_c(U∪V)`, `(α, β) ↦ ext α − ext β`. -/
noncomputable def cscMvSum (U V : Set ↑M) (k : ℕ) :
    CompactlySupportedCohomologyOpen U k × CompactlySupportedCohomologyOpen V k →ₗ[ZMod 2]
      CompactlySupportedCohomologyOpen (U ∪ V) k :=
  (cscOpenMonotone Set.subset_union_left k).comp (LinearMap.fst _ _ _)
    - (cscOpenMonotone Set.subset_union_right k).comp (LinearMap.snd _ _ _)

/-- **`Σ ∘ Δ = 0`** — the chain-complex condition of the compactly-supported-cohomology MV: both
composites are `mono_{U∩V⊆U∪V}` (functoriality `cscOpenMonotone_comp`) and cancel. -/
theorem cscMvSum_comp_cscMvDiag (U V : Set ↑M) (k : ℕ) :
    (cscMvSum U V k).comp (cscMvDiag U V k) = 0 := by
  ext x
  show cscOpenMonotone Set.subset_union_left k (cscOpenMonotone Set.inter_subset_left k x)
      - cscOpenMonotone Set.subset_union_right k (cscOpenMonotone Set.inter_subset_right k x) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, cscOpenMonotone_comp, cscOpenMonotone_comp]
  exact sub_eq_zero.mpr rfl

end SKEFTHawking.SingularCSCMayerVietoris
