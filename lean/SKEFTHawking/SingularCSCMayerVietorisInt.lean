import Mathlib
import SKEFTHawking.SingularCSCOpenMonotoneInt

/-!
# Phase 5q.H (E1 CSC-PD tower) — the integral compactly-supported cohomology MV maps

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCMayerVietoris`.

The maps of the integral compactly-supported-cohomology Mayer–Vietoris sequence for opens `U`, `V`,
  `Hᵏ_c(U∩V;ℤ) --Δ--> Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ) --Σ--> Hᵏ_c(U∪V;ℤ)`,
built from the integral open-monotone (extension-by-zero) maps `cscOpenMonotoneInt`:
* `Δ = (mono_{U∩V⊆U}, mono_{U∩V⊆V})` (the diagonal of restrictions);
* `Σ = mono_{U⊆U∪V}∘fst − mono_{V⊆U∪V}∘snd` (the difference).
The composite `Σ ∘ Δ = 0` is immediate from functoriality (`cscOpenMonotoneInt_comp`): both terms equal
`mono_{U∩V⊆U∪V}` and cancel. This is the `⊇`-half / the chain-complex condition of the colim-MV; the
substantive **middle exactness** (`ker Σ ⊆ range Δ`) is built separately (the integral duality
`5`-lemma's top row).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCompactlySupportedOpenInt SKEFTHawking.SingularCSCOpenMonotoneInt
  SKEFTHawking.SingularCompactsInOpen

namespace SKEFTHawking.SingularCSCMayerVietorisInt

variable {M : TopCat}

/-- **The integral MV diagonal** `Δ : Hᵏ_c(U∩V;ℤ) → Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ)`, the pair of
extension-by-zero maps from the intersection. -/
noncomputable def cscMvDiagInt (U V : Set ↑M) (k : ℕ) :
    CompactlySupportedCohomologyOpenInt (U ∩ V) k →ₗ[ℤ]
      CompactlySupportedCohomologyOpenInt U k × CompactlySupportedCohomologyOpenInt V k :=
  (cscOpenMonotoneInt Set.inter_subset_left k).prod (cscOpenMonotoneInt Set.inter_subset_right k)

/-- **The integral MV difference** `Σ : Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ) → Hᵏ_c(U∪V;ℤ)`, `(α, β) ↦ ext α − ext β`. -/
noncomputable def cscMvSumInt (U V : Set ↑M) (k : ℕ) :
    CompactlySupportedCohomologyOpenInt U k × CompactlySupportedCohomologyOpenInt V k →ₗ[ℤ]
      CompactlySupportedCohomologyOpenInt (U ∪ V) k :=
  (cscOpenMonotoneInt Set.subset_union_left k).comp (LinearMap.fst _ _ _)
    - (cscOpenMonotoneInt Set.subset_union_right k).comp (LinearMap.snd _ _ _)

/-- **`Σ ∘ Δ = 0`** — the chain-complex condition of the integral compactly-supported-cohomology MV: both
composites are `mono_{U∩V⊆U∪V}` (functoriality `cscOpenMonotoneInt_comp`) and cancel. -/
theorem cscMvSumInt_comp_cscMvDiagInt (U V : Set ↑M) (k : ℕ) :
    (cscMvSumInt U V k).comp (cscMvDiagInt U V k) = 0 := by
  ext x
  show cscOpenMonotoneInt Set.subset_union_left k (cscOpenMonotoneInt Set.inter_subset_left k x)
      - cscOpenMonotoneInt Set.subset_union_right k (cscOpenMonotoneInt Set.inter_subset_right k x) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, cscOpenMonotoneInt_comp, cscOpenMonotoneInt_comp]
  exact sub_eq_zero.mpr rfl

/-- **Computation rule for the integral MV diagonal** on a `K`-stage class `of_{U∩V}(K, g)`: `Δ` extends it
to the two `K`-stage classes over `U` and `V` (the same underlying compact `K`, included into
`CompactsIn U` / `CompactsIn V`). -/
@[simp] theorem cscMvDiagInt_of (U V : Set ↑M) (k : ℕ) (K : CompactsIn (U ∩ V))
    (g : cohomGWInt (U ∩ V) k K) :
    cscMvDiagInt U V k
        (Module.DirectLimit.of ℤ (CompactsIn (U ∩ V)) (cohomGWInt (U ∩ V) k) (cohomFWInt (U ∩ V) k) K g)
      = (Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U k) (cohomFWInt U k)
            (compactsInIncl Set.inter_subset_left K) g,
          Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V k) (cohomFWInt V k)
            (compactsInIncl Set.inter_subset_right K) g) := by
  rw [cscMvDiagInt, LinearMap.prod_apply]
  -- `Function.prod_def` is a deprecated alias with no equation theorems; only `simp only` with the
  -- real def's lemma pierces it.
  simp only [Function.prod_def]
  rw [ cscOpenMonotoneInt_of, cscOpenMonotoneInt_of]
  rfl

end SKEFTHawking.SingularCSCMayerVietorisInt
