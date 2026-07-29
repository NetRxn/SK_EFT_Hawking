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
  SKEFTHawking.SingularCompactsInOpen

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

/-- **Computation rule for the MV diagonal** on a `K`-stage class `of_{U∩V}(K, g)`: `Δ` extends it to the
two `K`-stage classes over `U` and `V` (the same underlying compact `K`, included into `CompactsIn U` /
`CompactsIn V`). -/
@[simp] theorem cscMvDiag_of (U V : Set ↑M) (k : ℕ) (K : CompactsIn (U ∩ V))
    (g : cohomGW (U ∩ V) k K) :
    cscMvDiag U V k
        (Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) k) (cohomFW (U ∩ V) k) K g)
      = (Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U k) (cohomFW U k)
            (compactsInIncl Set.inter_subset_left K) g,
          Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V k) (cohomFW V k)
            (compactsInIncl Set.inter_subset_right K) g) := by
  -- v4.32: `Function.prod_def` is a deprecated alias with no usable equation theorems, so `rw` cannot
  -- unfold it (`delta`/`show` pierce aliases; `rw`/`unfold` do not). Unfold via the real
  -- def's lemma with `simp only` first, then finish the two monotone rewrites.
  rw [cscMvDiag, LinearMap.prod_apply]
  simp only [Function.prod_def]
  rw [cscOpenMonotone_of, cscOpenMonotone_of]
  rfl

end SKEFTHawking.SingularCSCMayerVietoris
