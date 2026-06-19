import Mathlib
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularCompactlySupportedOpen

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6e-iii-b) — the open Poincaré-duality map `D_W`

`D_W : Hᵏ_c(W) → H_{n-k}(sub W)` for an open `W`, the colimit over compacts `K ⊆ W` of the per-`K`
`H(sub W)`-valued duality `relativeDualityK ((↑K)ᶜ) W z_K` (`legW`), capping the per-`K` fundamental
cycle `z_K = fundCycleW` (all derived from one global ancestor `z₀`). The `DirectLimit.lift`
compatibility (`legW_compat`) is the composite of the two built effects: the cohomology-restriction
(`relativeDualityK_restrict_compat`, moving the cohomology subspace `(↑K')ᶜ → (↑K)ᶜ` at fixed cycle
`z_{K'}`) and the cycle-difference (`relativeDualityK_cycle_compat_relB`, swapping `z_{K'} → z_K` at the
subspace `(↑K)ᶜ`, with `z_{K'} + z_K ∈ relBoundaries (↑K)ᶜ` from the two C0b rel-homologies of the common
ancestor `z₀`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularLocalDualityKRestrict
  SKEFTHawking.SingularFundCycleOpen SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularOpenDualityCycle

namespace SKEFTHawking.SingularOpenDuality

variable {X : TopCat} [T2Space ↑X]

/-- A `ℤ/2`-module rearrangement (`2•c = 0`): `a + b = (c + b) + (c + a)`. Used to combine the two
C0b rel-homologies of the common ancestor `z₀` into `z_{K'} + z_K ∈ relBoundaries`. -/
private theorem add_swap_zmod2 {Mod : Type*} [AddCommGroup Mod] [Module (ZMod 2) Mod] (a b c : Mod) :
    a + b = (c + b) + (c + a) := by
  rw [add_add_add_comm, ZModModule.add_self, zero_add, add_comm]

/-- **The per-compact duality leg** `legW K : Hᵏ(M|K) → H(sub W)`, capping the per-`K` fundamental cycle
`z_K = fundCycleW`. (`relativeDualityK ((↑K)ᶜ) W z_K`; the colimit cocone of `D_W`.) -/
noncomputable def legW {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    cohomGW W k K →ₗ[ZMod 2] Homology (sub W) (m + 1) :=
  relativeDualityK ((↑K.1 : Set ↑X)ᶜ) W k m (fundCycleW hW z₀ hz₀ K)
    (fundCycleW_mem_W hW z₀ hz₀ K) (fundCycleW_boundary hW z₀ hz₀ K)

/-- **The duality-leg colimit compatibility** `legW K' ∘ cohomFW = legW K` for `K ≤ K'`: the
cohomology-restriction (PD6e-i) then the cycle-difference (PD6e-ii via the `relB` form). -/
theorem legW_compat {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K K' : CompactsIn W) (h : K ≤ K') (x : cohomGW W k K) :
    legW hW z₀ hz₀ K' (cohomFW W k K K' h x) = legW hW z₀ hz₀ K x := by
  have hKK' : (↑K'.1 : Set ↑X)ᶜ ⊆ (↑K.1 : Set ↑X)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr h)
  have hzK'_S : chainBoundary X (k + m) (fundCycleW hW z₀ hz₀ K')
      ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) :=
    SKEFTHawking.SingularMayerVietoris.subspaceChains_mono hKK' (k + m)
      (fundCycleW_boundary hW z₀ hz₀ K')
  -- Step 1 (PD6e-i): move the cohomology subspace from `(↑K')ᶜ` to `(↑K)ᶜ`, fixed cycle `z_{K'}`.
  have step1 : legW hW z₀ hz₀ K' (cohomFW W k K K' h x)
      = relativeDualityK ((↑K.1 : Set ↑X)ᶜ) W k m (fundCycleW hW z₀ hz₀ K')
          (fundCycleW_mem_W hW z₀ hz₀ K') hzK'_S x :=
    relativeDualityK_restrict_compat (fundCycleW hW z₀ hz₀ K') hKK'
      (fundCycleW_mem_W hW z₀ hz₀ K') (fundCycleW_boundary hW z₀ hz₀ K') hzK'_S x
  rw [step1, legW]
  -- Step 2 (PD6e-ii / relB): swap the cycle `z_{K'} → z_K` at subspace `(↑K)ᶜ`.
  refine relativeDualityK_cycle_compat_relB (fundCycleW hW z₀ hz₀ K') (fundCycleW hW z₀ hz₀ K)
    (fundCycleW_mem_W hW z₀ hz₀ K') (fundCycleW_mem_W hW z₀ hz₀ K) hzK'_S
    (fundCycleW_boundary hW z₀ hz₀ K)
    (interiors_cover_of_compact_subset_open K.1.isCompact' hW K.2) ?_ x
  -- the rel-homology `z_{K'} + z_K ∈ relBoundaries (↑K)ᶜ` from the two C0b rel-homologies of `z₀`.
  set S : Set ↑X := (↑K.1 : Set ↑X)ᶜ with hS
  have hA := fundCycleW_relHomologous hW z₀ hz₀ K
  have hB : RelativeChain.mk S (k + m + 1) (z₀ + fundCycleW hW z₀ hz₀ K') ∈ relBoundaries S (k + m + 1) := by
    refine relBoundaries_mono hKK' _ ?_
    show Submodule.Quotient.mk (z₀ + fundCycleW hW z₀ hz₀ K')
      ∈ relBoundaries ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1)
    rw [Submodule.Quotient.mk_add]
    exact fundCycleW_relHomologous hW z₀ hz₀ K'
  have heq : RelativeChain.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K')
        + RelativeChain.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      = (RelativeChain.mk S (k + m + 1) z₀ + RelativeChain.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K))
        + RelativeChain.mk S (k + m + 1) (z₀ + fundCycleW hW z₀ hz₀ K') := by
    simp only [RelativeChain.mk, Submodule.Quotient.mk_add]
    exact add_swap_zmod2 _ _ _
  rw [heq]
  exact Submodule.add_mem _ hA hB

/-- **The open Poincaré-duality map** `D_W : Hᵏ_c(W) → H_{n-k}(sub W)`, the colimit of the per-compact
duality legs. -/
noncomputable def openDuality {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) :
    CompactlySupportedCohomologyOpen W k →ₗ[ZMod 2] Homology (sub W) (m + 1) :=
  Module.DirectLimit.lift (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k)
    (legW hW z₀ hz₀) (fun K K' h x => legW_compat hW z₀ hz₀ K K' h x)

/-- **Computation rule for `D_W`** on a `K`-stage class `of_W K a`: the colimit lift reads off as the
per-`K` duality leg `legW K a` (`DirectLimit.lift_of`). -/
@[simp] theorem openDuality_of {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (a : cohomGW W k K) :
    openDuality hW z₀ hz₀
        (Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) K a)
      = legW hW z₀ hz₀ K a :=
  Module.DirectLimit.lift_of _ _ a

end SKEFTHawking.SingularOpenDuality
