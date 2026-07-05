/-
# Phase 5q.H (E1 integral topology) — the open Poincaré-duality map `D_W` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDuality`. `D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)` for an open
`W`, the colimit over compacts `K ⊆ W` of the per-`K` `H(sub W)`-valued duality `relativeDualityKInt
((↑K)ᶜ) W z_K` (`legW`), capping the per-`K` fundamental cycle `z_K = fundCycleW` (all derived from one
global ancestor `z₀`). The `DirectLimit.lift` compatibility (`legW_compat`) is the composite of the two
built effects: the cohomology-restriction (`relativeDualityKInt_restrict_compat`, moving `(↑K')ᶜ → (↑K)ᶜ`
at fixed cycle) and the cycle-difference (`relativeDualityKInt_cycle_compat_relB`, swapping `z_{K'} → z_K`,
with `z_{K'}, z_K` rel-homologous via the two rel-homologies of the common ancestor `z₀`).

**ℤ-difference:** the mod-2 `add_swap_zmod2` (combining the ancestor rel-homologies via `2c = 0`) becomes
the honest identity `mk z_{K'} − mk z_K = (mk z₀ − mk z_K) − (mk z₀ − mk z_{K'})` — a `Submodule.sub_mem`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKRestrictInt
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularCompactlySupportedOpenInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularLocalDualityKRestrictInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularFundCycleOpen (interiors_cover_of_compact_subset_open)

namespace SKEFTHawking.SingularOpenDualityInt

variable {X : TopCat} [T2Space ↑X]

/-- **The per-compact duality leg** `legW K : Hᵏ(M|K;ℤ) → H(sub W;ℤ)`, capping the per-`K` fundamental
cycle `z_K = fundCycleW`. -/
noncomputable def legW {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    cohomGWInt W k K →ₗ[ℤ] Homology (sub W) (m + 1) :=
  relativeDualityKInt ((↑K.1 : Set ↑X)ᶜ) W k m (fundCycleW hW z₀ hz₀ K)
    (fundCycleW_mem_W hW z₀ hz₀ K) (fundCycleW_boundary hW z₀ hz₀ K)

/-- **The duality-leg colimit compatibility** `legW K' ∘ cohomFW = legW K` for `K ≤ K'`: the
cohomology-restriction (PD6e-i) then the cycle-difference (PD6e-ii via the `relB` form). -/
theorem legW_compat {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K K' : CompactsIn W) (h : K ≤ K') (x : cohomGWInt W k K) :
    legW hW z₀ hz₀ K' (cohomFWInt W k K K' h x) = legW hW z₀ hz₀ K x := by
  have hKK' : (↑K'.1 : Set ↑X)ᶜ ⊆ (↑K.1 : Set ↑X)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr h)
  have hzK'_S : chainBoundary X (k + m) (fundCycleW hW z₀ hz₀ K')
      ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) (k + m) :=
    subspaceChainsInt_mono hKK' (k + m) (fundCycleW_boundary hW z₀ hz₀ K')
  -- Step 1 (PD6e-i): move the cohomology subspace from `(↑K')ᶜ` to `(↑K)ᶜ`, fixed cycle `z_{K'}`.
  have step1 : legW hW z₀ hz₀ K' (cohomFWInt W k K K' h x)
      = relativeDualityKInt ((↑K.1 : Set ↑X)ᶜ) W k m (fundCycleW hW z₀ hz₀ K')
          (fundCycleW_mem_W hW z₀ hz₀ K') hzK'_S x :=
    relativeDualityKInt_restrict_compat (fundCycleW hW z₀ hz₀ K') hKK'
      (fundCycleW_mem_W hW z₀ hz₀ K') (fundCycleW_boundary hW z₀ hz₀ K') hzK'_S x
  rw [step1, legW]
  -- Step 2 (PD6e-ii / relB): swap the cycle `z_{K'} → z_K` at subspace `(↑K)ᶜ`.
  refine relativeDualityKInt_cycle_compat_relB (fundCycleW hW z₀ hz₀ K') (fundCycleW hW z₀ hz₀ K)
    (fundCycleW_mem_W hW z₀ hz₀ K') (fundCycleW_mem_W hW z₀ hz₀ K) hzK'_S
    (fundCycleW_boundary hW z₀ hz₀ K)
    (interiors_cover_of_compact_subset_open K.1.isCompact' hW K.2) ?_ x
  -- the rel-homology `mk z_{K'} − mk z_K ∈ relBoundaries (↑K)ᶜ` from the two ancestor rel-homologies.
  set S : Set ↑X := (↑K.1 : Set ↑X)ᶜ with hS
  have hA := fundCycleW_relHomologous hW z₀ hz₀ K
  have hB : RelativeChainInt.mk S (k + m + 1) z₀
      - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K') ∈ relBoundariesInt S (k + m + 1) := by
    have hB' := fundCycleW_relHomologous hW z₀ hz₀ K'
    have hsubK' : RelativeChainInt.mk ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1)
          (z₀ - fundCycleW hW z₀ hz₀ K')
        = RelativeChainInt.mk ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1) z₀
          - RelativeChainInt.mk ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K') :=
      Submodule.Quotient.mk_sub _
    have hchain : RelativeChainInt.mk ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1)
        (z₀ - fundCycleW hW z₀ hz₀ K') ∈ relBoundariesInt ((↑K'.1 : Set ↑X)ᶜ) (k + m + 1) := by
      rw [hsubK']; exact hB'
    have hmono := relBoundaries_monoInt hKK' (z₀ - fundCycleW hW z₀ hz₀ K') hchain
    have hsubS : RelativeChainInt.mk S (k + m + 1) (z₀ - fundCycleW hW z₀ hz₀ K')
        = RelativeChainInt.mk S (k + m + 1) z₀
          - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K') :=
      Submodule.Quotient.mk_sub _
    rwa [hsubS] at hmono
  have heq : RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K')
        - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      = (RelativeChainInt.mk S (k + m + 1) z₀
            - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K))
        - (RelativeChainInt.mk S (k + m + 1) z₀
            - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K')) := by abel
  rw [heq]
  exact Submodule.sub_mem _ hA hB

/-- **The open Poincaré-duality map** `D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)`, the colimit of the
per-compact duality legs. -/
noncomputable def openDuality {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) :
    CompactlySupportedCohomologyOpenInt W k →ₗ[ℤ] Homology (sub W) (m + 1) :=
  Module.DirectLimit.lift ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k)
    (legW hW z₀ hz₀) (fun K K' h x => legW_compat hW z₀ hz₀ K K' h x)

/-- **Computation rule for `D_W`** on a `K`-stage class: the colimit lift reads off as the per-`K`
duality leg `legW K a` (`DirectLimit.lift_of`). -/
@[simp] theorem openDuality_of {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (a : cohomGWInt W k K) :
    openDuality hW z₀ hz₀
        (Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) K a)
      = legW hW z₀ hz₀ K a :=
  Module.DirectLimit.lift_of _ _ a

end SKEFTHawking.SingularOpenDualityInt
