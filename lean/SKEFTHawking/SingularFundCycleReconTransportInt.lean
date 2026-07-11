/-
# Phase 5q.H (E1 CSC-PD tower) — fundamental-cycle boundary transport (integral, brick 6e-c-recon-transport)

The `z_K ↔ z_J` **boundary transport** the seam-match atomic identity consumes: it converts the committed
`fundCycleW` rel-homology reconciliation (`SingularFundCycleReconInt.fundCycleW_pair_relHomologousInt`) into
a directly usable chain identity via the chain-altitude transport
(`SingularFundCycleReconInt.chainBoundary_rel_transportInt`).

* `fundCycleW_pair_boundary_transportInt` — base form: for nested compacts `K₂ ⊆ K₁` sharing the ancestor
  cycle `z₀`, `∂(fundCycleW K₁) = ∂(fundCycleW K₂) + ∂ρ` with `ρ` supported in `K₂ᶜ`.
* `fundCycleW_pair_boundary_transport_sdInt` — the `z_J ↔ Sdᵘ(fundCycleW K)` form (both sides subdivided),
  the shape Brick M's `Sdᵘ(fundCycleW K)` seam datum consumes; the `Sdᵘ` on the `K₂`-side cycle is reconciled
  to the un-subdivided `z_J` downstream by the committed cap-subdivision invariance
  `SingularCapSubdivHomologousInt.capInt_sub_singularSd_mem_boundariesInt` (c-2).

Whnf-safe (all data lives in `SingularChainInt X` — no doubly-nested `sub (restr …)` seam types).
Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFundCycleReconInt
import SKEFTHawking.SingularSubdivisionInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW)
open SKEFTHawking.SingularFundCycleReconInt (fundCycleW_pair_relHomologousInt chainBoundary_rel_transportInt)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt singularSdInt_iterate_chainBoundary)

namespace SKEFTHawking.SingularFundCycleReconInt

variable {X : TopCat} [T2Space ↑X]

/-- **Base boundary transport.** For nested compacts `K₂ ⊆ K₁` sharing the ancestor cycle `z₀`, the
boundaries of the two fundamental cycles differ by the boundary of a `K₂ᶜ`-supported chain `ρ`. Direct
composition of `fundCycleW_pair_relHomologousInt` (the `z_K/z_J` reconciliation) with
`chainBoundary_rel_transportInt` (the chain-altitude transport). -/
theorem fundCycleW_pair_boundary_transportInt {k m : ℕ} {W₁ W₂ : Set ↑X}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (K₂ : CompactsIn W₂) (hsub : (↑K₂.1 : Set ↑X) ⊆ (↑K₁.1 : Set ↑X)) :
    ∃ ρ : SingularChainInt X (k + m + 1), ρ ∈ subspaceChainsInt ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) ∧
      chainBoundary X (k + m) (fundCycleW hW₁ z₀ hz₀ K₁)
        = chainBoundary X (k + m) (fundCycleW hW₂ z₀ hz₀ K₂) + chainBoundary X (k + m) ρ :=
  chainBoundary_rel_transportInt _ _ (fundCycleW_pair_relHomologousInt hW₁ hW₂ z₀ hz₀ K₁ K₂ hsub)

omit [T2Space ↑X] in
/-- Iterated-subdivision additivity (helper; `Sdᵐ` is a composite of ℤ-linear maps). -/
theorem sdIterate_addInt {n : ℕ} (μ : ℕ) (a b : SingularChainInt X n) :
    (⇑(singularSdInt X n))^[μ] (a + b)
      = (⇑(singularSdInt X n))^[μ] a + (⇑(singularSdInt X n))^[μ] b := by
  induction μ with
  | zero => simp
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply, Function.comp_apply,
      Function.comp_apply, ih, map_add]

/-- **Subdivided boundary transport (`z_J ↔ Sdᵘ(fundCycleW K)`).** For nested compacts `K₂ ⊆ K₁` sharing
`z₀`, the boundary of the cover-fine-subdivided union-side cycle `Sdᵘ(fundCycleW K₁)` differs from that of
the subdivided intersection-side cycle `Sdᵘ(fundCycleW K₂)` by the boundary of a `K₂ᶜ`-supported chain
`Sdᵘ ρ`. The form Brick M's `Sdᵘ(fundCycleW K)` seam datum consumes; the `Sdᵘ` on the `K₂` cycle is
reconciled to the un-subdivided `z_J` downstream by `capInt_sub_singularSd_mem_boundariesInt` (c-2). -/
theorem fundCycleW_pair_boundary_transport_sdInt {k m : ℕ} {W₁ W₂ : Set ↑X}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (K₂ : CompactsIn W₂) (hsub : (↑K₂.1 : Set ↑X) ⊆ (↑K₁.1 : Set ↑X)) (μ : ℕ) :
    ∃ ρ : SingularChainInt X (k + m + 1), ρ ∈ subspaceChainsInt ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) ∧
      chainBoundary X (k + m) ((⇑(singularSdInt X (k + m + 1)))^[μ] (fundCycleW hW₁ z₀ hz₀ K₁))
        = chainBoundary X (k + m) ((⇑(singularSdInt X (k + m + 1)))^[μ] (fundCycleW hW₂ z₀ hz₀ K₂))
          + chainBoundary X (k + m) ((⇑(singularSdInt X (k + m + 1)))^[μ] ρ) := by
  obtain ⟨ρ, hρmem, hρ⟩ :=
    fundCycleW_pair_boundary_transportInt hW₁ hW₂ z₀ hz₀ K₁ K₂ hsub
  refine ⟨ρ, hρmem, ?_⟩
  rw [singularSdInt_iterate_chainBoundary, singularSdInt_iterate_chainBoundary,
    singularSdInt_iterate_chainBoundary, hρ, sdIterate_addInt]

end SKEFTHawking.SingularFundCycleReconInt
