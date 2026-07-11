/-
# Phase 5q.H (E1 CSC-PD tower) — fundamental-cycle reconciliation + transport (integral, brick 6e-c-recon)

The two chain-level bricks that convert the `z_K`/`z_J` fundamental-cycle mismatch into a usable boundary
residual — the "genuinely new sub-fact" the seam-match atomic identity needs (over ℤ, cleaner than the
mod-2 `x+x=0`, and the constructive replacement for the mod-2 `cap_chainBoundary_relBoundaries_transport`):

* `fundCycleW_pair_relHomologousInt` — for compacts `K₂ ⊆ K₁` in opens sharing the ancestor `z₀`, the two
  fundamental cycles are rel-`K₂ᶜ` homologous (each is rel-homologous to the SAME `z₀` via
  `fundCycleW_relHomologous`; `relBoundaries_monoInt` lifts + the shared `z₀` cancels by signed subtraction).
  This is the `z_K`↔`z_J` bridge (`K₁=K`, `K₂=J=infCompact ⊆ K`).
* `chainBoundary_rel_transportInt` — from `mk_S(a−b) ∈ relBoundaries(S)`, extract an `S`-supported `ρ` with
  `∂a = ∂b + ∂ρ`. So `capInt c (∂z_K) = capInt c (∂z_J) + capInt c (∂ρ)` with `ρ` `infCompactᶜ`-supported.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityCycleInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_relHomologous relBoundaries_monoInt)

namespace SKEFTHawking.SingularFundCycleReconInt

variable {X : TopCat} [T2Space ↑X]

/-- **Paired `fundCycleW` rel-homology** (integral, the `z_K`/`z_J` reconciliation). For compacts
`K₂ ⊆ K₁` in opens `W₁, W₂` sharing the ancestor `z₀`, the two fundamental cycles are rel-`K₂ᶜ`
homologous: `mk fund₁ − mk fund₂ ∈ relBoundaries(K₂ᶜ)`. Each is rel-homologous to the SAME `z₀`
(`fundCycleW_relHomologous`); `relBoundaries_monoInt` (`K₁ᶜ ⊆ K₂ᶜ`) lifts the `K₁` relation to `K₂ᶜ`,
and the shared `z₀` cancels by signed subtraction (cleaner than the mod-2 `x+x=0`). -/
theorem fundCycleW_pair_relHomologousInt {k m : ℕ} {W₁ W₂ : Set ↑X} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (K₂ : CompactsIn W₂) (hsub : (↑K₂.1 : Set ↑X) ⊆ (↑K₁.1 : Set ↑X)) :
    RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₁ z₀ hz₀ K₁)
        - RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₂ z₀ hz₀ K₂)
      ∈ relBoundariesInt ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
  have hcompl : (↑K₁.1 : Set ↑X)ᶜ ⊆ (↑K₂.1 : Set ↑X)ᶜ := Set.compl_subset_compl.mpr hsub
  have mk_sub : ∀ (S : Set ↑X) (a b : SingularChainInt X (k + m + 1)),
      RelativeChainInt.mk S (k + m + 1) (a - b)
        = RelativeChainInt.mk S (k + m + 1) a - RelativeChainInt.mk S (k + m + 1) b :=
    fun _ _ _ => rfl
  -- lift the `K₁` relation to `K₂ᶜ`, as a relation on the single chain `z₀ − fund₁`
  have h1lift : RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
        (z₀ - fundCycleW hW₁ z₀ hz₀ K₁)
      ∈ relBoundariesInt ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
    refine relBoundaries_monoInt hcompl _ ?_
    rw [mk_sub]; exact fundCycleW_relHomologous hW₁ z₀ hz₀ K₁
  have h2' : RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
        (z₀ - fundCycleW hW₂ z₀ hz₀ K₂)
      ∈ relBoundariesInt ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
    rw [mk_sub]; exact fundCycleW_relHomologous hW₂ z₀ hz₀ K₂
  have hsub' := Submodule.sub_mem _ h1lift h2'
  rw [mk_sub, mk_sub] at hsub'
  -- (mk z₀ − mk fund₁) − (mk z₀ − mk fund₂) = −(mk fund₁ − mk fund₂)
  have hrw : RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) z₀
        - RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₁ z₀ hz₀ K₁)
      - (RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) z₀
        - RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₂ z₀ hz₀ K₂))
      = - (RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₁ z₀ hz₀ K₁)
          - RelativeChainInt.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW₂ z₀ hz₀ K₂)) := by
    abel
  rw [hrw] at hsub'
  exact (Submodule.neg_mem_iff _).mp hsub'

omit [T2Space ↑X] in
/-- **Chain-altitude transport of a rel-homology to a subspace-supported boundary residual** (integral).
From `mk_S(a − b) ∈ relBoundaries(S)`, extract an `S`-supported `ρ` with `∂a = ∂b + ∂ρ`. (`a − b = ∂D + ρ`
via `relBoundaryInt_mk` + `Submodule.Quotient.eq`; then `∂(a−b) = ∂ρ` by `∂²=0`.) The chain-level engine
that converts the `z_K`/`z_J` reconciliation into a usable boundary residual. -/
theorem chainBoundary_rel_transportInt {S : Set ↑X} {n : ℕ}
    (a b : SingularChainInt X (n + 1))
    (hrel : RelativeChainInt.mk S (n + 1) (a - b) ∈ relBoundariesInt S (n + 1)) :
    ∃ ρ : SingularChainInt X (n + 1), ρ ∈ subspaceChainsInt S (n + 1) ∧
      chainBoundary X n a = chainBoundary X n b + chainBoundary X n ρ := by
  obtain ⟨Dbar, hD⟩ := hrel
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ Dbar
  have hmk : RelativeChainInt.mk S (n + 1) (chainBoundary X (n + 1) D)
      = RelativeChainInt.mk S (n + 1) (a - b) := hD
  have hmem : a - b - chainBoundary X (n + 1) D ∈ subspaceChainsInt S (n + 1) :=
    (Submodule.Quotient.eq _).mp hmk.symm
  refine ⟨a - b - chainBoundary X (n + 1) D, hmem, ?_⟩
  have h2 : chainBoundary X n (chainBoundary X (n + 1) D) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary X n) D
  rw [map_sub, map_sub, h2, sub_zero]
  abel

end SKEFTHawking.SingularFundCycleReconInt
