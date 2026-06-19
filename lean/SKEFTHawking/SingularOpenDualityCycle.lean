import Mathlib
import SKEFTHawking.SingularLocalDualityKCycle
import SKEFTHawking.SingularLocalDualityKRestrict
import SKEFTHawking.SingularFundCycleOpen
import SKEFTHawking.SingularCompactsInOpen

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6e-iii-a) — the per-compact fundamental cycle family of `D_W`

The open Poincaré-duality map `D_W : Hᵏ_c(W) → H_{n-k}(sub W)` is the colimit, over compacts `K ⊆ W`, of
the `H(sub W)`-valued per-`K` duality `relativeDualityK ((↑K)ᶜ) W z_K`. Each `z_K` is a `W`-supported
fundamental cycle for `(M, Kᶜ)` produced by `exists_fundCycle_in_open` (C0b) from a **single global
absolute cycle `z₀`** (`∂z₀ = 0`). Using the same `z₀` for every `K` is what makes the family compatible
across the colimit: each `z_K` is relatively homologous to the common ancestor `z₀`, so for `K ⊆ K'` the
two cycles `z_K`, `z_{K'}` are relatively homologous in `(M, Kᶜ)` — the hypothesis of the cycle-difference
compatibility `relativeDualityK_cycle_compat`.

This module provides the per-`K` cycle `fundCycleW` and its three spec lemmas, and the `relBoundaries`-form
wrapper of the cycle-difference compatibility (extracting the explicit boundary witness once).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularLocalDualityKCycle SKEFTHawking.SingularFundCycleOpen
  SKEFTHawking.SingularCompactsInOpen

namespace SKEFTHawking.SingularOpenDualityCycle

variable {X : TopCat} [T2Space ↑X]

/-- **The per-compact `W`-supported fundamental cycle** `z_K` derived from the global absolute cycle `z₀`
(`∂z₀ = 0`) via `exists_fundCycle_in_open` (C0b). `W`-supported, with `∂z_K ∈ C(Kᶜ)`, and relatively
homologous to `z₀` in `(M, Kᶜ)`. -/
noncomputable def fundCycleW {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) : SingularChain X (k + m + 1) :=
  (exists_fundCycle_in_open K.1.isCompact' hW K.2
    (show chainBoundary X (k + m) z₀ ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) by
      rw [hz₀]; exact Submodule.zero_mem _)).choose

theorem fundCycleW_mem_W {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    fundCycleW hW z₀ hz₀ K ∈ subspaceChains W (k + m + 1) :=
  (exists_fundCycle_in_open K.1.isCompact' hW K.2
    (show chainBoundary X (k + m) z₀ ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) by
      rw [hz₀]; exact Submodule.zero_mem _)).choose_spec.1

theorem fundCycleW_boundary {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X (k + m) (fundCycleW hW z₀ hz₀ K) ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) :=
  (exists_fundCycle_in_open K.1.isCompact' hW K.2
    (show chainBoundary X (k + m) z₀ ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) by
      rw [hz₀]; exact Submodule.zero_mem _)).choose_spec.2.1

theorem fundCycleW_relHomologous {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) z₀
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) :=
  (exists_fundCycle_in_open K.1.isCompact' hW K.2
    (show chainBoundary X (k + m) z₀ ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m) by
      rw [hz₀]; exact Submodule.zero_mem _)).choose_spec.2.2

omit [T2Space ↑X] in
/-- **`relBoundaries`-form of the cycle-difference compatibility**: takes the rel-homology hypothesis
`[z] = [z']` in `H(M, S)` directly (extracting the explicit boundary witness once via the quotient). -/
theorem relativeDualityK_cycle_compat_relB {k m : ℕ} {S W : Set ↑X}
    (z z' : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains W (k + m + 1)) (hz'K : z' ∈ subspaceChains W (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hz'S : chainBoundary X (k + m) z' ∈ subspaceChains S (k + m))
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (hrel : RelativeChain.mk S (k + m + 1) z + RelativeChain.mk S (k + m + 1) z'
        ∈ relBoundaries S (k + m + 1))
    (x : RelativeCohomology S k) :
    relativeDualityK S W k m z hzK hzS x = relativeDualityK S W k m z' hz'K hz'S x := by
  obtain ⟨wRel, hwRel⟩ := hrel
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  refine relativeDualityK_cycle_compat z z' hzK hz'K hzS hz'S hcov w ?_ x
  have h1 : (Submodule.Quotient.mk (chainBoundary X (k + m + 1) w) : RelativeChain S (k + m + 1))
      = Submodule.Quotient.mk z + Submodule.Quotient.mk z' := hwRel
  rw [← RelativeChain.mk_eq_zero_iff]
  show Submodule.Quotient.mk ((z + z') + chainBoundary X (k + m + 1) w) = 0
  rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, h1, ZModModule.add_self]

omit [T2Space ↑X] in
/-- **`relBoundaries` transports across a subspace inclusion** `S' ⊆ S`: a relative boundary for the
smaller subspace `S'` is a relative boundary for the larger `S` (`subspaceChains S' ≤ subspaceChains S`,
so the same witness works). -/
theorem relBoundaries_mono {S' S : Set ↑X} (hSS' : S' ⊆ S) {n : ℕ} (c : SingularChain X (n + 1))
    (hc : RelativeChain.mk S' (n + 1) c ∈ relBoundaries S' (n + 1)) :
    RelativeChain.mk S (n + 1) c ∈ relBoundaries S (n + 1) := by
  obtain ⟨wRel, hwRel⟩ := hc
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  have hmem : c + chainBoundary X (n + 1) w ∈ subspaceChains S' (n + 1) := by
    rw [← RelativeChain.mk_eq_zero_iff]
    show Submodule.Quotient.mk (c + chainBoundary X (n + 1) w) = 0
    rw [Submodule.Quotient.mk_add,
      show (Submodule.Quotient.mk (chainBoundary X (n + 1) w) : RelativeChain S' (n + 1))
        = Submodule.Quotient.mk c from hwRel, ZModModule.add_self]
  refine ⟨RelativeChain.mk S (n + 2) w, ?_⟩
  rw [relBoundary_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [show chainBoundary X (n + 1) w - c = c + chainBoundary X (n + 1) w by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]; exact add_comm _ _]
  exact SKEFTHawking.SingularMayerVietoris.subspaceChains_mono hSS' (n + 1) hmem

end SKEFTHawking.SingularOpenDualityCycle
