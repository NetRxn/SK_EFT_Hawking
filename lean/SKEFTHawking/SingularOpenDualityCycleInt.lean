/-
# Phase 5q.H (E1 integral topology) — the per-compact fundamental cycle family of `D_W` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityCycle`. The open Poincaré-duality map
`D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)` is the colimit, over compacts `K ⊆ W`, of the per-`K` duality
`relativeDualityKInt ((↑K)ᶜ) W z_K`. Each `z_K = fundCycleW` is a `W`-supported fundamental cycle for
`(M, Kᶜ)` produced by `exists_fundCycle_in_openInt` from a **single global absolute cycle `z₀`**
(`∂z₀ = 0`); using the same `z₀` for every `K` makes the family compatible across the colimit (each `z_K`
is rel-homologous to `z₀`, so `z_K, z_{K'}` are rel-homologous — the hypothesis of the cycle-difference
compatibility).

This module provides `fundCycleW` + its three spec lemmas, the `relBoundaries`-form of the cycle
compatibility, and `relBoundaries_monoInt`. The `+`→`−` adaptation (mod-2 `mk z + mk z'` = ℤ `mk z − mk z'`)
threads through `fundCycleW_relHomologous`, the relB form, and `relBoundaries_monoInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKCycleInt
import SKEFTHawking.SingularFundCycleOpenInt
import SKEFTHawking.SingularCompactsInOpen
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularLocalDualityKCycleInt
open SKEFTHawking.SingularFundCycleOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

namespace SKEFTHawking.SingularOpenDualityCycleInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- The `(M, Kᶜ)` relative-cycle hypothesis for the global absolute cycle `z₀`. -/
private theorem z₀_rcyc {k m : ℕ} {W : Set ↑X} (z₀ : SingularChainInt X (k + m + 1))
    (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X (k + m) z₀ ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) (k + m) := by
  rw [hz₀]; exact Submodule.zero_mem _

/-- **The per-compact `W`-supported fundamental cycle** `z_K` derived from the global absolute cycle `z₀`
via `exists_fundCycle_in_openInt`. -/
noncomputable def fundCycleW {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) : SingularChainInt X (k + m + 1) :=
  (exists_fundCycle_in_openInt K.1.isCompact' hW K.2 (z₀_rcyc z₀ hz₀ K)).choose

theorem fundCycleW_mem_W {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    fundCycleW hW z₀ hz₀ K ∈ subspaceChainsInt W (k + m + 1) :=
  (exists_fundCycle_in_openInt K.1.isCompact' hW K.2 (z₀_rcyc z₀ hz₀ K)).choose_spec.1

theorem fundCycleW_boundary {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X (k + m) (fundCycleW hW z₀ hz₀ K)
      ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) (k + m) :=
  (exists_fundCycle_in_openInt K.1.isCompact' hW K.2 (z₀_rcyc z₀ hz₀ K)).choose_spec.2.1

/-- Rel-homologous (`−` form): `mk z₀ − mk z_K ∈ relBoundaries (Kᶜ)`. -/
theorem fundCycleW_relHomologous {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0) (K : CompactsIn W) :
    RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) z₀
        - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) :=
  (exists_fundCycle_in_openInt K.1.isCompact' hW K.2 (z₀_rcyc z₀ hz₀ K)).choose_spec.2.2

omit [T2Space ↑X] in
/-- **`relBoundariesInt` transports across a subspace inclusion** `S' ⊆ S`. -/
theorem relBoundaries_monoInt {S' S : Set ↑X} (hSS' : S' ⊆ S) {n : ℕ} (c : SingularChainInt X (n + 1))
    (hc : RelativeChainInt.mk S' (n + 1) c ∈ relBoundariesInt S' (n + 1)) :
    RelativeChainInt.mk S (n + 1) c ∈ relBoundariesInt S (n + 1) := by
  obtain ⟨wRel, hwRel⟩ := hc
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  have hmem : chainBoundary X (n + 1) w - c ∈ subspaceChainsInt S' (n + 1) := by
    have heq : RelativeChainInt.mk S' (n + 1) (chainBoundary X (n + 1) w)
        = RelativeChainInt.mk S' (n + 1) c := by rw [← relBoundaryInt_mk]; exact hwRel
    exact (Submodule.Quotient.eq _).mp heq
  refine ⟨RelativeChainInt.mk S (n + 2) w, ?_⟩
  rw [relBoundaryInt_mk]
  exact (Submodule.Quotient.eq _).mpr (subspaceChainsInt_mono hSS' (n + 1) hmem)

omit [T2Space ↑X] in
/-- **`relBoundaries`-form of the cycle-difference compatibility** (integral): takes the rel-homology
hypothesis `mk z − mk z' ∈ relBoundaries` directly. -/
theorem relativeDualityKInt_cycle_compat_relB {k m : ℕ} {S W : Set ↑X}
    (z z' : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt W (k + m + 1)) (hz'K : z' ∈ subspaceChainsInt W (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (hz'S : chainBoundary X (k + m) z' ∈ subspaceChainsInt S (k + m))
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (hrel : RelativeChainInt.mk S (k + m + 1) z - RelativeChainInt.mk S (k + m + 1) z'
        ∈ relBoundariesInt S (k + m + 1))
    (x : RelativeCohomologyInt S k) :
    relativeDualityKInt S W k m z hzK hzS x = relativeDualityKInt S W k m z' hz'K hz'S x := by
  obtain ⟨wRel, hwRel⟩ := hrel
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  refine relativeDualityKInt_cycle_compat z z' hzK hz'K hzS hz'S hcov (-w) ?_ x
  have hmem : chainBoundary X (k + m + 1) w - (z - z') ∈ subspaceChainsInt S (k + m + 1) :=
    (Submodule.Quotient.eq _).mp (hwRel.trans (Submodule.Quotient.mk_sub _).symm)
  rw [map_neg,
    show (z - z') + -chainBoundary X (k + m + 1) w
      = -(chainBoundary X (k + m + 1) w - (z - z')) by abel]
  exact Submodule.neg_mem _ hmem

end SKEFTHawking.SingularOpenDualityCycleInt
