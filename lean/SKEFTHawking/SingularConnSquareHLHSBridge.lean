import Mathlib
import SKEFTHawking.SingularCapMapChain
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularPairLES

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — hLHS `cap_mapChain` unwind bridge

The abstract `cap_mapChain`-unwind step of the connecting-square hLHS obligation
(`SingularConnSquareCrossReal`). With the two seam homeos carried as *explicit* continuous-map
variables `φ_seam`, `φ_sub` (NOT the anonymous `{toFun, continuous_toFun}` structs that whnf-wall
`kronecker_mapChain` in the concrete goal), the double `cap_mapChain` rewrite fires by plain `rw`,
reducing the seam-transported cap pairing to the **homeo-free** seam identity `hdual`
(`cap (pullbackCochainMap² a) d = lhs0`). The hard content — the local Poincaré-duality
identity `boundaryExtract zB = cap (dual) d` — is isolated as the hypothesis `hdual`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularCapMapChain

namespace SKEFTHawking.SingularConnSquareHLHSBridge

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularCapChainIncl

/-- **Cap–`boundaryExtract` naturality** (the genuine cap-Leibniz content of the hLHS, homeo-free):
for an ambient cocycle `a` and a relative cycle `w` (whose boundary lands in `S`), the `S`-included
cap of the *restricted* `a` against the seam-boundary `boundaryExtract S w` equals the ambient
boundary of the cap `a ⌢ w`. Pure composition of `cap_chainIncl` (cap commutes with inclusion),
`chainIncl_boundaryExtract` (`chainIncl ∘ boundaryExtract = ∂`), and `cap_cocycle_chainMap` (cap
commutes with `∂` for a cocycle). This is what makes `cap (dual) (∂-realization) = boundaryExtract`
hold (up to the injective `chainIncl`). -/
theorem cap_boundaryExtract_naturality {X : TopCat} {S : Set ↑X} {k m : ℕ}
    (a : SingularCochain X k) (ha : coboundaryₗ X k a = 0)
    (w : SingularPairLES.relCycleLift S (k + m)) :
    chainIncl S m (cap (pullbackCochain S k a) (SingularPairLES.boundaryExtract S (k + m) w))
      = chainBoundary X m (cap a (w : SingularChain X (k + m + 1))) := by
  rw [← cap_chainIncl, chainIncl_boundaryExtract, cap_cocycle_chainMap a ha]

/-- **hLHS `cap_mapChain` unwind.** The seam-transported pairing of a cocycle `ω` against the
`φ_sub∘φ_seam`-transport of a cap `cap a (mapChain² d)` equals its pairing against the transport of
`lhs0`, provided the homeo-free seam identity `hdual : cap (pullbackCochainMap² a) d = lhs0` holds.
Pure `cap_mapChain ×2 + hdual` — the whnf wall is dodged because `φ_seam`, `φ_sub` are explicit
`C(·,·)` variables, so `cap_mapChain` matches at `rw` reducibility. -/
theorem hLHS_cap_mapChain_bridge {Y Z W : TopCat} {p N : ℕ}
    (φ_seam : C(↑Y, ↑Z)) (φ_sub : C(↑Z, ↑W))
    (ω : SingularCochain ↑W (p + 1)) (a : SingularCochain ↑W (N + 1))
    (lhs0 : SingularChain Y (p + 1)) (d : SingularChain Y (N + 1 + (p + 1)))
    (hdual : cap (pullbackCochainMap φ_seam (N + 1) (pullbackCochainMap φ_sub (N + 1) a)) d = lhs0) :
    kronecker ω (mapChain φ_sub (p + 1) (mapChain φ_seam (p + 1) lhs0))
      = kronecker ω
          (cap a (mapChain φ_sub (N + 1 + (p + 1)) (mapChain φ_seam (N + 1 + (p + 1)) d))) := by
  rw [cap_mapChain, cap_mapChain, hdual]

/-- **hLHS `cap_mapChain` unwind, up to a boundary.** The actually-usable form: `hdual` need only hold
*modulo a boundary* `chainBoundary e` (the natural situation — `cap (dual)` and `boundaryExtract`
agree only up to a boundary), since the test cochain `ω` is a cocycle (`hω`) and `mapChain` is a chain
map (`chainBoundary_mapChain`), so the transported boundary slack pairs to zero. -/
theorem hLHS_cap_mapChain_bridge_mod {Y Z W : TopCat} {p N : ℕ}
    (φ_seam : C(↑Y, ↑Z)) (φ_sub : C(↑Z, ↑W))
    (ω : SingularCochain ↑W (p + 1)) (hω : coboundary W (p + 1) ω = 0)
    (a : SingularCochain ↑W (N + 1))
    (lhs0 : SingularChain Y (p + 1)) (d : SingularChain Y (N + 1 + (p + 1)))
    (e : SingularChain Y (p + 1 + 1))
    (hdual : cap (pullbackCochainMap φ_seam (N + 1) (pullbackCochainMap φ_sub (N + 1) a)) d
        = lhs0 + chainBoundary Y (p + 1) e) :
    kronecker ω (mapChain φ_sub (p + 1) (mapChain φ_seam (p + 1) lhs0))
      = kronecker ω
          (cap a (mapChain φ_sub (N + 1 + (p + 1)) (mapChain φ_seam (N + 1 + (p + 1)) d))) := by
  rw [cap_mapChain, cap_mapChain, hdual, map_add, map_add, kronecker_add_right,
    ← chainBoundary_mapChain, ← chainBoundary_mapChain, ← kronecker_coboundary_chainBoundary, hω]
  simp

/-- **Cocycle pairing descends to homology** (generic): for a cocycle `a` and two cycles `x`, `y` whose
homology classes agree, the chain-level Kronecker pairings agree. The clean reduction of a pairing equality
`⟨a, x⟩ = ⟨a, y⟩` to the homology-class equality `[x] = [y]` (via `kroneckerH_mk_mk`). Lets the hLHS pairing
close at the HOMOLOGY level (engine `boundaryExtract_class_eq_of_partition_homologous`), sidestepping both
the chain-level seam-fundamental `d` and the anonymous-φ `kronecker_mapChain` `rw`-wall. -/
theorem kronecker_eq_of_homology_eq {Y : TopCat} {n : ℕ}
    (a : LinearMap.ker (coboundaryₗ Y n)) {x y : SingularChain Y n}
    (hx : x ∈ cycles Y n) (hy : y ∈ cycles Y n)
    (hclass : (Submodule.Quotient.mk (⟨x, hx⟩ : cycles Y n) : Homology Y n)
      = Submodule.Quotient.mk ⟨y, hy⟩) :
    kronecker a.1 x = kronecker a.1 y := by
  rw [← kroneckerH_mk_mk a ⟨x, hx⟩, ← kroneckerH_mk_mk a ⟨y, hy⟩, hclass]

end SKEFTHawking.SingularConnSquareHLHSBridge
