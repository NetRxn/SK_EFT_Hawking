import Mathlib
import SKEFTHawking.SingularRelMvDeltaChain
import SKEFTHawking.SingularRelativePairing

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M9) — the relative MV connecting map's cover-partition chain action

The **relative** Mayer–Vietoris connecting map `relMvDelta : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` sends the class
of a relative cycle `c` whose boundary splits cover-subordinately `∂c = u + w` (`u ∈ C(U)`, `w ∈ C(V)`)
to the class of the **`V`-part `w`** of the boundary, realized as a `U∩V`-relative cycle:
`relMvDelta [c] = [w]`. The relative analogue of `SingularMvDeltaPartition.mvConnecting_cover_partition`
(M2, the *absolute* MV connecting). This is the explicit chain form of the connecting square's RHS leg
needed to match it against the LHS at the chain level (the shared fundamental cycle `z₀`).

Construction: the simplest lift `b := (mk U c, 0) ∈ relLift` (membership ⟺ `∂c ∈ C(U)+C(V)`); then
`iotaEquiv (relLiftToQHom b) = [c]` and `extractA b = [w]` (the unique `Δ`-preimage of `∂_B b = (∂c, 0)`),
so `SingularRelMvDeltaChain.relMvDelta_iotaEquiv_relLiftToQHom` (M1) gives `relMvDelta [c] = [w]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularRelMvDeltaChain SKEFTHawking.SingularRelativePairing

namespace SKEFTHawking.SingularRelMvDeltaPartition

variable {M : TopCat}

/-- **The relative MV connecting map's cover-partition chain action**: for a relative cycle `c` with
`∂c = u + w` (`u ∈ C(U)`, `w ∈ C(V)`), `relMvDelta [c] = [w]` (the `V`-part of `∂c`, a `U∩V`-cycle). -/
theorem relMvDelta_cover_partition (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (c : SingularChain M (n + 1)) (u w : SingularChain M n)
    (hu : u ∈ subspaceChains U n) (hw : w ∈ subspaceChains V n)
    (hbd : chainBoundary M n c = u + w)
    (hwcyc : RelativeChain.mk (U ∩ V) n w ∈ relCycles (U ∩ V) n)
    (hccyc : RelativeChain.mk (U ∪ V) (n + 1) c ∈ relCycles (U ∪ V) (n + 1)) :
    relMvDelta U V hU hV n
        (RelativeHomology.mk (U ∪ V) (n + 1) ⟨RelativeChain.mk (U ∪ V) (n + 1) c, hccyc⟩)
      = RelativeHomology.mk (U ∩ V) n ⟨RelativeChain.mk (U ∩ V) n w, hwcyc⟩ := by
  -- `∂c ∈ C(U) + C(V)`, so the simplest lift `b = (mk U c, 0)` lands in `relLift`.
  have hbd_un : chainBoundary M n c ∈ mvUnionChains U V n := by
    rw [hbd]; exact Submodule.add_mem_sup hu hw
  have hmem : ((RelativeChain.mk U (n + 1) c, RelativeChain.mk V (n + 1) 0)
      : RelativeChain U (n + 1) × RelativeChain V (n + 1)) ∈ relLift U V n := by
    rw [relLift, LinearMap.mem_ker, LinearMap.comp_apply, bBoundary_mk, map_zero, relMvChainSum_mk,
      add_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hbd_un
  set b : relLift U V n := ⟨_, hmem⟩ with hb
  -- `extractA b = [w]`: both have the same image `(mk U ∂c, 0)` under the injective `Δ`.
  have hextract : extractA U V n b = RelativeChain.mk (U ∩ V) n w := by
    apply relMvChainDiag_injective U V n
    rw [relMvChainDiag_extractA, relMvChainDiag_mk, hb, bBoundary_mk, map_zero]
    refine Prod.ext ?_ ?_
    · show RelativeChain.mk U n (chainBoundary M n c) = RelativeChain.mk U n w
      refine (Submodule.Quotient.eq _).mpr ?_
      have : chainBoundary M n c - w = u := by rw [hbd]; abel
      rw [this]; exact hu
    · show RelativeChain.mk V n (chainBoundary M n (0 : SingularChain M (n + 1)))
        = RelativeChain.mk V n w
      rw [map_zero]
      exact ((Submodule.Quotient.eq _).mpr (by simpa using hw)).symm
  -- the input class is `iotaEquiv (relLiftToQHom b)`.
  have hinput : RelativeHomology.mk (U ∪ V) (n + 1) ⟨RelativeChain.mk (U ∪ V) (n + 1) c, hccyc⟩
      = iotaEquiv U V hU hV n (relLiftToQHom U V n b) := by
    rw [iotaEquiv, LinearEquiv.ofBijective_apply, relLiftToQHom_apply, iota_mk]
    refine congrArg (RelativeHomology.mk (U ∪ V) (n + 1)) (Subtype.ext ?_)
    show RelativeChain.mk (U ∪ V) (n + 1) c
      = piMap U V (n + 1) (relMvChainSum U V (n + 1) (b : _))
    rw [hb, relMvChainSum_mk, add_zero]
    exact (piMap_mk U V (n + 1) c).symm
  rw [hinput, relMvDelta_iotaEquiv_relLiftToQHom]
  exact congrArg (RelativeHomology.mk (U ∩ V) n) (Subtype.ext hextract)

/-- **The connecting square's RHS leg, explicit**: pairing a relative cocycle `g` against the relative
MV connecting of a cover-partitioned relative cycle reduces to the chain-level Kronecker pairing of `g`'s
rep against the `V`-part `w` of `∂c`. Combines `relMvDelta_cover_partition` (M9) with `relKroneckerH_mk_mk`. -/
theorem relKroneckerH_relMvDelta_cover_partition (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (g : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (c : SingularChain M (N + 1 + 1)) (u w : SingularChain M (N + 1))
    (hu : u ∈ subspaceChains U (N + 1)) (hw : w ∈ subspaceChains V (N + 1))
    (hbd : chainBoundary M (N + 1) c = u + w)
    (hwcyc : RelativeChain.mk (U ∩ V) (N + 1) w ∈ relCycles (U ∩ V) (N + 1))
    (hccyc : RelativeChain.mk (U ∪ V) (N + 1 + 1) c ∈ relCycles (U ∪ V) (N + 1 + 1)) :
    relKroneckerH (U ∩ V) (RelativeCohomology.mk (U ∩ V) (N + 1) g)
        (relMvDelta U V hU hV (N + 1)
          (RelativeHomology.mk (U ∪ V) (N + 1 + 1) ⟨RelativeChain.mk (U ∪ V) (N + 1 + 1) c, hccyc⟩))
      = relKronecker (U ∩ V) g.1 (RelativeChain.mk (U ∩ V) (N + 1) w) := by
  rw [relMvDelta_cover_partition U V hU hV (N + 1) c u w hu hw hbd hwcyc hccyc, relKroneckerH_mk_mk]

end SKEFTHawking.SingularRelMvDeltaPartition
