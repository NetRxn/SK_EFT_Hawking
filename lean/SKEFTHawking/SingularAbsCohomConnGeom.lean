import Mathlib
import SKEFTHawking.SingularSubHomologyMVCohomConn
import SKEFTHawking.SingularConnSquareLHSLeg
import SKEFTHawking.SingularConnSquareLHSExplicit

/-!
# Phase 5q.F (w₂-foundation) — geometric cover-split realization of the ABSOLUTE cohomology MV connecting

Mirror of `SingularRelCohomMvConnectingGeom` for the **absolute** cohomology MV connecting
`SingularSubHomologyMVCohomConn.absCohomConn : Hᵖ⁺¹(sub(U∩V)) → Hᵖ⁺²(sub(U∪V))` (the `dualMap`-conjugate
of the homology MV connecting `subHomConnecting` through the perfect Kronecker pairing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularMvDeltaPartition
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularSubHomologyMVCohomConn
  SKEFTHawking.SingularConnSquareLHSLeg SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularAbsCohomConnGeom

variable {X : TopCat}

/-- **Geometric cover-split realization of the ABSOLUTE cohomology MV connecting (pairing form)**. The
Kronecker-defined `absCohomConn` (the `dualMap`-conjugate of the homology connecting `subHomConnecting`
through the perfect Kronecker pairing), paired against a class `w`, equals the **chain-level** Kronecker
pairing of `a'`'s cocycle rep against the seam cycle `z` pushed forward through both seam homeomorphisms
(`seamHomeo`, then `subSeamHomeo`). Given the seam factorisation
`subHomConnecting w = seamI (seamHom (mk z))` (`hsh`, with `z` carried **abstractly** to dodge the
`whnf` heartbeat wall the doubly-nested `restr (val⁻¹U) (val⁻¹V)` subspace triggers when spelled
concretely — see `SingularConnSquareLHSExplicit`), the proof is the defining adjunction
`SingularSubHomologyMVCohomConn.kroneckerH_absCohomConn` (moving `a'` off `absCohomConn` onto
`subHomConnecting`) followed by the explicit LHS-leg chain pairing
`SingularConnSquareLHSLeg.kroneckerH_subHomConnecting_seam`. The absolute analogue of
`SingularRelCohomMvConnectingGeom.relKroneckerH_relCohomMvConnecting_cover_partition` (the relative
pairing form): both transport the abstract `dualMap`-conjugate cohomology connecting onto a concrete
chain pairing, so downstream cap/cup computations have a representative to work with. -/
theorem kroneckerH_absCohomConn_seam (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a' : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
    (w : Homology (sub (U ∪ V)) (p + 1 + 1))
    (z : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) (p + 1))
    (hsh : subHomConnecting U V hU hV (p + 1) w
      = seamI U V (p + 1)
          (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
            (Homology.mk _ (p + 1) z))) :
    kroneckerH (X := sub (U ∪ V)) (p + 1 + 1)
        (absCohomConn U V hU hV p (Cohomology.mk (sub (U ∩ V)) (p + 1) a')) w
      = kronecker a'.1
          (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
              (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl)).continuous⟩ (p + 1)
            (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
              (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩ (p + 1)
              (z : SingularChain _ (p + 1)))) := by
  rw [show Cohomology.mk (sub (U ∩ V)) (p + 1) a' = Submodule.Quotient.mk a' from rfl,
    kroneckerH_absCohomConn]
  exact kroneckerH_subHomConnecting_seam U V hU hV (p + 1) a' w z hsh

/-- **Geometric cover-split realization of the ABSOLUTE cohomology MV connecting (cover-partition
form)**. For a cover-partitioned cycle `z = chainIncl (val⁻¹U) zA + chainIncl (val⁻¹V) zB` of
`sub (U ∪ V)`, there is a seam cycle (the `V`-part boundary `∂zB` extracted into the
`sub (restr (val⁻¹U) (val⁻¹V))` seam) realizing the bottom-row MV connecting
(`subHomConnecting [z] = seamI (seamHom (mk ∂zB))`, via `SingularConnSquareLHSExplicit`'s M2-direct
chain action `subHomConnecting_cover_partition` + `mvDelta_cover_partition`) and pairing `absCohomConn a'`
against `[z]` equals the chain pairing of `a'`'s rep against `∂zB` pushed through both seam
homeomorphisms (via `kroneckerH_absCohomConn_seam`). The seam cycle is bound under `∃` (its witness
constructed *in the proof*) so the doubly-nested `restr (val⁻¹U) (val⁻¹V)` subspace type never appears
*spelled in the committed conclusion* — the same wall-dodge `subHomConnecting_cover_partition` uses,
since spelling `boundaryExtract (restr (val⁻¹U) (val⁻¹V)) …` inline exceeds the elaborator's `whnf`
heartbeat budget. The absolute analogue of the relative
`SingularRelMvDeltaPartition.relKroneckerH_relMvDelta_cover_partition`, lifted through `absCohomConn`. -/
theorem kroneckerH_absCohomConn_cover_partition (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a' : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
    (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
    (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (p + 1 + 1) zA
        + chainIncl (Subtype.val ⁻¹' V) (p + 1 + 1) zB ∈ cycles (sub (U ∪ V)) (p + 1 + 1)) :
    ∃ z : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) (p + 1),
      subHomConnecting U V hU hV (p + 1)
          (Homology.mk (sub (U ∪ V)) (p + 1 + 1) ⟨_, hz_cyc⟩)
        = seamI U V (p + 1)
            (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
              (Homology.mk _ (p + 1) z))
      ∧ kroneckerH (X := sub (U ∪ V)) (p + 1 + 1)
            (absCohomConn U V hU hV p (Cohomology.mk (sub (U ∩ V)) (p + 1) a'))
            (Homology.mk (sub (U ∪ V)) (p + 1 + 1) ⟨_, hz_cyc⟩)
        = kronecker a'.1
            (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ => Iff.rfl)).continuous⟩ (p + 1)
              (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
                (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩
                  (p + 1) (z : SingularChain _ (p + 1)))) := by
  refine ⟨⟨_, boundaryExtract_mem_cycles
    (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
    ⟨zB, zB_mem_relCycleLift (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
      zA zB hz_cyc⟩⟩, ?_, ?_⟩
  · exact subHomConnecting_cover_partition U V hU hV (p + 1) zA zB hz_cyc _
      (mvDelta_cover_partition (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
        (cover_preimage U V hU hV) zA zB hz_cyc)
  · exact kroneckerH_absCohomConn_seam U V hU hV p a'
      (Homology.mk (sub (U ∪ V)) (p + 1 + 1) ⟨_, hz_cyc⟩) _
      (subHomConnecting_cover_partition U V hU hV (p + 1) zA zB hz_cyc _
        (mvDelta_cover_partition (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
          (cover_preimage U V hU hV) zA zB hz_cyc))

end SKEFTHawking.SingularAbsCohomConnGeom
