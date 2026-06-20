import Mathlib
import SKEFTHawking.SingularSubHomologyMV
import SKEFTHawking.SingularKroneckerFunctoriality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-LHSLeg) — the connecting square's LHS leg, explicit chain pairing

Pairing `a'` against `subHomConnecting w` reduces — given the seam factorisation
`subHomConnecting w = seamI (seamHom (mk z))` (the M2-direct form, with the `[∂zB]` seam cycle `z`
carried **abstractly** to dodge the `whnf` wall) — to the chain-level Kronecker pairing of `a'`'s rep
against `z` pushed forward through both seam homeomorphisms (`Homology.map_mk`). The counterpart of
`SingularRelMvDeltaPartition.relKroneckerH_relMvDelta_cover_partition` (M9b, the RHS leg).

The M2-direct hypothesis `hsh` is exactly what `SingularConnSquareLHSExplicit.subHomConnecting_cover_partition`
(+ `mvConnecting_cover_partition`) produces, with `z := boundaryExtract zB` supplied at the call site —
keeping the doubly-nested `restr (val⁻¹U) (val⁻¹V)` term a unification variable here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularSubHomologyMV

namespace SKEFTHawking.SingularConnSquareLHSLeg

variable {X : TopCat}

/-- **The connecting square's LHS leg, explicit** (seam cycle `z` abstract): pairing `a'` against
`subHomConnecting w`, given its seam factorisation `seamI (seamHom (mk z))`, equals the chain pairing of
`a'`'s rep against `z` pushed through both seam homeomorphisms. -/
theorem kroneckerH_subHomConnecting_seam (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (a' : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) n)) (w : Homology (sub (U ∪ V)) (n + 1))
    (z : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n)
    (hsh : subHomConnecting U V hU hV n w
      = seamI U V n (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n
          (Homology.mk _ n z))) :
    kroneckerH (X := sub (U ∩ V)) n (Submodule.Quotient.mk a') (subHomConnecting U V hU hV n w)
      = kronecker a'.1
          (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
              (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl)).continuous⟩ n
            (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
              (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩ n
              (z : SingularChain _ n))) := by
  rw [hsh, seamHomologyEquiv, LinearEquiv.ofBijective_apply, Homology.map_mk]
  show kroneckerH (X := sub (U ∩ V)) n (Submodule.Quotient.mk a')
      (Homology.map ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
          (fun _ => Iff.rfl), _⟩ n (Homology.mk _ n _)) = _
  rw [Homology.map_mk, Homology.mk, kroneckerH_mk_mk, cyclesMap_coe, cyclesMap_coe]

end SKEFTHawking.SingularConnSquareLHSLeg
