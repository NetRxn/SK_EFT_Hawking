import Mathlib
import SKEFTHawking.SingularAbsCohomConnClassForm
import SKEFTHawking.SingularKroneckerFunctoriality
import SKEFTHawking.SingularCohomologySnake
import SKEFTHawking.SingularConnSquareMatchLHS
import SKEFTHawking.SingularSeamExtend
import SKEFTHawking.SingularRelCohomMvConnectingGeom
import SKEFTHawking.SingularCapSubKDuality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — the ambient-lift seam-pairing bridge (BRICK 1 core)

Toward the UNCONDITIONAL class-form of `absCohomConn` (the absolute mirror of
`SingularRelCohomMvConnectingGeom.relCohomMvConnecting_eq_mk_coboundary_cochainSplit`): the absolute
cohomology MV connecting `SingularSubHomologyMVCohomConn.absCohomConn` is Kronecker-defined, and the
class-form realizer `SingularAbsCohomConnClassForm.absCohomConn_eq_mk_of_pair` reduces it to discharging
an abstract seam-pairing hypothesis `hb_pair` for an explicit cocycle `b` over `sub (U ∪ V)`.

This file ships the **core seam-pairing bridge** that any such discharge must thread: the
`ambientLift` — the double extend-by-zero (`SingularSeamExtend.seamExtend`, applied along the two nested
seam inclusions `sub (restr val⁻¹U val⁻¹V) ↪ sub (val⁻¹V) ↪ sub (U ∪ V)`) of the seam-transport
`seamTransport` of `a'` — paired against the seam-supported connecting boundary
`∂ (chainIncl val⁻¹V zB)` lands **exactly** the geometry pairing
`SingularAbsCohomConnGeom.kroneckerH_absCohomConn_cover_partition`'s right-hand side
`⟨a'.1, seam-push (boundaryExtract zB)⟩`. The proof threads, wall-free (the seam-transport is carried
through the seam homeos *abstractly* — no doubly-nested `restr` spelled in any heavy goal):
`chainIncl_chainBoundary` (push `∂` inside) → `kronecker_pullbackCochain` + `pullbackCochain_seamExtend`
(strip the OUTER extension) → `chainIncl_boundaryExtract` (the relCycleLift seam-support `hlift`) +
`kronecker_pullbackCochain` + `pullbackCochain_seamExtend` (strip the INNER extension) →
`kronecker_mapChain` ×2 (move the seam-transport from the cochain onto the chain).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularSubHomologyMVCohomConn SKEFTHawking.SingularCohomologySnake
  SKEFTHawking.SingularAbsCohomConnGeom SKEFTHawking.SingularAbsCohomConnClassForm
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularConnSquareMatchLHS
  SKEFTHawking.SingularSeamExtend SKEFTHawking.SingularRelCohomMvConnectingGeom
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularCapSubKDuality

namespace SKEFTHawking.SingularAbsCohomConnClassFormDischarge

variable {X : TopCat}

/-- The seam-transport of a `sub (U ∩ V)`-cochain to a seam cochain over
`restr (val⁻¹U) (val⁻¹V)` (a set in `sub (val⁻¹V)`): pull back through `subSeamHomeo` then `seamHomeo`. -/
noncomputable def seamTransport (U V : Set ↑X) (p : ℕ)
    (a' : SingularCochain (sub (U ∩ V)) (p + 1)) :
    SingularCochain (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)))
      (p + 1) :=
  pullbackCochainMap ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
      (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩ (p + 1)
    (pullbackCochainMap ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
        (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
          (fun _ => Iff.rfl)).continuous⟩ (p + 1) a')

/-- The ambient `sub (U ∪ V)`-cochain: double extend-by-zero of the seam-transport — first along the
inner seam inclusion `sub (restr val⁻¹U val⁻¹V) ↪ sub (val⁻¹V)`, then along `sub (val⁻¹V) ↪ sub (U∪V)`. -/
noncomputable def ambientLift (U V : Set ↑X) (p : ℕ)
    (a' : SingularCochain (sub (U ∩ V)) (p + 1)) :
    SingularCochain (sub (U ∪ V)) (p + 1) :=
  seamExtend (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (p + 1)
    (seamExtend (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
      (seamTransport U V p a'))

/-- **The seam pairing of the ambient lift.** Pairing the ambient lift against the seam-supported
boundary `∂(chainIncl val⁻¹V zB)` strips both extensions and lands the seam-transport pairing
`⟨a'.1, seam-push (boundaryExtract zB)⟩`. -/
theorem kronecker_ambientLift_chainIncl_boundary (U V : Set ↑X) (p : ℕ)
    (a' : SingularCochain (sub (U ∩ V)) (p + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
    (hlift : chainBoundary (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1) zB
      ∈ subspaceChains (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)) :
    kronecker (ambientLift U V p a')
        (chainBoundary (sub (U ∪ V)) (p + 1)
          (chainIncl (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (p + 1 + 1) zB))
      = kronecker a'
          (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
              (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl)).continuous⟩ (p + 1)
            (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
              (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩
                (p + 1)
              (boundaryExtract (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))
                (p + 1) ⟨zB, hlift⟩ : SingularChain _ (p + 1)))) := by
  -- Step 1: push `∂` inside `chainIncl`, then strip the outer extension via `pullbackCochain`.
  rw [← chainIncl_chainBoundary, ← kronecker_pullbackCochain]
  rw [show pullbackCochain (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (p + 1) (ambientLift U V p a')
      = seamExtend (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
          (seamTransport U V p a') from pullbackCochain_seamExtend _ _ _]
  -- Step 2: `∂zB` is seam-supported (the relCycleLift `hlift`); strip the inner extension.
  rw [show (chainBoundary (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1)) zB
      = chainIncl (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
          (boundaryExtract (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))
            (p + 1) ⟨zB, hlift⟩)
        from (chainIncl_boundaryExtract _ (p + 1) ⟨zB, hlift⟩).symm]
  rw [← kronecker_pullbackCochain]
  rw [show pullbackCochain (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
      (seamExtend (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
        (seamTransport U V p a'))
      = seamTransport U V p a' from pullbackCochain_seamExtend _ _ _]
  -- Step 3: `seamTransport = pullbackCochainMap seam (pullbackCochainMap subSeam a')`; move onto chain.
  rw [seamTransport, kronecker_mapChain]
  exact (kronecker_mapChain _ (p + 1) _ _).symm

end SKEFTHawking.SingularAbsCohomConnClassFormDischarge
