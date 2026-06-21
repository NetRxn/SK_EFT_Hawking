import Mathlib
import SKEFTHawking.SingularAbsCohomConnGeom
import SKEFTHawking.SingularCoverPartitionExist
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularConnSquareLHSExplicit

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — CLASS-FORM geometric representative of `absCohomConn`

`SingularSubHomologyMVCohomConn.absCohomConn` is **Kronecker-defined** (the `dualMap`-conjugate of the
homology MV connecting `subHomConnecting` through the perfect Kronecker pairing), so `b = absCohomConn a'`
gives no chain-level handle on `b` — only the pairing adjunction. The `hcross` reconciliation core in
`SingularHcrossClose` needs a class-form representative `absCohomConn [a'] = [b]` for an **explicit**
cocycle `b` over `sub (U ∪ V)`.

This file ships that class form, the absolute mirror of the committed relative
`SingularRelCohomMvConnectingGeom.relCohomMvConnecting_eq_mk_coboundary_cochainSplit`. The proof is
non-circular: by Kronecker non-degeneracy (`SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH`) the
two classes are equal iff they pair equally against every `sub (U ∪ V)`-cycle; every such cycle has a
cover-fine partition representative (`SingularCoverPartitionExist.exists_mvUnion_partition`, over the cover
`{val⁻¹U, val⁻¹V}` whose union is `univ`), on which the pairing form
`SingularAbsCohomConnGeom.kroneckerH_absCohomConn_cover_partition` reduces `absCohomConn`'s pairing to the
explicit chain pairing `⟨a'.1, seam-pushed ∂zB⟩`.

The explicit cocycle `b` and its chain-pairing value are carried **abstractly** (single hypothesis
`hb_pair`, which quantifies over the seam cycle `z` and the seam factorisation), exactly as
`kroneckerH_absCohomConn_seam`'s `hsh` carries the seam cycle abstractly — this dodges the documented
doubly-nested `restr (val⁻¹U) (val⁻¹V)` `whnf` heartbeat wall (the seam transport of `a'` into the cover
is where the wall lives; the abstract `hb_pair` keeps it a unification variable). A caller (e.g.
`SingularHcrossClose`) supplies `b := δ(cochainSplit (val⁻¹U) …)` and discharges `hb_pair` via
cap-Leibniz, getting the chain-computable representative the reconciliation core requires.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularExcision SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularSubHomologyMVCohomConn
  SKEFTHawking.SingularAbsCohomConnGeom SKEFTHawking.SingularCoverPartitionExist
  SKEFTHawking.SingularUniversalCoeff SKEFTHawking.SingularConnSquareLHSExplicit

namespace SKEFTHawking.SingularAbsCohomConnClassForm

variable {X : TopCat}

/-- **CLASS-FORM geometric representative of the ABSOLUTE cohomology MV connecting**. Given an explicit
cocycle `b : ker (coboundaryₗ (sub (U ∪ V)) (p + 1 + 1))` over `sub (U ∪ V)` whose Kronecker pairing
against every cover-partitioned cycle `chainIncl (val⁻¹U) zA + chainIncl (val⁻¹V) zB` equals the explicit
seam-pushed chain pairing of `a'` (hypothesis `hb_pair` — the same RHS the pairing form
`kroneckerH_absCohomConn_cover_partition` produces), the Kronecker-defined `absCohomConn (mk a')` IS the
`sub (U ∪ V)`-cohomology class `[b]`. The class-form mirror of
`SingularRelCohomMvConnectingGeom.relCohomMvConnecting_eq_mk_coboundary_cochainSplit`. -/
theorem absCohomConn_eq_mk_of_pair (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a' : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
    (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 1 + 1)))
    (hb_pair : ∀ (w : Homology (sub (U ∪ V)) (p + 1 + 1))
      (z : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) (p + 1)),
      subHomConnecting U V hU hV (p + 1) w
          = seamI U V (p + 1)
              (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)
                (Homology.mk _ (p + 1) z)) →
      kroneckerH (X := sub (U ∪ V)) (p + 1 + 1) (Submodule.Quotient.mk b) w
        = kronecker a'.1
            (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ => Iff.rfl)).continuous⟩ (p + 1)
              (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
                (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩
                  (p + 1) (z : SingularChain _ (p + 1))))) :
    absCohomConn U V hU hV p (Cohomology.mk (sub (U ∩ V)) (p + 1) a')
      = Cohomology.mk (sub (U ∪ V)) (p + 1 + 1) b := by
  refine sub_eq_zero.mp (cohomology_eq_zero_of_kroneckerH (p + 1) _ (fun w => ?_))
  rw [map_sub, LinearMap.sub_apply]
  -- Express `w` as the class of a cover-fine partition over `{val⁻¹U, val⁻¹V}` (whose union is `univ`).
  obtain ⟨wc, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨zA, zB, hcyc, hwpart⟩ := exists_mvUnion_partition
    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) (p + 1) wc
    (mem_subspaceChains_preimage_union U V (p + 1 + 1) wc.1)
  rw [show (Submodule.Quotient.mk wc : Homology (sub (U ∪ V)) (p + 1 + 1))
      = Homology.mk (sub (U ∪ V)) (p + 1 + 1) wc from rfl, hwpart]
  -- The pairing form supplies the seam cycle `hsh`, the seam factorisation (`hpair.1`), and the
  -- `absCohomConn`-pairing value (`hpair.2`). Both terms reduce to the same chain pairing.
  obtain ⟨hsh, hpair⟩ := kroneckerH_absCohomConn_cover_partition U V hU hV p a' zA zB hcyc
  rw [hpair.2, show Cohomology.mk (sub (U ∪ V)) (p + 1 + 1) b = Submodule.Quotient.mk b from rfl,
    hb_pair _ hsh hpair.1, sub_self]

end SKEFTHawking.SingularAbsCohomConnClassForm
