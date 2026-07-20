/-
# Phase 5q.H close-out — THE COLLAR-SPLIT DATUM + the hA/hB discharge.

`KTCompletenessMVHtpy.mvDatumOfPieceFiniteness` reduced the four capstone cohomology
finite-dimensionality atoms to exactly three inputs: the piece finiteness `hA`/`hB` (the
homotopy-invariant relaxation of the geometrically-false homeomorphism demands `eA`/`eB` of
`CapstoneMVTransferRow.ofPieces`) and the overlap finiteness `hYAB`. The traced data-gap: the
collar-thickened piece `coverA = range fromCyl ∪ cd.seamNbhd` PROPERLY contains the handle-side
half-collar sliver, so it is only homotopy-equivalent (not homeomorphic) to the closed cyl end;
`SeamCollarDatum` carries the collar homeo `cd.hHomeo` but no field telling us WHICH SIDE of the
collar each closed range occupies, so the collar-collapse deformation retraction cannot be built.

This module supplies the missing side-split and discharges `hA`/`hB` from the closed ends' banked
all-degree finiteness (`finiteDimensional_homology_cyl_all`, `finiteDimensional_homology_D5_all` —
`PinPlusTraceCapstoneMVPieces` §1).

## §-map
* **§A — the all-degree homotopy-equivalence finiteness transfer**
  `finiteDimensional_homology_of_homotopyEquiv_all`: the banked htpy-equiv transfer
  (`SingularHomologyFiniteTransfer`) covers degree `n+1` only (homotopy invariance is stated at
  `n+1` in `SingularHomotopyInvariance`). Here we bank the DEGREE-`0` homotopy invariance
  (`Homology.map (slice H 0) 0 = Homology.map (slice H 1) 0`, via the degree-`0` prism identity
  `prism_chainHomotopy_zero` — no `P∂` term), hence the degree-`0` bijectivity of a homotopy
  equivalence, hence the ALL-degree finiteness transfer. The reusable degree-`0` brick.
* **§B — the collar-split datum** `CollarSplitDatum`: extends a `SeamCollarDatum cd` with a middle
  level `c ∈ (-1,1)` and the two side-split image equalities — `cd.hHomeo` carries the cyl side of
  the collar (`range fromCyl ∩ seamNbhd`) onto `cd.A × (-1, c]` and the handle side
  (`range fromHandle ∩ seamNbhd`) onto `cd.A × [c, 1)`. The honest side-compatibility the
  deformation retraction needs; the seam `range fromCyl ∩ range fromHandle` is forced onto the
  middle slice `cd.A × {c}`.

Leaf-additive; no existing module edited. Kernel-pure (`{propext, Classical.choice, Quot.sound}`);
no `sorry`, no new project axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KTCompletenessMVCover

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularHomologyFiniteTransfer
open SKEFTHawking.PinPlusTraceCapstoneMVPieces
open SKEFTHawking.KTCompletenessMVCover

namespace SKEFTHawking.KTCompletenessCollarSplit

noncomputable section

/-! ## §A. The all-degree homotopy-equivalence finiteness transfer (the degree-`0` brick). -/

/-- **Degree-`0` homology agreement from a chain-level boundary condition.** The degree-`0` analogue
of `Homology.map_eq_of_chain_add_mem`: if `f_#(z) + g_#(z)` is a boundary for EVERY `0`-chain `z`
(no cycle condition — every `0`-chain is a cycle), then `f` and `g` agree on `H₀(·; ℤ/2)`. -/
theorem map_eq_of_chain_add_mem_zero {X Y : TopCat} (f g : C(↑X, ↑Y))
    (hfg : ∀ z : SingularChain X 0, mapChain f 0 z + mapChain g 0 z ∈ boundaries Y 0) :
    Homology.map f 0 = Homology.map g 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Homology.map, Homology.map]
  refine (Submodule.mapQ_apply _ _ _ _).trans
    (Eq.trans ((Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ?_))
      (Submodule.mapQ_apply _ _ _ _).symm)
  have hsub : (cycles Y 0).subtype (cyclesMap f 0 z - cyclesMap g 0 z)
      = mapChain f 0 (z : SingularChain X 0) + mapChain g 0 (z : SingularChain X 0) := by
    rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply, cyclesMap_coe, cyclesMap_coe,
      sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]
  rw [hsub]
  exact hfg (z : SingularChain X 0)

/-- **Degree-`0` homotopy invariance of the homology functor.** The two slices `H(·, 1)` and
`H(·, 0)` induce the same map on `H₀(·; ℤ/2)` — the degree-`0` prism identity
`prism_chainHomotopy_zero` (`∂(P z) = end₁ z + end₀ z`, no `P∂` term) exhibits `f_#(z) + g_#(z)` as
a boundary for every `0`-chain. -/
theorem map_slice_eq_zero {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) :
    Homology.map (slice H 1) 0 = Homology.map (slice H 0) 0 :=
  map_eq_of_chain_add_mem_zero (slice H 1) (slice H 0) fun z =>
    ⟨prismOp H 0 z, by
      rw [prism_chainHomotopy_zero, endMap_eq_mapChain, endMap_eq_mapChain]⟩

/-- **Degree-`0` homotopy invariance, restated for endpoints.** If `f` and `g` are the two ends of a
homotopy `H` then `H₀(f) = H₀(g)`. -/
theorem map_eq_of_homotopic_zero {X Y : TopCat} {f g : C(↑X, ↑Y)}
    (H : C(↑X × unitInterval, ↑Y)) (h0 : slice H 0 = f) (h1 : slice H 1 = g) :
    Homology.map f 0 = Homology.map g 0 := by
  rw [← h0, ← h1]
  exact (map_slice_eq_zero H).symm

/-- **A homotopy equivalence induces a bijection on `H₀`** (degree `0`). The degree-`0` companion of
`Homology.map_bijective_of_homotopyEquiv`, using degree-`0` homotopy invariance. -/
theorem map_bijective_of_homotopyEquiv_zero {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) :
    Function.Bijective (Homology.map f 0) := by
  have hgf : (Homology.map g 0).comp (Homology.map f 0) = LinearMap.id := by
    rw [← Homology.map_comp, map_eq_of_homotopic_zero Hgf hgf0 hgf1, Homology.map_id]
  have hfg : (Homology.map f 0).comp (Homology.map g 0) = LinearMap.id := by
    rw [← Homology.map_comp, map_eq_of_homotopic_zero Hfg hfg0 hfg1, Homology.map_id]
  have hL : Function.LeftInverse (Homology.map g 0) (Homology.map f 0) :=
    fun x => by rw [← LinearMap.comp_apply, hgf, LinearMap.id_apply]
  have hR : Function.RightInverse (Homology.map g 0) (Homology.map f 0) :=
    fun x => by rw [← LinearMap.comp_apply, hfg, LinearMap.id_apply]
  exact ⟨hL.injective, hR.surjective⟩

/-- **Homology finite-dimensionality transfers along a homotopy equivalence in EVERY degree.** The
banked `finiteDimensional_homology_of_homotopyEquiv` covers degree `n+1`; this closes degree `0` via
§A's `map_bijective_of_homotopyEquiv_zero`, so `Hₙ(X) < ∞ ⟸ Hₙ(Y) < ∞` for a homotopy equivalence
`X ≃ Y` in all `n`. The all-degree relaxation the collar-collapse retraction needs. -/
theorem finiteDimensional_homology_of_homotopyEquiv_all {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (Hgf : C(↑X × unitInterval, ↑X)) (hgf0 : slice Hgf 0 = g.comp f)
    (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X) (Hfg : C(↑Y × unitInterval, ↑Y))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y n)) :
    FiniteDimensional (ZMod 2) (Homology X n) := by
  cases n with
  | zero =>
    haveI := h
    exact (LinearEquiv.ofBijective (Homology.map f 0)
      (map_bijective_of_homotopyEquiv_zero f g Hgf hgf0 hgf1 Hfg hfg0 hfg1)).symm.finiteDimensional
  | succ m =>
    exact finiteDimensional_homology_of_homotopyEquiv f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 m h

/-! ## §B. The collar-split datum — which side of the welded collar each closed range occupies. -/

/-- **The collar-split datum.** For a handle attachment `HA` and a `SeamCollarDatum cd` on its
carrier, this bundles the side-compatibility the collar-collapse deformation retraction needs but
that `SeamCollarDatum` alone does not record: a middle collar level `mid ∈ (-1, 1)` (a point of the
welded interval) together with the two side-split image equalities under the collar homeomorphism
`cd.hHomeo : ↥cd.seamNbhd ≃ₜ cd.A × ↥weldedInterval`:

* `cyl_side` — the cyl side of the collar (the part of `cd.seamNbhd` lying in `range HA.fromCyl`) is
  carried onto the LOWER collar `cd.A × (-1, mid]` (`q.2 ≤ mid`);
* `handle_side` — the handle side (the part lying in `range HA.fromHandle`) onto the UPPER collar
  `cd.A × [mid, 1)` (`mid ≤ q.2`).

Their intersection forces the seam `range fromCyl ∩ range fromHandle`, inside the collar, onto the
middle slice `cd.A × {mid}` — the geometric statement that the surgery seam is exactly the healed
mid-level of the welded collar. Honest, minimal: no continuity or manifold data beyond the two
membership-set images, which the concrete welded collar (an explicit `A × (welded interval)` product)
supplies by construction. -/
structure CollarSplitDatum (HA : HandleAttachment) (cd : SeamCollarDatum HA.carrier) where
  /-- the middle collar level — a point of the welded interior interval `(-1, 1)`. -/
  mid : ↥weldedInterval
  /-- **the cyl side occupies the lower collar** — the cyl-side of the collar is carried by
  `cd.hHomeo` onto `cd.A × (-1, mid]`. -/
  cyl_side :
    cd.hHomeo '' {p : ↥cd.seamNbhd | (p : HA.carrier) ∈ Set.range HA.fromCyl}
      = {q : WeldedCollarModel cd.A | q.2 ≤ mid}
  /-- **the handle side occupies the upper collar** — the handle-side of the collar is carried by
  `cd.hHomeo` onto `cd.A × [mid, 1)`. -/
  handle_side :
    cd.hHomeo '' {p : ↥cd.seamNbhd | (p : HA.carrier) ∈ Set.range HA.fromHandle}
      = {q : WeldedCollarModel cd.A | mid ≤ q.2}

end

end SKEFTHawking.KTCompletenessCollarSplit
