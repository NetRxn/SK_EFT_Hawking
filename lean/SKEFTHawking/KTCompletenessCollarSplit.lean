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
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
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

/-! ## §Bʹ. Collar geometry from the split datum — the seam sits at the middle collar slice. -/

/-- From the split datum: a collar point lying in `range fromCyl` has collar coordinate `≤ mid`
(it is in the lower collar `cd.A × (-1, mid]`). -/
theorem collar_coord_le_mid {HA : HandleAttachment} {cd : SeamCollarDatum HA.carrier}
    (csd : CollarSplitDatum HA cd) (p : ↥cd.seamNbhd)
    (hp : (p : HA.carrier) ∈ Set.range HA.fromCyl) :
    (cd.hHomeo p).2 ≤ csd.mid := by
  have hmem : cd.hHomeo p
      ∈ cd.hHomeo '' {p : ↥cd.seamNbhd | (p : HA.carrier) ∈ Set.range HA.fromCyl} :=
    Set.mem_image_of_mem _ hp
  rw [csd.cyl_side] at hmem
  exact hmem

/-- From the split datum: a collar point lying in `range fromHandle` has collar coordinate `≥ mid`
(it is in the upper collar `cd.A × [mid, 1)`). -/
theorem collar_coord_ge_mid {HA : HandleAttachment} {cd : SeamCollarDatum HA.carrier}
    (csd : CollarSplitDatum HA cd) (p : ↥cd.seamNbhd)
    (hp : (p : HA.carrier) ∈ Set.range HA.fromHandle) :
    csd.mid ≤ (cd.hHomeo p).2 := by
  have hmem : cd.hHomeo p
      ∈ cd.hHomeo '' {p : ↥cd.seamNbhd | (p : HA.carrier) ∈ Set.range HA.fromHandle} :=
    Set.mem_image_of_mem _ hp
  rw [csd.handle_side] at hmem
  exact hmem

/-- **The seam sits at the middle collar slice.** A collar point in BOTH closed ranges — a seam
point, inside the collar — has collar coordinate exactly `mid`. This is the geometric content of the
split datum: the surgery seam `range fromCyl ∩ range fromHandle` is the healed mid-level of the
welded collar, so the collar slide (which fixes the level `mid`) fixes the seam — the compatibility
that lets the retraction glue to the identity on `range fromCyl`. -/
theorem seam_collar_coord_eq_mid {HA : HandleAttachment} {cd : SeamCollarDatum HA.carrier}
    (csd : CollarSplitDatum HA cd) (p : ↥cd.seamNbhd)
    (hpC : (p : HA.carrier) ∈ Set.range HA.fromCyl)
    (hpH : (p : HA.carrier) ∈ Set.range HA.fromHandle) :
    (cd.hHomeo p).2 = csd.mid :=
  le_antisymm (collar_coord_le_mid csd p hpC) (collar_coord_ge_mid csd p hpH)

/-! ## §Bʺ. The collar-slide coordinate — the explicit interval deformation collapsing to `mid`. -/

/-- The real value of the collar slide: `min w ((1-τ)·w + τ·mid)`. Fixes levels `≤ mid` (there the
convex combination is `≥ w`, so the `min` is `w`) and pushes a level `≥ mid` down toward `mid` (there
the convex combination is in `[mid, w]`). -/
def slideVal (mid w : ℝ) (τ : unitInterval) : ℝ :=
  min w ((1 - (τ : ℝ)) * w + (τ : ℝ) * mid)

/-- The slide value stays in the OPEN welded interval `(-1, 1)` — a `min` of `w ∈ (-1,1)` and a
convex combination of `w`, `mid ∈ (-1,1)`. -/
theorem slideVal_mem (mid w : ℝ) (τ : unitInterval)
    (hw : (-1 : ℝ) < w ∧ w < 1) (hm : (-1 : ℝ) < mid ∧ mid < 1) :
    (-1 : ℝ) < slideVal mid w τ ∧ slideVal mid w τ < 1 := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hm1, _⟩ := hm
  have hτ0 : (0 : ℝ) ≤ (τ : ℝ) := τ.2.1
  have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
  refine ⟨lt_min hw1 ?_, lt_of_le_of_lt (min_le_left _ _) hw2⟩
  have hconv_ge : min w mid ≤ (1 - (τ : ℝ)) * w + (τ : ℝ) * mid := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (τ : ℝ))
        (sub_nonneg.mpr (min_le_left w mid)),
      mul_nonneg hτ0 (sub_nonneg.mpr (min_le_right w mid))]
  exact lt_of_lt_of_le (lt_min hw1 hm1) hconv_ge

/-- The collar-slide coordinate as a point of the welded interval `(-1,1)`: `slideVal` packaged as an
element of `↥weldedInterval` (the nested `Icc(-1,1)`-then-open-interval subtype). -/
def slideCoord (mid w : ↥weldedInterval) (τ : unitInterval) : ↥weldedInterval :=
  ⟨⟨slideVal mid.val.val w.val.val τ,
      ⟨le_of_lt (slideVal_mem _ _ _ w.2 mid.2).1, le_of_lt (slideVal_mem _ _ _ w.2 mid.2).2⟩⟩,
    slideVal_mem _ _ _ w.2 mid.2⟩

/-- **The collar slide is continuous jointly in the level and the time.** `slideVal` is a `min` of
continuous real functions; packaged through the two nested subtype memberships it gives a continuous
`↥weldedInterval × unitInterval → ↥weldedInterval`. -/
theorem continuous_slideCoord (mid : ↥weldedInterval) :
    Continuous (fun p : ↥weldedInterval × unitInterval => slideCoord mid p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hw : Continuous (fun p : ↥weldedInterval × unitInterval => (p.1.val.val : ℝ)) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst
  have hτ : Continuous (fun p : ↥weldedInterval × unitInterval => ((p.2 : ℝ))) :=
    continuous_subtype_val.comp continuous_snd
  exact (hw.min (((continuous_const.sub hτ).mul hw).add (hτ.mul continuous_const)))

/-- At a level `w ≤ mid` the slide is the identity — the convex combination is `≥ w`, so the `min`
is `w`. -/
theorem slideVal_fix_of_le (mid w : ℝ) (τ : unitInterval) (h : w ≤ mid) :
    slideVal mid w τ = w := by
  rw [slideVal, min_eq_left]
  nlinarith [mul_nonneg τ.2.1 (sub_nonneg.mpr h)]

/-- At time `0` the slide is the identity. -/
theorem slideVal_at_zero (mid w : ℝ) : slideVal mid w 0 = w := by
  simp [slideVal, Set.Icc.coe_zero]

/-- The `↥weldedInterval` slide fixes a level `≤ mid`. -/
theorem slideCoord_fix_of_le (mid w : ↥weldedInterval) (τ : unitInterval) (h : w ≤ mid) :
    slideCoord mid w τ = w := by
  have hle : w.val.val ≤ mid.val.val := h
  exact Subtype.ext (Subtype.ext (slideVal_fix_of_le _ _ _ hle))

/-- The `↥weldedInterval` slide is the identity at time `0`. -/
theorem slideCoord_at_zero (mid w : ↥weldedInterval) : slideCoord mid w 0 = w :=
  Subtype.ext (Subtype.ext (slideVal_at_zero _ _))

/-! ## §B‴. The collar slide transported to the seam neighbourhood. -/

/-- **The collar slide on the seam neighbourhood.** Transport the interval slide `slideCoord`
through the collar homeomorphism `cd.hHomeo` (fixing the `cd.A` attaching-base factor): at time `τ`
it fixes collar levels `≤ mid` and pushes levels `≥ mid` down toward the middle slice. Continuous. -/
def slideCollarMap {W : Type} [TopologicalSpace W] (cd : SeamCollarDatum W) (mid : ↥weldedInterval) :
    ↥cd.seamNbhd × unitInterval → ↥cd.seamNbhd :=
  fun p => cd.hHomeo.symm ((cd.hHomeo p.1).1, slideCoord mid (cd.hHomeo p.1).2 p.2)

theorem continuous_slideCollarMap {W : Type} [TopologicalSpace W] (cd : SeamCollarDatum W)
    (mid : ↥weldedInterval) : Continuous (slideCollarMap cd mid) := by
  refine cd.hHomeo.symm.continuous.comp (Continuous.prodMk ?_ ?_)
  · exact continuous_fst.comp (cd.hHomeo.continuous.comp continuous_fst)
  · exact (continuous_slideCoord mid).comp (Continuous.prodMk
      (continuous_snd.comp (cd.hHomeo.continuous.comp continuous_fst)) continuous_snd)

/-- **The collar slide fixes a point whose collar level is `≤ mid`.** In particular (with §Bʹ) it
fixes the cyl side of the collar and the seam — the identity-gluing compatibility on `range fromCyl`. -/
theorem slideCollarMap_fix_of_le {W : Type} [TopologicalSpace W] (cd : SeamCollarDatum W)
    (mid : ↥weldedInterval) (p : ↥cd.seamNbhd) (τ : unitInterval) (h : (cd.hHomeo p).2 ≤ mid) :
    slideCollarMap cd mid (p, τ) = p := by
  rw [slideCollarMap, slideCoord_fix_of_le _ _ _ h]
  simp

/-- **The collar slide is the identity at time `0`.** -/
theorem slideCollarMap_at_zero {W : Type} [TopologicalSpace W] (cd : SeamCollarDatum W)
    (mid : ↥weldedInterval) (p : ↥cd.seamNbhd) :
    slideCollarMap cd mid (p, 0) = p := by
  rw [slideCollarMap, slideCoord_at_zero]
  simp

/-! ## §C. The closed ends as carrier subspaces, and their banked all-degree finiteness. -/

/-- **The cyl end `B` sits inside `W` as the closed subspace `↥(range fromCyl)`** — `fromCyl` is a
closed embedding, so it is a homeomorphism onto its range. The `Homeomorph`-packaged form of the
banked `isClosedEmbedding_fromCyl`. -/
def cylRangeHomeo (HA : HandleAttachment) : HA.B ≃ₜ ↥(Set.range HA.fromCyl) :=
  HA.isClosedEmbedding_fromCyl.isEmbedding.toHomeomorph

/-- **The handle end `Ha` sits inside `W` as the closed subspace `↥(range fromHandle)`.** -/
def handleRangeHomeo (HA : HandleAttachment) : HA.Ha ≃ₜ ↥(Set.range HA.fromHandle) :=
  HA.isClosedEmbedding_fromHandle.isEmbedding.toHomeomorph

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)

/-- **`H_*(range fromCyl) < ∞` in every degree** — the cyl end is `s.M × I`, so its all-degree
homology finiteness is the banked `finiteDimensional_homology_cyl_all`, transported across the
closed-embedding homeomorphism `cylRangeHomeo`. The closed-end stock the collar-collapse retraction
transfers to `coverA`. -/
theorem finiteDimensional_homology_sub_range_fromCyl (n : ℕ) :
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)) n) := by
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) s.M :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M)
  exact finiteDimensional_homology_of_homeomorph
    (cylRangeHomeo (ktHandleAttachment s.M D5 S hS φ hφ hφinj)).symm n
    (finiteDimensional_homology_cyl_all n)

/-- **`H_*(range fromHandle) < ∞` in every degree** — the handle end is `D⁵`, so its all-degree
homology finiteness is the banked `finiteDimensional_homology_D5_all`, transported across the
closed-embedding homeomorphism `handleRangeHomeo`. The closed-end stock the collar-collapse
retraction transfers to `coverB`. -/
theorem finiteDimensional_homology_sub_range_fromHandle (n : ℕ) :
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)) n) :=
  finiteDimensional_homology_of_homeomorph
    (handleRangeHomeo (ktHandleAttachment s.M D5 S hS φ hφ hφinj)).symm n
    (finiteDimensional_homology_D5_all n)

/-! ## §D. The `hA`/`hB` discharge, reduced to the collar-collapse homotopy equivalence. -/

variable (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The `hA` discharge, given the collar-collapse deformation retraction.** The collar-thickened
cyl piece `coverA = range fromCyl ∪ cd.seamNbhd` is homotopy-equivalent to the closed cyl end
`range fromCyl` (the collar-collapse deformation retraction — the geometrically-honest replacement
for the false homeomorphism `eA`). Given that homotopy equivalence
(`f`/`g`/`Hgf`/`Hfg` — the retraction, the inclusion, and the two witnessing homotopies), the
all-degree homology finiteness `hA` of `coverA` transfers from the closed cyl end's banked
finiteness (§C `finiteDimensional_homology_sub_range_fromCyl`) through §A's all-degree
homotopy-equivalence transfer. This is `hA` reduced to EXACTLY the collar-collapse homotopy
equivalence — the residual the `CollarSplitDatum` collar slide supplies geometrically. -/
theorem finiteDimensional_homology_coverA_of_htpyEquiv
    (f : C(↑(sub (coverA s t S hS φ hφ hφinj cd hseam d)),
        ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl))))
    (g : C(↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)),
        ↑(sub (coverA s t S hS φ hφ hφinj cd hseam d))))
    (Hgf : C(↑(sub (coverA s t S hS φ hφ hφinj cd hseam d)) × unitInterval,
        ↑(sub (coverA s t S hS φ hφ hφinj cd hseam d))))
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id _)
    (Hfg : C(↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)) × unitInterval,
        ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl))))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id _) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n) :=
  finiteDimensional_homology_of_homotopyEquiv_all f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 n
    (finiteDimensional_homology_sub_range_fromCyl s S hS φ hφ hφinj n)

/-- **The `hB` discharge, given the collar-collapse deformation retraction.** Symmetric to
`finiteDimensional_homology_coverA_of_htpyEquiv`: the collar-thickened handle piece
`coverB = range fromHandle ∪ cd.seamNbhd` is homotopy-equivalent to the closed handle end
`range fromHandle` (`≃ D⁵`), so `hB` transfers from §C's
`finiteDimensional_homology_sub_range_fromHandle`. -/
theorem finiteDimensional_homology_coverB_of_htpyEquiv
    (f : C(↑(sub (coverB s t S hS φ hφ hφinj cd hseam d)),
        ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle))))
    (g : C(↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)),
        ↑(sub (coverB s t S hS φ hφ hφinj cd hseam d))))
    (Hgf : C(↑(sub (coverB s t S hS φ hφ hφinj cd hseam d)) × unitInterval,
        ↑(sub (coverB s t S hS φ hφ hφinj cd hseam d))))
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id _)
    (Hfg : C(↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)) × unitInterval,
        ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle))))
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id _) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n) :=
  finiteDimensional_homology_of_homotopyEquiv_all f g Hgf hgf0 hgf1 Hfg hfg0 hfg1 n
    (finiteDimensional_homology_sub_range_fromHandle s S hS φ hφ hφinj n)

end

end SKEFTHawking.KTCompletenessCollarSplit
