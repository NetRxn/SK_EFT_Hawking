/-
# Phase 5q.H — the S²×S² cross-value WITNESS: `hcross_pm` reduced to the hemisphere class

The geometric slices of the hcross MV cup–Stokes peel (task #289; B2's generic engine is
`SphereProdStokesPeel`, the cocycle-generic circle peel is `TorusCrossPeelGen`, the partition input
is `SingularCoverPartitionAmbientInt`). This module builds the concrete S²-witness data and
executes the full value chain:

* §1 — the UCT-dual **generator pair** on `S²`: the class `xS` with `⟨xS, ·⟩ = topSphereIsoInt 1`
  (Kronecker-dual to the computed `H₂(S²;ℤ) ≅ ℤ`), a cocycle representative `wSc`, a fundamental
  cycle representative `zSc`, and the normalization `⟨wSc, zSc⟩ = 1`.
* §2 — **primitives on the punctured caps**: `H²(S²∖{u};ℤ) = 0` (punctured acyclicity + UCT), so
  the restriction of `wSc` to each cap has an explicit 1-cochain primitive.
* §3 — the **polar product-cover leg data** on `S²×S²` (cover on the SECOND factor): the pullback
  cochains `aC = fst*wSc`, `bC = snd*wSc`, and the leg-primitive equations
  `ι_leg* bC = δ(legSnd* ω)` the seam assembly consumes.
* §4 — the **equator cross map** `S²×S¹ → seam` and the factorization of the transported seam
  difference through the second projection: `crossJ* d = snd* ηS` with `ηS` a 1-COCYCLE on `S¹`.
* §5 — the **peel evaluation**: `F(g) = ⟨ηS, [S¹-cycle]⟩ · ⟨wSc, zSc⟩ = ⟨ηS, t1chain⟩`, and the
  **filling argument**: `⟨ηS, t1chain⟩ = ⟨wSc, hemiDiff⟩` where `hemiDiff` is the explicit
  hemisphere-difference 2-cycle on `S²` (cap fillings of the pushed equator loop, which exist by
  `H₁(S²∖{u};ℤ) = 0`).
* §6 — **the conditional headline** `hcross_pm_of_hemiUnit`: if the hemisphere-difference class
  pairs to a UNIT against `xS` (the ONE remaining geometric fact — `[D_B − D_A] = ±[S²]`), then
  `interFormInt fc (alphaOf xS) (betaOf xS)` is a unit — the ±-sign Eilenberg–Zilber cross value.
  The ℤ-divisibility closes everything else: `F(g) = (e γ)·F(t_B)` with `F(t_B)` the hcross value
  (coordinate-1 seam class) forces BOTH factors to be units once `F(g) = ±1`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdCrossInt
import SKEFTHawking.SphereProdStokesPeel
import SKEFTHawking.TorusCrossPeelGen
import SKEFTHawking.KummerT4GramCross
import SKEFTHawking.SingularCoverPartitionAmbientInt
import SKEFTHawking.SingularSphereMiddleInt

namespace SKEFTHawking.SphereProdCrossWitnessInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_cup
  cochainPullbackInt_mem_ker kronecker_cochainPullbackInt coboundary_cochainPullbackInt
  cohomologyPullbackInt cohomologyPullbackInt_mk)
open SKEFTHawking.SingularAbsoluteUCInt (ucIntEquivOfFree ucIntEquivOfFree_apply)
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc antipode ne_antipode)
open SKEFTHawking.SingularSphereHomologyInt (punctured_sphere_homology_trivialInt)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_middleInt)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst)
open SKEFTHawking.SphereProdHOneInt (coverA coverB coverAB_cover)
open SKEFTHawking.SphereProdHTwoInt (SphSph sndCM)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl seamHomeo)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularMvDeltaPartitionInt (mvDelta_cover_partition zB_mem_relCycleLift)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf)
open SKEFTHawking.SphereProdStokesPeel (cochainPullbackInt_comp cochainPullbackInt_id
  seamCochainOf interCommMap seam_difference_cocycle kronecker_cup_cover_seam_cup_form)

/-! ## §1. The UCT-dual generator pair on `S²` -/

/-- `H₁(S²;ℤ) = 0` — the below-top vanishing instance the degree-2 UCT consumes. -/
instance : Subsingleton (Homology (Sph 2) 1) :=
  subsingleton_of_forall_eq 0 fun x => sphere_homology_middleInt 1 2 one_pos one_lt_two x

instance : Module.Free ℤ (Homology (Sph 2) 1) := Module.Free.of_subsingleton ℤ _

/-- The `(0 + 1)`-keyed form the UCT instance search asks for. -/
instance : Module.Free ℤ (Homology (Sph 2) (0 + 1)) :=
  inferInstanceAs (Module.Free ℤ (Homology (Sph 2) 1))

/-- **The dual generator class** `xS ∈ H²(S²;ℤ)`: the UCT preimage of the computed coordinate
functional `topSphereIsoInt 1 : H₂(S²;ℤ) ≅ ℤ`. -/
noncomputable def xS : Cohomology (Sph 2) 2 :=
  (ucIntEquivOfFree (Sph 2) 0).symm (topSphereIsoInt 1).toLinearMap

/-- The defining pairing rule: `⟨xS, h⟩ = topSphereIsoInt 1 h` for every `h : H₂(S²;ℤ)`. -/
theorem kroneckerHInt_xS (h : Homology (Sph 2) 2) :
    kroneckerHInt 2 xS h = topSphereIsoInt 1 h := by
  have hx : ucIntEquivOfFree (Sph 2) 0 xS = (topSphereIsoInt 1).toLinearMap :=
    (ucIntEquivOfFree (Sph 2) 0).apply_symm_apply _
  rw [ucIntEquivOfFree_apply] at hx
  exact LinearMap.congr_fun hx h

/-- A cocycle representative of `xS`. -/
noncomputable def wSc : LinearMap.ker (coboundaryₗ (Sph 2) 2) :=
  (Submodule.Quotient.mk_surjective _ xS).choose

theorem wSc_spec : Cohomology.mk (Sph 2) 2 wSc = xS :=
  (Submodule.Quotient.mk_surjective _ xS).choose_spec

theorem wSc_cocycle : coboundaryₗ (Sph 2) 2 wSc.1 = 0 := wSc.2

/-- A fundamental-cycle representative: a cycle whose class is `(topSphereIsoInt 1).symm 1`. -/
noncomputable def zSc : cycles (Sph 2) 2 :=
  (Submodule.Quotient.mk_surjective _ ((topSphereIsoInt 1).symm 1)).choose

theorem zSc_spec : Homology.mk (Sph 2) 2 zSc = (topSphereIsoInt 1).symm 1 :=
  (Submodule.Quotient.mk_surjective _ ((topSphereIsoInt 1).symm 1)).choose_spec

/-- **The witness normalization** `⟨wSc, zSc⟩ = 1`. -/
theorem kronecker_wSc_zSc : kronecker wSc.1 zSc.1 = 1 := by
  have h := kroneckerHInt_mk_mk wSc zSc
  rw [show (Submodule.Quotient.mk wSc : Cohomology (Sph 2) 2) = Cohomology.mk (Sph 2) 2 wSc
      from rfl, wSc_spec,
    show (Submodule.Quotient.mk zSc : Homology (Sph 2) 2) = Homology.mk (Sph 2) 2 zSc from rfl,
    zSc_spec, kroneckerHInt_xS] at h
  rw [← h, LinearEquiv.apply_symm_apply]

/-! ## §2. Primitives on the punctured caps: `H²(S²∖{u};ℤ) = 0` -/

section Punctured

variable (u : ↑(Sph 2))

instance : Subsingleton (Homology (Apunc 2 u) 1) :=
  subsingleton_of_forall_eq 0 fun x => punctured_sphere_homology_trivialInt 0 x

instance : Module.Free ℤ (Homology (Apunc 2 u) 1) := Module.Free.of_subsingleton ℤ _

instance : Module.Free ℤ (Homology (Apunc 2 u) (0 + 1)) :=
  inferInstanceAs (Module.Free ℤ (Homology (Apunc 2 u) 1))

/-- `H²(S²∖{u};ℤ) = 0`: the UCT sends it into the dual of the (trivial) `H₂` of the punctured
sphere. -/
theorem cohomology_two_punctured_eq_zero (ω : Cohomology (Apunc 2 u) 2) : ω = 0 := by
  have h0 : ucIntEquivOfFree (Apunc 2 u) 0 ω = 0 := by
    refine LinearMap.ext fun h => ?_
    rw [punctured_sphere_homology_trivialInt 1 h, map_zero, LinearMap.zero_apply]
  calc ω = (ucIntEquivOfFree (Apunc 2 u) 0).symm (ucIntEquivOfFree (Apunc 2 u) 0 ω) :=
        ((ucIntEquivOfFree (Apunc 2 u) 0).symm_apply_apply ω).symm
    _ = 0 := by rw [h0, map_zero]

/-- **Primitive extraction**: every 2-cocycle on the punctured sphere is an explicit coboundary. -/
theorem exists_primitive_two_punctured (c : SingularCochainInt (Apunc 2 u) 2)
    (hc : coboundaryₗ (Apunc 2 u) 2 c = 0) :
    ∃ ω₁ : SingularCochainInt (Apunc 2 u) 1, coboundaryₗ (Apunc 2 u) 1 ω₁ = c := by
  have hcls : Cohomology.mk (Apunc 2 u) 2 ⟨c, LinearMap.mem_ker.mpr hc⟩ = 0 :=
    cohomology_two_punctured_eq_zero u _
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hcls
  have hrange : c ∈ LinearMap.range (coboundaryₗ (Apunc 2 u) 1) := by
    have := Submodule.mem_comap.mp hmem
    exact this
  obtain ⟨ω₁, hω₁⟩ := hrange
  exact ⟨ω₁, hω₁⟩

end Punctured

/-! ## §3. The polar product-cover leg data on `S²×S²` -/

/-- The ambient `a`-cochain: the first-factor pullback of the witness cocycle — a cocycle
representative of `alphaOf xS`. -/
noncomputable def aC : SingularCochainInt SphSph 2 :=
  cochainPullbackInt (prodFst (Sph 2) (Sph 2)) 2 wSc.1

/-- The ambient `b`-cochain: the second-factor pullback — a cocycle representative of
`betaOf xS`. -/
noncomputable def bC : SingularCochainInt SphSph 2 :=
  cochainPullbackInt sndCM 2 wSc.1

theorem aC_cocycle : coboundaryₗ SphSph 2 aC = 0 :=
  LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker (prodFst (Sph 2) (Sph 2)) wSc)

theorem bC_cocycle : coboundaryₗ SphSph 2 bC = 0 :=
  LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker sndCM wSc)

/-- `[aC] = alphaOf xS` — the cocycle representative realizes the α-shape class. -/
theorem mk_aC : Cohomology.mk SphSph 2 ⟨aC, cochainPullbackInt_mem_ker _ wSc⟩ = alphaOf xS := by
  rw [alphaOf, ← wSc_spec]
  rfl

/-- `[bC] = betaOf xS`. -/
theorem mk_bC : Cohomology.mk SphSph 2 ⟨bC, cochainPullbackInt_mem_ker _ wSc⟩ = betaOf xS := by
  rw [betaOf, ← wSc_spec]
  rfl

/-- The inclusion of a punctured cap into the sphere. -/
noncomputable def puncIncl (u : ↑(Sph 2)) : C(↑(Apunc 2 u), ↑(Sph 2)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The second-coordinate collapse of a product-cover leg onto its punctured cap. -/
noncomputable def legSnd (u : ↑(Sph 2)) :
    C(↑(sub (X := SphSph) (coverA u)), ↑(Apunc 2 u)) :=
  ⟨fun p => ⟨p.1.2, p.2.2⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _⟩

/-- The cap primitive: `δ(omegaCap u) = (puncIncl u)* wSc`. -/
noncomputable def omegaCap (u : ↑(Sph 2)) : SingularCochainInt (Apunc 2 u) 1 :=
  (exists_primitive_two_punctured u (cochainPullbackInt (puncIncl u) 2 wSc.1)
    (LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker (puncIncl u) wSc))).choose

theorem omegaCap_spec (u : ↑(Sph 2)) :
    coboundaryₗ (Apunc 2 u) 1 (omegaCap u) = cochainPullbackInt (puncIncl u) 2 wSc.1 :=
  (exists_primitive_two_punctured u (cochainPullbackInt (puncIncl u) 2 wSc.1)
    (LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker (puncIncl u) wSc))).choose_spec

/-- The leg primitive: the second-coordinate pullback of the cap primitive. -/
noncomputable def uLeg (u : ↑(Sph 2)) : SingularCochainInt (sub (X := SphSph) (coverA u)) 1 :=
  cochainPullbackInt (legSnd u) 1 (omegaCap u)

/-- **The leg-primitive equation** `ι_leg* bC = δ(uLeg u)` — the `hb` input of the seam
assembly, at every punctured cap `u`. -/
theorem hbLeg (u : ↑(Sph 2)) :
    cochainPullbackInt (ambIncl (coverA u)) 2 bC
      = coboundaryₗ (sub (X := SphSph) (coverA u)) 1 (uLeg u) := by
  rw [bC, cochainPullbackInt_comp,
    show sndCM.comp (ambIncl (coverA u)) = (puncIncl u).comp (legSnd u) from
      ContinuousMap.ext fun p => rfl,
    ← cochainPullbackInt_comp]
  show cochainPullbackInt (legSnd u) 2 (cochainPullbackInt (puncIncl u) 2 wSc.1)
    = coboundary (sub (X := SphSph) (coverA u)) 1 (cochainPullbackInt (legSnd u) 1 (omegaCap u))
  rw [coboundary_cochainPullbackInt,
    show coboundary (Apunc 2 u) 1 (omegaCap u) = coboundaryₗ (Apunc 2 u) 1 (omegaCap u) from rfl,
    omegaCap_spec]

/-! ## §4. The equator cross map `S²×S¹ → seam` -/

/-- The polar puncture point of the second factor: the cover parameter `v = basePoint 2`. -/
noncomputable def vN : ↑(Sph 2) := basePoint 2

/-- The underlying equator vector `(0, s₀, s₁) ∈ ℝ³` of a circle point `s`. -/
noncomputable def eqVec (s : ↑(Sph 1)) : EuclideanSpace ℝ (Fin 3) :=
  ((s : EuclideanSpace ℝ (Fin 2)) 0) • EuclideanSpace.single 1 (1 : ℝ)
    + ((s : EuclideanSpace ℝ (Fin 2)) 1) • EuclideanSpace.single 2 (1 : ℝ)

theorem eqVec_apply_zero (s : ↑(Sph 1)) : eqVec s 0 = 0 := by
  simp [eqVec]

theorem eqVec_apply_one (s : ↑(Sph 1)) : eqVec s 1 = (s : EuclideanSpace ℝ (Fin 2)) 0 := by
  simp [eqVec]

theorem eqVec_apply_two (s : ↑(Sph 1)) : eqVec s 2 = (s : EuclideanSpace ℝ (Fin 2)) 1 := by
  simp [eqVec]

theorem eqVec_mem_sphere (s : ↑(Sph 1)) :
    eqVec s ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hs : ‖(s : EuclideanSpace ℝ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hs
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    eqVec_apply_zero, eqVec_apply_one, eqVec_apply_two]
  simpa using hs

/-- **The equatorial embedding** `S¹ ↪ S²`, `(s₀, s₁) ↦ (0, s₀, s₁)`. -/
noncomputable def eqIncl : C(↑(Sph 1), ↑(Sph 2)) :=
  ⟨fun s => ⟨eqVec s, eqVec_mem_sphere s⟩, by
    refine Continuous.subtype_mk ?_ _
    unfold eqVec
    fun_prop⟩

/-- The equator avoids the north pole (`first coordinate 0 ≠ 1`). -/
theorem eqIncl_ne_vN (s : ↑(Sph 1)) : eqIncl s ≠ vN := by
  intro h
  have h0 : eqVec s 0 = ((vN : ↑(Sph 2)) : EuclideanSpace ℝ (Fin 3)) 0 :=
    congrArg (fun p : ↑(Sph 2) => (p : EuclideanSpace ℝ (Fin 3)) 0) h
  have hv : ((vN : ↑(Sph 2)) : EuclideanSpace ℝ (Fin 3)) 0 = 1 := by
    show (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) 0 = 1
    simp
  rw [eqVec_apply_zero, hv] at h0
  norm_num at h0

/-- The equator avoids the south pole. -/
theorem eqIncl_ne_antipode_vN (s : ↑(Sph 1)) : eqIncl s ≠ antipode vN := by
  intro h
  have h0 : eqVec s 0 = ((antipode vN : ↑(Sph 2)) : EuclideanSpace ℝ (Fin 3)) 0 :=
    congrArg (fun p : ↑(Sph 2) => (p : EuclideanSpace ℝ (Fin 3)) 0) h
  have hv : ((antipode vN : ↑(Sph 2)) : EuclideanSpace ℝ (Fin 3)) 0 = -1 := by
    show (-(EuclideanSpace.single 0 (1 : ℝ)) : EuclideanSpace ℝ (Fin 3)) 0 = -1
    simp
  rw [eqVec_apply_zero, hv] at h0
  norm_num at h0

/-- The equator embedding into the NORTH punctured cap. -/
noncomputable def eqInclCapA : C(↑(Sph 1), ↑(Apunc 2 vN)) :=
  ⟨fun s => ⟨eqIncl s, eqIncl_ne_vN s⟩,
    Continuous.subtype_mk eqIncl.continuous _⟩

/-- The equator embedding into the SOUTH punctured cap. -/
noncomputable def eqInclCapB : C(↑(Sph 1), ↑(Apunc 2 (antipode vN))) :=
  ⟨fun s => ⟨eqIncl s, eqIncl_ne_antipode_vN s⟩,
    Continuous.subtype_mk eqIncl.continuous _⟩

open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.TorusCrossPeel (prodSnd torCross chainBoundary_torCross)

/-- **The equator cross map** `S²×S¹ → sub(coverA v ∩ coverB v)`: identity on the first factor,
the equator embedding on the second — landing in the seam because the equator avoids both
poles. -/
noncomputable def crossJ : C(↑(Tor (Sph 2)), ↑(sub (X := SphSph) (coverA vN ∩ coverB vN))) :=
  ⟨fun p => ⟨(p.1, eqIncl p.2),
      ⟨⟨Set.mem_univ _, eqIncl_ne_vN p.2⟩, ⟨Set.mem_univ _, eqIncl_ne_antipode_vN p.2⟩⟩⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.prodMk (eqIncl.continuous.comp continuous_snd)⟩

/-- The explicit cross 3-cycle on the seam: the pushforward of `torCross zSc` — the chain-level
`[S²] × [S¹]` inside the seam. -/
noncomputable def gChain : SingularChainInt (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 :=
  mapChainInt crossJ 3 (torCross (Sph 2) 2 zSc.1)

theorem zSc_cycle : chainBoundary (Sph 2) 1 zSc.1 = 0 := zSc.2

theorem gChain_cycle :
    chainBoundary (sub (X := SphSph) (coverA vN ∩ coverB vN)) 2 gChain = 0 := by
  rw [gChain, chainBoundary_mapChainInt,
    chainBoundary_torCross (Sph 2) 1 zSc.1 zSc_cycle, map_zero]

/-! ## §5. The seam difference, its `S¹`-factorization, the peel value, and the filling argument -/

open SKEFTHawking.CircleWindingCocycle (pathEdge arcA arcB)
open SKEFTHawking.KummerT4GramCross (t1chain t1_cycle)
open SKEFTHawking.TorusCrossPeelGen (kronecker_cup_snd_torCross_gen)
open SKEFTHawking.SphereProdStokesPeel (pullbackCochainInt_eq_cochainPullbackInt_ambIncl)

/-- The seam-difference 1-cochain of the assembly at the polar cover. -/
noncomputable def dSeam :
    SingularCochainInt (sub (X := SphSph) (coverA vN ∩ coverB vN)) 1 :=
  seamCochainOf (coverA vN) (coverB vN) 1 (uLeg (antipode vN))
    - cochainPullbackInt (interCommMap (coverB vN) (coverA vN)) 1
        (seamCochainOf (coverB vN) (coverA vN) 1 (uLeg vN))

/-- The circle-level seam difference: the equator pullbacks of the two cap primitives. -/
noncomputable def etaS : SingularCochainInt (Sph 1) 1 :=
  cochainPullbackInt eqInclCapB 1 (omegaCap (antipode vN))
    - cochainPullbackInt eqInclCapA 1 (omegaCap vN)

/-- Both cap composites `puncIncl ∘ eqInclCap` are the plain equator embedding. -/
theorem puncIncl_comp_eqInclCapA : (puncIncl vN).comp eqInclCapA = eqIncl :=
  ContinuousMap.ext fun _ => rfl

theorem puncIncl_comp_eqInclCapB : (puncIncl (antipode vN)).comp eqInclCapB = eqIncl :=
  ContinuousMap.ext fun _ => rfl

/-- **`etaS` is a 1-cocycle**: its coboundary is the difference of the two equator restrictions of
`wSc`, which agree. -/
theorem etaS_cocycle : coboundaryₗ (Sph 1) 1 etaS = 0 := by
  rw [etaS, map_sub]
  have hA : coboundaryₗ (Sph 1) 1 (cochainPullbackInt eqInclCapA 1 (omegaCap vN))
      = cochainPullbackInt eqIncl 2 wSc.1 := by
    show coboundary (Sph 1) 1 (cochainPullbackInt eqInclCapA 1 (omegaCap vN)) = _
    rw [coboundary_cochainPullbackInt,
      show coboundary (Apunc 2 vN) 1 (omegaCap vN) = coboundaryₗ (Apunc 2 vN) 1 (omegaCap vN)
        from rfl,
      omegaCap_spec, cochainPullbackInt_comp, puncIncl_comp_eqInclCapA]
  have hB : coboundaryₗ (Sph 1) 1 (cochainPullbackInt eqInclCapB 1 (omegaCap (antipode vN)))
      = cochainPullbackInt eqIncl 2 wSc.1 := by
    show coboundary (Sph 1) 1 (cochainPullbackInt eqInclCapB 1 (omegaCap (antipode vN))) = _
    rw [coboundary_cochainPullbackInt,
      show coboundary (Apunc 2 (antipode vN)) 1 (omegaCap (antipode vN))
        = coboundaryₗ (Apunc 2 (antipode vN)) 1 (omegaCap (antipode vN)) from rfl,
      omegaCap_spec, cochainPullbackInt_comp, puncIncl_comp_eqInclCapB]
  rw [hA, hB, sub_self]

/-- **The B-side seam-transport factorization**: the `crossJ`-pullback of the transported B-leg
primitive is the second-projection pullback of the equatorial cap primitive. All five transports
are subtype repackagings over the same underlying points. -/
theorem crossJ_seamB :
    cochainPullbackInt crossJ 1
        (seamCochainOf (coverA vN) (coverB vN) 1 (uLeg (antipode vN)))
      = cochainPullbackInt (prodSnd (Sph 2) (Sph 1)) 1
          (cochainPullbackInt eqInclCapB 1 (omegaCap (antipode vN))) := by
  unfold seamCochainOf uLeg
  rw [pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    cochainPullbackInt_comp, cochainPullbackInt_comp, cochainPullbackInt_comp,
    cochainPullbackInt_comp]
  exact congrArg (fun φ => cochainPullbackInt φ 1 (omegaCap (antipode vN)))
    (ContinuousMap.ext fun p => Subtype.ext rfl)

/-- **The A-side factorization** (through the extra `interComm` reassociation). -/
theorem crossJ_seamA :
    cochainPullbackInt crossJ 1
        (cochainPullbackInt (interCommMap (coverB vN) (coverA vN)) 1
          (seamCochainOf (coverB vN) (coverA vN) 1 (uLeg vN)))
      = cochainPullbackInt (prodSnd (Sph 2) (Sph 1)) 1
          (cochainPullbackInt eqInclCapA 1 (omegaCap vN)) := by
  unfold seamCochainOf uLeg
  rw [pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    cochainPullbackInt_comp, cochainPullbackInt_comp, cochainPullbackInt_comp,
    cochainPullbackInt_comp, cochainPullbackInt_comp]
  exact congrArg (fun φ => cochainPullbackInt φ 1 (omegaCap vN))
    (ContinuousMap.ext fun p => Subtype.ext rfl)

/-- **The seam-difference factorization**: `crossJ* dSeam = snd* etaS`. -/
theorem crossJ_dSeam :
    cochainPullbackInt crossJ 1 dSeam
      = cochainPullbackInt (prodSnd (Sph 2) (Sph 1)) 1 etaS := by
  rw [dSeam, etaS, map_sub, map_sub, crossJ_seamB, crossJ_seamA]

/-- The first-factor collapse: `crossJ* ((ι∩)* aC) = fst* wSc` on the torus. -/
theorem crossJ_aC :
    cochainPullbackInt crossJ 2
        (cochainPullbackInt (ambIncl (coverA vN ∩ coverB vN)) 2 aC)
      = cochainPullbackInt (prodFst (Sph 2) (Sph 1)) 2 wSc.1 := by
  unfold aC
  rw [cochainPullbackInt_comp, cochainPullbackInt_comp]
  exact congrArg (fun φ => cochainPullbackInt φ 2 wSc.1) (ContinuousMap.ext fun p => rfl)

/-- **THE PEEL VALUE**: the seam pairing of the assembly cochain against the explicit cross cycle
is the chain-level circle pairing `⟨etaS, eA⟩ + ⟨etaS, eB⟩`. -/
theorem F_gChain :
    kronecker
        (cup (cochainPullbackInt (ambIncl (coverA vN ∩ coverB vN)) 2 aC) dSeam) gChain
      = etaS (pathEdge (Sph 1) arcA) + etaS (pathEdge (Sph 1) arcB) := by
  rw [gChain, ← kronecker_cochainPullbackInt crossJ, cochainPullbackInt_cup, crossJ_aC,
    crossJ_dSeam, kronecker_cup_snd_torCross_gen (Sph 2) etaS etaS_cocycle wSc.1 zSc.1,
    kronecker_wSc_zSc]
  ring

/-! ### The filling argument: `⟨etaS, [S¹]⟩ = ⟨wSc, hemisphere difference⟩` -/

/-- **Filling extraction on a punctured cap**: every 1-cycle bounds (`H₁(S²∖{u};ℤ) = 0`). -/
theorem exists_filling_punctured (u : ↑(Sph 2)) (c : SingularChainInt (Apunc 2 u) 1)
    (hc : chainBoundary (Apunc 2 u) 0 c = 0) :
    ∃ D : SingularChainInt (Apunc 2 u) 2, chainBoundary (Apunc 2 u) 1 D = c := by
  have hcls : Homology.mk (Apunc 2 u) 1 ⟨c, LinearMap.mem_ker.mpr hc⟩ = 0 :=
    punctured_sphere_homology_trivialInt 0 _
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hcls
  have hrange : c ∈ LinearMap.range (chainBoundary (Apunc 2 u) 1) := by
    have := Submodule.mem_comap.mp hmem
    exact this
  obtain ⟨D, hD⟩ := hrange
  exact ⟨D, hD⟩

/-- The pushed equator loop in the north cap. -/
noncomputable def loopCapA : SingularChainInt (Apunc 2 vN) 1 := mapChainInt eqInclCapA 1 t1chain

/-- The pushed equator loop in the south cap. -/
noncomputable def loopCapB : SingularChainInt (Apunc 2 (antipode vN)) 1 :=
  mapChainInt eqInclCapB 1 t1chain

theorem loopCapA_cycle : chainBoundary (Apunc 2 vN) 0 loopCapA = 0 := by
  rw [loopCapA, chainBoundary_mapChainInt, t1_cycle, map_zero]

theorem loopCapB_cycle : chainBoundary (Apunc 2 (antipode vN)) 0 loopCapB = 0 := by
  rw [loopCapB, chainBoundary_mapChainInt, t1_cycle, map_zero]

/-- The north-cap filling of the equator loop. -/
noncomputable def fillA : SingularChainInt (Apunc 2 vN) 2 :=
  (exists_filling_punctured vN loopCapA loopCapA_cycle).choose

theorem fillA_spec : chainBoundary (Apunc 2 vN) 1 fillA = loopCapA :=
  (exists_filling_punctured vN loopCapA loopCapA_cycle).choose_spec

/-- The south-cap filling. -/
noncomputable def fillB : SingularChainInt (Apunc 2 (antipode vN)) 2 :=
  (exists_filling_punctured (antipode vN) loopCapB loopCapB_cycle).choose

theorem fillB_spec : chainBoundary (Apunc 2 (antipode vN)) 1 fillB = loopCapB :=
  (exists_filling_punctured (antipode vN) loopCapB loopCapB_cycle).choose_spec

/-- **The hemisphere-difference 2-chain on `S²`**: the difference of the two cap fillings, pushed
into the sphere. -/
noncomputable def hemiDiff : SingularChainInt (Sph 2) 2 :=
  mapChainInt (puncIncl (antipode vN)) 2 fillB - mapChainInt (puncIncl vN) 2 fillA

/-- `hemiDiff` is a 2-CYCLE: both fillings' boundaries push to the same equator loop. -/
theorem hemiDiff_cycle : chainBoundary (Sph 2) 1 hemiDiff = 0 := by
  rw [hemiDiff, map_sub, chainBoundary_mapChainInt, chainBoundary_mapChainInt,
    fillA_spec, fillB_spec, loopCapA, loopCapB, ← mapChainInt_comp, ← mapChainInt_comp,
    puncIncl_comp_eqInclCapA, puncIncl_comp_eqInclCapB, sub_self]

/-- **The hemisphere class** — the ONE remaining geometric object: the class of the
hemisphere-difference cycle in `H₂(S²;ℤ)`. -/
noncomputable def hemiClass : Homology (Sph 2) 2 :=
  Homology.mk (Sph 2) 2 ⟨hemiDiff, LinearMap.mem_ker.mpr hemiDiff_cycle⟩

/-- Left-subtraction unfolding for the pairing. -/
theorem kronecker_sub_left' {X : TopCat} {n : ℕ} (f g : SingularCochainInt X n)
    (c : SingularChainInt X n) :
    kronecker (f - g) c = kronecker f c - kronecker g c := by
  have h : f - g = f + (-1 : ℤ) • g := by rw [neg_one_smul]; ring
  rw [h, kronecker_add_left, kronecker_smul_left, neg_one_smul, ← sub_eq_add_neg]

/-- **THE FILLING IDENTITY**: the circle pairing of the seam difference equals the `wSc`-pairing
of the hemisphere-difference cycle — i.e. the `topSphereIsoInt`-coordinate of `hemiClass`. -/
theorem etaS_pairing_eq_hemi :
    etaS (pathEdge (Sph 1) arcA) + etaS (pathEdge (Sph 1) arcB)
      = topSphereIsoInt 1 hemiClass := by
  have hsum : etaS (pathEdge (Sph 1) arcA) + etaS (pathEdge (Sph 1) arcB)
      = kronecker etaS t1chain := by
    rw [t1chain, kronecker_add_right, kronecker_single, kronecker_single, one_mul, one_mul]
  rw [hsum, etaS, kronecker_sub_left', kronecker_cochainPullbackInt, kronecker_cochainPullbackInt]
  have hB : kronecker (omegaCap (antipode vN)) (mapChainInt eqInclCapB 1 t1chain)
      = kronecker wSc.1 (mapChainInt (puncIncl (antipode vN)) 2 fillB) := by
    rw [show mapChainInt eqInclCapB 1 t1chain = loopCapB from rfl, ← fillB_spec,
      ← kronecker_coboundary_chainBoundary,
      show coboundary (Apunc 2 (antipode vN)) 1 (omegaCap (antipode vN))
        = coboundaryₗ (Apunc 2 (antipode vN)) 1 (omegaCap (antipode vN)) from rfl,
      omegaCap_spec, kronecker_cochainPullbackInt]
  have hA : kronecker (omegaCap vN) (mapChainInt eqInclCapA 1 t1chain)
      = kronecker wSc.1 (mapChainInt (puncIncl vN) 2 fillA) := by
    rw [show mapChainInt eqInclCapA 1 t1chain = loopCapA from rfl, ← fillA_spec,
      ← kronecker_coboundary_chainBoundary,
      show coboundary (Apunc 2 vN) 1 (omegaCap vN)
        = coboundaryₗ (Apunc 2 vN) 1 (omegaCap vN) from rfl,
      omegaCap_spec, kronecker_cochainPullbackInt]
  rw [hB, hA]
  have hkr : kronecker wSc.1 (mapChainInt (puncIncl (antipode vN)) 2 fillB)
        - kronecker wSc.1 (mapChainInt (puncIncl vN) 2 fillA)
      = kronecker wSc.1 hemiDiff := by
    rw [hemiDiff]
    have h2 : mapChainInt (puncIncl (antipode vN)) 2 fillB - mapChainInt (puncIncl vN) 2 fillA
        = mapChainInt (puncIncl (antipode vN)) 2 fillB
          + (-1 : ℤ) • mapChainInt (puncIncl vN) 2 fillA := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [h2, kronecker_add_right, kronecker_smul_right, neg_one_smul, ← sub_eq_add_neg]
  rw [hkr]
  have hclass := kroneckerHInt_mk_mk wSc ⟨hemiDiff, LinearMap.mem_ker.mpr hemiDiff_cycle⟩
  rw [show (Submodule.Quotient.mk wSc : Cohomology (Sph 2) 2) = Cohomology.mk (Sph 2) 2 wSc
      from rfl, wSc_spec,
    show (Submodule.Quotient.mk ⟨hemiDiff, LinearMap.mem_ker.mpr hemiDiff_cycle⟩ :
        Homology (Sph 2) 2) = hemiClass from rfl, kroneckerHInt_xS] at hclass
  exact hclass.symm

/-! ## §6. The conditional headline: `hcross_pm` from the hemisphere-class unit -/

open SKEFTHawking.SphereProdHFourInt (sphereProdFundClassInt sphereProdHFourEquivInt
  sphereProdCohomFourEquivInt sphereProdCohomFourEquivInt_apply interFormInt_honest
  coverInterHThreeEquivInt sphereProdIntFundClassHonest)
open SKEFTHawking.SingularCoverPartitionAmbientInt (exists_cover_partition_ambient)

/-- Right-subtraction unfolding for the pairing. -/
theorem kronecker_sub_right' {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c d : SingularChainInt X n) :
    kronecker f (c - d) = kronecker f c - kronecker f d := by
  have h : c - d = c + (-1 : ℤ) • d := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, kronecker_add_right, kronecker_smul_right, neg_one_smul, ← sub_eq_add_neg]

/-- **Cocycle pairings descend to homology, `k`-scaled form**: if `[c₁] = k • [c₂]` then
`⟨w, c₁⟩ = k · ⟨w, c₂⟩` for any cocycle `w`. -/
theorem kronecker_homologous {X : TopCat} {n : ℕ} (w : SingularCochainInt X n)
    (hw : coboundaryₗ X n w = 0) (c₁ c₂ : cycles X n) (k : ℤ)
    (h : Homology.mk X n c₁ = k • Homology.mk X n c₂) :
    kronecker w c₁.1 = k * kronecker w c₂.1 := by
  have hdiff : Homology.mk X n (c₁ - k • c₂) = 0 := by
    rw [show Homology.mk X n (c₁ - k • c₂)
        = Homology.mk X n c₁ - k • Homology.mk X n c₂ from rfl, h, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hdiff
  have hrange : (c₁ - k • c₂ : cycles X n).1 ∈ boundaries X n := Submodule.mem_comap.mp hmem
  obtain ⟨d, hd⟩ := hrange
  have hzero : kronecker w (c₁.1 - k • c₂.1) = 0 := by
    rw [show (c₁.1 - k • c₂.1 : SingularChainInt X n) = (c₁ - k • c₂ : cycles X n).1 from rfl,
      ← hd, ← kronecker_coboundary_chainBoundary,
      show coboundary X n w = coboundaryₗ X n w from rfl, hw]
    simp [kronecker_apply]
  rw [kronecker_sub_right', kronecker_smul_right, sub_eq_zero] at hzero
  rw [hzero, smul_eq_mul]

theorem isOpen_coverA_vN : IsOpen (coverA vN) := isOpen_univ.prod isOpen_compl_singleton

theorem isOpen_coverB_vN : IsOpen (coverB vN) := isOpen_univ.prod isOpen_compl_singleton

theorem coverAB_union : coverA vN ∪ coverB vN = Set.univ := by
  have h := coverAB_cover vN
  rwa [Set.biUnion_pair, isOpen_coverA_vN.interior_eq, isOpen_coverB_vN.interior_eq] at h

set_option maxRecDepth 4000 in
/-- The MV coordinate of the fundamental class is `1` — the normalization
`sphereProdFundClassInt := (coverInterHThreeEquivInt ∘ mvDeltaInt).symm 1`, restated at the
witness parameter `vN` (definitionally `basePoint 2`). Metaprogram-depth option only (the
`hFourToInt` defeq chain is recursion-deep, exactly as in `SphereProdHFourInt`); no heartbeat
change, no proof-content change. -/
theorem coverInterHThreeEquivInt_mvDelta_fundClass :
    coverInterHThreeEquivInt vN
        (mvDeltaInt (coverA vN) (coverB vN) 3 (coverAB_cover vN) sphereProdFundClassInt) = 1 := by
  have h1 : coverInterHThreeEquivInt vN
      (mvDeltaInt (coverA vN) (coverB vN) 3 (coverAB_cover vN) sphereProdFundClassInt)
      = SKEFTHawking.SphereProdHFourInt.hFourToInt sphereProdFundClassInt :=
    (SKEFTHawking.SphereProdHFourInt.hFourToInt_apply sphereProdFundClassInt).symm
  rw [h1, show SKEFTHawking.SphereProdHFourInt.hFourToInt sphereProdFundClassInt
      = sphereProdHFourEquivInt sphereProdFundClassInt from rfl]
  exact sphereProdHFourEquivInt.apply_symm_apply 1

/-- **THE ±-SIGN CROSS VALUE, conditional on the hemisphere unit** (`hcross_pm`-of-hemi). If the
hemisphere-difference class pairs to a unit against the dual generator (`[D_B − D_A] = ±[S²]` in
coordinates), then the Eilenberg–Zilber cross value `⟨α ∪ β, [S²×S²]⟩` at the witness generator
`xS` is a UNIT (`±1`). The ℤ-divisibility of the seam pairing closes everything else: the peel
value on the explicit cross cycle is `(e γ)·V` with `V` the cross value, so a unit peel value
forces `V = ±1` — no seam-class or cross-class coordinate computation is needed. -/
theorem hcross_pm_of_hemiUnit (hHemi : IsUnit (topSphereIsoInt 1 hemiClass)) :
    IsUnit (interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS)) := by
  -- the partitioned representative of the fundamental class
  obtain ⟨zA, zB, hz_cyc, hrep⟩ := exists_cover_partition_ambient (coverA vN) (coverB vN)
    isOpen_coverA_vN isOpen_coverB_vN coverAB_union (n := 3) sphereProdFundClassInt
  have hliftB : zB ∈ relCycleLift (restr (coverA vN) (coverB vN)) 3 :=
    zB_mem_relCycleLift (coverA vN) (coverB vN) 3 zA zB hz_cyc
  have hz_cyc' : chainIncl (coverB vN) 4 zB + chainIncl (coverA vN) 4 zA
      ∈ cycles SphSph 4 := by rwa [add_comm]
  have hliftA : zA ∈ relCycleLift (restr (coverB vN) (coverA vN)) 3 :=
    zB_mem_relCycleLift (coverB vN) (coverA vN) 3 zB zA hz_cyc'
  -- the assembly seam cochain and the transported seam chain
  set W : SingularCochainInt (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 :=
    cup (cochainPullbackInt (ambIncl (coverA vN ∩ coverB vN)) 2 aC) dSeam with hWdef
  have hWcocycle : coboundaryₗ (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 W = 0 := by
    rw [hWdef]
    exact LinearMap.mem_ker.mp (cup_cocycle _ _
      (LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker (ambIncl (coverA vN ∩ coverB vN))
        ⟨aC, cochainPullbackInt_mem_ker _ wSc⟩))
      (seam_difference_cocycle (coverA vN) (coverB vN) bC (uLeg vN) (uLeg (antipode vN))
        (hbLeg vN) (hbLeg (antipode vN))))
  set tB : SingularChainInt (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 :=
    mapChainInt ⟨seamHomeo (coverA vN) (coverB vN),
      (seamHomeo (coverA vN) (coverB vN)).continuous⟩ 3
      (boundaryExtract (restr (coverA vN) (coverB vN)) 3 ⟨zB, hliftB⟩) with htBdef
  have htB_cyc : tB ∈ cycles (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 := by
    show chainBoundary _ 2 tB = 0
    rw [htBdef, chainBoundary_mapChainInt,
      show chainBoundary (sub (restr (coverA vN) (coverB vN))) 2
          (boundaryExtract (restr (coverA vN) (coverB vN)) 3 ⟨zB, hliftB⟩) = 0 from
        boundaryExtract_mem_cyclesInt (restr (coverA vN) (coverB vN)) 3 ⟨zB, hliftB⟩,
      map_zero]
  set τc : cycles (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 := ⟨tB, htB_cyc⟩ with hτcdef
  set γc : cycles (sub (X := SphSph) (coverA vN ∩ coverB vN)) 3 :=
    ⟨gChain, LinearMap.mem_ker.mpr gChain_cycle⟩ with hγcdef
  set e := coverInterHThreeEquivInt vN with hedef
  -- (i) the transported seam class has coordinate 1
  have hδ : mvDeltaInt (coverA vN) (coverB vN) 3 (coverAB_cover vN) sphereProdFundClassInt
      = Homology.mk _ 3 τc := by
    rw [hrep, mvDelta_cover_partition (coverA vN) (coverB vN) 3 (coverAB_cover vN) zA zB hz_cyc,
      seamHomologyEquivInt_apply, Homology.mapInt_mk]
    rfl
  have heτ : e (Homology.mk _ 3 τc) = 1 := by
    rw [← hδ]
    exact coverInterHThreeEquivInt_mvDelta_fundClass
  -- (ii) the cross-cycle class is `(e γ)` times the seam class
  have hγ : Homology.mk _ 3 γc = (e (Homology.mk _ 3 γc)) • Homology.mk _ 3 τc := by
    have h1 : Homology.mk _ 3 τc = e.symm 1 := by rw [← heτ, LinearEquiv.symm_apply_apply]
    rw [h1, show (e (Homology.mk _ 3 γc)) • e.symm 1
        = e.symm ((e (Homology.mk _ 3 γc)) • 1) from (map_smul e.symm _ _).symm,
      smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  -- (iii) the value transfer
  have hval : kronecker W gChain = (e (Homology.mk _ 3 γc)) * kronecker W tB :=
    kronecker_homologous W hWcocycle γc τc _ hγ
  -- (iv) the peel value is the hemisphere coordinate — a unit
  have hpeel : kronecker W gChain = topSphereIsoInt 1 hemiClass := by
    rw [hWdef]
    exact F_gChain.trans etaS_pairing_eq_hemi
  have hunit_tB : IsUnit (kronecker W tB) := by
    have : IsUnit ((e (Homology.mk _ 3 γc)) * kronecker W tB) := by
      rw [← hval, hpeel]; exact hHemi
    exact isUnit_of_mul_isUnit_right this
  -- (v) the value chain: the cross value IS the seam pairing
  have hVal1 : interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS)
      = kroneckerHInt 4 (cupH24 (alphaOf xS) (betaOf xS)) sphereProdFundClassInt := by
    rw [interFormInt_honest, sphereProdCohomFourEquivInt_apply]
  have hVal2 : cupH24 (alphaOf xS) (betaOf xS)
      = Cohomology.mk SphSph 4 ⟨cup aC bC, cup_cocycle aC bC
          (LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker _ wSc))
          (LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker _ wSc))⟩ := by
    rw [← mk_aC, ← mk_bC]
    exact cupH24_mk_mk _ _
  have hVal3 : kroneckerHInt 4 (cupH24 (alphaOf xS) (betaOf xS)) sphereProdFundClassInt
      = kronecker (cup aC bC) (chainIncl (coverA vN) 4 zA + chainIncl (coverB vN) 4 zB) := by
    rw [hVal2, hrep]
    exact kroneckerHInt_mk_mk _ _
  have hVal4 := kronecker_cup_cover_seam_cup_form (coverA vN) (coverB vN) (p := 2) (q := 1)
    aC bC aC_cocycle (uLeg vN) (uLeg (antipode vN)) (hbLeg vN) (hbLeg (antipode vN))
    zA zB hz_cyc hliftB hliftA
  have hfinal : interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS)
      = kronecker W tB := by
    refine (hVal1.trans hVal3).trans (hVal4.trans ?_)
    rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, one_mul]
    rfl
  rw [hfinal]
  exact hunit_tB

end SKEFTHawking.SphereProdCrossWitnessInt
