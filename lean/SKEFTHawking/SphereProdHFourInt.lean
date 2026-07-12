/-
# Phase 5q.H (N5 witness tower) — the TOP of the S²×S² integral arc:
# `H₃(S²×S²;ℤ) = 0`, `H₄(S²×S²;ℤ) ≅ ℤ`, and the HONEST fundamental class

Arc slice 5: the same polar product cover (`SphereProdHOneInt`: `A = S²×(S²∖{v})`,
`B = S²×(S²∖{−v})`) run at degrees 3 and 4, closing the S²×S² homology tower at the top and
building the honest integral fundamental class `[S²×S²] ∈ H₄(S²×S²;ℤ)` — the `fc` input of the
Gram pin `interMatrix fc B = sphereProdFormDatum`, previously a fully abstract datum.

* §1 — the missing intersection input: **`H₃(S²×(ℝ²∖{0});ℤ) ≅ ℤ`** (`slitProdHThreeEquivInt`).
  The slit-plane MV at degree 3: legs collapse onto `H₃(S²;ℤ) = 0` (high-degree sphere vanishing),
  so `δ₂` is injective; its image is `ker Δ₂ =` the ANTI-diagonal of `H₂(A∩B) ≅ H₂(S²)²`
  (`diag_fst_via_split`/`diag_snd_via_split` — the same coordinates whose DIAGONAL is `im Δ₂` in
  slice 1's H₂ computation). The comparison map reads the positive-component coordinate of `δ₂`.
  This is the `[S²×S¹]`-grade class: `H₃(S²×S¹) ≅ ℤ`. Transported to the polar-cover intersection
  by `interProdHomeo` (`coverInterHThreeEquivInt`).
* §2 — **`H₃(S²×S²;ℤ) = 0`** (`sphereProd_homology_three_eq_zero`): the polar MV at degree 3 —
  legs vanish (`H₃(S²) = 0`), so `δ₂` is injective; the complex condition `Δ₂∘δ₂ = 0` against the
  INJECTIVE `Δ₂` on `H₂(A∩B) ≅ ℤ` (the first-coordinate readout `coverInterHTwoEquivInt_eq_fst`)
  kills every `δ₂`-image. `b₃(S²×S²) = 0`, matching Künneth/Poincaré duality.
* §3 — **`H₄(S²×S²;ℤ) ≅ ℤ`** (`sphereProdHFourEquivInt`): the polar MV at degree 4 — legs vanish
  at 3 AND 4 (`H₃(S²) = H₄(S²) = 0`), so `δ₃ : H₄(S²×S²) → H₃(A∩B) ≅ ℤ` is injective (no `Σ₄`)
  and surjective (no `Δ₃`) — an isomorphism outright. `b₄(S²×S²) = 1`: the space is closed
  orientable, and the generator is canonical up to sign (pinned by `δ₃`-value `1`).
* §4 — **the honest fundamental class** `sphereProdFundClassInt := sphereProdHFourEquivInt.symm 1`
  and the honest `IntFundamentalClass` datum `sphereProdIntFundClassHonest :=
  intFundamentalClassOfHomology [S²×S²]` — the S²×S² mirror of S⁴'s global-generator route
  (`SphereFourOrientationDataInt.sphere4GenInt`): the class is available OUTRIGHT from the MV
  computation, no chartAt-pinned local generator is ever compared (settled fork
  `5qH-orient-normalized-vs-chartAt-pinned-generators` is never touched).
* §5 — the top-degree pairing bookkeeping: `H⁴(S²×S²;ℤ) ≅ ℤ` by the absolute UCT over `H₃ = 0`
  free (`sphereProdCohomFourEquivInt`), whose coordinate IS the Kronecker pairing against the
  fundamental class (definitional readout), hence **the honest `eval` is BIJECTIVE**
  (`sphereProdIntFundClassHonest_eval_bijective` — the top pairing is unimodular: the honest datum
  is nondegenerate, not a junk functional). The degree-4 expansion rule
  (`kroneckerHInt_sphereProd_four_expand`) and the Gram-entry reduction
  (`interMatrix_honest_apply`): every intersection-matrix entry against the honest `fc` equals the
  `H⁴`-coordinate of a cup product of basis classes — the Gram pin's remaining wall is EXACTLY the
  cup-product computation `sphereProdCohomFourEquivInt (cupH24 bᵢ bⱼ)`, nothing else.
* Bonus: `H³(S²×S²;ℤ) = 0` (UCT flip of `H₃ = 0` over `H₂` free).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdPuncturedPlaneInt
import SKEFTHawking.SphereProdHTwoInt
import SKEFTHawking.SingularSphereHighDegreeInt
import SKEFTHawking.SphereWitnessTowerInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularSphereHighDegreeInt (sphere_homology_high)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularAbsoluteUCInt (ucIntEquivOfFree)
open SKEFTHawking.SphereProdHOneInt (coverA coverB coverAB_cover)
open SKEFTHawking.SphereProdHTwoInt (SphSph coverAEquivInt coverBEquivInt diag_fst diag_snd
  coverInterHTwoEquivInt_eq_fst)
open SKEFTHawking.SphereProdPuncturedPlaneInt (SlitProd legUp legDown compPos compNeg legs_cover
  interSplitEquiv compPosEquivInt compNegEquivInt legUpEquivInt legDownEquivInt
  diag_fst_via_split diag_snd_via_split interProdHomeo coverInterHTwoEquivInt coverInterFstCM)
open SKEFTHawking.SpinSigmaRoute (SphereProd)
open SKEFTHawking.SphereWitnessTowerInt (SphereProdT SphereProdHData)

namespace SKEFTHawking.SphereProdHFourInt

/-! ## §1a. High-degree leg vanishing: every collapsing leg dies at degrees 3 and 4 -/

/-- `H₃(S² × slitUp; ℤ) = 0` — the leg collapses onto `H₃(S²;ℤ) = 0` (high-degree vanishing). -/
theorem legUp_homology_three_eq_zero (u : Homology (sub (X := SlitProd) legUp) 3) : u = 0 :=
  (legUpEquivInt 2).map_eq_zero_iff.mp
    (sphere_homology_high 2 3 (by norm_num) (legUpEquivInt 2 u))

/-- `H₃(S² × slitDown; ℤ) = 0`. -/
theorem legDown_homology_three_eq_zero (u : Homology (sub (X := SlitProd) legDown) 3) : u = 0 :=
  (legDownEquivInt 2).map_eq_zero_iff.mp
    (sphere_homology_high 2 3 (by norm_num) (legDownEquivInt 2 u))

/-- `H₃(S²×(S²∖{v}); ℤ) = 0` — the polar `A`-leg dies at degree 3. -/
theorem coverA_homology_three_eq_zero (v : ↑(Sph 2))
    (u : Homology (sub (coverA v)) 3) : u = 0 :=
  (coverAEquivInt v 2).map_eq_zero_iff.mp
    (sphere_homology_high 2 3 (by norm_num) (coverAEquivInt v 2 u))

/-- `H₃(S²×(S²∖{−v}); ℤ) = 0` — the polar `B`-leg dies at degree 3. -/
theorem coverB_homology_three_eq_zero (v : ↑(Sph 2))
    (u : Homology (sub (coverB v)) 3) : u = 0 :=
  (coverBEquivInt v 2).map_eq_zero_iff.mp
    (sphere_homology_high 2 3 (by norm_num) (coverBEquivInt v 2 u))

/-- `H₄(S²×(S²∖{v}); ℤ) = 0` — the polar `A`-leg dies at degree 4. -/
theorem coverA_homology_four_eq_zero (v : ↑(Sph 2))
    (u : Homology (sub (coverA v)) 4) : u = 0 :=
  (coverAEquivInt v 3).map_eq_zero_iff.mp
    (sphere_homology_high 2 4 (by norm_num) (coverAEquivInt v 3 u))

/-- `H₄(S²×(S²∖{−v}); ℤ) = 0` — the polar `B`-leg dies at degree 4. -/
theorem coverB_homology_four_eq_zero (v : ↑(Sph 2))
    (u : Homology (sub (coverB v)) 4) : u = 0 :=
  (coverBEquivInt v 3).map_eq_zero_iff.mp
    (sphere_homology_high 2 4 (by norm_num) (coverBEquivInt v 3 u))

/-! ## §1b. `H₃(S²×(ℝ²∖{0}); ℤ) ≅ ℤ` — the anti-diagonal `ker Δ₂` through the slit MV -/

/-- **The H₃ comparison map** `x ↦ (positive-component H₂-coordinate of δ₂x)`: the slit-cover MV
connecting image read through the clopen split and the positive-component collapse. The
anti-diagonal `ker Δ₂` in `H₂(A∩B) ≅ H₂(S²)²` coordinates — the degree-3 mirror of
`SphereProdPuncturedPlaneInt.hOneToInt` (which reads `ker Δ₀` through augmentations). -/
noncomputable def hThreeToInt : Homology SlitProd 3 →ₗ[ℤ] ℤ :=
  ((topSphereIsoInt 1).toLinearMap.comp (compPosEquivInt 1).toLinearMap).comp
    ((LinearMap.fst ℤ _ _).comp
      (((interSplitEquiv 2).toLinearMap).comp (mvDeltaInt legUp legDown 2 legs_cover)))

theorem hThreeToInt_apply (x : Homology SlitProd 3) :
    hThreeToInt x = topSphereIsoInt 1 (compPosEquivInt 1
      (interSplitEquiv 2 (mvDeltaInt legUp legDown 2 legs_cover x)).1) := rfl

/-- `hThreeToInt` is injective: a vanishing positive coordinate forces the negative coordinate to
vanish too (the complex condition `Δ₂∘δ₂ = 0` says the two coordinates SUM to zero in `H₂(S²)`),
so `δ₂x = 0`; exactness at `H₃(X)` lifts `x` to the legs, whose `H₃` vanish. -/
theorem hThreeToInt_injective : Function.Injective hThreeToInt := by
  refine (injective_iff_map_eq_zero hThreeToInt).mpr fun x hx => ?_
  rw [hThreeToInt_apply] at hx
  set w := mvDeltaInt legUp legDown 2 legs_cover x with hwdef
  -- the positive coordinate vanishes (the hypothesis)
  have ha : (interSplitEquiv 2 w).1 = 0 :=
    (compPosEquivInt 1).map_eq_zero_iff.mp ((topSphereIsoInt 1).map_eq_zero_iff.mp hx)
  -- the complex condition: the leg-pushforward of δ₂x is zero, whose coordinates SUM
  have hdiag : mvHomDiagInt legUp legDown 2 w = 0 := by
    rw [hwdef]
    exact mvHomDiagInt_mvDeltaInt legUp legDown 2 legs_cover x
  have hsum := diag_fst_via_split w
  rw [show (mvHomDiagInt legUp legDown 2 w).1 = 0 from congrArg Prod.fst hdiag, map_zero, ha,
    map_zero, zero_add] at hsum
  have hb : (interSplitEquiv 2 w).2 = 0 := (compNegEquivInt 1).map_eq_zero_iff.mp hsum.symm
  have hw0 : w = 0 := (interSplitEquiv 2).map_eq_zero_iff.mp (Prod.ext ha hb)
  obtain ⟨⟨u, u'⟩, hx'⟩ := (mv_exact_ambientInt legUp legDown 2 legs_cover x).mp hw0
  rw [← hx', mvHomSumInt_apply, legUp_homology_three_eq_zero u,
    legDown_homology_three_eq_zero u', map_zero, map_zero, sub_zero]

/-- `hThreeToInt` is surjective: hit `m` with the anti-diagonal class `(m, −m)` of
`H₂(A∩B) ≅ H₂(S²)²` — its `Δ₂`-image is the coordinate SUM `m + (−m) = 0` on both legs, so
exactness at `H₂(A∩B)` realizes it as a `δ₂`-image. -/
theorem hThreeToInt_surjective : Function.Surjective hThreeToInt := by
  intro m
  set a := (compPosEquivInt 1).symm ((topSphereIsoInt 1).symm m) with hadef
  set b := (compNegEquivInt 1).symm (-((topSphereIsoInt 1).symm m)) with hbdef
  set w := (interSplitEquiv 2).symm (a, b) with hwdef
  have hcoords : interSplitEquiv 2 w = (a, b) := (interSplitEquiv 2).apply_symm_apply _
  have hval : compPosEquivInt 1 a + compNegEquivInt 1 b = 0 := by
    rw [hadef, hbdef, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      add_neg_cancel]
  have hdiag : mvHomDiagInt legUp legDown 2 w = 0 := by
    refine Prod.ext ?_ ?_
    · show (mvHomDiagInt legUp legDown 2 w).1 = 0
      apply (legUpEquivInt 1).injective
      rw [map_zero, diag_fst_via_split w, hcoords]
      exact hval
    · show (mvHomDiagInt legUp legDown 2 w).2 = 0
      apply (legDownEquivInt 1).injective
      rw [map_zero, diag_snd_via_split w, hcoords]
      exact hval
  obtain ⟨x, hx⟩ := (mv_exact_interInt legUp legDown 2 legs_cover w).mp hdiag
  refine ⟨x, ?_⟩
  rw [hThreeToInt_apply, hx, hcoords, hadef, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **`H₃(S²×(ℝ²∖{0}); ℤ) ≅ ℤ`** — the `[S²×S¹]`-grade top class of the polar-cover
intersection: the missing degree-3 input of the S²×S² MV at degree 4. -/
noncomputable def slitProdHThreeEquivInt : Homology SlitProd 3 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective hThreeToInt ⟨hThreeToInt_injective, hThreeToInt_surjective⟩

/-- **`H₃(S²×(S²∖{v,−v}); ℤ) ≅ ℤ`** at the polar-cover intersection — the degree-4 slice's
δ-target datum (the `interProdHomeo` transport of `slitProdHThreeEquivInt`). -/
noncomputable def coverInterHThreeEquivInt (v : ↑(Sph 2)) :
    Homology (sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)) 3 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (interProdHomeo v) 3).trans slitProdHThreeEquivInt

/-! ## §2. `H₃(S²×S²; ℤ) = 0` — injective `δ₂` against injective `Δ₂` -/

/-- **`H₃(S²×S²; ℤ) = 0`**: the polar-cover MV at degree 3. Legs vanish (`H₃(S²) = 0`), so `δ₂`
is injective (exactness at `H₃(X)`); the complex condition `Δ₂∘δ₂ = 0` against the INJECTIVE
`Δ₂` (the first-coordinate readout of `H₂(A∩B) ≅ ℤ`) forces `δ₂x = 0`, hence `x = 0`.
`b₃(S²×S²) = 0` — the Künneth/PD value, COMPUTED. -/
theorem sphereProd_homology_three_eq_zero (x : Homology (TopCat.of SphereProd) 3) : x = 0 := by
  set v := basePoint 2
  set w := mvDeltaInt (coverA v) (coverB v) 2 (coverAB_cover v) x with hwdef
  have hdiag : mvHomDiagInt (coverA v) (coverB v) 2 w = 0 :=
    mvHomDiagInt_mvDeltaInt (coverA v) (coverB v) 2 (coverAB_cover v) x
  have hmap : Homology.mapInt (coverInterFstCM v) 2 w = 0 := by
    rw [← diag_fst v w, show (mvHomDiagInt (coverA v) (coverB v) 2 w).1 = 0 from
      congrArg Prod.fst hdiag, map_zero]
  have hw0 : w = 0 := by
    apply (coverInterHTwoEquivInt v).map_eq_zero_iff.mp
    rw [coverInterHTwoEquivInt_eq_fst v w, hmap, map_zero]
  obtain ⟨⟨u, u'⟩, hx'⟩ :=
    (mv_exact_ambientInt (coverA v) (coverB v) 2 (coverAB_cover v) x).mp hw0
  rw [← hx', mvHomSumInt_apply, coverA_homology_three_eq_zero v u,
    coverB_homology_three_eq_zero v u', map_zero, map_zero, sub_zero]

instance : Subsingleton (Homology (TopCat.of SphereProd) 3) :=
  subsingleton_of_forall_eq 0 sphereProd_homology_three_eq_zero

/-- `H₃(S²×S²;ℤ) = 0` is free — the degree-3 instance the H⁴ UCT flip consumes. -/
instance : Module.Free ℤ (Homology (TopCat.of SphereProd) 3) := Module.Free.of_subsingleton ℤ _

instance : Module.Finite ℤ (Homology (TopCat.of SphereProd) 3) :=
  SKEFTHawking.SphereWitnessTowerInt.moduleFinite_of_subsingleton ℤ _

/-! ## §3. `H₄(S²×S²; ℤ) ≅ ℤ` — `δ₃` is an isomorphism outright -/

/-- **The H₄ comparison map** `x ↦ coverInterHThreeEquivInt(δ₃x)`: at degree 4 the polar MV has
NO legs on either side (`H₃(S²) = H₄(S²) = 0`), so the connecting map to `H₃(A∩B) ≅ ℤ` is the
whole story. -/
noncomputable def hFourToInt : Homology SphSph 4 →ₗ[ℤ] ℤ :=
  (coverInterHThreeEquivInt (basePoint 2)).toLinearMap.comp
    (mvDeltaInt (coverA (basePoint 2)) (coverB (basePoint 2)) 3 (coverAB_cover (basePoint 2)))

set_option maxRecDepth 4000 in
theorem hFourToInt_apply (x : Homology SphSph 4) :
    hFourToInt x = coverInterHThreeEquivInt (basePoint 2)
      (mvDeltaInt (coverA (basePoint 2)) (coverB (basePoint 2)) 3
        (coverAB_cover (basePoint 2)) x) := rfl

set_option maxRecDepth 4000 in
/-- `hFourToInt` is injective: `δ₃x = 0` lifts `x` to the legs (exactness at `H₄(X)`), whose
`H₄` vanish. -/
theorem hFourToInt_injective : Function.Injective hFourToInt := by
  refine (injective_iff_map_eq_zero hFourToInt).mpr fun x hx => ?_
  set v := basePoint 2
  have hδ : mvDeltaInt (coverA v) (coverB v) 3 (coverAB_cover v) x = 0 :=
    (coverInterHThreeEquivInt v).map_eq_zero_iff.mp hx
  obtain ⟨⟨u, u'⟩, hx'⟩ :=
    (mv_exact_ambientInt (coverA v) (coverB v) 3 (coverAB_cover v) x).mp hδ
  rw [← hx', mvHomSumInt_apply, coverA_homology_four_eq_zero v u,
    coverB_homology_four_eq_zero v u', map_zero, map_zero, sub_zero]

/-- `hFourToInt` is surjective: `Δ₃ = 0` (legs vanish at degree 3), so exactness at `H₃(A∩B)`
realizes EVERY intersection class as a `δ₃`-image. -/
theorem hFourToInt_surjective : Function.Surjective hFourToInt := by
  intro m
  set v := basePoint 2
  set w := (coverInterHThreeEquivInt v).symm m with hwdef
  have hdiag : mvHomDiagInt (coverA v) (coverB v) 3 w = 0 :=
    Prod.ext (coverA_homology_three_eq_zero v _) (coverB_homology_three_eq_zero v _)
  obtain ⟨x, hx⟩ := (mv_exact_interInt (coverA v) (coverB v) 3 (coverAB_cover v) w).mp hdiag
  refine ⟨x, ?_⟩
  rw [hFourToInt_apply, hx, hwdef, LinearEquiv.apply_symm_apply]

/-- **`H₄(S²×S²; ℤ) ≅ ℤ`** — the top of the S²×S² integral arc, at the witness tower's carrier
`TopCat.of SphereProd`. `b₄(S²×S²) = 1`: the closed orientable top class exists and is unique up
to sign — the raw material of the fundamental class. -/
noncomputable def sphereProdHFourEquivInt : Homology (TopCat.of SphereProd) 4 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective hFourToInt ⟨hFourToInt_injective, hFourToInt_surjective⟩

instance : Module.Free ℤ (Homology (TopCat.of SphereProd) 4) :=
  Module.Free.of_equiv sphereProdHFourEquivInt.symm

instance : Module.Finite ℤ (Homology (TopCat.of SphereProd) 4) :=
  Module.Finite.equiv sphereProdHFourEquivInt.symm

/-! ## §4. The honest fundamental class -/

/-- **The integral fundamental class `[S²×S²] ∈ H₄(S²×S²;ℤ)`** — the generator
`sphereProdHFourEquivInt.symm 1`, available OUTRIGHT from the MV computation (the S²×S² mirror of
S⁴'s chart-free global generator `sphere4GenInt`). Canonical up to the sign convention pinned by
its `δ₃`-value `1` on the `[S²×S¹]` intersection class. -/
noncomputable def sphereProdFundClassInt : Homology SphereProdT 4 :=
  sphereProdHFourEquivInt.symm 1

/-- **The HONEST `IntFundamentalClass` datum at S²×S²** — `eval := ⟨·, [S²×S²]⟩`, the integral
Kronecker pairing against the COMPUTED fundamental class (`intFundamentalClassOfHomology`). The
Gram pin's `fc` input is no longer an arbitrary functional datum: it is produced by the in-tree
homology computation. -/
noncomputable def sphereProdIntFundClassHonest : IntFundamentalClass SphereProdT :=
  intFundamentalClassOfHomology sphereProdFundClassInt

/-! ## §5. Top-degree pairing bookkeeping: `H⁴ ≅ ℤ`, bijective eval, the Gram-entry reduction -/

/-- **`H⁴(S²×S²;ℤ) ≅ ℤ`** — the absolute-UCT flip of `H₄ ≅ ℤ` over `H₃ = 0` free
(`ucIntEquivOfFree` at `M = 2`, dualized through the computed top iso and `(ℤ)* ≅ ℤ`). The
S²×S² mirror of `sphere4Cohomology4Iso`. -/
noncomputable def sphereProdCohomFourEquivInt : Cohomology SphereProdT 4 ≃ₗ[ℤ] ℤ :=
  haveI : Module.Free ℤ (Homology SphereProdT (2 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology SphereProdT 3))
  (ucIntEquivOfFree SphereProdT 2).trans
    ((sphereProdHFourEquivInt.symm.dualMap).trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))

/-- **The `H⁴`-coordinate IS the Kronecker pairing against the fundamental class** — definitional
readout of the UCT flip (the degree-4 mirror of `sphereProdCohomTwoEquivInt_fst`). -/
theorem sphereProdCohomFourEquivInt_apply (ω : Cohomology SphereProdT 4) :
    sphereProdCohomFourEquivInt ω = kroneckerHInt 4 ω sphereProdFundClassInt := rfl

/-- **The honest `eval` is the `H⁴`-coordinate** — the honest datum's evaluation functional is
exactly the UCT iso's underlying map. -/
theorem sphereProdIntFundClassHonest_eval (ω : Cohomology SphereProdT 4) :
    sphereProdIntFundClassHonest.eval ω = sphereProdCohomFourEquivInt ω := rfl

/-- **The honest `eval` is BIJECTIVE** — the top-degree pairing against `[S²×S²]` is unimodular
(the honest fundamental-class datum is nondegenerate: `⟨·, [M]⟩` hits every integer exactly
once). An arbitrary `IntFundamentalClass` datum need not satisfy this; the computed one does. -/
theorem sphereProdIntFundClassHonest_eval_bijective :
    Function.Bijective sphereProdIntFundClassHonest.eval := by
  have h : ⇑sphereProdIntFundClassHonest.eval = ⇑sphereProdCohomFourEquivInt :=
    funext sphereProdIntFundClassHonest_eval
  rw [h]
  exact sphereProdCohomFourEquivInt.bijective

/-- **The full degree-4 Kronecker pairing rule in coordinates**: every top-degree pairing
`⟨ω, h⟩` is the product of the `H⁴`-coordinate of `ω` and the `H₄`-coordinate of `h` — the
degree-4 mirror of `kroneckerHInt_sphereProd_expand`. -/
theorem kroneckerHInt_sphereProd_four_expand (ω : Cohomology SphereProdT 4)
    (h : Homology SphereProdT 4) :
    kroneckerHInt 4 ω h = sphereProdCohomFourEquivInt ω * sphereProdHFourEquivInt h := by
  have hh : h = (sphereProdHFourEquivInt h) • sphereProdHFourEquivInt.symm 1 := by
    apply sphereProdHFourEquivInt.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc kroneckerHInt 4 ω h
      = kroneckerHInt 4 ω ((sphereProdHFourEquivInt h) • sphereProdHFourEquivInt.symm 1) := by
        rw [← hh]
    _ = (sphereProdHFourEquivInt h) • kroneckerHInt 4 ω (sphereProdHFourEquivInt.symm 1) := by
        rw [map_smul]
    _ = _ := by
        rw [smul_eq_mul, show kroneckerHInt 4 ω (sphereProdHFourEquivInt.symm 1)
          = sphereProdCohomFourEquivInt ω from (sphereProdCohomFourEquivInt_apply ω).symm,
          mul_comm]

/-- **The intersection form against the honest `fc` is the `H⁴`-coordinate of the cup product** —
`interFormInt fc a b = (a ∪ b)`-coordinate under `H⁴(S²×S²;ℤ) ≅ ℤ`. Every Gram computation
reduces through this to integral cup-product data. -/
theorem interFormInt_honest (a b : Cohomology SphereProdT 2) :
    interFormInt sphereProdIntFundClassHonest a b
      = sphereProdCohomFourEquivInt (cupH24 a b) := by
  rw [interFormInt_apply]
  exact sphereProdIntFundClassHonest_eval (cupH24 a b)

/-- **The Gram pin's remaining wall, isolated**: against the honest `fc`, the intersection-matrix
entry on ANY frozen geometric basis is the `H⁴`-coordinate of the basis classes' cup product.
The pin `interMatrix fc d.intH2Basis = sphereProdFormDatum` (= `Hyp`) is now EXACTLY the four
cup-product evaluations `sphereProdCohomFourEquivInt (cupH24 (d.basis2 i) (d.basis2 j)) = Hyp i j`
— no fundamental-class or pairing content remains open. -/
theorem interMatrix_honest_apply (d : SphereProdHData) (i j : Fin 2) :
    interMatrix sphereProdIntFundClassHonest d.intH2Basis i j
      = sphereProdCohomFourEquivInt (cupH24 (d.basis2 i) (d.basis2 j)) :=
  interFormInt_honest (d.basis2 i) (d.basis2 j)

/-! ## §6. Bonus: `H³(S²×S²;ℤ) = 0` (the UCT flip of the computed `H₃ = 0`) -/

instance : Subsingleton (Cohomology SphereProdT 3) :=
  haveI : Module.Free ℤ (Homology SphereProdT (1 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology SphereProdT 2))
  haveI : Subsingleton (Homology SphereProdT (1 + 2)) :=
    inferInstanceAs (Subsingleton (Homology SphereProdT 3))
  SKEFTHawking.SphereWitnessTowerInt.cohomology_subsingleton_of_homology SphereProdT 1

/-- **`H³(S²×S²;ℤ) = 0`** — the UCT flip of the computed `H₃(S²×S²;ℤ) = 0` over `H₂` free. -/
theorem sphereProd_cohomology_three_eq_zero (ω : Cohomology SphereProdT 3) : ω = 0 :=
  Subsingleton.elim ω 0

end SKEFTHawking.SphereProdHFourInt
