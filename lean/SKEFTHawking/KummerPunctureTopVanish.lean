/-
# `H₄(T⁴°;ℤ) = H₅(T⁴°;ℤ) = 0` — the two `T⁴°` inputs of the `orientInput` residual, DISCHARGED

`KummerQuotientTransferSequence` reduced the whole remaining `orientInput` residual to three
top-degree vanishings: `H₄(T⁴°;ℤ)`, `H₅(T⁴°;ℤ)` (`T⁴°` = the project's `PTtop`, `T⁴` minus sixteen
open chart balls) and `H₅(Q;ℤ)`. This module discharges **the two `T⁴°` ones, unconditionally**, and
feeds them into the transfer sequence.

## Route

`KummerPuncturedTorusHighVanish.torusFourPunctured_high` gives `Hₚ = 0` for `p ≥ 4` on the *open*
punctured torus `W = T⁴ ∖ fixedSet` (the 16 two-torsion points removed). The project's carrier
`PTtop` is the *closed* complement of sixteen open chart balls, so the two must be bridged. The
bridge is one Mayer–Vietoris step **inside `W`**, on the banked interior cover
`punc_hcov : interior thickA ∪ interior ballsV = T⁴` restricted to `W` (legitimate because
`thickA ⊆ W`, `thickA` being the complement of the sixteen open half-balls, each of which contains
its centre):

    `Hₚ(thickA) ⊕ Hₚ(ballsV ∩ W) --Σ--> Hₚ(W) = 0`,  `ker Σ = im Δ`,
    `Δ` out of `Hₚ(thickA ∩ ballsV) = ⊕₁₆ Hₚ(Ann⁴) = ⊕₁₆ Hₚ(S³) = 0`  (`p ≥ 4`)

so `Σ` is injective with zero target, hence `Hₚ(thickA;ℤ) = 0` for `p ≥ 4`. The banked deformation
retraction `KummerPuncturedMV.puncIncl_mapInt_bijective` then transports this onto `PTtop`, and
`hmlEquivHomology` onto the engine's `Hml` form.

## Consequences shipped here

* **`ptTop_homology_high` / `ptTop_hml_high`** — `Hₚ(T⁴°;ℤ) = 0` for every `p ≥ 4`;
* **`deltaIII_four_bijective_uncond`, `h5QEquivTransferKer_uncond`** — the §4 sharp form of
  `KummerQuotientTransferSequence` with its two hypotheses discharged: `H₅(Q;ℤ) ≅ ker (t)` on the
  nose;
* **`transferH_three_injective_iff_h5Q_eq_zero_uncond`** — `t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)` is injective
  **iff** `H₅(Q;ℤ) = 0`, now hypothesis-free;
* **`twoTorsionFree_of_h5Q`, `h3K3_eq_zero_of_h5Q_of_evenDescent`,
  `nonempty_intOrientation_of_h5Q_of_evenDescent`** — the downstream chain with the two `T⁴°`
  hypotheses removed. The residual is now exactly `H₅(Q;ℤ) = 0` plus even descent.

## Vacuity attack

`ptTop_homology_high` is not vacuous and its threshold is sharp: `H₃(T⁴°;ℤ)` does **not** vanish —
it surjects onto `H₃(T⁴;ℤ) ≅ ℤ⁴` (`KummerPunctureH3.thickIncl3_surjective`). The `iff` shipped here
is not a tautology either: its right-hand side `H₅(Q;ℤ) = 0` is equivalent, through the banked
`KummerQuotientH3Descent.twoTorsionFree_iff_transferH_three_injective`, to `H₃(Q;ℤ)` being
2-torsion-free, which feeds an open computation — so no hypothesis-free discharge of the
left-hand side lives in this window, and none is claimed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedTorusHighVanish
import SKEFTHawking.KummerPunctureH3
import SKEFTHawking.KummerQuotientTransferSequence

namespace SKEFTHawking.KummerPunctureTopVanish

open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt mv_exact_middleInt
  mvHomSumInt_apply mvHomDiagInt_apply)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)
open SKEFTHawking.ChainComplexLESInt (Hml)
open SKEFTHawking.KummerRP3SmithSES (hmlEquivHomology)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus (fixedSet centeredChartParam_zero sqNorm)
open SKEFTHawking.KummerPunctureBalls (ann4 thickA ballsV punc_hcov fixedSet_finite mem_thickA_iff
  halfD4o)
open SKEFTHawking.KummerPunctureAnnulus (ann4HomeoE annE sphIncl_mapInt_bijective sphHalf
  sphHalfHomeoSph3)
open SKEFTHawking.KummerQuotientCovering (PTtop)
open SKEFTHawking.KummerPuncturedTorusHighVanish (torusFourPunctured_high)

noncomputable section

/-! ## §1. The chart annulus above the top degree: `Hₚ(Ann⁴;ℤ) = 0` for `p ≥ 4` -/

/-- **`Hₚ(Ann⁴;ℤ) = 0` for `p ≥ 4`** — the closed chart annulus retracts onto its outer sphere,
which scales to the unit `S³`, whose homology vanishes above degree 3. The high-degree companion of
the banked middle-degree `ann4_homology_vanish` (`0 < j < 3`). -/
theorem ann4_homology_high (p : ℕ) (hp : 3 < p) (x : Homology (TopCat.of ↥ann4) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  set e := homologyCongrInt (X := TopCat.of ↥ann4) (Y := sub (X := Eucl 4) annE)
    ann4HomeoE (k + 1) with he
  refine (LinearEquiv.map_eq_zero_iff e).mp ?_
  obtain ⟨y, hy⟩ := (sphIncl_mapInt_bijective k).surjective (e x)
  have hy0 : y = 0 := by
    set e2 := homologyCongrInt (X := sub (X := Eucl 4) sphHalf) (Y := Sph 3)
      sphHalfHomeoSph3 (k + 1) with he2
    refine (LinearEquiv.map_eq_zero_iff e2).mp ?_
    exact SKEFTHawking.SingularSphereHighDegreeInt.sphere_homology_high 3 (k + 1) (by omega) _
  rw [hy0, map_zero] at hy
  exact hy.symm

/-- **`Hₚ(thickA ∩ ballsV;ℤ) = 0` for `p ≥ 4`** — the seam is sixteen disjoint chart annuli
(`interHnEquiv`), each vanishing above degree 3. -/
theorem inter_homology_high (p : ℕ) (hp : 3 < p)
    (x : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) p) : x = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (SKEFTHawking.KummerPuncturedMV.interHnEquiv p)).mp ?_
  funext _
  exact ann4_homology_high p hp _

/-! ## §2. `thickA` lives inside the open punctured torus -/

/-- **`thickA` misses every `τ`-fixed point** — each fixed point is the centre of its own open
half-ball (`centeredChartParam c 0 = c`, `sqNorm 0 = 0 < 1/16`), and `thickA` is the complement of
those half-balls. -/
theorem thickA_subset_fixedCompl : thickA ⊆ ((fixedSet : Set TorusFour)ᶜ) := by
  intro x hx hfix
  refine (mem_thickA_iff.mp hx) x hfix ⟨0, ?_, centeredChartParam_zero _⟩
  show sqNorm (0 : ℝ × ℝ × ℝ × ℝ) < 1 / 16
  simp [sqNorm]

/-- The open punctured torus `W = T⁴ ∖ fixedSet` is open (`fixedSet` is finite, hence closed). -/
theorem isOpen_fixedCompl : IsOpen ((fixedSet : Set TorusFour)ᶜ) :=
  (fixedSet_finite.isClosed).isOpen_compl

/-- A subspace of a subspace: for `S ⊆ W`, the preimage of `S` in `W` is `S`. -/
def subSubHomeo {X : TopCat} {W S : Set ↑X} (hSW : S ⊆ W) :
    ↥((Subtype.val : ↥W → ↑X) ⁻¹' S) ≃ₜ ↥S where
  toFun p := ⟨p.1.1, p.2⟩
  invFun q := ⟨⟨q.1, hSW q.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The banked interior cover `punc_hcov` restricted to the open punctured torus `W`. -/
theorem hcovW :
    (⋃ U ∈ ({(Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' thickA,
        (Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' ballsV} :
      Set (Set ↥((fixedSet : Set TorusFour)ᶜ))), interior U) = Set.univ := by
  have hmap : IsOpenMap (Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) :=
    isOpen_fixedCompl.isOpenMap_subtype_val
  have h := punc_hcov
  rw [Set.biUnion_pair] at h
  rw [Set.biUnion_pair,
    ← hmap.preimage_interior_eq_interior_preimage continuous_subtype_val thickA,
    ← hmap.preimage_interior_eq_interior_preimage continuous_subtype_val ballsV,
    ← Set.preimage_union, h, Set.preimage_univ]

/-- Restriction-to-`W` homology transport for `thickA` (which already sits inside `W`). -/
def thickTransport (n : ℕ) :
    Homology (sub (X := sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ))
      ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' thickA)) n
      ≃ₗ[ℤ] Homology (sub (X := TopCat.of TorusFour) thickA) n :=
  homeoHomologyEquivInt (subSubHomeo thickA_subset_fixedCompl) n

/-- Restriction-to-`W` homology transport for the seam `thickA ∩ ballsV`. -/
def seamTransport (n : ℕ) :
    Homology (sub (X := sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ))
      ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' (thickA ∩ ballsV))) n
      ≃ₗ[ℤ] Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) n :=
  homeoHomologyEquivInt (subSubHomeo (fun _ hy => thickA_subset_fixedCompl hy.1)) n

/-! ## §3. `Hₚ(T⁴°;ℤ) = 0` for `p ≥ 4` -/

/-- **`Hₚ(thickA;ℤ) = 0` for `p ≥ 4`** — one Mayer–Vietoris step inside the open punctured torus
`W`: the sum map `Hₚ(thickA) ⊕ Hₚ(ballsV ∩ W) → Hₚ(W)` has zero target
(`torusFourPunctured_high`) and injective (its kernel is the image of
`Hₚ(thickA ∩ ballsV) = 0`, `inter_homology_high`). -/
theorem thickA_homology_high (p : ℕ) (hp : 3 < p)
    (x : Homology (sub (X := TopCat.of TorusFour) thickA) p) : x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  -- The seam of the restricted cover vanishes above degree 3.
  have hseam : ∀ w : Homology (sub (X := sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ))
      (((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' thickA)
        ∩ ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' ballsV)))
      (n + 1), w = 0 := by
    intro w
    refine (seamTransport (n + 1)).map_eq_zero_iff.mp ?_
    exact inter_homology_high (n + 1) hp _
  -- Push `x` into the subspace presentation and run one Mayer–Vietoris step inside `W`.
  refine (thickTransport (n + 1)).symm.map_eq_zero_iff.mp ?_
  set u := (thickTransport (n + 1)).symm x with hu
  have hsum : mvHomSumInt (X := sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ))
      ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' thickA)
      ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' ballsV)
      (n + 1) (u, 0) = 0 :=
    torusFourPunctured_high (n + 1) hp _
  obtain ⟨w, hw⟩ := (mv_exact_middleInt (X := sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ))
    ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' thickA)
    ((Subtype.val : ↥((fixedSet : Set TorusFour)ᶜ) → TorusFour) ⁻¹' ballsV) n hcovW
    (u, 0)).mp hsum
  rw [hseam w, map_zero] at hw
  exact congrArg Prod.fst hw.symm

/-- **`Hₚ(T⁴°;ℤ) = 0` for every `p ≥ 4`** on the project's carrier `PTtop` — the banked deformation
retraction of `PTtop` onto `thickA` (`puncIncl_mapInt_bijective`) transports
`thickA_homology_high`. -/
theorem ptTop_homology_high (p : ℕ) (hp : 3 < p) (x : Homology PTtop p) : x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  refine (SKEFTHawking.KummerPuncturedMV.puncIncl_mapInt_bijective n).injective ?_
  rw [map_zero]
  exact thickA_homology_high (n + 1) hp _

/-- Engine (`Hml`) form of `ptTop_homology_high`. -/
theorem ptTop_hml_high (p : ℕ) (hp : 3 < p) (x : Hml (chainBoundary PTtop) p) : x = 0 := by
  have h := ptTop_homology_high p hp (hmlEquivHomology PTtop p x)
  have h2 := (hmlEquivHomology PTtop p).symm_apply_apply x
  rw [h, map_zero] at h2
  exact h2.symm

/-- **`H₄(T⁴°;ℤ) = 0`** — the first discharged `orientInput` input. -/
theorem h4PT (x : Hml (chainBoundary PTtop) 4) : x = 0 := ptTop_hml_high 4 (by omega) x

/-- **`H₅(T⁴°;ℤ) = 0`** — the second discharged `orientInput` input. -/
theorem h5PT (x : Hml (chainBoundary PTtop) 5) : x = 0 := ptTop_hml_high 5 (by omega) x

/-! ## §4. The transfer sequence with its `T⁴°` hypotheses discharged -/

open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (Qtop qmkC)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerQuotientSmithSES (deltaIII transferH)
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3)
open SKEFTHawking.KummerQuotientTransferSequence

/-- **`δ³₄ : H₅(Q;ℤ) → H₄(B;ℤ)` is bijective, unconditionally.** -/
theorem deltaIII_four_bijective_uncond : Function.Bijective (deltaIII 4) :=
  deltaIII_four_bijective h4PT h5PT

/-- **`H₅(Q;ℤ) ≅ ker (t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)) = H₃(Q;ℤ)[2]`, unconditionally** — the sharp form of
the residual with both `T⁴°`-side hypotheses discharged. -/
def h5QEquivTransferKer_uncond :
    Hml (chainBoundary Qtop) 5 ≃ₗ[ℤ] LinearMap.ker (transferH 3) :=
  h5QEquivTransferKer h4PT h5PT

/-- **THE RESIDUAL, UNCONDITIONALLY.** The degree-3 transfer is injective — equivalently `H₃(Q;ℤ)`
is 2-torsion-free — **iff** `H₅(Q;ℤ) = 0`. Every hypothesis of
`KummerQuotientTransferSequence.transferH_three_injective_iff_h5Q_eq_zero` is now discharged, so the
entire remaining `orientInput` residual (modulo even descent) is the single statement
`H₅(Q;ℤ) = 0`. -/
theorem transferH_three_injective_iff_h5Q_eq_zero_uncond :
    Function.Injective (transferH 3) ↔ ∀ x : Hml (chainBoundary Qtop) 5, x = 0 :=
  transferH_three_injective_iff_h5Q_eq_zero h4PT h5PT

/-- `H₅(Q;ℤ) = 0` alone makes the degree-3 transfer injective. -/
theorem transferH_three_injective_of_h5Q (h5Q : ∀ x : Homology Qtop 5, x = 0) :
    Function.Injective (transferH 3) :=
  transferH_three_injective_of_top_vanishing h5Q (fun x => h4PT x)

/-- **`H₃(Q;ℤ)` is 2-torsion-free from `H₅(Q;ℤ) = 0` alone.** -/
theorem twoTorsionFree_of_h5Q (h5Q : ∀ x : Homology Qtop 5, x = 0)
    (y : Homology (TopCat.of FreeQuotient) 3) (hy : (2 : ℤ) • y = 0) : y = 0 :=
  twoTorsionFree_of_top_vanishing h5Q (fun x => h4PT x) y hy

/-- **`H₃(K3;ℤ) = 0` from `H₅(Q;ℤ) = 0` plus even descent.** -/
theorem h3K3_eq_zero_of_h5Q_of_evenDescent (h5Q : ∀ x : Homology Qtop 5, x = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v)
    (x : Homology KummerK3top 3) : x = 0 :=
  h3K3_eq_zero_of_top_vanishing_of_evenDescent h5Q (fun y => h4PT y) hd x

open scoped SKEFTHawking.KummerK3E1Package in
/-- **The `orientInput` atom from `H₅(Q;ℤ) = 0` plus even descent** — the two `T⁴°` hypotheses of
`KummerQuotientTransferSequence.nonempty_intOrientation_of_top_vanishing_of_evenDescent` are gone. -/
theorem nonempty_intOrientation_of_h5Q_of_evenDescent (h5Q : ∀ x : Homology Qtop 5, x = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Nonempty (SingularHomologyInt.IntOrientation SKEFTHawking.KummerWeld.KummerK3) :=
  nonempty_intOrientation_of_top_vanishing_of_evenDescent h5Q (fun x => h4PT x) hd

/-! ## §5. The Q-side high-degree recursion — the residual is only degrees 4 and 5 -/

/-- `Hₘ(A;ℤ) = 0` whenever `Hₘ(Q;ℤ) = 0`, through the transfer chain isomorphism
`KummerQuotientTransferSequence.qHmlEquivA` (`A = N·C(T⁴°) ≅ C(Q)`). -/
theorem hml_a_eq_zero_of {m : ℕ} (hq : ∀ y : Hml (chainBoundary Qtop) m, y = 0)
    (x : Hml SKEFTHawking.KummerQuotientSmithSES.dA m) : x = 0 := by
  have h := hq ((qHmlEquivA m).symm x)
  have h2 := congrArg (qHmlEquivA m) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

/-- **The Q-side two-step Smith recursion** `Hₘ(Q;ℤ) = 0 ⟹ Hₘ₊₂(Q;ℤ) = 0` for `m ≥ 4`. Exactly the
`KummerRP3HomologyTop.rp3_hml_step` pattern with the covering `T⁴°` in place of `S³`, now that
`Hₚ(T⁴°;ℤ) = 0` for `p ≥ 4` is discharged: `δ'(m)` kills `δ³(m+1) x` into `Hₘ(A) ≅ Hₘ(Q) = 0`, then
`ker δ' = im D̄` lands in `Hₘ₊₁(T⁴°) = 0`, then `ker δ³ = im p̄` lands in `Hₘ₊₂(T⁴°) = 0`.

**Route note (why this does not close the residual).** The recursion runs *upward*: it reduces
`Hₘ₊₂(Q)` to `Hₘ(Q)`, so degrees `4` and `5` are its base cases, not its conclusions. Both Smith
long exact sequences are compatible with the `ℝP^∞` pattern `Hₚ(Q) ≅ Hₚ₋₂(Q)` in every high degree,
so — exactly as on the `ℝP³` lane (`KummerRP3HomologyTop`'s termination hypotheses `h4`, `h5`, which
needed the 4-chart good-cover telescope) — a genuine **`Q`-side geometric input** is required. No
amount of `T⁴°`-side data terminates it. -/
theorem hmlQ_step (m : ℕ) (hm : 4 ≤ m) (hind : ∀ y : Hml (chainBoundary Qtop) m, y = 0)
    (x : Hml (chainBoundary Qtop) (m + 2)) : x = 0 := by
  have h0 : SKEFTHawking.KummerQuotientSmithSES.deltaI m
      (SKEFTHawking.KummerQuotientSmithSES.deltaIII (m + 1) x) = 0 := hml_a_eq_zero_of hind _
  have hdI : SKEFTHawking.KummerQuotientSmithSES.deltaIII (m + 1) x = 0 := by
    obtain ⟨w, hw⟩ := (SKEFTHawking.KummerQuotientSmithSES.exact_diffH_deltaI m
      (SKEFTHawking.KummerQuotientSmithSES.deltaIII (m + 1) x)).mp h0
    rw [← hw, ptTop_hml_high (m + 1) (by omega) w, map_zero]
  obtain ⟨t, ht⟩ := (SKEFTHawking.KummerQuotientSmithSES.exact_projH_deltaIII (m + 1) x).mp hdI
  rw [← ht, ptTop_hml_high (m + 2) (by omega) t, map_zero]

/-- `Hₚ₊₄(Q;ℤ) = 0` for every `p`, from the two base degrees `4` and `5` (strong induction on the
degree shift, stepping by two through `hmlQ_step`). -/
theorem hmlQ_high_shift (h4Q : ∀ x : Hml (chainBoundary Qtop) 4, x = 0)
    (h5Q : ∀ x : Hml (chainBoundary Qtop) 5, x = 0) :
    ∀ n, ∀ x : Hml (chainBoundary Qtop) (n + 4), x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h4Q
    | 1, _ => exact h5Q
    | (k + 2), ih =>
        intro x
        exact hmlQ_step (k + 4) (by omega) (ih k (by omega)) x

/-- **`Hₚ(Q;ℤ) = 0` for every `p ≥ 4`, from degrees 4 and 5 alone.** With the `T⁴°` side fully
discharged, the entire high-degree homology of the free quotient is pinned by its two bottom
top-degrees — so a `Q`-side geometric input in degrees `4, 5` (a good-cover telescope for the free
quotient, mirroring `KummerRP3GoodCoverTelescope`) is the *only* thing the `orientInput` residual
still needs from the quotient. -/
theorem hmlQ_high (h4Q : ∀ x : Hml (chainBoundary Qtop) 4, x = 0)
    (h5Q : ∀ x : Hml (chainBoundary Qtop) 5, x = 0) (p : ℕ) (hp : 4 ≤ p)
    (x : Hml (chainBoundary Qtop) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 4 := ⟨p - 4, by omega⟩
  exact hmlQ_high_shift h4Q h5Q k x

end

end SKEFTHawking.KummerPunctureTopVanish
