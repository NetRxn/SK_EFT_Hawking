/-
# EVEN DESCENT, ANATOMISED — and the seam-lattice fact that refutes it

`KummerQuotientH3Descent.qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent` closes the
`H₃(K3;ℤ)` orientation residual from two inputs: 2-torsion-freeness of `H₃(Q;ℤ)` and the **even**
descent containment

    (ED)   im (p_* : H₃(T⁴°;ℤ) → H₃(Q;ℤ))  ⊆  2 · im qSeamCoord3.

`(ED)` was adopted because the covering projection restricted to a boundary `S³` of `T⁴°` is the
double cover of the corresponding boundary `ℝP³` of `Q`, so **boundary** classes push forward to
*twice* seam classes. This module asks what `(ED)` asserts beyond that, and answers precisely.

## §1. The `T⁴°`-side necessary condition — the whole `Q` side eliminated

Composing `(ED)` with the transfer and using `t ∘ p̄ = 1 + τ_*`
(`KummerQuotientSmithSES.transferH_projH`) removes every `Q`-side object:

    (ED)  ⟹  ∀ x : H₃(T⁴°;ℤ),  x + τ_* x ∈ 2 · H₃(T⁴°;ℤ)      (`two_smul_of_evenDescent`)

— unconditional, no torsion hypothesis, and stated entirely on the punctured torus. Everything
below is a refutation engine for *that*.

## §2. Anatomy: `(ED)` is the goal PLUS a strictly extra 2-divisibility

Modulo 2-torsion-freeness of `H₃(Q;ℤ)`, `(ED)` factors exactly as

    (ED)  ↔  Function.Surjective qSeamCoord3  ∧  im p_* ⊆ 2 · H₃(Q;ℤ)

(`evenDescent_iff_surjective_and_rangeTwoDivisible`). The first conjunct **is** the conclusion the
criterion is used to derive (`qSeamCoord3_surjective_iff_h3K3_eq_zero`: it is `H₃(K3;ℤ) = 0`). So
`(ED)` is strictly stronger than its own conclusion, and the excess is the second conjunct — a
2-divisibility statement about `im p_*` that the seam geometry does **not** supply.

§3 shows the excess cannot be trimmed: the *usable* content of `(ED)` in the criterion's proof is
`∀ u, 2 • u ∈ 2 · im qSeamCoord3`, and modulo 2-torsion-freeness that is **equivalent** to
surjectivity (`evenTwoSaturated_iff_surjective`). The even mechanism therefore has no
strictly-intermediate weakening: any hypothesis weak enough to be plausible and strong enough to run
the argument is already the conclusion.

## §4/§5. Where the seam geometry runs out: the boundary sublattice has corank 4

`ptSeam3 : ℤ¹⁶ → H₃(T⁴°;ℤ)` is the boundary-`S³` lattice map (the MV diagonal on the sixteen
annuli, transported to `T⁴°` through `punctureThickHEquiv`). Its image is **exactly** the kernel of
`H₃(T⁴°;ℤ) → H₃(T⁴;ℤ)` (`range_ptSeam3_eq_ker_mapInt_inclXC`), and that map is onto, so

    H₃(T⁴°;ℤ) / im ptSeam3  ≅  H₃(T⁴;ℤ)  ≅  ℤ⁴      (`punctureH3ModSeamEquivFin4`).

The "boundary `S³` ↦ twice `ℝP³`" geometry only ever controls `im ptSeam3`. The classes it does not
control form a free rank-4 quotient — the four bulk 3-torus directions of `T⁴`. That is the precise
gap `(ED)` silently claims to fill.

## §6. THE REFUTATION, conditional on two named seam facts

* `SeamKernelEvenlyConstant` — every relation among the sixteen boundary classes has all sixteen
  coordinates congruent mod 2. Implied by the tree's own named open input "`im ∂₃` is the diagonal
  `ℤ ⊆ ℤ¹⁶`" (`KummerPunctureH3`, §"The single remaining GEOMETRIC input"), via
  `ptSeam3_eq_zero_iff` + `seamKernelEvenlyConstant_of_kernel_constant`.
* `SeamNormOddity` — **some** 3-cycle of `T⁴°` has τ-norm `x + τ_* x` equal to a seam combination
  two of whose coordinates have *opposite parity*. Its containment half is standard and is split off
  as `NormLandsInSeam` (`τ_* = −1` on `H₃(T⁴;ℤ)`, i.e. `Λ³` of the banked degree-1
  `tauStar_eq_neg`) via `norm_mem_range_ptSeam3`, leaving **parity** as the only new content.

Then `not_evenDescent_of_seamNormOddity : SeamKernelEvenlyConstant → SeamNormOddity → ¬ (ED)`.

Geometrically `SeamNormOddity` is the slab computation: for the 3-subtorus `T³ = {x₄ = 1/4} ⊂ T⁴°`,
`τ(T³) = {x₄ = 3/4}` and `T³ − τ(T³)` bounds the slab `{1/4 ≤ x₄ ≤ 3/4}` minus the **eight**
punctures on `{x₄ = 1/2}`; since `τ_*` acts by `−1` on `H₃(T⁴)`, `x + τ_* x` is the sum of those
eight boundary classes — a `0/1` vector that is neither constant `0` nor constant `1` mod 2.

⚠ That slab paragraph is **informal geometry, not in tree**: it is the reason to *expect*
`SeamNormOddity`, and `SeamNormOddity` is exactly the Prop one must construct to convert the
expectation into the kernel-checked `¬ (ED)` above. What IS kernel-checked here is the reduction:
`(ED)` survives **only if** one of the two named seam facts fails. The route finding to carry
forward is therefore: **`(ED)` overreaches onto exactly the bulk classes the boundary geometry never
reached (§4/§5's free rank-4 quotient), and it is expected to be false there** — so the even form
should not be aimed at. The banked *weak* form
(`KummerK3H3SeamWindow.twoTorsionFree_iff_qSeamCoord3_surjective_of_descent`,
`im p_* ⊆ im qSeamCoord3`) is untouched by any of this — it is satisfied by those same eight-fold
seam sums, which is why it, not `(ED)`, is the form to keep.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerQuotientH3Descent
import SKEFTHawking.KummerPunctureH3

namespace SKEFTHawking.KummerQuotientH3EvenDescent

open SKEFTHawking.ChainComplexLESInt (Hml)
open SKEFTHawking.SingularHomologyInt (Homology chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC)
open SKEFTHawking.KummerQuotientSmithSES (projH transferH tauH transferH_projH)
open SKEFTHawking.KummerQuotientH2Solve (inclXC)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerPunctureBalls (thickA ballsV punc_hcov)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt mvDeltaInt
  mvHomSumInt_apply mvHomDiagInt_apply mvHomSumInt_mvHomDiagInt)
open SKEFTHawking.KummerPuncturedMV (puncInclC mapInt_inclXC_eq puncIncl_mapInt_bijective)
open SKEFTHawking.KummerPunctureH3 (interH3EquivEIndex puncMiddle3_exact puncInter3_exact
  thickIncl3_surjective torusFourH3_twoTorsionFree ballsVH3_eq_zero)
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3 projH_eq_mapInt two_smul_mem_range_mapInt_qmkC)
open SKEFTHawking.KummerQuotientH3Descent (punctureThickHEquiv)

noncomputable section

/-! ## §1. The `T⁴°`-side necessary condition: `(1 + τ_*) H₃(T⁴°;ℤ) ⊆ 2 · H₃(T⁴°;ℤ)` -/

/-- **THE HANDLE.** Even descent forces every τ-**norm** on `H₃(T⁴°;ℤ)` to be divisible by 2 —
a statement with no `Q`-side object left in it, and no torsion hypothesis.

Proof: `x + τ_* x = t (p̄ x)` (`KummerQuotientSmithSES.transferH_projH`), `p̄ = p_*`
(`KummerK3H3SeamWindow.projH_eq_mapInt`), and even descent replaces `p_* x` by `2 • qSeamCoord3 v`,
which the ℤ-linear transfer carries out of the smul. Every refutation of even descent below runs
through this reduction. -/
theorem two_smul_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v)
    (x : Hml (chainBoundary PTtop) 3) :
    ∃ z : Hml (chainBoundary PTtop) 3, x + tauH 3 x = (2 : ℤ) • z := by
  obtain ⟨v, hv⟩ := hd x
  refine ⟨transferH 3 (qSeamCoord3 v), ?_⟩
  rw [← transferH_projH 3 x, projH_eq_mapInt 2 x, hv]
  exact map_zsmul _ _ _

/-- Contrapositive of `two_smul_of_evenDescent`: a single 3-cycle of `T⁴°` whose τ-norm is not
2-divisible kills even descent outright. -/
theorem not_evenDescent_of_norm_not_two_smul
    (h : ∃ x : Hml (chainBoundary PTtop) 3, ∀ z : Hml (chainBoundary PTtop) 3,
      x + tauH 3 x ≠ (2 : ℤ) • z) :
    ¬ ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v := by
  intro hd
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, hz⟩ := two_smul_of_evenDescent hd x
  exact hx z hz

/-! ## §2. Anatomy: even descent = surjectivity + a strictly extra 2-divisibility -/

/-- The *excess* of even descent over its own conclusion: `im p_* ⊆ 2 · H₃(Q;ℤ)`. Nothing in the
covering geometry supplies this for the bulk classes (§5). -/
def RangeTwoDivisible : Prop :=
  ∀ x : Homology PTtop 3, ∃ w : Homology Qtop 3, Homology.mapInt qmkC 3 x = (2 : ℤ) • w

/-- Even descent contains the excess: `2 · im qSeamCoord3 ⊆ 2 · H₃(Q;ℤ)`. -/
theorem rangeTwoDivisible_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    RangeTwoDivisible := by
  intro x
  obtain ⟨v, hv⟩ := hd x
  exact ⟨qSeamCoord3 v, hv⟩

/-- Conversely, once the seam classes generate `H₃(Q;ℤ)` the excess *is* even descent: the two
differ only by whether the doubled class is doubled inside the seam span. -/
theorem evenDescent_of_surjective_of_rangeTwoDivisible
    (hs : Function.Surjective qSeamCoord3) (hr : RangeTwoDivisible) (x : Homology PTtop 3) :
    ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v := by
  obtain ⟨w, hw⟩ := hr x
  obtain ⟨v, rfl⟩ := hs w
  exact ⟨v, hw⟩

/-- **THE ANATOMY.** Modulo 2-torsion-freeness of `H₃(Q;ℤ)` — the criterion's *other* input — even
descent splits exactly into its own conclusion and one strictly extra assertion:

    even descent  ↔  `Surjective qSeamCoord3`  ∧  `im p_* ⊆ 2 · H₃(Q;ℤ)`.

Since `Function.Surjective qSeamCoord3 ↔ H₃(K3;ℤ) = 0`
(`KummerK3H3SeamWindow.qSeamCoord3_surjective_iff_h3K3_eq_zero`), the left conjunct is the whole
target; the right conjunct is pure excess, and §5–§6 locate and refute it. -/
theorem evenDescent_iff_surjective_and_rangeTwoDivisible
    (h2 : ∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0) :
    (∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) ↔
      (Function.Surjective qSeamCoord3 ∧ RangeTwoDivisible) := by
  constructor
  · intro hd
    exact ⟨SKEFTHawking.KummerQuotientH3Descent.qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent
      h2 hd, rangeTwoDivisible_of_evenDescent hd⟩
  · rintro ⟨hs, hr⟩
    exact evenDescent_of_surjective_of_rangeTwoDivisible hs hr

/-- Under the excess, the covering's unconditional `2 · H₃(Q;ℤ) ⊆ im p_*`
(`KummerK3H3SeamWindow.two_smul_mem_range_mapInt_qmkC`) becomes an equality: `im p_*` is *exactly*
the doubled classes. So the excess is not a mild strengthening — it pins the descent image. -/
theorem range_mapInt_qmkC_eq_two_smul_of_rangeTwoDivisible (hr : RangeTwoDivisible) :
    Set.range (Homology.mapInt qmkC 3) = {y : Homology Qtop 3 | ∃ w, y = (2 : ℤ) • w} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact hr x
  · rintro ⟨w, rfl⟩
    exact two_smul_mem_range_mapInt_qmkC 2 w

/-! ## §3. The even mechanism admits no strictly-intermediate weakening -/

/-- The *usable* content of even descent inside
`qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent`: every doubled `H₃(Q;ℤ)` class is a
doubled seam class. -/
def EvenTwoSaturated : Prop :=
  ∀ u : Homology Qtop 3, ∃ v, (2 : ℤ) • u = (2 : ℤ) • qSeamCoord3 v

/-- Even descent implies its usable content, through `p̄ ∘ t = 2`. -/
theorem evenTwoSaturated_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    EvenTwoSaturated := by
  intro u
  obtain ⟨x, hx⟩ := two_smul_mem_range_mapInt_qmkC 2 u
  obtain ⟨v, hv⟩ := hd x
  exact ⟨v, hx.symm.trans hv⟩

/-- **THE MECHANISM CANNOT BE TRIMMED.** Modulo 2-torsion-freeness the usable content of even
descent is *equivalent* to the conclusion it is used to prove. Hence there is no hypothesis strictly
between "even descent" and "`qSeamCoord3` surjective" that still runs the argument: weakening even
descent to what the proof actually consumes lands exactly on the goal. -/
theorem evenTwoSaturated_iff_surjective
    (h2 : ∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0) :
    EvenTwoSaturated ↔ Function.Surjective qSeamCoord3 := by
  constructor
  · intro h u
    obtain ⟨v, hv⟩ := h u
    refine ⟨v, ?_⟩
    have hz : (2 : ℤ) • (u - qSeamCoord3 v) = 0 := by
      rw [smul_sub]; exact sub_eq_zero.mpr hv
    exact (sub_eq_zero.mp (h2 _ hz)).symm
  · intro hs u
    obtain ⟨v, rfl⟩ := hs u
    exact ⟨v, rfl⟩

/-! ## §4. The boundary-`S³` seam lattice of `T⁴°` -/

/-- The live half of the degree-3 puncture MV diagonal, `H₃(collar;ℤ) → H₃(thickA;ℤ)`. -/
abbrev collarToThickA3 :
    Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3 →ₗ[ℤ]
      Homology (sub (X := TopCat.of TorusFour) thickA) 3 :=
  Homology.mapInt (subIncl (Set.inter_subset_left (s := thickA) (t := ballsV))) 3

/-- **THE `T⁴°` SEAM LATTICE MAP** `ℤ¹⁶ → H₃(T⁴°;ℤ)`: the sixteen boundary-`S³` classes, read
through the banked `interH3EquivEIndex : H₃(collar;ℤ) ≅ ℤ¹⁶` and the thickening equivalence
`punctureThickHEquiv 2 : H₃(T⁴°;ℤ) ≅ H₃(thickA;ℤ)`. Upstairs counterpart of
`KummerK3H3SeamWindow.qSeamCoord3`. -/
def ptSeam3 : (EIndex → ℤ) →ₗ[ℤ] Homology PTtop 3 :=
  ((punctureThickHEquiv 2).symm.toLinearMap ∘ₗ collarToThickA3) ∘ₗ
    interH3EquivEIndex.symm.toLinearMap

theorem ptSeam3_apply (v : EIndex → ℤ) :
    ptSeam3 v = (punctureThickHEquiv 2).symm (collarToThickA3 (interH3EquivEIndex.symm v)) := rfl

/-- `punctureThickHEquiv 2` is the inclusion-induced map, so it undoes its own inverse. -/
theorem mapInt_puncInclC_symm (y : Homology (sub (X := TopCat.of TorusFour) thickA) 3) :
    Homology.mapInt puncInclC 3 ((punctureThickHEquiv 2).symm y) = y := by
  simp [punctureThickHEquiv]

/-- **Seam classes die in `H₃(T⁴;ℤ)`.** Both MV routes out of the collar agree
(`mvHomSumInt_mvHomDiagInt`) and the ball side is acyclic in degree 3 (`ballsVH3_eq_zero`), so the
boundary-`S³` classes are exactly the ones that bound in the ambient torus. -/
theorem mapInt_inclXC_ptSeam3 (v : EIndex → ℤ) :
    Homology.mapInt inclXC 3 (ptSeam3 v) = 0 := by
  set w := interH3EquivEIndex.symm v with hw
  have hball : Homology.mapInt
      (subIncl (Set.inter_subset_right (s := thickA) (t := ballsV))) 3 w = 0 :=
    ballsVH3_eq_zero _
  have h := mvHomSumInt_mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3 w
  rw [mvHomDiagInt_apply, mvHomSumInt_apply, hball, map_zero, sub_zero] at h
  rw [mapInt_inclXC_eq 3, LinearMap.comp_apply, ptSeam3_apply, mapInt_puncInclC_symm]
  exact h

/-- **The seam lattice IS the kernel of `H₃(T⁴°;ℤ) → H₃(T⁴;ℤ)`.** `⊆` is
`mapInt_inclXC_ptSeam3`; `⊇` is exactness of the puncture MV at the middle
(`puncMiddle3_exact`) once the dead ball summand is discarded. -/
theorem range_ptSeam3_eq_ker_mapInt_inclXC :
    LinearMap.range ptSeam3 = LinearMap.ker (Homology.mapInt inclXC 3) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact mapInt_inclXC_ptSeam3 v
  · intro hx
    have hx0 : Homology.mapInt inclXC 3 x = 0 := hx
    have hsum : mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 3
        (Homology.mapInt puncInclC 3 x, 0) = 0 := by
      rw [mvHomSumInt_apply, map_zero, sub_zero]
      rw [← LinearMap.comp_apply, ← mapInt_inclXC_eq 3]
      exact hx0
    obtain ⟨w, hw⟩ := (puncMiddle3_exact _).mp hsum
    refine ⟨interH3EquivEIndex w, ?_⟩
    have hfst : collarToThickA3 w = Homology.mapInt puncInclC 3 x := by
      have := congrArg Prod.fst hw
      rwa [mvHomDiagInt_apply] at this
    rw [ptSeam3_apply, LinearEquiv.symm_apply_apply, hfst]
    simp [punctureThickHEquiv]

/-- `H₃(T⁴°;ℤ) ↠ H₃(T⁴;ℤ)` — `thickIncl3_surjective` through the thickening equivalence. -/
theorem mapInt_inclXC_three_surjective :
    Function.Surjective (Homology.mapInt inclXC 3) := by
  rw [mapInt_inclXC_eq 3, LinearMap.coe_comp]
  exact thickIncl3_surjective.comp (puncIncl_mapInt_bijective 2).surjective

/-- **THE CORANK OF THE SEAM LATTICE.** `H₃(T⁴°;ℤ) / im ptSeam3 ≅ H₃(T⁴;ℤ)`: the boundary-`S³`
classes are precisely the ones the ambient torus does not see, so the quotient by them is the
torus's own degree-3 homology. -/
def punctureH3ModSeam :
    (Homology PTtop 3 ⧸ LinearMap.range ptSeam3) ≃ₗ[ℤ] Homology (TopCat.of TorusFour) 3 :=
  (Submodule.quotEquivOfEq _ _ range_ptSeam3_eq_ker_mapInt_inclXC).trans
    ((Homology.mapInt inclXC 3).quotKerEquivRange.trans
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr mapInt_inclXC_three_surjective)))

/-- **THE CORANK IS 4, EXPLICITLY.** `H₃(T⁴°;ℤ) / im ptSeam3 ≅ ℤ⁴`
(`KummerHomologyT4Full.torusFourH3EquivFin4`). This is the quantitative statement of where the
"boundary `S³` ↦ twice `ℝP³`" geometry runs out: it controls `im ptSeam3` and nothing else, and what
it fails to control is a **free rank-4** module — the four bulk 3-torus directions. Even descent
asserts 2-divisibility across that whole free quotient with no geometric warrant. -/
def punctureH3ModSeamEquivFin4 :
    (Homology PTtop 3 ⧸ LinearMap.range ptSeam3) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  punctureH3ModSeam.trans SKEFTHawking.KummerHomologyT4Full.torusFourH3EquivFin4

/-- **THE SEAM LATTICE IS A PROPER SUBGROUP — unconditionally.** `ptSeam3` is not surjective, since
its cokernel is `ℤ⁴ ≠ 0` (`punctureH3ModSeamEquivFin4`). This is the sharpest one-line form of the
overreach, and the non-vacuity witness for §4/§5: there provably *are* classes of `H₃(T⁴°;ℤ)`
outside the boundary-`S³` lattice, and even descent asserts 2-divisibility of their `p_*`-images
with nothing but the boundary geometry behind it. -/
theorem not_surjective_ptSeam3 : ¬ Function.Surjective ptSeam3 := by
  intro hs
  haveI : Subsingleton (Homology PTtop 3 ⧸ LinearMap.range ptSeam3) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hs)
  haveI : Subsingleton (Fin 4 → ℤ) := punctureH3ModSeamEquivFin4.symm.injective.subsingleton
  exact one_ne_zero
    (congrFun (Subsingleton.elim (fun _ => (1 : ℤ)) (fun _ => (0 : ℤ))) (0 : Fin 4))

/-- The seam lattice's kernel is the image of the puncture connecting map `∂₃ : H₄(T⁴;ℤ) → ℤ¹⁶`
(`puncInter3_exact`) — the tree's own named remaining geometric input for `H₃(T⁴°;ℤ) ≅ ℤ¹⁹`. This
is what ties `SeamKernelEvenlyConstant` below to an already-tracked crux rather than to a new one. -/
theorem ptSeam3_eq_zero_iff (v : EIndex → ℤ) :
    ptSeam3 v = 0 ↔ interH3EquivEIndex.symm v ∈
      Set.range (mvDeltaInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov) := by
  rw [← puncInter3_exact (interH3EquivEIndex.symm v)]
  constructor
  · intro h
    have hthick : collarToThickA3 (interH3EquivEIndex.symm v) = 0 :=
      (LinearEquiv.map_eq_zero_iff (punctureThickHEquiv 2).symm).mp h
    rw [mvHomDiagInt_apply]
    exact Prod.ext hthick (ballsVH3_eq_zero _)
  · intro h
    have hthick : collarToThickA3 (interH3EquivEIndex.symm v) = 0 := by
      have := congrArg Prod.fst h
      rwa [mvHomDiagInt_apply] at this
    rw [ptSeam3_apply, hthick, map_zero]

/-! ## §5. The two named seam facts -/

/-- **Named geometric fact #1.** Every ℤ-relation among the sixteen boundary-`S³` classes of `T⁴°`
has all sixteen coordinates congruent mod 2.

*Vacuity attack.* This is not free: it is exactly the assertion that `ker ptSeam3 = im ∂₃`
(`ptSeam3_eq_zero_iff`) contains no vector of mixed parity — i.e. that the fundamental class `[T⁴]`
bounds with the **same** local degree at every one of the sixteen punctures. A relation like
`(1,0,…,0)` would violate it. It is implied by, and strictly weaker than, the tree's named input
"`im ∂₃` is the diagonal `ℤ ⊆ ℤ¹⁶`" (`seamKernelEvenlyConstant_of_kernel_constant`), which
`KummerPunctureH3` already records as the single remaining geometric input for
`H₃(T⁴°;ℤ) ≅ ℤ¹⁹`. -/
def SeamKernelEvenlyConstant : Prop :=
  ∀ v : EIndex → ℤ, ptSeam3 v = 0 → ∀ c c' : EIndex, (2 : ℤ) ∣ v c - v c'

/-- The diagonal form of the connecting-map input implies fact #1. -/
theorem seamKernelEvenlyConstant_of_kernel_constant
    (h : ∀ v : EIndex → ℤ, ptSeam3 v = 0 → ∃ k : ℤ, v = fun _ => k) :
    SeamKernelEvenlyConstant := by
  intro v hv c c'
  obtain ⟨k, rfl⟩ := h v hv
  simp

/-- **Named geometric fact #2.** Some 3-cycle of `T⁴°` has τ-norm `x + τ_* x` equal to a seam
combination two of whose coordinates have opposite parity.

*Vacuity attack.* This is **false** on the seam lattice itself: `τ` fixes each puncture and acts on
its boundary `S³` by the antipodal map of `S³ ⊂ ℝ⁴` (degree `+1`), so `ptSeam3 v + τ_* (ptSeam3 v)`
is `2 • ptSeam3 v`, whose coordinate vector `2v` is constant `0` mod 2. The Prop therefore cannot be
discharged from the boundary geometry at all; it asserts the existence of a class in the free rank-4
quotient `punctureH3ModSeamEquivFin4` with an *odd* seam norm, which is a genuine construction (the
slab bounded by `{x₄ = 1/4}` and `{x₄ = 3/4}` meets exactly eight of the sixteen punctures). No
zero-geometric-input proof of it exists inside this window. -/
def SeamNormOddity : Prop :=
  ∃ (x : Hml (chainBoundary PTtop) 3) (v : EIndex → ℤ) (c c' : EIndex),
    x + tauH 3 x = ptSeam3 v ∧ ¬ (2 : ℤ) ∣ v c - v c'

/-- The **standard half** of `SeamNormOddity`: τ-norms of `T⁴°` classes die in `H₃(T⁴;ℤ)`. This is
the usual `τ_* = −1` on `H₃(T⁴;ℤ)` (it is `Λ³` of `−1` on `H₁(T⁴;ℤ)`, the degree-3 sibling of the
banked degree-1 `KummerK3H1SeamLattice.tauStar_eq_neg`), read through the inclusion. Splitting it off
isolates what is *genuinely new* in `SeamNormOddity`: only the **parity** of the resulting seam
vector, not its existence. -/
def NormLandsInSeam : Prop :=
  ∀ x : Hml (chainBoundary PTtop) 3, Homology.mapInt inclXC 3 (x + tauH 3 x) = 0

/-- Under the standard half, every τ-norm *is* a seam class, so `SeamNormOddity` reduces to a pure
parity assertion about its sixteen coordinates. -/
theorem norm_mem_range_ptSeam3 (h : NormLandsInSeam) (x : Hml (chainBoundary PTtop) 3) :
    ∃ v : EIndex → ℤ, x + tauH 3 x = ptSeam3 v := by
  have hmem : (x + tauH 3 x : Homology PTtop 3) ∈ LinearMap.ker (Homology.mapInt inclXC 3) := h x
  rw [← range_ptSeam3_eq_ker_mapInt_inclXC] at hmem
  obtain ⟨v, hv⟩ := hmem
  exact ⟨v, hv.symm⟩

/-! ## §6. The refutation -/

/-- **A seam class of mixed parity is not 2-divisible in `H₃(T⁴°;ℤ)`.** If `ptSeam3 v = 2 • z` then
`z` dies in the torsion-free `H₃(T⁴;ℤ)` (`torusFourH3_twoTorsionFree`), hence `z` is itself a seam
class `ptSeam3 w` (`range_ptSeam3_eq_ker_mapInt_inclXC`), so `v − 2w ∈ ker ptSeam3` and fact #1
forces every coordinate difference of `v` to be even. -/
theorem not_two_smul_ptSeam3 (hk : SeamKernelEvenlyConstant) (v : EIndex → ℤ) (c c' : EIndex)
    (hv : ¬ (2 : ℤ) ∣ v c - v c') (z : Homology PTtop 3) : ptSeam3 v ≠ (2 : ℤ) • z := by
  intro hz
  have hzero : Homology.mapInt inclXC 3 ((2 : ℤ) • z) = 0 := by
    rw [← hz]; exact mapInt_inclXC_ptSeam3 v
  have hzT : Homology.mapInt inclXC 3 z = 0 := by
    refine torusFourH3_twoTorsionFree _ ?_
    rw [← map_zsmul]; exact hzero
  obtain ⟨w, hw⟩ : z ∈ LinearMap.range ptSeam3 := by
    rw [range_ptSeam3_eq_ker_mapInt_inclXC]; exact hzT
  have hker : ptSeam3 (v - (2 : ℤ) • w) = 0 := by
    rw [map_sub, map_zsmul, hw, ← hz, sub_self]
  have := hk _ hker c c'
  refine hv ?_
  have hcoord : (v - (2 : ℤ) • w) c - (v - (2 : ℤ) • w) c'
      = (v c - v c') - (2 : ℤ) * (w c - w c') := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcoord] at this
  omega

/-- **THE REFUTATION OF EVEN DESCENT**, from the two named seam facts. `(ED)` forces every τ-norm to
be 2-divisible (§1); fact #2 produces a τ-norm that is a mixed-parity seam class; fact #1 says such a
class is never 2-divisible.

Both inputs are geometric statements about the sixteen boundary `S³`s of `T⁴°`, and fact #1 is the
tree's own already-named connecting-map crux. So the even route is dead unless one of those two
fails — while the banked **weak** form `im p_* ⊆ im qSeamCoord3`
(`KummerK3H3SeamWindow.twoTorsionFree_iff_qSeamCoord3_surjective_of_descent`) survives both, being
satisfied by exactly the mixed-parity seam sums that kill `(ED)`. -/
theorem not_evenDescent_of_seamNormOddity (hk : SeamKernelEvenlyConstant) (ho : SeamNormOddity) :
    ¬ ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v := by
  obtain ⟨x, v, c, c', hnorm, hv⟩ := ho
  refine not_evenDescent_of_norm_not_two_smul ⟨x, fun z hz => ?_⟩
  exact not_two_smul_ptSeam3 hk v c c' hv z (hnorm ▸ hz)

/-- **The excess of §2 is what dies.** Under the two named seam facts the extra conjunct
`im p_* ⊆ 2 · H₃(Q;ℤ)` of `evenDescent_iff_surjective_and_rangeTwoDivisible` fails *given*
surjectivity — i.e. the failure of `(ED)` is located exactly in the excess, not in the conclusion.
So refuting `(ED)` costs `H₃(K3;ℤ) = 0` nothing. -/
theorem not_rangeTwoDivisible_of_seamNormOddity (hk : SeamKernelEvenlyConstant)
    (ho : SeamNormOddity) (hs : Function.Surjective qSeamCoord3) : ¬ RangeTwoDivisible := by
  intro hr
  exact not_evenDescent_of_seamNormOddity hk ho
    (evenDescent_of_surjective_of_rangeTwoDivisible hs hr)

end

end SKEFTHawking.KummerQuotientH3EvenDescent
