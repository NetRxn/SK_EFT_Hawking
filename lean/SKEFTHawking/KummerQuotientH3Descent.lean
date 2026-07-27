/-
# `H₃(Q;ℤ)` through the free double cover: the descent defect, its exponent, and a sharp
sufficient criterion for the `orientInput` residual

`KummerK3H3SeamWindow` landed the whole `H₃(K3;ℤ)` orientation residual on one map,
`qSeamCoord3 : ℤ¹⁶ → H₃(Q;ℤ)`, leaving `H₃(Q;ℤ)` as the single uncomputed object.
`Q = FreeQuotient = T⁴°/τ` is the **free** `ℤ/2` quotient of the punctured 4-torus, so the only
tool that reaches it is the covering `p : T⁴° → Q` and its transfer. This module extracts
everything that structure gives **unconditionally**, and then converts it into a criterion.

## §1. The transfer kernel is 2-torsion (every degree)

`p̄ ∘ t = 2` (`KummerK3H3SeamWindow.projH_transferH`) forces `ker t ⊆ Hₙ(Q;ℤ)[2]`. Consequently a
class of **odd** order that the transfer kills is zero, and — if `Hₙ(T⁴°;ℤ)` is torsion-free —
`Hₙ(Q;ℤ)` has **no odd torsion at all**: all of its torsion is concentrated in exponent 2. That is
the first genuine partial computation of `H₃(Q;ℤ)`: whatever torsion it has is an `𝔽₂`-space.

## §1b. The `T⁴°`-side input, discharged unconditionally — and the crux renamed

The `thickA ↝ T⁴°` carrier gap is **not** open: `KummerPuncturedMV.puncIncl_mapInt_bijective`
(built from the glued radial `puncFlow` deformation retraction) makes the inclusion
`T⁴° ↪ thickA` induce a bijection on `Hₙ₊₁(–;ℤ)` in every positive degree. Transporting the
unconditional `KummerPunctureH3Mod2.thickA_H3_twoTorsionFree` across it gives

    `punctureH3_twoTorsionFree` :  H₃(T⁴°;ℤ) is 2-torsion-free   (unconditional),

whence two unconditional consequences: the 2-primary torsion of `H₃(Q;ℤ)` has exponent at most 2
(`two_smul_eq_zero_of_two_pow_smul_eq_zero`), and — sharply —

    H₃(Q;ℤ)[2] = ker (t : H₃(Q;ℤ) → H₃(T⁴°;ℤ))    (`transferH_three_eq_zero_iff`),

so "`H₃(Q;ℤ)` is 2-torsion-free" **is** "the transfer is injective in degree 3"
(`twoTorsionFree_iff_transferH_three_injective`). The remaining crux is a property of one banked
map, not of an unknown group.

⚠ This does **not** cross the second, fatal gap: torsion-freeness still does not descend along the
*free* `ℤ/2` quotient `T⁴° → Q` (`H₁(S³;ℤ) = 0` but `H₁(ℝP³;ℤ) = ℤ/2`). Nothing here asserts it —
`punctureH3_twoTorsionFree` is a `T⁴°` statement and is used only through the transfer.

## §2. The descent defect `Hₙ₊₁(Q;ℤ)/im p_*` is an `𝔽₂`-vector space

`2 · Hₙ₊₁(Q;ℤ) ⊆ im p_*` (`KummerK3H3SeamWindow.two_smul_mem_range_projH`) plus SES-III exactness
gives `2 · im (δ³ₙ) = 0`, hence — by exactness at `Hₙ(B)` — **`ker (ι_B : Hₙ(B) → Hₙ(T⁴°))` is
killed by 2**, in every degree. `descentDefectEquiv` packages this as an explicit ℤ-linear
isomorphism

    H₃(Q;ℤ) / im p_*  ≅  ker (ι_B : H₂(B) → H₂(T⁴°)),

so the defect group of the descent is *computed*, not merely bounded: it is the kernel of a single
banked map, and it is an `𝔽₂`-vector space.

## §3. The sharp criterion: 2-torsion-freeness + **even** descent ⟹ `H₃(K3;ℤ) = 0`

The geometry of the covering sends each boundary `S³` of `T⁴°` to **twice** the corresponding
boundary `ℝP³` class of `Q` (a degree-2 double cover on the top class of the boundary piece). So the
geometrically natural containment is not `im p_* ⊆ im qSeamCoord3` (the hypothesis of the banked
`twoTorsionFree_iff_qSeamCoord3_surjective_of_descent`) but the **even** form

    im p_*  ⊆  2 · im qSeamCoord3.

`qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent` shows the even form together with
2-torsion-freeness of `H₃(Q;ℤ)` gives **surjectivity** of `qSeamCoord3` outright, hence
`H₃(K3;ℤ) = 0` (`KummerK3H3SeamWindow.qSeamCoord3_surjective_iff_h3K3_eq_zero`) and the orientation
atom. The even form also *implies* the banked weak form (`descent_of_evenDescent`), so nothing is
lost by stating it this way.

## Vacuity attack (run, and it fails)

Neither hypothesis is free, and the conclusion cannot be reached without geometry:

* the conclusion `Function.Surjective qSeamCoord3` is **equivalent** to `∀ x : H₃(K3;ℤ), x = 0`
  (banked `qSeamCoord3_surjective_iff_h3K3_eq_zero`), an open computation — so no hypothesis-free
  proof of it can exist inside this window;
* the 2-torsion-freeness hypothesis is degree-sensitive and has real content: its **degree-1
  analogue is not vacuous but violent** — `twoTorsionFree_one_forces_trivial_descent` derives from
  it that `p_* : H₁(T⁴°;ℤ) → H₁(Q;ℤ)` is the zero map, using the banked
  `KummerK3H1SeamLattice.two_zsmul_mapInt_qmkC`. A hypothesis with that much bite in degree 1 is not
  a tautology in degree 3;
* the even-descent hypothesis fails for any `p_*`-image that is an odd multiple of a seam class, and
  nothing here discharges it.

## ⛔ Not re-attempted

The degree-1/2 Smith walk (`KummerQuotientH2Solve`) does **not** lift to degree 3: its engine is
`X_H1_fixed_eq_zero` (`τ`-FIXED ⟹ zero, i.e. `τ_* = −1` on `H₁`), and one degree up `τ_* = +1` on
`H₂(T⁴)` — the tree records exactly that asymmetry (`X_H2_anti_eq_zero`, with **no**
`X_H2_fixed_eq_zero`). So `inclBH 2` is not injective by that route and `projH 3` is not surjective.
Consistently, §2 shows the defect `H₃(Q;ℤ)/im p_*` is *exactly* `ker (inclBH 2)` — the walk's
failure is not a gap in the argument, it is the defect group being nonzero.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3H3SeamWindow
import SKEFTHawking.KummerK3H1SeamLattice
import SKEFTHawking.KummerPunctureH3Mod2

namespace SKEFTHawking.KummerQuotientH3Descent

open SKEFTHawking.SingularHomologyInt (Homology chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerK3H1SeamLattice (exact_inclBH_projH two_zsmul_mapInt_qmkC)
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3 projH_transferH two_smul_mem_range_projH
  two_smul_mem_range_mapInt_qmkC qSeamCoord3_surjective_iff_h3K3_eq_zero
  nonempty_intOrientation_of_qSeamCoord3_surjective two_smul_mem_range_qSeamCoord3_of_descent
  twoTorsionFree_iff_qSeamCoord3_surjective_of_descent)

noncomputable section

/-! ## §0. Scalar algebra: odd order plus exponent 2 forces vanishing -/

/-- An element killed by `2` and by an **odd** integer is zero. -/
theorem eq_zero_of_odd_smul_of_two_smul_eq_zero {M : Type*} [AddCommGroup M] {y : M} {k : ℤ}
    (h2 : (2 : ℤ) • y = 0) (hk : (2 * k + 1) • y = 0) : y = 0 := by
  have h : (2 * k + 1) • y = y := by
    rw [add_smul, one_smul, mul_comm, mul_smul, h2, smul_zero, zero_add]
  exact h.symm.trans hk

/-! ## §1. The transfer kernel is 2-torsion in every degree -/

/-- **`ker t ⊆ Hₙ(Q;ℤ)[2]`.** Immediate from `p̄ ∘ t = 2`
(`KummerK3H3SeamWindow.projH_transferH`): a class the transfer kills is killed by `2`. This is the
only *unconditional* torsion information the free double cover gives about `Hₙ(Q;ℤ)` itself (as
opposed to about `im p_*`). -/
theorem two_smul_eq_zero_of_transferH_eq_zero (n : ℕ) {y : Hml (chainBoundary Qtop) n}
    (h : transferH n y = 0) : (2 : ℤ) • y = 0 := by
  have hp := projH_transferH n y
  rw [h, map_zero] at hp
  exact hp.symm

/-- A class of odd order that the transfer kills is zero. -/
theorem eq_zero_of_odd_smul_of_transferH_eq_zero (n : ℕ) {y : Hml (chainBoundary Qtop) n} {k : ℤ}
    (htr : transferH n y = 0) (hk : (2 * k + 1) • y = 0) : y = 0 :=
  eq_zero_of_odd_smul_of_two_smul_eq_zero (two_smul_eq_zero_of_transferH_eq_zero n htr) hk

/-- **ALL torsion of `Hₙ(Q;ℤ)` has exponent 2, once `Hₙ(T⁴°;ℤ)` is torsion-free.** The transfer of
a torsion class is a torsion class upstairs, hence vanishes; then §1's `ker t ⊆ Hₙ(Q;ℤ)[2]` applies.

This is the first genuine partial computation of the torsion of `H₃(Q;ℤ)`: it is an `𝔽₂`-vector
space, resting on the one `T⁴°`-side input (torsion-freeness of `H₃(T⁴°;ℤ)`) rather than on any
`Q`-side guess. Note the input is *strictly* a `T⁴°` statement — it is emphatically **not** the
false "2-torsion-freeness descends along a free `ℤ/2` quotient" (`H₁(S³;ℤ) = 0` vs
`H₁(ℝP³;ℤ) = ℤ/2`): the conclusion here still allows `H₃(Q;ℤ)` an `𝔽₂`-torsion subgroup. -/
theorem two_smul_eq_zero_of_smul_eq_zero_of_ptTorsionFree (n : ℕ)
    (hPT : ∀ (x : Hml (chainBoundary PTtop) n) (m : ℤ), m ≠ 0 → m • x = 0 → x = 0)
    {y : Hml (chainBoundary Qtop) n} {m : ℤ} (hm : m ≠ 0) (h : m • y = 0) : (2 : ℤ) • y = 0 := by
  refine two_smul_eq_zero_of_transferH_eq_zero n (hPT _ m hm ?_)
  rw [← map_zsmul, h, map_zero]

/-- **`Hₙ(Q;ℤ)` has no odd torsion once `Hₙ(T⁴°;ℤ)` is torsion-free.** Odd order plus exponent 2
forces vanishing (§0), so the `𝔽₂` bound of the previous theorem is sharp in the only direction
available. -/
theorem eq_zero_of_odd_smul_of_ptTorsionFree (n : ℕ)
    (hPT : ∀ (x : Hml (chainBoundary PTtop) n) (m : ℤ), m ≠ 0 → m • x = 0 → x = 0)
    {y : Hml (chainBoundary Qtop) n} {k : ℤ} (hk : (2 * k + 1) • y = 0) : y = 0 :=
  eq_zero_of_odd_smul_of_two_smul_eq_zero
    (two_smul_eq_zero_of_smul_eq_zero_of_ptTorsionFree n hPT (by omega) hk) hk

/-- **Torsion-freeness of `Hₙ(Q;ℤ)` collapses to 2-torsion-freeness** over a torsion-free
`Hₙ(T⁴°;ℤ)`. This is what makes the 2-torsion hypothesis of §3's criterion the *geometrically*
natural one rather than an artificially weak stand-in: modulo the `T⁴°`-side input, the two are the
same statement. -/
theorem torsionFree_iff_twoTorsionFree_of_ptTorsionFree (n : ℕ)
    (hPT : ∀ (x : Hml (chainBoundary PTtop) n) (m : ℤ), m ≠ 0 → m • x = 0 → x = 0) :
    (∀ (y : Hml (chainBoundary Qtop) n) (m : ℤ), m ≠ 0 → m • y = 0 → y = 0) ↔
      ∀ y : Hml (chainBoundary Qtop) n, (2 : ℤ) • y = 0 → y = 0 := by
  constructor
  · exact fun h y hy => h y 2 (by norm_num) hy
  · exact fun h y m hm hy =>
      h y (two_smul_eq_zero_of_smul_eq_zero_of_ptTorsionFree n hPT hm hy)

/-! ## §1b. The `T⁴°` side, discharged: `H₃(T⁴°;ℤ)` is 2-torsion-free, and the crux is exactly
transfer-injectivity -/

/-- A 2-torsion-free abelian group has no `2`-power torsion either. -/
theorem eq_zero_of_two_pow_smul_eq_zero {M : Type*} [AddCommGroup M]
    (h2 : ∀ x : M, (2 : ℤ) • x = 0 → x = 0) :
    ∀ (a : ℕ) (x : M), ((2 : ℤ) ^ a) • x = 0 → x = 0 := by
  intro a
  induction a with
  | zero => intro x hx; simpa using hx
  | succ a ih =>
    intro x hx
    rw [pow_succ, mul_smul] at hx
    exact h2 x (ih _ hx)

/-- **THE `thickA ≃ T⁴°` BRIDGE, as an explicit ℤ-linear isomorphism** in every positive degree:
`Hₙ₊₁(T⁴°;ℤ) ≅ Hₙ₊₁(thickA;ℤ)`, induced by the inclusion. Packaging
`KummerPuncturedMV.puncIncl_mapInt_bijective` this way makes every banked `thickA` homology fact
directly transportable to the carrier the free-quotient machinery runs on — the `punctureH3_*`
result below is the first consumer. -/
def punctureThickHEquiv (n : ℕ) :=
  LinearEquiv.ofBijective (Homology.mapInt SKEFTHawking.KummerPuncturedMV.puncInclC (n + 1))
    (SKEFTHawking.KummerPuncturedMV.puncIncl_mapInt_bijective n)

/-- **`H₃(T⁴°;ℤ)` IS 2-TORSION-FREE — UNCONDITIONALLY.**

The `thickA → T⁴°` carrier gap is *not* open: `KummerPuncturedMV.puncIncl_mapInt_bijective` proves
the inclusion `T⁴° ↪ thickA` induces a **bijection** on `Hₙ₊₁(–;ℤ)` in every positive degree — it is
built from the glued radial `puncFlow` deformation retraction (`puncRetrC`, `thickHtpyC`), not
assumed. Transporting the unconditional `KummerPunctureH3Mod2.thickA_H3_twoTorsionFree` across it
lands the statement on the carrier the free-quotient machinery actually runs on.

(The *sets* `thickA = (⋃ halfBall c)ᶜ` and `puncturedTorus = excisedBallsᶜ` really are distinct;
what is in tree — and used here — is that the inclusion between them is a homotopy equivalence.) -/
theorem punctureH3_twoTorsionFree (x : Homology PTtop 3) (hx : (2 : ℤ) • x = 0) : x = 0 := by
  have hinj : Function.Injective
      (Homology.mapInt SKEFTHawking.KummerPuncturedMV.puncInclC 3) :=
    (SKEFTHawking.KummerPuncturedMV.puncIncl_mapInt_bijective 2).1
  refine hinj ?_
  rw [map_zero]
  refine SKEFTHawking.KummerPunctureH3Mod2.thickA_H3_twoTorsionFree _ ?_
  rw [← map_zsmul, hx, map_zero]

/-- **`H₃(Q;ℤ)[2] = ker (t : H₃(Q;ℤ) → H₃(T⁴°;ℤ))`, exactly and unconditionally.** `⊆` is §1b's
`T⁴°`-side 2-torsion-freeness; `⊇` is §1's `p̄ ∘ t = 2`. So the whole 2-torsion question about the
free quotient's degree-3 homology is *the injectivity of the transfer* — a single banked map — and
not an unstructured unknown. -/
theorem transferH_three_eq_zero_iff (y : Hml (chainBoundary Qtop) 3) :
    transferH 3 y = 0 ↔ (2 : ℤ) • y = 0 := by
  constructor
  · exact two_smul_eq_zero_of_transferH_eq_zero 3
  · intro hy
    refine punctureH3_twoTorsionFree _ ?_
    have h0 : transferH 3 ((2 : ℤ) • y) = 0 := by rw [hy, map_zero]
    exact (map_zsmul (transferH 3) 2 y).symm.trans h0

/-- **THE CRUX, RENAMED TO A BANKED MAP.** `H₃(Q;ℤ)` is 2-torsion-free **iff** the transfer
`t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)` is injective. Unconditional. -/
theorem twoTorsionFree_iff_transferH_three_injective :
    (∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0) ↔
      Function.Injective (transferH 3) := by
  constructor
  · intro h a b hab
    have hz : transferH 3 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (h _ ((transferH_three_eq_zero_iff _).mp hz))
  · intro h y hy
    exact h (((transferH_three_eq_zero_iff y).mpr hy).trans (map_zero (transferH 3)).symm)

/-- **The 2-primary torsion of `H₃(Q;ℤ)` has exponent at most 2 — unconditionally.** A class killed
by a power of 2 is killed by 2: its transfer is killed by that power of 2 upstairs, where §1b's
2-torsion-freeness kills it outright, and then §1 applies. This is a genuine unconditional partial
computation of `H₃(Q;ℤ)`: whatever 2-primary torsion it carries is an `𝔽₂`-vector space. -/
theorem two_smul_eq_zero_of_two_pow_smul_eq_zero (a : ℕ) {y : Hml (chainBoundary Qtop) 3}
    (h : ((2 : ℤ) ^ a) • y = 0) : (2 : ℤ) • y = 0 := by
  refine two_smul_eq_zero_of_transferH_eq_zero 3 ?_
  refine eq_zero_of_two_pow_smul_eq_zero punctureH3_twoTorsionFree a _ ?_
  have h0 : transferH 3 (((2 : ℤ) ^ a) • y) = 0 := by rw [h, map_zero]
  exact (map_zsmul (transferH 3) ((2 : ℤ) ^ a) y).symm.trans h0

/-! ## §2. The descent defect is an `𝔽₂`-vector space -/

/-- **`2 · im δ³ = 0`.** Every doubled `Q`-class lifts (`two_smul_mem_range_projH`) and the
connecting map kills lifted classes (SES-III exactness at `Hₙ₊₁(Q;ℤ)`). -/
theorem two_smul_deltaIII_eq_zero (n : ℕ) (z : Hml (chainBoundary Qtop) (n + 1)) :
    (2 : ℤ) • deltaIII n z = 0 := by
  obtain ⟨x, hx⟩ := two_smul_mem_range_projH (n + 1) z
  have h0 : deltaIII n (projH (n + 1) x) = 0 := (exact_projH_deltaIII n).apply_apply_eq_zero x
  have h1 : deltaIII n ((2 : ℤ) • z) = 0 := by rw [← hx]; exact h0
  rwa [map_zsmul] at h1

/-- **`ker (ι_B : Hₙ(B) → Hₙ(T⁴°))` is killed by 2**, in every degree — a structural fact about the
Smith "twisted" complex `B = ker p_# = im (1 − τ_#)` that holds with no geometric input beyond the
freeness of the action. Exactness at `Hₙ(B)` identifies that kernel with `im δ³`, which §2's first
lemma shows has exponent 2. -/
theorem two_smul_eq_zero_of_inclBH_eq_zero (n : ℕ) {b : Hml dB n} (h : inclBH n b = 0) :
    (2 : ℤ) • b = 0 := by
  obtain ⟨z, rfl⟩ := (exact_deltaIII_inclBH n b).mp h
  exact two_smul_deltaIII_eq_zero n z

/-- `im p_* = ker δ³` in degree 3 (SES-III exactness at `H₃(Q;ℤ)`). -/
theorem range_projH_three_eq_ker_deltaIII_two :
    LinearMap.range (projH 3) = LinearMap.ker (deltaIII 2) :=
  ((exact_projH_deltaIII 2).linearMap_ker_eq).symm

/-- `im δ³ = ker ι_B` in degree 2 (SES-III exactness at `H₂(B)`). -/
theorem range_deltaIII_two_eq_ker_inclBH_two :
    LinearMap.range (deltaIII 2) = LinearMap.ker (inclBH 2) :=
  ((exact_deltaIII_inclBH 2).linearMap_ker_eq).symm

/-- **THE DESCENT DEFECT, COMPUTED.** The obstruction to `H₃(Q;ℤ)` being generated by classes
lifted from the punctured torus is *exactly* the kernel of the banked map
`ι_B : H₂(B;ℤ) → H₂(T⁴°;ℤ)`:

    H₃(Q;ℤ) / im (p_* : H₃(T⁴°;ℤ) → H₃(Q;ℤ))  ≅  ker (ι_B : H₂(B;ℤ) → H₂(T⁴°;ℤ)),

and by `two_smul_eq_zero_of_inclBH_eq_zero` that group is an `𝔽₂`-vector space. This is the precise
form of "the degree-1/2 Smith walk does not lift": the walk's conclusion `projH 3` surjective is the
statement that this defect vanishes, and the defect is a concrete, named, still-uncomputed group —
not a gap in the bookkeeping. -/
def descentDefectEquiv :
    (Hml (chainBoundary Qtop) 3 ⧸ LinearMap.range (projH 3)) ≃ₗ[ℤ]
      LinearMap.ker (inclBH 2) :=
  (Submodule.quotEquivOfEq _ _ range_projH_three_eq_ker_deltaIII_two).trans
    ((deltaIII 2).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ range_deltaIII_two_eq_ker_inclBH_two))

/-- `ker p_* = im ι_B` in degree 3 (SES-III exactness at `H₃(T⁴°;ℤ)`, from the parallel `H₁` lane's
`KummerK3H1SeamLattice.exact_inclBH_projH`, which holds in **every** degree). -/
theorem range_inclBH_three_eq_ker_projH_three :
    LinearMap.range (inclBH 3) = LinearMap.ker (projH 3) :=
  ((exact_inclBH_projH 3).linearMap_ker_eq).symm

/-- **THE LIFTED SUBGROUP, COMPUTED.** The subgroup of `H₃(Q;ℤ)` reached from the punctured torus
is an explicit quotient of `H₃(T⁴°;ℤ)`:

    im (p_* : H₃(T⁴°;ℤ) → H₃(Q;ℤ))  ≅  H₃(T⁴°;ℤ) / im (ι_B : H₃(B;ℤ) → H₃(T⁴°;ℤ)).

Paired with `descentDefectEquiv` this is a **two-step presentation of `H₃(Q;ℤ)`**: an extension of
the `𝔽₂`-vector space `ker (ι_B : H₂(B;ℤ) → H₂(T⁴°;ℤ))` by `H₃(T⁴°;ℤ)/im (ι_B)`. Both outer terms
are `T⁴°`/Smith-side objects; no `Q`-side unknown survives except through them. -/
def liftedSubmoduleEquiv :
    (Hml (chainBoundary PTtop) 3 ⧸ LinearMap.range (inclBH 3)) ≃ₗ[ℤ]
      LinearMap.range (projH 3) :=
  (Submodule.quotEquivOfEq _ _ range_inclBH_three_eq_ker_projH_three).trans
    (projH 3).quotKerEquivRange

/-- Every class of the descent defect is killed by 2 (transport of
`two_smul_eq_zero_of_inclBH_eq_zero` along `descentDefectEquiv`). -/
theorem two_smul_descentDefect_eq_zero (c : Hml (chainBoundary Qtop) 3 ⧸ LinearMap.range (projH 3)) :
    (2 : ℤ) • c = 0 := by
  have h : (2 : ℤ) • descentDefectEquiv c = 0 :=
    Subtype.ext (two_smul_eq_zero_of_inclBH_eq_zero 2 (descentDefectEquiv c).2)
  have := congrArg descentDefectEquiv.symm h
  rwa [map_zsmul, descentDefectEquiv.symm_apply_apply, map_zero] at this

/-! ## §3. The sharp criterion for the `orientInput` residual -/

/-- **THE CRITERION.** If `H₃(Q;ℤ)` has no 2-torsion and every class lifted from the punctured
torus is an **even** multiple of a seam class, then the sixteen boundary-`ℝP³` classes generate
`H₃(Q;ℤ)` outright.

The proof is three banked lines: `2 · u` lifts (`two_smul_mem_range_mapInt_qmkC`), the lift is
`2 · qSeamCoord3 v` by hypothesis, so `2 · (u − qSeamCoord3 v) = 0` and 2-torsion-freeness closes it.
The "even" shape is the geometrically correct one: `p` restricted to a boundary `S³` of `T⁴°` is the
double cover of the corresponding `ℝP³`, so lifted top classes are *twice* seam classes. -/
theorem qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent
    (h2 : ∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Function.Surjective qSeamCoord3 := by
  intro u
  obtain ⟨x, hx⟩ := two_smul_mem_range_mapInt_qmkC 2 u
  obtain ⟨v, hv⟩ := hd x
  refine ⟨v, ?_⟩
  have key : (2 : ℤ) • u = (2 : ℤ) • qSeamCoord3 v := hx.symm.trans hv
  have hz : (2 : ℤ) • (u - qSeamCoord3 v) = 0 := by rw [smul_sub, key, sub_self]
  exact (sub_eq_zero.mp (h2 _ hz)).symm

/-- **THE CRITERION, with the crux named as a banked map.** Same statement as
`qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent`, with the 2-torsion hypothesis replaced by
its unconditional equivalent (§1b): *injectivity of the transfer* `t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)`. Both
remaining inputs are now properties of concrete banked maps, not of an unknown group. -/
theorem qSeamCoord3_surjective_of_transferH_injective_of_evenDescent
    (ht : Function.Injective (transferH 3))
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Function.Surjective qSeamCoord3 :=
  qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent
    (twoTorsionFree_iff_transferH_three_injective.mpr ht) hd

/-- **The even form implies the banked weak form.** `im p_* ⊆ 2 · im qSeamCoord3 ⊆ im qSeamCoord3`,
so `qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent` strictly refines — never bypasses —
`KummerK3H3SeamWindow.twoTorsionFree_iff_qSeamCoord3_surjective_of_descent`. -/
theorem descent_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Set.range (Homology.mapInt qmkC 3) ⊆ Set.range qSeamCoord3 := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨v, hv⟩ := hd x
  exact ⟨(2 : ℤ) • v, by rw [map_zsmul]; exact hv.symm⟩

/-- **Even descent alone already bounds the residual**: without any torsion hypothesis it makes
`H₃(K3;ℤ) = coker qSeamCoord3` an `𝔽₂`-vector space, so the residual's *only* remaining content is
whether that space is zero. -/
theorem two_smul_mem_range_qSeamCoord3_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v)
    (u : Homology (TopCat.of FreeQuotient) 3) : (2 : ℤ) • u ∈ Set.range qSeamCoord3 :=
  two_smul_mem_range_qSeamCoord3_of_descent (descent_of_evenDescent hd) u

/-- Under even descent the weak (2-saturation) and strong (surjectivity) forms of the residual
coincide — the banked collapse, now available from the geometrically correct hypothesis. -/
theorem twoTorsionFree_iff_qSeamCoord3_surjective_of_evenDescent
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    KummerK3E1Package.KummerK3H3TwoTorsionFree ↔ Function.Surjective qSeamCoord3 :=
  twoTorsionFree_iff_qSeamCoord3_surjective_of_descent (descent_of_evenDescent hd)

/-- `H₃(K3;ℤ) = 0` from the criterion, via
`KummerK3H3SeamWindow.qSeamCoord3_surjective_iff_h3K3_eq_zero`. -/
theorem h3K3_eq_zero_of_twoTorsionFree_of_evenDescent
    (h2 : ∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v)
    (x : Homology KummerK3top 3) : x = 0 :=
  qSeamCoord3_surjective_iff_h3K3_eq_zero.mp
    (qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent h2 hd) x

open scoped SKEFTHawking.KummerK3E1Package in
/-- **The orientation atom of the welded `K3` from the two `Q`-side facts.** Chains the criterion
into `KummerK3E1Package.nonempty_intOrientation_kummerK3` through
`KummerK3H3SeamWindow.nonempty_intOrientation_of_qSeamCoord3_surjective`. -/
theorem nonempty_intOrientation_of_twoTorsionFree_of_evenDescent
    (h2 : ∀ y : Homology (TopCat.of FreeQuotient) 3, (2 : ℤ) • y = 0 → y = 0)
    (hd : ∀ x : Homology PTtop 3, ∃ v, Homology.mapInt qmkC 3 x = (2 : ℤ) • qSeamCoord3 v) :
    Nonempty (SingularHomologyInt.IntOrientation SKEFTHawking.KummerWeld.KummerK3) :=
  nonempty_intOrientation_of_qSeamCoord3_surjective
    (qSeamCoord3_surjective_of_twoTorsionFree_of_evenDescent h2 hd)

/-! ## §4. Vacuity attack on the 2-torsion-freeness hypothesis -/

/-- **The zero-geometric-input attack, run and failed.** The hypothesis "`Hₙ(Q;ℤ)` has no
2-torsion" is not a tautology of the covering algebra: in degree 1 it *forces the covering
projection to be zero on homology*, because `im (p_* : H₁(T⁴°;ℤ) → H₁(Q;ℤ))` consists entirely of
2-torsion (`KummerK3H1SeamLattice.two_zsmul_mapInt_qmkC`). A hypothesis whose degree-1 instance
collapses `p_*` is carrying genuine geometric content in degree 3, where it is assumed. -/
theorem twoTorsionFree_one_forces_trivial_descent
    (h : ∀ y : Homology Qtop 1, (2 : ℤ) • y = 0 → y = 0) (y : Homology PTtop 1) :
    Homology.mapInt qmkC 1 y = 0 :=
  h _ (two_zsmul_mapInt_qmkC y)

end

end SKEFTHawking.KummerQuotientH3Descent
