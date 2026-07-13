/-
# Phase 5q.H (N1a → N1c → D5) — the σ-route door's algebra/construction inputs, discharged

Companion to `SpinSigmaRouteDoor.lean`. The fully-decomposed door
`omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full` consumes eight inputs
`{hA, hB, g, hg, hdvd, F, hfwd, h2g, hexact}`. Three of them are named in the door docstring as
"largely in-tree algebra/construction":

* `hg` — the K3 generator witness `R.sig [g] = −16` (the `Ω₄^{Spin} ≅ ℤ` side);
* `hfwd` — KT Lemma 5.3 forward `F x = 0 → 32 ∣ σ(x)` (Pin⁺-bounds ⟹ `32 ∣ σ`, the double-cover `÷32`);
* `h2g` — `2·[g]` bounds Pin⁺, `F (2•[g]) = 0`.

**What this module proves (kernel-pure).** `hfwd` and `h2g` are BOTH discharged from the σ-route
completeness (`hA, hB, hg, hdvd`, giving `generates`: every class is `n•[g]`) plus a **single
geometric atom** — the additive order of the forgetful image of the generator:

    hord : addOrderOf (F [g]) = 2      -- KT Lemma 5.3: image(Ω₄^{Spin} → Ω₄^{Pin⁺}) = ℤ/2

* `image_zsmul_eq_zero_iff` — from `hord`, `n • F[g] = 0 ⟺ 2 ∣ n` (mirrors `g8_zmultiples_ker`);
* `sigma_route_hfwd` — `hfwd` DISCHARGED (`F x = 0` ⟹ `2 ∣ n` ⟹ `32 ∣ −16n = σ(x)`);
* `sigma_route_h2g` — `h2g` DISCHARGED (`F (2•[g]) = 2•F[g] = 0`, image 2-torsion from `hord`);
* `..._via_sigma_route_atom` — the σ-route door from the **single** atom `hord` (+ `hexact`);
* `..._via_sigma_route_g8` — the atom specialized to the concrete in-tree Kummer image
  `F [g] = g8` (`PinPlusGMWitness.g8`, `addOrderOf_g8 = 2`), so `hfwd`/`h2g` need NO new input;
* `forgetGen_eq_zmultiples_g8` — UNIFICATION: under `F [g] = g8` the σ-route `s`-map `forgetGen F g`
  is literally the in-tree KT `s`-map `zmultiplesHom g8`, so the σ-route `hexact` is the SAME object
  as the in-tree KT `hexact` (`PinPlusGMWitness.hexact_of_ker_le_spin_range`).

**Honest residual.** `hg` (the `σ = −16` K3 generator) is NOT dischargeable kernel-pure for an
abstract presentation `R`: an abstract `SpinSigmaPresentation` carries no `σ = −16` class (the
in-tree `trivialPresentation` has `sig = 0`; the in-tree `RokhlinBridge.rokhlin_sharp` σ = −16 lives
on the unrelated `SpinManifold4.signature`, not `R.sig` on `DataBordismGrp ξ`). Per the DR route
(`Omega4Spin_Z_formalization_route_20260706.md`: "K3, abstract — no hand-built K3 needed") `g`/`hg`
are consumed as the disclosed generator datum. Building a synthetic `σ = −16` presentation (or a
synthetic `F [g] = g8`) is the settled-dead `synthetic-smith-map-to-tied-carrier` /
`synthetic-grade-ker-bot-nogo` framing and is deliberately NOT attempted. The residual geometric
atom for `hfwd`/`h2g` is exactly `hord` (`addOrderOf (F [g]) = 2` = KT Lemma 5.3 image content),
which discharges the moment a genuine forgetful `F` with `F [g] = g8` is instantiated.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaRoute
import SKEFTHawking.SpinSigmaRouteDoor
import SKEFTHawking.PinPlusGMWitness

namespace SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMTiedData SKEFTHawking.GuillouMarin
open SKEFTHawking.PinPlusGMWitness

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

universe u

variable {G : Type*} [AddCommGroup G]

/-! ### The order-2 atom: the forgetful image of the generator kills exactly the even multiples -/

/-- **From the order-2 atom, `n • F[g] = 0 ⟺ 2 ∣ n`** (mirrors `PinPlusGMWitness.g8_zmultiples_ker`,
here for an abstract forgetful image of additive order `2`). This is the arithmetic engine of both
`hfwd` and `h2g`: a nonzero 2-torsion image detects exactly the even multiples. -/
theorem image_zsmul_eq_zero_iff {ξ : TangentialData X k I} (F : DataBordismGrp ξ →+ G)
    (g : StrMfd ξ) (hord : addOrderOf (F (DataBordismGrp.mk ξ g)) = 2) (n : ℤ) :
    n • F (DataBordismGrp.mk ξ g) = 0 ↔ (2 : ℤ) ∣ n := by
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hord]
  norm_num

/-! ### `hfwd` and `h2g` discharged from the atom + the σ-route -/

/-- **`hfwd` DISCHARGED (KT Lemma 5.3 forward).** Given the σ-route completeness (`hA, hB, hg, hdvd`,
so every class is `n•[g]` via `generates`) and the order-2 atom `hord`, `F x = 0` forces `2 ∣ n`,
hence `32 ∣ σ(x) = −16n`. This is `hfwd : ∀ x, F x = 0 → 32 ∣ R.sig x` in the door's shape. -/
theorem sigma_route_hfwd {ξ : TangentialData X k I} (R : SpinSigmaPresentation ξ)
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ G) (hord : addOrderOf (F (DataBordismGrp.mk ξ g)) = 2)
    (x : DataBordismGrp ξ) (hx : F x = 0) : (32 : ℤ) ∣ R.sig x := by
  obtain ⟨n, rfl⟩ := R.generates hA hB g hg hdvd x
  rw [map_zsmul] at hx
  have h2n : (2 : ℤ) ∣ n := (image_zsmul_eq_zero_iff F g hord n).mp hx
  rw [map_zsmul, hg, smul_eq_mul]
  obtain ⟨m, rfl⟩ := h2n
  exact ⟨-m, by ring⟩

/-- **`h2g` DISCHARGED (`2·K3` bounds Pin⁺).** `F (2•[g]) = 2•F[g]`, and the order-2 atom `hord`
gives `2•F[g] = 0`. So `h2g : F (2•[g]) = 0` in the door's shape, from the same single atom. -/
theorem sigma_route_h2g {ξ : TangentialData X k I} (F : DataBordismGrp ξ →+ G)
    (g : StrMfd ξ) (hord : addOrderOf (F (DataBordismGrp.mk ξ g)) = 2) :
    F ((2 : ℤ) • DataBordismGrp.mk ξ g) = 0 := by
  rw [map_zsmul]
  exact (image_zsmul_eq_zero_iff F g hord 2).mpr (dvd_refl 2)

/-! ### The σ-route door from the SINGLE geometric atom -/

/-- **The σ-route door assembled from the single atom `hord`.** The fully-decomposed door
`omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full` with its two arithmetic/construction inputs
`hfwd`, `h2g` discharged from `hord := addOrderOf (F [g]) = 2` (KT Lemma 5.3: the image of
`Ω₄^{Spin} → Ω₄^{Pin⁺}` is `ℤ/2`). Remaining open inputs: `hg` (the `σ = −16` K3 generator), `hord`
(the order-2 image atom), and `hexact` (the deep KT §5 exactness). -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_atom {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hord : addOrderOf (F (DataBordismGrp.mk ξ g)) = 2)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
        = (forgetGen F g).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  SKEFTHawking.SpinSigmaRouteDoor.omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full
    R hA hB g hg hdvd F
    (fun x hx => sigma_route_hfwd R hA hB g hg hdvd F hord x hx)
    (sigma_route_h2g F g hord) hexact

/-! ### The atom specialized to the concrete in-tree Kummer image `F [g] = g8` -/

/-- **From `F [g] = g8`, the order-2 atom is DISCHARGED** by the in-tree `addOrderOf_g8 = 2`. So the
sole geometric content of both `hfwd` and `h2g` collapses to "the forgetful map sends the `σ = −16`
generator to the grade-`8` Kummer class `g8`" — the concrete shape of KT Lemma 5.3's image `ℤ/2`. -/
theorem addOrderOf_image_eq_two_of_eq_g8 {ξ : TangentialData X k I}
    (F : DataBordismGrp ξ →+ DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (g : StrMfd ξ) (himg : F (DataBordismGrp.mk ξ g) = g8) :
    addOrderOf (F (DataBordismGrp.mk ξ g)) = 2 := by
  rw [himg]; exact addOrderOf_g8

/-- **UNIFICATION — the σ-route `s`-map IS the in-tree KT `s`-map under `F [g] = g8`.** Both
`forgetGen F g` and `zmultiplesHom g8` are homs `ℤ →+ carrier` determined by their value at `1`;
under `F [g] = g8` that value is `g8` on both sides, so they are equal. Hence the σ-route `hexact`
(`ker = (forgetGen F g).range`) is literally the in-tree KT `hexact`
(`ker = (zmultiplesHom g8).range`, `PinPlusGMWitness.hexact_of_ker_le_spin_range`). -/
theorem forgetGen_eq_zmultiples_g8 {ξ : TangentialData X k I}
    (F : DataBordismGrp ξ →+ DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (g : StrMfd ξ) (himg : F (DataBordismGrp.mk ξ g) = g8) :
    forgetGen F g
      = zmultiplesHom (DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4))) g8 := by
  apply AddMonoidHom.ext_int
  simp only [forgetGen_apply, one_zsmul, himg, zmultiplesHom_apply]

/-- **The σ-route door from the concrete Kummer image `F [g] = g8`** — `hfwd`/`h2g` need NO new
input beyond `F [g] = g8` (the geometric fact "K3 forgets to the grade-`8` Kummer class"). Remaining
open inputs: `hg` (σ = −16 generator) and `hexact` (deep KT §5 exactness). -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_g8 {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (himg : F (DataBordismGrp.mk ξ g) = g8)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
        = (forgetGen F g).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_atom R hA hB g hg hdvd F
    (addOrderOf_image_eq_two_of_eq_g8 F g himg) hexact

end SKEFTHawking.SpinSigmaRoute
