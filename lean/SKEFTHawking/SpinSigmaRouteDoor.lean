/-
# Phase 5q.H (N1a → N1c → D5) — the σ-route door into the tied ℤ/16 capstone

The composition glue wiring the N1a σ-route layer (`SpinSigmaRoute.lean`) into the E4 assembly's
D5 door (`PinPlusGMWitness.omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53`): given

* a σ-presentation `R` of a (spin) tangential carrier `ξ` with a `σ = −16` generator witness `g`
  (K3, abstract — the `Ω₄^{Spin} ≅ ℤ` side, route-complete modulo the two `SpinSigmaRoute`
  freezes),
* the forgetful map `F : Ω^ξ →+ Ω₄^{Pin⁺,GM-tied}` (N1b's shape — the geometric Smith/forgetful
  transport into the tied carrier, E3),
* **KT Lemma 5.3 frozen at the class level** (`hker`: `F x = 0 ⟺ 32 ∣ σ(x)` — Kirby–Taylor §5,
  Lemma 5.3: a spin 4-manifold bounds Pin⁺ iff `32 ∣ σ`; its `⟸` direction consumes the full
  `Ω₄^{Spin} ≅ ℤ`, per the no-Rokhlin-only-shortcut caveat 2026-07-06b),
* the KT §5 exactness `hexact` (`ker(reduce ∘ abk) = range s` — the N1 completeness key),

the genuine tied carrier is `≃+ ZMod 16`. Everything else (surjectivity, the ℝP⁴ generator, the
order-16 algebra, `spin_image_card_two`) is already discharged in-tree; this module adds NO new
open input — it re-expresses the D5 door's `(s, hs)` pair through the σ-route vocabulary, so that
when E1/E2/E3 discharge the freezes the capstone assembles by instantiation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaRoute
import SKEFTHawking.PinPlusGMWitness

namespace SKEFTHawking.SpinSigmaRouteDoor

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMTiedData SKEFTHawking.GuillouMarin
open SKEFTHawking.SpinSigmaRoute

universe u

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The σ-route door — `Ω₄^{Pin⁺,GM-tied} ≅ ℤ/16` from the N1a vocabulary.** The D5 door
(`omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53`) with its `(s, hs)` pair assembled from the
σ-route: `s := forgetGen F g` (the forgetful map on generator multiples) and `hs` from the frozen
KT Lemma 5.3 kernel identity via `forgetGen_eq_zero_iff`. Remaining open inputs, both named:
`hker` (Lemma 5.3, geometric: "2·K3 bounds Pin⁺" + bordism-invariance) and `hexact` (KT §5
exactness — the N1 completeness key, apex-equivalent to `hbound`/`hthom` per the settled fork). -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_sigma_route {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hker : ∀ x, F x = 0 ↔ (32 : ℤ) ∣ R.sig x)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
        = (forgetGen F g).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  SKEFTHawking.PinPlusGMWitness.omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53
    (forgetGen F g) (forgetGen_eq_zero_iff R F g hg hker) hexact

end SKEFTHawking.SpinSigmaRouteDoor
