/-
# Phase 5q.H (N1) — the KT §5 exactness keystone `hexact`, DECOMPOSED to the single completeness node

The σ-route door `SpinSigmaRouteDoor.omega4PinPlusGMTied_equiv_zmod16_via_sigma_route` consumes the
KT §5 exact-sequence exactness

    `hexact : ker(reduce16to8 ∘ abkGMTied16) = (forgetGen F g).range`

(the middle exactness of `0 → ℤ/2 → Ω₄^{Pin⁺} → ℤ/8 → 0`: the kernel of the mod-8 characteristic
map `[∩w₁²]` equals the image of the forgetful `Ω₄^{Spin} → Ω₄^{Pin⁺}`) as its single deepest open
input — the N1 completeness key, `frontier_impact` = the whole phase.

This module DECOMPOSES that keystone **at the door's abstraction level** — for the abstract σ-route
forgetful map `forgetGen F g`, not just the concrete in-tree `g8` map that `PinPlusGMWitness` already
handles (`spin_range_le_ker_reduce` / `spin_range_ge_of_grade0_inj`). The decomposition closes the
exactness **from below** (per the 2026-07-06/06b re-anchor, `SETTLED_FORKS.md`
§`5qH-injectivity-routes`): the `card ≤ 16 = 2×8` assembles from the `ℤ/8` (done) + the Spin image
`≤ ℤ/2` (Lemma 5.3 + `Ω₄^{Spin}≅ℤ`, the σ-route freezes), and the ONLY irreducible residual is the
middle exactness itself, which is proven here to be **apex-equivalent to `hbound`** — the single
completeness node `∀ x, abkGMTied16 x = 0 → x = 0` (grade-0 tied-Pin⁺ class bounds), already the common
apex of all injectivity routes (`5qH-injectivity-routes-all-equal-one-completeness-prop`, kernel-settled).

Results (all kernel-pure; `hbound` remains the disclosed, open geometric residual — NO new axiom):

* `forgetGen_range_le_ker_reduce` — the ⊆ (composite-zero, EASY) half: the forgetful Spin image lands
  in `ker[∩w₁²]`, from the single placement fact `habk8 : abkGMTied16 (F [g]) = 8` (the Kummer image is
  the order-2 grade-8 Pin⁺ class). This is the algebraically-forced inclusion `im(Ω₄^{Spin}) ⊆ ker[∩w₁²]`.
* `ker_reduce_le_forgetGen_range_of_grade0` — the ⊇ (completeness, HARD) half: from `hbound` + `habk8`,
  a mod-8-grade-`0` class has full grade `0` or `8`; grade `0 ⟹ x = 0 = forgetGen F g 0`; grade `8 ⟹
  x − F[g]` grade `0 ⟹ x = F[g] = forgetGen F g 1`. This is the σ-route analog of the g8-map
  `spin_range_ge_of_grade0_inj`.
* `forgetGen_hexact_of_grade0` — the FULL `hexact` for `forgetGen F g`, assembled `le_antisymm` from the
  two halves. So the door's keystone binder collapses to `hbound` + `habk8`.
* `abk_forgetGen_gen_eq_eight` — `habk8` DERIVED from the full door's own binders (`hg`, `hker`, `h2g`)
  plus `hbound`: `F[g] ≠ 0` (Lemma 5.3 forward, `¬ 32 ∣ −16`), `2•(abk F[g]) = 0` (from `h2g`), and
  `abk` injective (`hbound`) force `abk F[g] = 8`. So `habk8` is NOT an independent residual.
* `omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_grade0` /
  `omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_grade0_full` — the σ-route capstone with the door's
  `hexact` binder **entirely replaced by `hbound`**, every other binder identical to the door's. This is
  the decisive artifact: `hexact ≡ hbound` (given the door's already-disclosed inputs), so the KT §5
  exactness is provably NOT an independent geometric input — it is the ONE completeness node, in the
  σ-route vocabulary.

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

universe u

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The ⊆ half of the door's `hexact` — the composite-zero (EASY) direction, for the abstract
forgetful `forgetGen F g`.** Given the single placement fact `habk8 : abkGMTied16 (F [g]) = 8` (the
Spin generator's Pin⁺ image is the order-2 class of mod-8-vanishing grade `8`), the forgetful Spin
image sits inside `ker(reduce16to8 ∘ abkGMTied16)`: every `forgetGen F g n = F (n•[g])` has grade
`8n`, and `reduce16to8 8 = 0` in `ZMod 8`. This is the algebraically-forced `im(Ω₄^{Spin}) ⊆ ker[∩w₁²]`
at the door's abstraction level (cf. the g8-map form `PinPlusGMWitness.spin_range_le_ker_reduce`). -/
theorem forgetGen_range_le_ker_reduce {ξ : TangentialData X k I}
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (g : StrMfd ξ)
    (habk8 : abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 8) :
    (forgetGen F g).range ≤
      (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker := by
  rintro _ ⟨n, rfl⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, forgetGen_apply, map_zsmul, habk8]
  rw [show (reduce16to8 (8 : ZMod 16) = 0) from by decide, zsmul_zero]

/-- **The ⊇ half of the door's `hexact` — the completeness (HARD) direction, from `hbound`.** Given the
single completeness node `hbound` (every grade-`0` tied-Pin⁺ class is `0`) and the placement fact
`habk8`, any class killed by `reduce16to8 ∘ abkGMTied16` (mod-8 GM grade `0`, so full grade `0` or `8`)
lies in `(forgetGen F g).range`: grade `0 ⟹ x = 0 = forgetGen F g 0` (`hbound`); grade `8 ⟹`
`abkGMTied16 (x − F[g]) = 0 ⟹ x = F[g] = forgetGen F g 1` (`hbound`). The σ-route analog of the g8-map
`PinPlusGMWitness.spin_range_ge_of_grade0_inj`. -/
theorem ker_reduce_le_forgetGen_range_of_grade0 {ξ : TangentialData X k I}
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (g : StrMfd ξ)
    (habk8 : abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 8)
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        abkGMTied16 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker ≤
      (forgetGen F g).range := by
  intro x hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe] at hx
  have hcase : ∀ y : ZMod 16, reduce16to8 y = 0 → y = 0 ∨ y = 8 := by decide
  rcases hcase _ hx with h0 | h8
  · exact ⟨0, by rw [forgetGen_apply, zero_zsmul, map_zero]; exact (hbound x h0).symm⟩
  · refine ⟨1, ?_⟩
    rw [forgetGen_apply, one_zsmul]
    have hd : abkGMTied16 (k := 0) (I := 𝓡 4) (x - F (DataBordismGrp.mk ξ g)) = 0 := by
      rw [map_sub, h8, habk8, sub_self]
    have hxg := hbound _ hd
    rwa [sub_eq_zero, eq_comm] at hxg

/-- **The door's keystone `hexact` for `forgetGen F g`, ASSEMBLED from the single completeness node.**
`le_antisymm` of the two halves: the full KT §5 exactness `ker[∩w₁²] = im(Ω₄^{Spin})` holds given
`hbound` (grade-`0` bounds) + `habk8` (the Kummer image placement). So the door's `hexact` binder
collapses to these two — with `habk8` itself derivable from the door's other binders
(`abk_forgetGen_gen_eq_eight`), leaving `hbound` as the SOLE irreducible residual. -/
theorem forgetGen_hexact_of_grade0 {ξ : TangentialData X k I}
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (g : StrMfd ξ)
    (habk8 : abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 8)
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        abkGMTied16 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
      = (forgetGen F g).range :=
  le_antisymm (ker_reduce_le_forgetGen_range_of_grade0 F g habk8 hbound)
    (forgetGen_range_le_ker_reduce F g habk8)

/-- **The placement fact `habk8` DERIVED from the full door's own binders + `hbound`.** `F [g] ≠ 0`
(Lemma 5.3 forward `hker` at `[g]`: `¬ 32 ∣ σ([g]) = −16`); `2•(abkGMTied16 F[g]) = 0` (from
`h2g : F (2•[g]) = 0`); and `abkGMTied16` injective (`hbound`) force `abkGMTied16 F[g] = 8` (the unique
nonzero 2-torsion element of `ZMod 16`). So `habk8` is NOT an independent input — the full-door
decomposition below carries `hbound` as its ONLY geometric residual beyond the σ-route freezes. -/
theorem abk_forgetGen_gen_eq_eight {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hker : ∀ x, F x = 0 ↔ (32 : ℤ) ∣ R.sig x)
    (h2g : F ((2 : ℤ) • DataBordismGrp.mk ξ g) = 0)
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        abkGMTied16 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 8 := by
  have hspec := hker (DataBordismGrp.mk ξ g)
  rw [hg] at hspec
  have hFne : F (DataBordismGrp.mk ξ g) ≠ 0 := fun h => absurd (hspec.mp h) (by decide)
  have habkne : abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) ≠ 0 :=
    fun h => hFne (hbound _ h)
  have h2t : (2 : ℤ) • abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 0 := by
    have h := congrArg (abkGMTied16 (k := 0) (I := 𝓡 4)) h2g
    rwa [map_zsmul, map_zsmul, map_zero] at h
  rw [zsmul_eq_mul] at h2t
  have hcase : ∀ y : ZMod 16, ((2 : ℤ) : ZMod 16) * y = 0 → y = 0 ∨ y = 8 := by decide
  rcases hcase _ h2t with h | h
  · exact absurd h habkne
  · exact h

/-- **The σ-route capstone with the keystone `hexact` REPLACED by the single completeness node `hbound`.**
The D5 door `omega4PinPlusGMTied_equiv_zmod16_via_sigma_route` (its `(s, hs)` from the σ-route), with
`hexact` supplied by `forgetGen_hexact_of_grade0` from `hbound` + `habk8`. The disclosed surface shrinks
from "the monolithic KT §5 exactness" to "grade-`0` injectivity + the Kummer-image placement `habk8`". -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_grade0 {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hker : ∀ x, F x = 0 ↔ (32 : ℤ) ∣ R.sig x)
    (habk8 : abkGMTied16 (k := 0) (I := 𝓡 4) (F (DataBordismGrp.mk ξ g)) = 8)
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        abkGMTied16 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  SKEFTHawking.SpinSigmaRouteDoor.omega4PinPlusGMTied_equiv_zmod16_via_sigma_route
    R g hg F hker (forgetGen_hexact_of_grade0 F g habk8 hbound)

/-- **The FULLY-decomposed σ-route capstone — `hexact` GONE, `hbound` the SOLE geometric residual.**
Identical binders to the door's `omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full` EXCEPT the
`hexact` keystone is dropped and replaced by the single completeness node `hbound`. `hker` is rebuilt
from `hfwd` + `h2g` (`hker_of_forward_and_two_gen`), `habk8` is derived (`abk_forgetGen_gen_eq_eight`),
and `hexact` is assembled (`forgetGen_hexact_of_grade0`). This is the decisive decomposition of the
phase's deepest node: **the KT §5 exactness `hexact` is apex-equivalent to `hbound`** — the ONE
completeness Prop (`grade-0 ⟹ 0` = the relative fundamental class `[W,∂W]` + surgery, per
`SETTLED_FORKS.md` §`5qH-injectivity-routes`), now shown so in the door's own σ-route vocabulary. -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_grade0_full {ξ : TangentialData X k I}
    (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hfwd : ∀ x, F x = 0 → (32 : ℤ) ∣ R.sig x)
    (h2g : F ((2 : ℤ) • DataBordismGrp.mk ξ g) = 0)
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        abkGMTied16 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  have hker := hker_of_forward_and_two_gen R hA hB g hg hdvd F hfwd h2g
  omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_grade0 R g hg F hker
    (abk_forgetGen_gen_eq_eight R g hg F hker h2g hbound) hbound

end SKEFTHawking.SpinSigmaRoute
