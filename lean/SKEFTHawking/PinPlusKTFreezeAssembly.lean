/-
# Phase 5q.H W-D — the σ-engine freeze assembly: Freeze A from the terminal atoms, Freeze B consumed

Re-triage + assembly of the two `SpinSigmaRoute` freezes (`hA = RealizesSphereProducts`,
`hB = SphereProductBounds`) against today's tree, threading the σ-engine headlines
(`SpinSigmaRoute.SpinSigmaPresentation.{sig_injective, generates, dataBordismGrp_equiv_int,
thirtytwo_dvd_sig_iff}` + the KT §5 `s`-map `hker_of_forward_and_two_gen`/`forgetGen_eq_zero_iff`)
through the **finest-grain Freeze-A geometric residual** and the **discharged Freeze B**. This is the
classical assembly the DR route names (`Lit-Search/Phase-5qH/
Omega4Spin_Z_formalization_route_20260706.md`):

    σ = 0 spin ⟹ form ≅ n·H          (lattice, IN-TREE unconditional: `exists_hyperbolic_congr`)
              ⟹ M realizes #ⁿ(S²×S²)  (handle-trade induction: the Freeze-A atoms)
              ⟹ M bounds               (Freeze B: each S²×S² = ∂(S²×D³))

wired to speak from the *terminal in-substrate atoms* instead of the two monolithic freeze Props.

## Per-atom strength audit (what the atoms honestly reach, and what they still lack)

* **Freeze A** decomposes (all reductions kernel-pure, in-tree today):
  `HandleTradeCobordism → HandleTradeSplit → HyperbolicPeel`  (+ `HyperbolicBase`)  `→
  RealizesSphereProducts`
  (`SphereProductRealization.realizesSphereProducts_of_peel_and_base`,
  `SphereProductRealizationAtoms.hyperbolicPeel_of_handleTradeSplit`,
  `HandleTradeSurgery.handleTradeSplit_of_cobordism` /
  `realizesSphereProducts_of_cobordism_and_base`). The **terminal residual** is
  `HandleTradeCobordism` — the ONE raw structured cobordism `IsDataBordant ξ p ((S²×S²) ⊔ p')`
  (Benedetti arXiv:1907.10297 Prop 20.16 / Lemma 20.17, attaching-circle standardization in a
  chart) — plus `HyperbolicBase` (rank-0 nullbordism, Thm 20.14; itself a *consequence* of the
  freeze via `hyperbolicBase_of_realizesSphereProducts`, so the NET new geometric ask is exactly the
  single handle-trade cobordism). **Both are shipped as `Prop`s, NOT inhabited constructions**: they
  LACK any actual construction of the residual manifold `p'` and the cobordism `W` — that needs a
  manifold-surgery foundation the disjoint-union substrate does not provide (flagged terminal).
  Everything else the handle-trade would classically certify (the residual's whole intersection form
  `≅ N'`, the block iteration, the `q = rank/2` count) is discharged kernel-pure by the lattice
  engine (`intCongr_of_evenUnimodular_sig_zero` = σ=0 uniqueness) + `AddCommGroup`/`Nat` algebra.

* **Freeze B** is **DISCHARGED, kernel-pure, NO hypothesis** for the concrete `S²×S²` presentation:
  `SphereDiskFreezeB.trivialSpherePresentation_freezeB` fires the §5 conditional
  (`SphereProductBounding.sphereProductBounds_of_package`) on the complete `SphereDiskSmoothData`
  (`SphereDiskFreezeB.sphereDiskSmoothData`, the re-associated collar atlas of `S²×D³` — the two
  Mathlib-absent atlas items of `SphereProductBounding` §4 discharged in `SphereDiskJ5`/
  `SphereDiskFreezeB`). The bounding is a genuine `C^k` project `Bordism` `S²×S² = ∂(S²×D³)`. So
  Freeze B LACKS NOTHING for the concrete presentation; for the genuine spin datum the only residual
  is the structure-extension (`strBor`), trivial on the concrete carrier (`Bor ≡ PUnit`). This
  module CONSUMES that discharge (§3); it does not re-derive it (no double-counting).

## What assembles vs what stays open
The whole σ-route (injective direction, `Ω^ξ ≃+ ℤ`, the `÷32` bridge, the KT §5 `s`-map) is
restated here from `{HandleTradeCobordism, HyperbolicBase, SphereProductBounds}` in place of
`{hA, hB}` — collapsing the engine's geometric hypothesis surface to its terminal grain (§1, §2).
Nothing is discharged: every headline stays conditional on the two open Freeze-A atoms + the
surjectivity binders (generator `hg` = K3, Rokhlin `hdvd`). The concrete Freeze-B consumability is
witnessed (§3), with its **vacuity line**: `trivialSpherePresentation.sig ≡ 0`, so no `σ = −16`
generator exists on the toy (`trivialSpherePresentation_no_generator`) — the concrete Freeze-B
discharge's value is exactly as the engine's `hB`-slot fillability witness, NOT a route to the iso on
the toy (which needs the genuine, nontrivial-σ spin datum).

Additive module: imports the atoms (`HandleTradeSurgery`) and the Freeze-B discharge
(`SphereDiskFreezeB`); modifies nothing. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HandleTradeSurgery
import SKEFTHawking.SphereDiskFreezeB

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {ξ : TangentialData X k I}

namespace SpinSigmaPresentation

/-! ### §1. The σ-engine headlines threaded from the terminal Freeze-A atoms

Each engine headline (`SpinSigmaRoute.lean`) takes `hA : R.RealizesSphereProducts`; here `hA` is
supplied at the finest grain by `realizesSphereProducts_of_cobordism_and_base` (the raw handle-trace
cobordism + the rank-0 base). So the injective direction, the full `Ω^ξ ≃+ ℤ`, and the `÷32` bridge
speak directly from `{HandleTradeCobordism, HyperbolicBase, SphereProductBounds}`. -/

/-- **The injective direction of `Ω^ξ ≅ ℤ` from the terminal atoms**: `σ` is injective on `Ω^ξ`
given the raw handle-trace cobordism `HandleTradeCobordism`, the rank-0 base `HyperbolicBase`, and
Freeze B `SphereProductBounds`. The lattice half (σ=0 ⟹ n·H) is in-tree; the two geometric atoms
are the only open input. -/
theorem sig_injective_of_cobordism_and_base (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds) :
    Function.Injective R.sig :=
  R.sig_injective (realizesSphereProducts_of_cobordism_and_base R hCob hBase) hB

/-- **`Ω^ξ` is generated by any `σ = −16` witness, from the terminal atoms**: modulo the two
Freeze-A atoms + Freeze B + Rokhlin `16 ∣ σ` + a `σ = −16` generator (K3), every class is an integer
multiple of `[g]`. -/
theorem generates_of_cobordism_and_base (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (x : DataBordismGrp ξ) : ∃ n : ℤ, x = n • DataBordismGrp.mk ξ g :=
  R.generates (realizesSphereProducts_of_cobordism_and_base R hCob hBase) hB g hg hdvd x

/-- **`Ω₄^{Spin} ≅ ℤ` — the N1a headline, from the terminal atoms**: the whole
`hyp:spin_bordism_iso_Z` iso ("≅ ℤ, generated by K3 with σ(K3) = −16"), with the engine's `hA` slot
filled at the finest grain (one raw handle-trace cobordism + the rank-0 base) and its `hB` slot by
Freeze B; the iso is the normalized signature `σ = −16·e`, `e [g] = 1`. -/
theorem dataBordismGrp_equiv_int_of_cobordism_and_base (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) :
    ∃ e : DataBordismGrp ξ ≃+ ℤ,
      (∀ x, R.sig x = -16 * e x) ∧ e (DataBordismGrp.mk ξ g) = 1 :=
  R.dataBordismGrp_equiv_int (realizesSphereProducts_of_cobordism_and_base R hCob hBase) hB g hg hdvd

/-- **The `÷32` bridge from the terminal atoms** (KT §5 Lemma 5.3 arithmetic half): modulo the two
Freeze-A atoms + Freeze B + Rokhlin + generator, `32 ∣ σ(x) ⟺ x` is an **even** multiple of the
generator — the algebra `PinPlusExactSequence.spin_image_card_two` consumes at the `Ω₄^{Spin}`
apex. -/
theorem thirtytwo_dvd_sig_iff_of_cobordism_and_base (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (x : DataBordismGrp ξ) :
    (32 : ℤ) ∣ R.sig x ↔ ∃ m : ℤ, x = (2 * m) • DataBordismGrp.mk ξ g :=
  R.thirtytwo_dvd_sig_iff (realizesSphereProducts_of_cobordism_and_base R hCob hBase) hB g hg hdvd x

end SpinSigmaPresentation

/-! ### §2. The KT §5 `s`-map (`D5` door input) threaded from the terminal atoms

`SpinSigmaRoute`'s `hker_of_forward_and_two_gen` derives Lemma 5.3's kernel identity
`F x = 0 ↔ 32 ∣ σ(x)` from `hA`/`hB` + the KT forward direction (`hfwd`) + `2·K3 bounds Pin⁺`
(`h2g`); `forgetGen_eq_zero_iff` turns that into the door's `hs` (`s n = 0 ↔ 2 ∣ n`). Both are
restated from the terminal Freeze-A atoms. -/

variable {G : Type*} [AddCommGroup G]

/-- **KT Lemma 5.3's kernel identity from the terminal atoms**: `F x = 0 ↔ 32 ∣ σ(x)`, with `hA`
supplied by the raw handle-trace cobordism + rank-0 base. The open inputs are the two Freeze-A atoms,
Freeze B, Rokhlin, generator, plus the two KT geometric facts (`hfwd`: Pin⁺-bounds ⟹ `32 ∣ σ`;
`h2g`: `2·K3` bounds Pin⁺). -/
theorem hker_of_forward_and_two_gen_of_atoms (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ G) (hfwd : ∀ x, F x = 0 → (32 : ℤ) ∣ R.sig x)
    (h2g : F ((2 : ℤ) • DataBordismGrp.mk ξ g) = 0) (x : DataBordismGrp ξ) :
    F x = 0 ↔ (32 : ℤ) ∣ R.sig x :=
  hker_of_forward_and_two_gen R
    (SpinSigmaPresentation.realizesSphereProducts_of_cobordism_and_base R hCob hBase) hB g hg
    hdvd F hfwd h2g x

/-- **The D5 door's `hs` input, fully threaded from the terminal atoms**: `s := forgetGen F g` kills
exactly the even multiples (`s n = 0 ↔ 2 ∣ n`) — the shape
`omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53` consumes through
`PinPlusExactSequence.spin_image_card_two` — from `{HandleTradeCobordism, HyperbolicBase,
SphereProductBounds}` + Rokhlin + generator + the KT forward (`hfwd`) + `2·K3` bounds (`h2g`).
Composes `hker_of_forward_and_two_gen_of_atoms` with `forgetGen_eq_zero_iff`. -/
theorem forgetGen_eq_zero_iff_of_atoms (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ G) (hfwd : ∀ x, F x = 0 → (32 : ℤ) ∣ R.sig x)
    (h2g : F ((2 : ℤ) • DataBordismGrp.mk ξ g) = 0) (n : ℤ) :
    forgetGen F g n = 0 ↔ (2 : ℤ) ∣ n :=
  forgetGen_eq_zero_iff R F g hg
    (hker_of_forward_and_two_gen_of_atoms R hCob hBase hB g hg hdvd F hfwd h2g) n

/-! ### §3. Freeze B consumed on the concrete `S²×S²` presentation, and its vacuity line

`trivialSpherePresentation_freezeB` discharges Freeze B (kernel-pure, no hypothesis) for the concrete
`S²×S²` presentation. Consuming it collapses the engine's `hB` slot: on that presentation the ONLY
open engine input is the pair of Freeze-A atoms. The **vacuity line**: the concrete presentation
carries `sig ≡ 0`, so no `σ = −16` generator exists — the full iso is vacuously conditional on the
toy, and the concrete Freeze-B discharge's value is exactly as the `hB`-fillability witness. -/

universe u₁ u₂

/-- The concrete `S²×S²` presentation has `sig ≡ 0` (its `sig` field is the zero hom). -/
theorem trivialSpherePresentation_sig_apply_eq_zero (k : WithTop ℕ∞)
    (x : DataBordismGrp (trivialData (X := PUnit) (k := k) (I := I4))) :
    (trivialSpherePresentation k).sig x = 0 := rfl

/-- **VACUITY LINE**: no `σ = −16` generator exists on the concrete presentation — its `sig ≡ 0`, so
`sig [g] = 0 ≠ −16` for every candidate `g`. Hence the full-iso headline
(`dataBordismGrp_equiv_int_of_cobordism_and_base`) is vacuously conditional on the toy: the concrete
Freeze-B discharge unblocks the `hB` slot, not the iso. The genuine, nontrivial-σ spin datum is the
only host for the generator. -/
theorem trivialSpherePresentation_no_generator (k : WithTop ℕ∞)
    (g : StrMfd (trivialData (X := PUnit) (k := k) (I := I4))) :
    (trivialSpherePresentation k).sig (DataBordismGrp.mk _ g) ≠ (-16 : ℤ) := by
  rw [trivialSpherePresentation_sig_apply_eq_zero]; norm_num

/-- **Freeze B consumed: the concrete presentation's `hB`-slot is filled by a genuine term.** On the
concrete `S²×S²` presentation the σ-engine's injective direction reduces to the two Freeze-A atoms
ALONE — Freeze B is no longer a hypothesis (`trivialSpherePresentation_freezeB`). This is the
`hB`-fillability witness the concrete Benedetti-Freeze-B discharge supplies to the engine; per §3's
vacuity line the injectivity of the toy's `sig ≡ 0` is the triviality of the toy carrier, contingent
on the (still-open) Freeze-A atoms for that carrier — NOT the genuine iso. -/
theorem trivialSpherePresentation_sig_injective_of_atoms (k : WithTop ℕ∞)
    (hCob : (trivialSpherePresentation.{u₁, u₂} k).HandleTradeCobordism)
    (hBase : (trivialSpherePresentation.{u₁, u₂} k).HyperbolicBase) :
    Function.Injective (trivialSpherePresentation.{u₁, u₂} k).sig := by
  exact SpinSigmaPresentation.sig_injective_of_cobordism_and_base _ hCob hBase
    (trivialSpherePresentation_freezeB.{u₁, u₂} k)

end SKEFTHawking.SpinSigmaRoute
