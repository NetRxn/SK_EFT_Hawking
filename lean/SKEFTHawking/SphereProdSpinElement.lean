/-
# Phase 5q.H — THE `S²×S²` SPIN ELEMENT: the Freeze-B lane's NON-VACUITY, and the slot pin loosened

The Freeze-B lane closed out in `PinPlusKTSphereProdP23Close` discharges the whole `S²×D³`
coboundary geometry, but every one of its statements is quantified over a tangential structure
`str : (spinEmptyData prov).Mfd (sphereProdSM4 k)` on the concrete `S²×S²` — and NO inhabitant of
that type existed in tree. Until one does, `isDataBordant_empty_sphereDisk` /
`sphereProdCoboundaryWAdm_sphereDisk` / the whole `…_sphereDiskPinned` headline family are
**∀-vacuous**: true, and about nothing. This module removes that risk and then uses the inhabitant
to loosen the lane's residual pin.

## §1–§5 — the inhabitant (the S⁴ stock-element pattern, at the genuinely non-degenerate carrier)

`sphereProdSpinStr` builds the empty-Σ `CharPairStrBundled (𝓡 4) (sphereProdSM4 k)` on the genuine
Mathlib `S²×S²` (product of unit 2-spheres, re-associated to the `𝓡 4` model in
`PinPlusKTSphereProdReassoc`). Two fields are carrier-specific and BOTH are genuine computations,
not subsingleton collapses:

* `cert : PinPlusCertK` — the Pin⁺/`w₂ = 0` certificate `w₂ = v₂ + v₁² = 0`, from
  - `v₂ = 0` (`sphereProd_wuClass2_eq_zero`): the middle Wu class is the Poincaré dual of the
    cup-square functional, and the cup square vanishes on `H²(S²×S²;ℤ/2)`
    (`SphereProdBoundaryCupSquare.sphereProd_cupSquare_eq_zero`, the banked `{pr₁*g, pr₂*g}`
    basis argument);
  - `v₁ = 0` (`sphereProd_wuClass1_eq_zero`): `H¹(S²×S²;ℤ/2) = 0`, derived here from the PD
    dimension equality `dim H¹ = dim H³` of `poincareDual4Lo_of_closed` fed the banked
    `H₃(S²×S²;ℤ/2) = 0` (`SphereProdHThreeMod2`).
  Contrast the S⁴ stock element (`PinPlusKTSpinSigmaStockElement.sphere4_hcert`), where the same
  obligation is free because `H²(S⁴;ℤ/2) = 0`. Here `H²(S²×S²;ℤ/2)` is **2-dimensional**
  (`sphereProd_finrank_cohomology_two`), so `v₂ = 0` is a genuine vanishing in a nontrivial group.
* `hchar` — the arm-4 R1 characteristic-surface tie `⟨a, emb₊[Σ]⟩ = μ(a ⌣ a)` at the NONEMPTY
  carrier: LHS `0` because `[Σ] = 0`, RHS `0` by the same cup-square vanishing. (This is exactly
  the field that FORBIDS an empty-Σ bundle on `ℝP⁴` — `RP4CharPairWitness.
  no_empty_surface_bundle_on_rp4` — so its discharge here is the spin-side content, not a formality.)

## §6 — the payload

`sphereProdSpinElement_class_eq_zero` : `[S²×S²] = 0` in `Ω^{spinEmptyData prov}`, **hypothesis-free**
at every regularity `k`. This is Freeze B's literal content (`S²×S² = ∂(S²×D³)`) at the concrete
slot, with the coboundary supplied by the banked `isDataBordant_empty_sphereDisk`. Its proof is a
BORDISM WITNESS, so its content does not depend on the ambient group being nontrivial (which is
downstream of the still-open σ-presentation atom and is NOT claimed here).

## §7–§9 — the slot pin LOOSENED (what this buys the assembly row)

The banked terminal form (`PinPlusKTSphereProdP23Close.kt_equiv_zmod16_ofKRS_phig_sphereDiskPinned`)
carries `hs2s2 : (row.R.s2s2).1 = sphereProdSM4 k` — the distinguished slot must BE the standard
manifold. Two strictly weaker pins are shown to suffice, and the banked form is re-derived from the
second, so "the pin loosened" is a kernel fact and not a docstring claim:

* `SlotBordantToSphereProd` (§7) — the slot is merely *structured-bordant* to a standard `S²×S²`.
  `slotBordantToSphereProd_of_base` is the arrow `hs2s2 ⟹ this` (reflexivity of `IsDataBordant`).
* `SphereProdRankTwo` (§8) — the presentation assigns `b₂ = 2` to SOME structure on the standard
  `S²×S²`. Given `hA` (already a row binder — Benedetti handle-trading), this alone forces Freeze B:
  `[S²×S²] = 0` + `sig_eq` + `even_unimod` make the concrete element hyperbolic-congruent, so `hA`
  fires there and gives `(rank / 2) • [s2s2] = 0`. `sphereProdRankTwo_of_base` is the arrow
  `hs2s2 ⟹ this` (through the presentation's OWN `s2s2_rank` field).

**No converse is claimed** in either case, and no claim is made that the row shrank in arity: it did
not (seven binders, as in the banked lane). The improvement is that one binder is weaker — and, for
the `SphereProdRankTwo` form, that the surviving binder is a NUMERICAL normalization on disclosed E1
data (`b₂(S²×S²) = 2`, cf. `PinPlusKTSpinSigmaStock.sphereProd_s2s2_rank`) rather than a geometric
identification of the row's slot.

**Honest limit / where the rank pin's weight sits** (`realizes_forces_rank_nsmul_eq_zero` +
`rank_zero_forcing_is_trivial`): the forcing lemma yields only `(R.rank p / 2) • [s2s2] = 0`, which is
vacuously true at `R.rank p = 0`. So `hrk` is load-bearing, and the geometric weight of the route now
rests on `hA` — which is where the literature (Benedetti Prop 20.16 / Lemma 20.17) puts it. What this
module does NOT do is discharge `hB` for an ARBITRARY row: `SpinSigmaPresentation` constrains its
`s2s2` slot only through `rank s2s2 = 2`, `s2s2_hyp` and `sig_eq` — all of which are satisfied by a
slot of nonzero class (they force only `sig [s2s2] = 0`, and `sig`-detection of the class is exactly
what `sig_injective` is trying to prove). Some pin tying the slot to the standard `S²×S²` is therefore
irreducible; this module makes the cheapest known one numerical.

## §10 — the rank pin lands on COMPUTED in-tree data

For a presentation built from the disclosed E1 bundle
(`PinPlusKTSpinSigmaAtom.spinSigmaPresentation_of_atoms`), `rank` IS `(a.B ·).rank`, so
`SphereProdRankTwo` reads "the bundle's `H²(·;ℤ)` basis at the `S²×S²` element has rank 2" — and it
is DISCHARGED (`sphereProdRankTwo_of_atoms_agree`) from the data-agreement equation
`a.B (sphereProdSpinElement prov) = sphereProdIntH2Basis` against the in-tree COMPUTED product basis,
whose rank is `2` by `rfl`. Consequence: `dataBordismGrp_equiv_int_of_atoms_agree` is the N1a
`Ω₄^{Spin} ≅ ℤ` headline with the Freeze-B binder GONE — the surviving geometric row is `hA` plus the
two Freeze-A atoms (the settled E1-surgery floor `freeze-atoms-not-composable-from-sigma-trace`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSphereProdP23Close
import SKEFTHawking.PinPlusKTSpinSigmaStock

open scoped Manifold
open SKEFTHawking
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusTiedData
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.T2TangentialBordism
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTSphereProdP23Close

attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartR4

namespace SKEFTHawking.SphereProdSpinElement

variable {k : WithTop ℕ∞}

/-! ## §1. The closed-manifold instances on `S²×S²`. -/

/-- `S²×S²` is Hausdorff, compact and nonempty — the `[T2Space] [CompactSpace] [Nonempty]` binders
of the closed-4-manifold Poincaré-duality theorem-instances, all from Mathlib's sphere/product
stack. -/
example : T2Space SphereProd := inferInstance
example : CompactSpace SphereProd := inferInstance
example : Nonempty SphereProd := inferInstance

/-- The merged `E⁴` atlas of `S²×S²` at the `Fin (2 + 2)` spelling the closed-4-manifold
Poincaré-duality instances (`SingularPD4Instances`) demand. -/
@[reducible] noncomputable def chartR4' :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) SphereProd :=
  SKEFTHawking.SpinSigmaRoute.chartR4

attribute [local instance] chartR4'

/-! ## §2. `H³(S²×S²;ℤ/2) = 0`, hence `H¹(S²×S²;ℤ/2) = 0`. -/

/-- **`H₃(S²×S²;ℤ/2) = 0`** as an instance — the banked mod-2 homology computation
(`SphereProdHThreeMod2`, via the integral `H₃ = 0` + `H₂` 2-torsion-freeness lift/halve lemma). -/
instance sphereProd_subsingleton_homologyMod2_three :
    Subsingleton (Homology (TopCat.of SphereProd) (2 + 1)) :=
  subsingleton_of_forall_eq 0 SphereProdHThreeMod2.sphereProd_homologyMod2_three_eq_zero

/-- **`H³(S²×S²;ℤ/2) = 0`** — the UC flip of the mod-2 homology vanishing. -/
instance sphereProd_subsingleton_cohomology_three :
    Subsingleton (Cohomology (TopCat.of SphereProd) 3) :=
  PinPlusKTSphereProdCohomology.subsingleton_cohomology_of_homology
    (X := TopCat.of SphereProd) 2

/-- **`H¹(S²×S²;ℤ/2) = 0`** — NOT computed by a fresh MV chase: it is read off the genuine
Poincaré-duality datum of the closed 4-manifold, whose `dimeq` field IS the Betti identity
`b₁ = b₃`, fed `H³ = 0`. Finite-dimensionality comes from the same datum's `findim₁`. -/
instance sphereProd_subsingleton_cohomology_one :
    Subsingleton (Cohomology (TopCat.of SphereProd) 1) := by
  have hP := poincareDual4Lo_of_closed (M := SphereProd)
  haveI := hP.findim₁
  have h3 : Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereProd) 3) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h1 : Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereProd) 1) = 0 := by
    rw [hP.dimeq, h3]
  exact Module.finrank_zero_iff.mp h1

/-! ## §3. The two Wu classes of `S²×S²` vanish. -/

/-- **`v₁(S²×S²) = 0`** — the first Wu class lives in `H¹(S²×S²;ℤ/2) = 0`. -/
theorem sphereProd_wuClass1_eq_zero :
    wuClass1 (poincareDual4Lo_of_closed (M := SphereProd)) = 0 :=
  Subsingleton.elim _ _

/-- **The falsifiability pin of §3**: `H²(S²×S²;ℤ/2)` is `2`-dimensional. So the middle-Wu vanishing
`sphereProd_wuClass2_eq_zero` below is a genuine vanishing inside a nontrivial group — NOT the
subsingleton collapse that discharges the same obligation on `S⁴` (`H²(S⁴;ℤ/2) = 0`,
`PinPlusKTSpinSigmaStockElement.sphere4_hcert`). -/
theorem sphereProd_finrank_cohomology_two :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereProd) 2) = 2 := by
  rw [PoincareLefschetzRelFundClassCylinderSuspension.finrank_cohomology_eq_homology
      (X := TopCat.of SphereProd) 1,
    SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two]

/-- **The non-degeneracy statement in usable form**: `H²(S²×S²;ℤ/2)` is NONTRIVIAL. So
`sphereProd_wuClass2_eq_zero` below cannot be obtained the way the `S⁴` stock element's is
(`Subsingleton.elim` on a vanishing `H²`) — it needs the actual cup-square computation. -/
theorem sphereProd_cohomology_two_nontrivial :
    Nontrivial (Cohomology (TopCat.of SphereProd) 2) :=
  Module.nontrivial_of_finrank_pos
    (R := ZMod 2) (by rw [sphereProd_finrank_cohomology_two]; norm_num)

/-- **The Wu functional `x ↦ ⟨Sq²x,[M]⟩ = μ(x ⌣ x)` vanishes identically on `H²(S²×S²;ℤ/2)`** — the
banked cup-square vanishing (`SphereProdBoundaryCupSquare.sphereProd_cupSquare_eq_zero`) evaluated
against the fundamental-class functional. -/
theorem sphereProd_wuFunctional_eq_zero :
    wuFunctional (poincareDual4Mid_of_closed (M := SphereProd)) = 0 := by
  ext x
  show (poincareDual4Mid_of_closed (M := SphereProd)).mu (cupSquare2 x) = 0
  rw [cupSquare2_apply, SphereProdBoundaryCupSquare.sphereProd_cupSquare_eq_zero, map_zero]

/-- **`v₂(S²×S²) = 0`** — the middle Wu class is the Poincaré-dual REPRESENTATIVE of the Wu
functional; the functional is zero and the duality pairing is a bijection, so the representative is
`0`. By `sphereProd_finrank_cohomology_two` this is a genuine vanishing in a 2-dimensional group. -/
theorem sphereProd_wuClass2_eq_zero :
    wuClass2 (poincareDual4Mid_of_closed (M := SphereProd)) = 0 := by
  rw [wuClass2, sphereProd_wuFunctional_eq_zero, Equiv.symm_apply_eq]
  exact (map_zero (pairing (poincareDual4Mid_of_closed (M := SphereProd)))).symm

/-- **`w₂(S²×S²) = 0` — `S²×S²` is spin**, in the singular Wu-formula form `w₂ = v₂ + v₁²` on the
genuine closed-4-manifold PD data. Both summands vanish (§3). -/
theorem sphereProd_wuW2_eq_zero :
    wuW2 (poincareDual4Mid_of_closed (M := SphereProd))
      (poincareDual4Lo_of_closed (M := SphereProd)) = 0 := by
  rw [wuW2, sphereProd_wuClass2_eq_zero, sphereProd_wuClass1_eq_zero, map_zero, add_zero]

/-! ## §4. The Pin⁺ / `w₂ = 0` certificate on `S²×S²`. -/

/-- **The Pin⁺/`w₂ = 0` admissibility certificate of the `S²×S²` carrier**, at every regularity `k`.
The `[T2Space] [Nonempty]` binders of `PinPlusCertK` are `Prop`-classes, so they agree with the
ambient instances by proof irrelevance and the §3 computation applies verbatim. -/
theorem sphereProd_hcert : PinPlusCertK (𝓡 4) (sphereProdSM4 k) := by
  intro _ _
  exact sphereProd_wuW2_eq_zero

/-! ## §5. The empty-Σ char-pair bundle and the spin element. -/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic in
/-- **The char-pair (algebraic) core on `S²×S²`** — rank-0 enhancement (`n = 0`,
`q = stdQuadratic 0`, the empty-characteristic-surface shadow), the Hausdorff witness, and the
genuine `w₂ = 0` certificate of §4. -/
noncomputable def sphereProdCharPairStr : CharPairStr (𝓡 4) (sphereProdSM4 k) where
  t2 := inferInstanceAs (T2Space SphereProd)
  cert := sphereProd_hcert
  n := 0
  q := stdQuadratic 0

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic in
/-- **The empty-Σ `CharPairStrBundled` on the concrete `S²×S²`.** The `surf`/`basis`/`hpolar`/
`surfClass` fields are the rank-0 `charPairBundledEmpty` pattern; the carrier-specific content is
`cert` (§4) and the NONEMPTY-carrier `hchar` tie, both of which turn on the cup-square vanishing.
`hchar` is the field that provably has NO empty-Σ solution on `ℝP⁴`
(`RP4CharPairWitness.no_empty_surface_bundle_on_rp4`), so discharging it here is the spin-side
content of the element, not bookkeeping. -/
noncomputable def sphereProdCharPairBundled : CharPairStrBundled (𝓡 4) (sphereProdSM4 k) where
  toCharPairStr := sphereProdCharPairStr
  surf := (emptySM : SingularManifold.{0} PUnit.{1} k (𝓡 2))
  surfT2 := ⟨fun x => x.elim⟩
  emb := fun x => x.elim
  embSmooth := fun x => x.elim
  embInj := fun x => x.elim
  surfClass := 0
  basis := by
    show _ ≃ₗ[ZMod 2] (Fin 0 → ZMod 2)
    exact LinearEquiv.ofSubsingleton _ _
  hpolar := fun a b => by
    have hz : ∀ x y : Fin 0 → ZMod 2, (stdQuadratic 0).B x y = 0 :=
      fun x y => by rw [Subsingleton.elim x 0]; exact (stdQuadratic 0).B_zero_left y
    show (stdQuadratic 0).B _ _ = _
    rw [hz, map_zero]
  hchar := by
    intro _ _ a
    rw [map_zero, map_zero,
      show ((cupH24 a) a) = 0 from SphereProdBoundaryCupSquare.sphereProd_cupSquare_eq_zero a,
      map_zero]

/-! ## §6. THE `S²×S²` SPIN ELEMENT and the unconditional Freeze-B class identity. -/

/-- **The empty-Σ spin-carrier structure on the concrete `S²×S²`** — an inhabitant of the type
`(spinEmptyData prov).Mfd (sphereProdSM4 k)` that every statement of the banked Freeze-B lane
quantifies over. -/
noncomputable def sphereProdSpinStr (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (spinEmptyData prov).Mfd (sphereProdSM4 k) :=
  ⟨sphereProdCharPairBundled, inferInstanceAs (IsEmpty PEmpty)⟩

/-- **THE NON-VACUITY CERTIFICATE OF THE FREEZE-B LANE.** `PinPlusKTSphereProdP23Close`'s
`isDataBordant_empty_sphereDisk`, `sphereProdCoboundaryWAdm_sphereDisk` and the whole
`…_sphereDiskPinned` headline family are stated `∀ str : (spinEmptyData prov).Mfd (sphereProdSM4 k)`.
This theorem says that quantifier ranges over a nonempty type — the lane is not ∀-vacuous. -/
theorem nonempty_sphereProdSpinStr (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Nonempty ((spinEmptyData prov).Mfd (sphereProdSM4 k)) :=
  ⟨sphereProdSpinStr prov⟩

/-- **THE `S²×S²` SPIN ELEMENT** — the `StrMfd (spinEmptyData prov)` member on the genuine
product-of-2-spheres with empty characteristic surface. The spin-carrier sibling of
`PinPlusKTSpinSigmaStockElement.sphere4Element`, at the carrier where the Wu obligations are
non-degenerate. -/
noncomputable def sphereProdSpinElement (prov : CharPairWProviderPerOp (𝓡 4) k) :
    StrMfd (spinEmptyData prov) :=
  ⟨sphereProdSM4 k, sphereProdSpinStr prov⟩

/-- The element's underlying manifold is the standard `S²×S²` (`rfl`) — the shape the banked
`…_ofBase` discharges consume. -/
@[simp] theorem sphereProdSpinElement_base (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (sphereProdSpinElement prov).1 = sphereProdSM4 k := rfl

/-- **FREEZE B AT THE CONCRETE SLOT, UNCONDITIONALLY**: `[S²×S²] = 0` in the empty-Σ spin carrier
`Ω^{spinEmptyData prov}`, at every regularity `k`, with NO hypothesis. The witness is the banked
`S²×D³` coboundary (`isDataBordant_empty_sphereDisk`, whose own Lefschetz–Wu / relative-fundamental-
class / `(2,3)`-PD inputs are all proved sister nodes), fed the §6 element. This is the literal
content of the DR's Freeze-B sub-piece (1) `S²×S² = ∂(S²×D³)` on the genuine carrier. -/
theorem sphereProdSpinElement_class_eq_zero (prov : CharPairWProviderPerOp (𝓡 4) k) :
    DataBordismGrp.mk (spinEmptyData prov) (sphereProdSpinElement prov) = 0 :=
  DataBordismGrp.mk_eq_of_bordant _
    (PinPlusKTSphereProdP23Close.isDataBordant_empty_sphereDisk prov (sphereProdSpinStr prov))

/-- **The class-zero identity is uniform in the tangential-structure component**: ANY spin-carrier
element whose MANIFOLD is the standard `S²×S²` has class `0`. (The banked coboundary discharge is
uniform in `p.2`; destructure + `subst` lands the concrete slot.) -/
theorem sphereProd_class_eq_zero_ofBase (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (spinEmptyData prov)) (hp : p.1 = sphereProdSM4 k) :
    DataBordismGrp.mk (spinEmptyData prov) p = 0 := by
  obtain ⟨M, s⟩ := p
  subst hp
  exact DataBordismGrp.mk_eq_of_bordant _
    (PinPlusKTSphereProdP23Close.isDataBordant_empty_sphereDisk prov s)

/-! ## §7. Freeze B from the SLOT-BORDANT pin (no `hA` needed). -/

/-- **Reflexivity of the structured-bordism relation** — the cylinder with its product structure
(`reflCylinder` + `cylBor`). Generic tangential-layer infrastructure; the `Quot` on
`IsDataBordant` already relies on it implicitly, but it was not named. -/
theorem isDataBordant_refl {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    (ξ : TangentialData X k I) (p : StrMfd ξ) : IsDataBordant ξ p p :=
  ⟨reflCylinder p.1, ⟨ξ.cylBor p.2⟩⟩

/-- **The slot-bordant pin** — the distinguished `s2s2` slot is structured-BORDANT to some
empty-Σ structure on the standard `S²×S²` (rather than definitionally equal to it, as the banked
`hs2s2` demands). -/
def SlotBordantToSphereProd (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation (spinEmptyData prov)) : Prop :=
  ∃ p : StrMfd (spinEmptyData prov),
    p.1 = sphereProdSM4 k ∧ IsDataBordant (spinEmptyData prov) R.s2s2 p

/-- **Freeze B from the slot-bordant pin** — no `hA` needed: bordance transports the class, and the
standard `S²×S²` class is `0` unconditionally (§6). -/
theorem sphereProductBounds_of_slotBordant {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (h : SlotBordantToSphereProd prov R) :
    R.SphereProductBounds := by
  obtain ⟨p, hp, hbor⟩ := h
  exact (DataBordismGrp.mk_eq_of_bordant _ hbor).trans (sphereProd_class_eq_zero_ofBase prov p hp)

/-- **The arrow `hs2s2 ⟹ SlotBordantToSphereProd`** (reflexivity of `IsDataBordant`), which is what
makes "the pin loosened" a kernel fact for §7. No converse is claimed. -/
theorem slotBordantToSphereProd_of_base {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (hp : (R.s2s2).1 = sphereProdSM4 k) :
    SlotBordantToSphereProd prov R :=
  ⟨R.s2s2, hp, isDataBordant_refl _ _⟩

/-! ## §8. Freeze B from the RANK-TWO pin, given `hA`. -/

/-- **The rank-two pin** — the presentation assigns `b₂ = 2` to SOME empty-Σ structure on the
standard `S²×S²`. A NUMERICAL normalization on the disclosed E1 data (cf. the computed
`PinPlusKTSpinSigmaStock.sphereProd_s2s2_rank : SphereWitnessTowerInt.sphereProdIntH2Basis.rank = 2`), asserting nothing
whatsoever about the row's distinguished slot. -/
def SphereProdRankTwo (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation (spinEmptyData prov)) : Prop :=
  ∃ p : StrMfd (spinEmptyData prov), p.1 = sphereProdSM4 k ∧ R.rank p = 2

/-- **What `hA` forces at the standard `S²×S²`.** For any spin-carrier element `p` whose manifold is
the standard `S²×S²`: its class is `0` (§6), hence its `sig` is `0` (`sig_eq`), hence its form is
even-unimodular of signature `0` (`even_unimod`), hence hyperbolic-congruent
(`exists_hyperbolic_congr`) — so the realization freeze `hA` fires at `p` and yields
`(R.rank p / 2) • [s2s2] = 0`. This is the exact leverage the rank pin converts into Freeze B, and
it makes the rank's role falsifiable: see `rank_zero_forcing_is_trivial`. -/
theorem realizes_forces_rank_nsmul_eq_zero {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (hA : R.RealizesSphereProducts)
    (p : StrMfd (spinEmptyData prov)) (hp : p.1 = sphereProdSM4 k) :
    (R.rank p / 2) • DataBordismGrp.mk (spinEmptyData prov) R.s2s2 = 0 := by
  have hz : DataBordismGrp.mk (spinEmptyData prov) p = 0 := sphereProd_class_eq_zero_ofBase prov p hp
  have hsig0 : latticeSig (R.form p) = 0 := by rw [← R.sig_eq p, hz, map_zero]
  obtain ⟨N, hN, hcong⟩ := exists_hyperbolic_congr (R.form p) (R.even_unimod p) hsig0
  have hrealize := hA p ⟨N, hN, hcong⟩
  rw [hz] at hrealize
  exact hrealize.symm

/-- **FREEZE B FROM `hA` + THE RANK-TWO PIN.** With `R.rank p = 2` the forcing lemma reads
`1 • [s2s2] = 0`, i.e. `R.SphereProductBounds`. The geometric weight of the route sits in `hA`
(Benedetti Prop 20.16 / Lemma 20.17), already a row binder; what leaves the row is the geometric
identification of the slot. -/
theorem sphereProductBounds_of_realizes_of_rankTwo {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (hA : R.RealizesSphereProducts)
    (h : SphereProdRankTwo prov R) : R.SphereProductBounds := by
  obtain ⟨p, hp, hrk⟩ := h
  have hforce := realizes_forces_rank_nsmul_eq_zero R hA p hp
  rw [hrk] at hforce
  show DataBordismGrp.mk (spinEmptyData prov) R.s2s2 = 0
  simpa using hforce

/-- **The rank pin is LOAD-BEARING** — at `R.rank p = 0` the forcing lemma
`realizes_forces_rank_nsmul_eq_zero` degenerates to `0 • [s2s2] = 0`, which holds with no hypothesis
at all and yields nothing. So `SphereProdRankTwo`'s `= 2` cannot be dropped or weakened to "some
rank". -/
theorem rank_zero_forcing_is_trivial {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (p : StrMfd (spinEmptyData prov))
    (h0 : R.rank p = 0) :
    (R.rank p / 2) • DataBordismGrp.mk (spinEmptyData prov) R.s2s2 = 0 := by
  rw [h0]
  simp

/-- **The arrow `hs2s2 ⟹ SphereProdRankTwo`** — through the presentation's OWN `s2s2_rank` field, so
no new input. This is what makes "the pin loosened" a kernel fact for §8. No converse is claimed. -/
theorem sphereProdRankTwo_of_base {prov : CharPairWProviderPerOp (𝓡 4) k}
    (R : SpinSigmaPresentation (spinEmptyData prov)) (hp : (R.s2s2).1 = sphereProdSM4 k) :
    SphereProdRankTwo prov R :=
  ⟨R.s2s2, hp, R.s2s2_rank⟩

/-! ## §9. The assembly rewires. -/

/-- **The seven-binder assembly with the slot-BORDANT pin** — `PinPlusKTAssemblyResiduals.
kt_equiv_zmod16_of_residuals_ofKRS_phig` with `hB` produced from §7. Row:
`{hKRS, row, hA, hcol, hker, hΦg}` + the pin `hslot`. -/
theorem kt_equiv_zmod16_ofKRS_phig_slotBordant {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts)
    (hslot : SlotBordantToSphereProd prov row.R)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS_phig prov hKRS row hA
    (sphereProductBounds_of_slotBordant row.R hslot) hcol hker hΦg

/-- **THE SEVEN-BINDER ASSEMBLY WITH THE RANK-TWO PIN** — `Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful
tethered carrier at ANY smoothness `k`, with `hB` produced from `hA` + the numerical pin (§8). Row:
`{hKRS, row, hA, hcol, hker, hΦg}` + `hrk`. Same arity as the banked
`PinPlusKTSphereProdP23Close.kt_equiv_zmod16_ofKRS_phig_sphereDiskPinned`; the pin is weaker (the
banked form is re-derived from this one immediately below). -/
theorem kt_equiv_zmod16_ofKRS_phig_rankTwo {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts)
    (hrk : SphereProdRankTwo prov row.R)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS_phig prov hKRS row hA
    (sphereProductBounds_of_realizes_of_rankTwo row.R hA hrk) hcol hker hΦg

/-- **The banked `hs2s2` form as a COROLLARY of the rank-two form** — statement identical to
`PinPlusKTSphereProdP23Close.kt_equiv_zmod16_ofKRS_phig_sphereDiskPinned`, proof factoring through
`sphereProdRankTwo_of_base`. This is the kernel check that the trade runs
`hs2s2 ⟹ SphereProdRankTwo` and not laterally. -/
theorem kt_equiv_zmod16_ofKRS_phig_sphereDiskPinned_of_rankTwo {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 k)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_ofKRS_phig_rankTwo prov hKRS row hA
    (sphereProdRankTwo_of_base row.R hs2s2) hcol hker hΦg

/-- **THE SMOOTH-CATEGORY HEADLINE WITH THE RANK-TWO PIN** (`k = ⊤`) — the `C^∞` instantiation, the
regularity the literature's `Ω₄^{Pin⁺} ≅ ℤ/16` is about (fence `k0-to-k1-transport-refuted`: this is
a re-declaration at `⊤`, not a transport from `0` — the whole lane is `k`-generic). -/
theorem kt_equiv_zmod16_smooth_phig_rankTwo
    (hKRS : KernelReducesToSpin (residualProvK ⊤))
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts)
    (hrk : SphereProdRankTwo (residualProvK ⊤) row.R)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hΦg : spinForgetPhi (residualProvK ⊤)
        (DataBordismGrp.mk (spinEmptyData (residualProvK ⊤)) row.g)
        = ktKernelRep (residualProvK ⊤)) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤)) ≃+ ZMod 16) :=
  kt_equiv_zmod16_ofKRS_phig_rankTwo (residualProvK ⊤) hKRS row hA hrk hcol hker hΦg

/-- **W-E, SMOOTH, RANK-TWO PIN** — `Nat.card Ω₄^{Pin⁺} = 16` on the smooth carrier. Pure transport
across the additive equivalence; no new residual atom. -/
theorem rokhlin_sixteen_smooth_phig_rankTwo
    (hKRS : KernelReducesToSpin (residualProvK ⊤))
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts)
    (hrk : SphereProdRankTwo (residualProvK ⊤) row.R)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hΦg : spinForgetPhi (residualProvK ⊤)
        (DataBordismGrp.mk (spinEmptyData (residualProvK ⊤)) row.g)
        = ktKernelRep (residualProvK ⊤)) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤))) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_smooth_phig_rankTwo hKRS row hA hrk hcol hker hΦg
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §10. The rank pin ON THE DISCLOSED E1 BUNDLE — it lands on computed in-tree data.

For a σ-presentation BUILT from the disclosed E1 atom bundle
(`PinPlusKTSpinSigmaAtom.spinSigmaPresentation_of_atoms`), `rank p` IS `(a.B p).rank`, so the §8 pin
reads: *the bundle's `H²(·;ℤ)` basis at the standard `S²×S²` has rank 2*. That is a data-agreement
statement against the in-tree COMPUTED basis (`SphereWitnessTowerInt.SphereWitnessTowerInt.sphereProdIntH2Basis`, whose
rank is `2` by `rfl` — `PinPlusKTSpinSigmaStock.sphereProd_s2s2_rank`), of exactly the kind
`PinPlusKTSpinSigmaStock.K3RealizingElement.hB` already uses at the generator slot. -/

open SKEFTHawking.PinPlusKTSpinSigmaAtom in
/-- **The rank pin at the atoms-built presentation is exactly the bundle's `b₂` at `S²×S²`.** -/
theorem sphereProdRankTwo_of_atoms {prov : CharPairWProviderPerOp (𝓡 4) k}
    (a : SpinSigmaAtoms prov) (hb2 : (a.B (sphereProdSpinElement prov)).rank = 2) :
    SphereProdRankTwo prov (spinSigmaPresentation_of_atoms a) :=
  ⟨sphereProdSpinElement prov, rfl, hb2⟩

open SKEFTHawking.PinPlusKTSpinSigmaAtom in
/-- **The rank pin DISCHARGED from a data-agreement equation.** If the disclosed E1 bundle's
`H²(·;ℤ)` basis at the `S²×S²` spin element is the in-tree COMPUTED product basis, then the §8 pin
holds — its rank is `2` by computation, not by assumption. -/
theorem sphereProdRankTwo_of_atoms_agree {prov : CharPairWProviderPerOp (𝓡 4) k}
    (a : SpinSigmaAtoms prov)
    (hagree : a.B (sphereProdSpinElement prov) = SphereWitnessTowerInt.sphereProdIntH2Basis) :
    SphereProdRankTwo prov (spinSigmaPresentation_of_atoms a) :=
  sphereProdRankTwo_of_atoms a (by rw [hagree]; exact PinPlusKTSpinSigmaStock.sphereProd_s2s2_rank)

open SKEFTHawking.PinPlusKTSpinSigmaAtom in
/-- **FREEZE B FOR THE ATOMS-BUILT PRESENTATION, from `hA` + basis agreement.** The Freeze-B binder
of `PinPlusKTSpinSigmaAtom.dataBordismGrp_equiv_int_of_atoms` (and of the dA/dC consumption sites) is
discharged for any disclosed E1 bundle that agrees with the computed `S²×S²` basis — no slot
identification, no geometric obligation beyond `hA`. -/
theorem sphereProductBounds_of_atoms_agree {prov : CharPairWProviderPerOp (𝓡 4) k}
    (a : SpinSigmaAtoms prov)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hagree : a.B (sphereProdSpinElement prov) = SphereWitnessTowerInt.sphereProdIntH2Basis) :
    (spinSigmaPresentation_of_atoms a).SphereProductBounds :=
  sphereProductBounds_of_realizes_of_rankTwo _ hA (sphereProdRankTwo_of_atoms_agree a hagree)

open SKEFTHawking.PinPlusKTSpinSigmaAtom in
/-- **`Ω₄^{Spin} ≅ ℤ` from the atom bundle with Freeze B GONE** — the N1a headline
(`dataBordismGrp_equiv_int_of_atoms`) with its `hSB` binder supplied by §10 instead of assumed. The
surviving geometric row is the two Freeze-A atoms (`HandleTradeCobordism`/`HyperbolicBase`, the
settled E1-surgery floor) plus `hA`; Freeze B has left it. -/
theorem dataBordismGrp_equiv_int_of_atoms_agree {prov : CharPairWProviderPerOp (𝓡 4) k}
    (a : SpinSigmaAtoms prov) (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData prov)) (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (SingularCohomologyInt.interMatrix (a.fc g) (a.B g))) k3Form)
    (hCob : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism)
    (hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hagree : a.B (sphereProdSpinElement prov) = SphereWitnessTowerInt.sphereProdIntH2Basis) :
    ∃ e : DataBordismGrp (spinEmptyData prov) ≃+ ℤ,
      (∀ x, a.sig x = -16 * e x) ∧ e (DataBordismGrp.mk (spinEmptyData prov) g) = 1 :=
  dataBordismGrp_equiv_int_of_atoms a hdvd g hrank hk3 hCob hBase
    (sphereProductBounds_of_atoms_agree a hA hagree)

end SKEFTHawking.SphereProdSpinElement
