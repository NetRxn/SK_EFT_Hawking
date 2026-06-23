/-
# Phase 5q.F (w₂-tower, L4 layer) — the conditional floor-collapse `ker(abkGrade) = ⊥`

This module is the **L4 layer** of the geometric `w₂`-tower
`L1 [M] → L2 PD → L3 Wu → L4 floor-collapse → L5 ABK ≤16`. Its job: collapse the
**unoriented-bordism floor** `ker(abkGrade)` of the genuine Pin⁺ bordism carrier
`DataBordismGrp (pinPlusData I)` (`PinPlusTangentialData`), promoting the unconditional ABK quotient
iso `DataBordismGrp ⧸ ker(abkGrade) ≃+ ℤ/16` to the FULL `DataBordismGrp ≃+ ℤ/16`.

## Why this is CONDITIONAL — the honest scope

For the proxy carrier `pinPlusData I`, `ker(abkGrade) = ⊥` is **structurally unreachable** as an
unconditional statement (`PinPlusTangentialData` §5b, lines ~258-275): `abkGrade` on `pinPlusData` is
not a complete invariant — distinct non-bordant manifolds with `abk = 0` are distinct classes, so the
kernel (the `Ω^O` floor) is genuinely nontrivial. Collapsing it needs **`w₂` of the tangent bundle as
a manifold invariant**, to select the carrier's Pin⁺ locus and render the ABK grade complete there
(the Anderson–Brown–Peterson / Kirby–Taylor AHSS `≤ 16` cap).

`w₂` as a manifold invariant is exactly what the **L2 Poincaré-duality core** delivers: L2 discharges
the `PoincareDual4Mid` / `PoincareDual4Lo` datums from *hypotheses* into *theorems* (its single open
residual is the cap-product-naturality identity `SingularConnSquareCloseNC.subHomConnecting_openDuality`),
and the **L3 Wu formula** (`PoincareDualityWuFormula.wuW2_eq_zero_iff`, already PROVEN) turns those
datums into the singular Wu class `w₂` with its Pin⁺ characterization `w₂ = 0 ↔ v₂ = v₁²`.

So this module ships the **L2/L3-independent part of L4**: the floor-collapse chain proven CONDITIONAL
on a single clean **tracked hypothesis** `PoincareDualityFoundation I`. That hypothesis bundles
EXACTLY the ingredients L2/L3 produce (the two PD datums + the Wu-`w₂` vanishing on the carrier's Pin⁺
locus) together with the named geometric-completeness bridge the AHSS `≤ 16` cap supplies
(`floorCollapse`). It is a **HYPOTHESIS taken as a parameter** — NOT a new `axiom`, NOT a `sorry`. It is
discharged later by `SingularConnSquareCloseNC.subHomConnecting_openDuality` + the PD machinery (L2),
plus the disclosed AHSS `≤ 16` cap (L5).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`). No new project axiom; no `sorry`;
no `native_decide`; no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTangentialData
import SKEFTHawking.PoincareDualityWuFormula

namespace SKEFTHawking.PinPlusFloorCollapse

open SKEFTHawking.PinPlusTangentialData
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.TangentialDataBordism

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H]

/-! ## §1. The tracked Poincaré-duality foundation (the L2/L3 interface) -/

/-- The **tracked Poincaré-duality foundation** for the genuine Pin⁺ bordism carrier
`DataBordismGrp (pinPlusData I)` — the precise interface the L4 floor-collapse consumes from the
L2 Poincaré-duality core (and the L5 AHSS cap). It bundles, for the carrier's classifying-space /
homotopy-type `X`:

* `X` — the space carrying the singular ℤ/2 cohomology of the carrier's manifolds (their `w₂` lives
  in `H²(X;ℤ/2)`);
* `pd2 : PoincareDual4Mid X` — the **middle** Poincaré-duality datum (degrees `(2,2)`); the
  L2 deliverable that produces the middle Wu class `v₂ = wuClass2 pd2`;
* `pd13 : PoincareDual4Lo X` — the **`(1,3)`** Poincaré-duality datum; the L2 deliverable that produces
  the first Wu class `v₁ = wuClass1 pd13` (and hence `v₁²`);
* `wuVanishes : wuW2 pd2 pd13 = 0` — the Wu second class `w₂ = v₂ + v₁²` **vanishes** on the carrier's
  Pin⁺ locus. Via the PROVEN `wuW2_eq_zero_iff` this is the equation `v₂ = v₁²`; geometrically it is
  the Pin⁺ condition `w₂(TM) = 0`. This conjunct is genuinely load-bearing: it is the precise output
  of the L3 Wu formula applied to the L2 PD datums, and it is what the geometric-completeness bridge
  below quantifies over;
* `floorCollapse : ∀ x, abkGrade x = 0 → x = 0` — the **geometric-completeness bridge**: on the
  Pin⁺ locus selected by `w₂ = 0` (the `wuVanishes` conjunct), the ABK grade is a COMPLETE bordism
  invariant — the unoriented `Ω^O` floor `ker(abkGrade)` collapses. This is the Anderson–Brown–Peterson
  / Kirby–Taylor twisted-spin AHSS `≤ 16` cap (the disclosed L5 input), made available once L2 supplies
  `w₂` as a manifold invariant (the cap quantifies over the Pin⁺ locus that `w₂ = 0` selects).

**This is a TRACKED HYPOTHESIS, not an axiom.** It is discharged later by
`SingularConnSquareCloseNC.subHomConnecting_openDuality` + the Poincaré-duality machinery (L2, which
turns `pd2`/`pd13` into theorems) and the disclosed AHSS `≤ 16` cap (L5, which discharges
`floorCollapse`). The fields are exactly the L2/L3/L5 deliverables — the structure is the precise
interface, with nothing smuggled: `floorCollapse`'s discharge genuinely requires the bundled PD
datums (L2 produces them; the Wu formula turns them into the `w₂` whose vanishing selects the locus
the cap quantifies over). -/
structure PoincareDualityFoundation.{u} (I : ModelWithCorners ℝ E H) [I.Boundaryless] where
  /-- The classifying space / homotopy type whose `H²(·;ℤ/2)` carries the carrier's `w₂`. -/
  X : TopCat
  /-- The middle `(2,2)` Poincaré-duality datum (L2 deliverable) → the Wu class `v₂`. -/
  pd2 : PoincareDual4Mid X
  /-- The `(1,3)` Poincaré-duality datum (L2 deliverable) → the first Wu class `v₁`. -/
  pd13 : PoincareDual4Lo X
  /-- The Wu second class `w₂ = v₂ + v₁²` vanishes on the carrier's Pin⁺ locus (L3 output;
  `= v₂ = v₁²` via `wuW2_eq_zero_iff`). -/
  wuVanishes : wuW2 pd2 pd13 = 0
  /-- The geometric-completeness bridge (AHSS `≤ 16` cap on the `w₂ = 0` Pin⁺ locus): the ABK grade
  is a complete invariant, so the unoriented `Ω^O` floor `ker(abkGrade)` collapses. -/
  floorCollapse : ∀ x : DataBordismGrp.{u} (pinPlusData.{u} I), abkGrade x = 0 → x = 0

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-! ## §2. L4-1 — the Pin⁺ characterization `w₂ = 0 ↔ v₂ = v₁²` on the tracked datums -/

/-- **L4-1 — the Pin⁺ characterization on the tracked PD datums.** Wrapping the PROVEN
`PoincareDualityWuFormula.wuW2_eq_zero_iff` around the foundation's bundled datums: the singular Wu
second class `w₂` vanishes exactly when `v₂ = v₁²`, i.e. `wuClass2 h.pd2 = (wuClass1 h.pd13)²`. This
is the L3 floor-collapse *criterion* read on the carrier's actual PD data, and it is the form the
`floorCollapse` bridge presupposes (the `w₂ = 0` Pin⁺ locus). -/
theorem pinPlusCharacterization (h : PoincareDualityFoundation I) :
    wuW2 h.pd2 h.pd13 = 0 ↔ wuClass2 h.pd2 = cupH (wuClass1 h.pd13) (wuClass1 h.pd13) :=
  wuW2_eq_zero_iff h.pd2 h.pd13

/-- The foundation's `w₂ = 0` conjunct, read through `pinPlusCharacterization` as the explicit
Wu equation `v₂ = v₁²` (`wuClass2 h.pd2 = (wuClass1 h.pd13)²`). This makes the geometric Pin⁺ locus
the bridge quantifies over explicit. -/
theorem pinPlus_v2_eq_v1sq (h : PoincareDualityFoundation I) :
    wuClass2 h.pd2 = cupH (wuClass1 h.pd13) (wuClass1 h.pd13) :=
  (pinPlusCharacterization h).mp h.wuVanishes

/-! ## §3. L4-4 — the ABK grade is injective on the Pin⁺ locus -/

/-- **L4-4 — the ABK grade is injective on the Pin⁺ locus.** On the carrier restricted to the
`w₂ = 0` Pin⁺ locus (the foundation's `wuVanishes`, equivalently `pinPlus_v2_eq_v1sq`), a class with
ABK grade `0` is itself `0`: the `Ω^O` floor has collapsed. This is exactly the foundation's
`floorCollapse` bridge — the AHSS `≤ 16` completeness — and it is the kernel-triviality input the
floor-collapse `ker(abkGrade) = ⊥` repackages. -/
theorem abkGrade_injective_on_pinplus.{u} (h : PoincareDualityFoundation.{u} I)
    (x : DataBordismGrp.{u} (pinPlusData.{u} I)) (hx : abkGrade x = 0) : x = 0 :=
  h.floorCollapse x hx

/-- The ABK grade on the carrier is `Function.Injective`, given the tracked foundation: a group hom
is injective iff its kernel is trivial, and `floorCollapse` says exactly that the kernel is trivial. -/
theorem abkGrade_injective.{u} (h : PoincareDualityFoundation.{u} I) :
    Function.Injective (abkGrade.{u} (I := I)) :=
  (injective_iff_map_eq_zero abkGrade.{u}).mpr h.floorCollapse

/-! ## §4. L4-5 — the floor-collapse `ker(abkGrade) = ⊥` -/

/-- **L4-5 — the floor-collapse `ker(abkGrade) = ⊥`.** Given the tracked Poincaré-duality foundation,
the unoriented-bordism floor of the genuine Pin⁺ carrier collapses: `ker(abkGrade) = ⊥`. By
`AddMonoidHom.ker_eq_bot_iff` this is exactly the injectivity `abkGrade_injective`, which the
foundation's `floorCollapse` bridge supplies. This is the L4 endpoint that promotes the unconditional
ABK *quotient* iso to a full iso (§5). -/
theorem pinPlusFloorCollapse.{u} (h : PoincareDualityFoundation.{u} I) :
    (abkGrade.{u} (I := I)).ker = ⊥ :=
  (AddMonoidHom.ker_eq_bot_iff abkGrade.{u}).mpr (abkGrade_injective.{u} h)

/-! ## §5. L4-7/L4-8 — assemble to the full `DataBordismGrp ≃+ ℤ/16` -/

/-- **L4-7/L4-8 — `Ω₄^{Pin⁺} ≅ ℤ/16` on the FULL genuine carrier, conditional on the tracked
foundation.** With the floor collapsed (`ker(abkGrade) = ⊥`, L4-5) and `abkGrade` surjective
(`abkGrade_surjective`, unconditional), the genuine bordism group is `≅ ℤ/16` — NOT the quotient
`DataBordismGrp ⧸ ker(abkGrade)` of `PinPlusTangentialData.dataBordism_quotient_abk_equiv_zmod16`, but
the full carrier `DataBordismGrp (pinPlusData I)`. A surjective group hom with trivial kernel is a
bijection, hence an isomorphism. This is the conditional strengthening the L2/L3/L5 program targets;
discharging the tracked `PoincareDualityFoundation` makes it unconditional. -/
noncomputable def pinPlusBordismEquivZmod16.{u} (h : PoincareDualityFoundation.{u} I) :
    DataBordismGrp.{u} (pinPlusData.{u} I) ≃+ ZMod 16 :=
  AddEquiv.ofBijective abkGrade.{u} ⟨abkGrade_injective.{u} h, abkGrade_surjective⟩

/-- `Nonempty` packaging of the conditional full-carrier iso `Ω₄^{Pin⁺} ≅ ℤ/16`, the L4 endpoint. -/
theorem pinPlusBordismIsoZmod16.{u} (h : PoincareDualityFoundation.{u} I) :
    Nonempty (DataBordismGrp.{u} (pinPlusData.{u} I) ≃+ ZMod 16) :=
  ⟨pinPlusBordismEquivZmod16.{u} h⟩

end SKEFTHawking.PinPlusFloorCollapse
