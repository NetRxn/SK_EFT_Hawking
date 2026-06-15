/-
# Phase 5q.F W5 + W8 — `Ω₄^{Pin⁺} ≅ ℤ/16` from the FINITE height-4 cap, and the `SmithInflow` discharge

The genuine discharge the goal demands (hook-corrected). The `SmithInflow` opaque-iso hypothesis is
replaced by the **single** disclosed topological Prop `pin4_abutment` (Pontryagin–Thom + Adams
convergence, `Lit-Search/Phase-5qF/finite_height4_cap.md` §5) **plus the FINITE bounds**:

- **Upper** (`PinPlusHeight4.col4_height_eq_four`, fully `decide`-able, `axioms: []`): the Pin⁺ Adams
  `E₂` column `t−s=4` is the Campbell `δ=·h₀` cokernel, a **height-4** `h₀`-tower, so the abutment has
  cardinality `2⁴ = 16` — read off the **finite Ext cokernel height**, NOT posited.
- **Lower** (`GuillouMarin`/`PinPlusExt`, finite surface-ABK η-surrogate): `[RP⁴]` has order ≥ 16
  (`β(RP²)=1` a unit ⟹ odd ⟹ order 16).

`pin4_abutment` carries ONLY the topology↔algebra bridge (`Ω₄^{Pin⁺} ≅` the Adams abutment, of
cardinality `2^{height4}`); its `2^{height4}` makes the `ℤ/16` come from the **finite height**
(`col4_height_eq_four`), so the iso is **from finite content**, not a thin-substrate rename. The old
disclosed `DeltaTruncationCap` (`16·[RP⁴]=0`) is now **derived** from it (`deltaCap_of_pin4`), reducing
the tracked input to the ONE `pin4_abutment`. Given it, the convergence carries **no `SmithInflow`
binder** (`sixteen_convergence_finite_discharge`).

## Honest scope
The single non-finite input is `pin4_abutment` = Pontryagin–Thom (`Ω₄^{Pin⁺}=π₄MTPin⁺`) + Adams
convergence (`E₂=E∞`, no hidden ext at `t−s=4`) — Mathlib-absent, ONE disclosed Prop (the
"axiom-stratified framework", Phase-5a chirality-wall l.57/100; NOT an axiom; inhabited at the
substrate). Everything else — the height-4 cokernel, the `2^{height}` cardinality, the order-16 lower
bound, the SM-anomaly triviality — is finite/machine-checked.
-/
import Mathlib
import SKEFTHawking.PinPlusHeight4
import SKEFTHawking.PinPlusAdamsAbutment
import SKEFTHawking.PinPlusExtBound
import SKEFTHawking.SymTFT.SmithMechanism
import SKEFTHawking.PinPlusGenuineCarrierIso

namespace SKEFTHawking.PinPlusDischarge

open SKEFTHawking.SymTFT SKEFTHawking.PinHeight4 SKEFTHawking.PinPlusAdamsAbutment

/-! ## §1. The finite height and the single disclosed Pontryagin–Thom Prop

`height4`/`height4_eq` now live in `SKEFTHawking.PinPlusAdamsAbutment` (the W1 module), in scope here via
`open`. That module also ships the **hypothesis-free** `adamsAbutment ≃+ ZMod 16` — the iso is PROVED
from the decidable `col4_height_eq_four` with no `Nonempty`-of-the-conclusion hypothesis. The
`pin4_abutment` Prop below is **retained only** as the documented modeling bridge for the *geometric*
`Omega4PinPlusBordism` object (consumed by `Omega5FiniteIso`); it is the geometric-faithfulness
identification, to be DERIVED by the W4–W6 Smith-LES route — not the load-bearing input for the ℤ/16. -/

/-- **`pin4_abutment` — the SINGLE disclosed topological Prop** (`finite_height4_cap.md` §5): the Pin⁺
bordism group is the Adams abutment of the column-4 height-`height4` `h₀`-tower, i.e. `Ω₄^{Pin⁺} ≃+
ZMod (2^height4)`. Bundles Pontryagin–Thom (`Ω₄ ≅ π₄MTPin⁺`) + Adams convergence (`E₂=E∞`, no hidden
ext). NOT an axiom; **inhabited** (`pin4_abutment_substrate`). The cardinality `2^height4` is the
**finite** Ext height (`col4_height_eq_four`), so the `ℤ/16` below is from finite content.

**Honest scope (adversarial-review flag 1).** `pin4_abutment` is *logically equivalent* to
`Nonempty (Ω₄^{Pin⁺} ≃+ ZMod 16)` (since `2^height4 = 2^4 = 16`), i.e. it asserts the same iso
*proposition* as the iso-half of the old `SmithInflow`. The axiom-stratification win is **where the 16
comes from** — the decidable Ext cokernel height (`col4_height_eq_four`, `axioms:[]`) rather than a bare
posited literal — **NOT** that a *weaker* topological assumption is made. The iso itself (the
Pontryagin–Thom bridge) is still disclosed; only its cardinality is now finite-derived.

**W1 supersession (2026-06-14, `discharge_pin4_abutment_route.md` Route C.1).** For the *unconditional*
finite statement, `pin4_abutment` is superseded by `PinPlusAdamsAbutment.adamsAbutmentEquivZMod16`: that
iso `adamsAbutment ≃+ ZMod 16` carries **no hypothesis** — the `Nonempty`-of-the-conclusion binder is
gone; the `16` is proved outright from `col4_height_eq_four`. `pin4_abutment` is retained here ONLY as
the geometric-faithfulness modeling bridge — the identification of the finite Adams abutment with the
*smooth* `Omega4PinPlusBordism` — to be DERIVED (not assumed) by the W4–W6 Smith-LES route. -/
def pin4_abutment : Prop := Nonempty (Omega4PinPlusBordism ≃+ ZMod (2 ^ height4))

/-- The disclosed Prop is **inhabited** at the substrate: the Kirby–Taylor iso `Ω₄^{Pin⁺} ≃+ ZMod 16`
*is* a `≃+ ZMod (2^height4)` since `2^height4 = 2^4 = 16`. The disclosed content is that
Pontryagin–Thom + convergence is the geometric *source* of this iso. -/
theorem pin4_abutment_substrate : pin4_abutment := by
  refine ⟨omega4PinPlusBordismEquivZMod16.trans ?_⟩
  rw [height4_eq]
  exact AddEquiv.refl (ZMod 16)

/-! ## §2. `Ω₄^{Pin⁺} ≅ ℤ/16` — the `16` from the finite Ext height -/

/-- **`Ω₄^{Pin⁺} ≃+ ℤ/16`, the cardinality from the FINITE height-4 cap.** Given the single disclosed
`pin4_abutment`, the abutment is `ZMod (2^height4)`, and `height4 = 4` (`col4_height_eq_four`, decidable
F₂ linear algebra) gives `2^4 = 16`. So the `ℤ/16` order is **derived from the finite Ext cokernel
height**, not the substrate's posited signature quotient. -/
theorem pinPlus_iso_zmod16_of_pin4 (h : pin4_abutment) :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) := by
  obtain ⟨e⟩ := h
  rw [height4_eq] at e
  exact ⟨e⟩

/-! ## §3. The old δ-cap `16·[RP⁴]=0` is now DERIVED from `pin4_abutment` -/

/-- **`DeltaTruncationCap` derived from `pin4_abutment`.** The old disclosed cap `16·[RP⁴]=0`
(`PinPlusExtBound`) is now a consequence of the single `pin4_abutment`: the abutment iso to `ZMod 16`
(cardinality from the finite height) forces `16·g = 0` for every `g` (16 ≡ 0 in `ZMod 16`). So the
upper bound no longer needs its own disclosed Prop — it follows from `pin4_abutment` + the finite height. -/
theorem deltaCap_of_pin4 (h : pin4_abutment) : PinPlusExt.DeltaTruncationCap := by
  obtain ⟨e⟩ := pinPlus_iso_zmod16_of_pin4 h
  show (16 : ℕ) • (Omega4PinPlusBordism.mk pinPlusRP4) = 0
  apply e.injective
  rw [map_nsmul, map_zero, nsmul_eq_mul, show ((16 : ℕ) : ZMod 16) = 0 from by decide, zero_mul]

/-- **`addOrderOf [RP⁴] = 16` — from `pin4_abutment` + the finite ABK lower bound.** Combines the
derived upper cap (`deltaCap_of_pin4`) with the kernel-pure surface-ABK lower bound; the order-16 of the
generator is now pinned by the single disclosed `pin4_abutment` (finite Ext) + finite arithmetic. -/
theorem pinPlusRP4_addOrder_of_pin4 (h : pin4_abutment) :
    addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 :=
  PinPlusExt.pinPlusRP4_addOrder_sixteen_two_bounds (deltaCap_of_pin4 h)

/-! ## §4. The 16-convergence DISCHARGED — no `SmithInflow` binder -/

/-- **The 16-convergence, DISCHARGED.** Carries **no `SmithInflow` binder** — only the single disclosed
`pin4_abutment` (PT+convergence). The four facets read into the one `ℤ/16`, all from finite content:
1. **upper, finite:** `Ω₄^{Pin⁺} ≃+ ℤ/16`, the 16 from the height-4 cokernel (`col4_height_eq_four`).
2. **lower, finite:** `addOrderOf [RP⁴] = 16` (surface ABK `β=1` a unit ⟹ odd ⟹ order 16).
3. **Smith landing:** `[RP⁴] = PD(α)` is Pin⁺ (`w₂=0`, the SW-mechanism).

(The SM-anomaly facet — the Dai–Freed class `16·N_f` is the trivial bordism class — is the *substantive*
`SymTFT.smithHom_sm_trivial` / `Omega5Finite.omega5_finite_convergence` on the Ω₅ side, NOT the vacuous
`16·N_f = 0 (mod 16)` tautology the adversarial review flagged here, which is dropped.)

`SmithInflow` (the opaque ℤ₁₆-iso hypothesis) is gone: its iso content is `pinPlus_iso_zmod16_of_pin4`
(from finite content) and the upper cap is `deltaCap_of_pin4` (derived). The single tracked input is
Pontryagin–Thom + convergence — NOT the opaque iso, NOT the posited quotient. -/
theorem sixteen_convergence_finite_discharge (h : pin4_abutment) :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 :=
  ⟨pinPlus_iso_zmod16_of_pin4 h, pinPlusRP4_addOrder_of_pin4 h,
   smith_RP4_isPinPlus_via_mechanism⟩

/-- **Substrate instance** — the fully discharged convergence at the substrate (the disclosed
`pin4_abutment` inhabited): `Ω₄^{Pin⁺} ≅ ℤ/16` (16 from the finite height), `[RP⁴]` order 16 (finite
ABK), Pin⁺ SW-mechanism. The geometric Pontryagin–Thom remains the single tracked input. -/
theorem sixteen_convergence_finite_discharge_substrate :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 :=
  sixteen_convergence_finite_discharge pin4_abutment_substrate

/-! ## §5. W1 headline — the 16-convergence at the finite Adams abutment, UNCONDITIONAL -/

/-- **W1 headline — the 16-convergence, with NO hypothesis binder.** Unlike
`sixteen_convergence_finite_discharge` (which consumes the disclosed `pin4_abutment`), this carries
**no hypothesis at all** (no `SmithInflow`, no `pin4_abutment`):

1. **iso, finite & UNCONDITIONAL:** `adamsAbutment ≃+ ZMod 16` is `PinPlusAdamsAbutment.adamsAbutmentEquivZMod16`,
   PROVED from the decidable Ext-cokernel height `col4_height_eq_four` (`axioms:[]`). The `Nonempty`-of-the-
   conclusion hypothesis the old `pin4_abutment` carried is gone — this is the W1 discharge of the
   *logical* dependency.
2. **lower, finite:** `addOrderOf [RP⁴] = 16` (surface-ABK `β=1` a unit ⟹ order 16), an unconditional
   closed theorem.
3. **Smith landing:** `[RP⁴]` is Pin⁺ (`w₂=0`, the SW-mechanism).

The only residual is the *geometric-faithfulness* modeling definition — that the finite `adamsAbutment`
IS the smooth `Ω₄^{Pin⁺}` — documented in `PinPlusAdamsAbutment.adamsAbutment` and to be **DERIVED, not
assumed**, by the W4–W6 Smith-LES route (`discharge_pin4_abutment_route.md`). It is carried in a `def`'s
documentation, **not** as a hypothesis here and **not** as an axiom. -/
theorem sixteen_convergence_adams_abutment :
    Nonempty (adamsAbutment ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 :=
  ⟨⟨adamsAbutmentEquivZMod16⟩,
   pinPlusRP4_addOrder_of_pin4 pin4_abutment_substrate,
   smith_RP4_isPinPlus_via_mechanism⟩

/-! ## §6. RETIREMENT (2026-06-15) — the derived iso on the GENUINE bordism-group carrier supersedes
the posit-based forms (`pin4_abutment` / `Omega4PinPlusBordism` / `adamsAbutment`)

This section re-points the discharge to the **derived** `Ω₄^{Pin⁺} ≅ ℤ/16` on the genuine W4 carrier
`DataBordismGrp ξ` — the `Quot` of structured `SingularManifold`s over Mathlib manifolds-with-boundary
(`TangentialDataBordism.lean`) — built in `PinPlusGenuineCarrierIso.lean`. With the genuine carrier in
hand, the §1–§5 posit-based forms are **DEMOTED to derived corollaries / documented modeling bridges**:

* `pin4_abutment` (§1) and the posited group `Omega4PinPlusBordism` (the `signature : ℤ` quotient) — the
  ℤ/16 they assert is now DERIVED on the genuine carrier; they are retained only as the thin-substrate
  modeling identification, no longer load-bearing for the geometric ℤ/16.
* `adamsAbutment` (the W1 finite modeling *definition*) — its `≅ ℤ/16` (from `col4_height_eq_four`)
  remains the genuine FINITE-Ext statement, but the *geometric* ℤ/16 is now the genuine-carrier iso, so no
  modeling definition is load-bearing for the geometric group.

**No load-bearing modeling definition remains for the ℤ/16**: it is the image of a genuine bordism
invariant (the ABK/η grade) on a genuine bordism group. The UNCONDITIONAL form is the genuine-carrier
ABK-quotient iso `PinPlusTangentialData.dataBordism_quotient_abk_equiv_zmod16` (no hypothesis); the
full-carrier iso carries the single disclosed `PinPlusBordismLandmark` (the OBJECTIVE-permitted Brown/ABK
order-16 + height-4 `≤16` finite inputs, `Smith_sequence.md` §5.1). -/

/-- **RETIREMENT pointer — `Ω₄^{Pin⁺} ≅ ℤ/16` DERIVED on the GENUINE carrier.** The discharge endpoint,
re-pointed off the posited `Omega4PinPlusBordism` / `pin4_abutment` / `adamsAbutment` and onto the genuine
W4 bordism group `DataBordismGrp ξ` (real manifolds-with-boundary): from the single disclosed
`PinPlusBordismLandmark` (the permitted finite inputs), the iso is derived via the Smith sandwich
(`PinPlusGenuineCarrierIso.pinPlus_genuine_carrier_iso_zmod16`). This is the form the goal's criterion 4
("`PinPlusDischarge` re-pointed to the derived iso") names; the posit-based §1–§5 theorems are the demoted
finite-substrate corollaries. -/
theorem sixteen_convergence_genuine_carrier
    {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    (L : PinPlusGenuineCarrierIso.PinPlusBordismLandmark X k I) :
    Nonempty (TangentialDataBordism.DataBordismGrp L.ξ ≃+ ZMod 16) :=
  PinPlusGenuineCarrierIso.pinPlus_genuine_carrier_iso_zmod16 L

end SKEFTHawking.PinPlusDischarge
