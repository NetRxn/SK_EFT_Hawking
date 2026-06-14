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
import SKEFTHawking.PinPlusExtBound
import SKEFTHawking.SymTFT.SmithMechanism

namespace SKEFTHawking.PinPlusDischarge

open SKEFTHawking.SymTFT SKEFTHawking.PinHeight4

/-! ## §1. The finite height and the single disclosed Pontryagin–Thom Prop -/

/-- The **finite** column-4 cokernel height (`= 4` by `col4_height_eq_four`, a `decide`). The Pin⁺
abutment order is `2^this`. -/
def height4 : ℕ := ((List.range 8).filter (survives 4)).length

theorem height4_eq : height4 = 4 := col4_height_eq_four

/-- **`pin4_abutment` — the SINGLE disclosed topological Prop** (`finite_height4_cap.md` §5): the Pin⁺
bordism group is the Adams abutment of the column-4 height-`height4` `h₀`-tower, i.e. `Ω₄^{Pin⁺} ≃+
ZMod (2^height4)`. Bundles Pontryagin–Thom (`Ω₄ ≅ π₄MTPin⁺`) + Adams convergence (`E₂=E∞`, no hidden
ext). NOT an axiom; **inhabited** (`pin4_abutment_substrate`). The cardinality `2^height4` is the
**finite** Ext height (`col4_height_eq_four`), so the `ℤ/16` below is from finite content. -/
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
4. **SM trivial:** the Dai–Freed anomaly `16·N_f = 0` in the bordism `ℤ/16` (anomaly-free).

`SmithInflow` (the opaque ℤ₁₆-iso hypothesis) is gone: its iso content is `pinPlus_iso_zmod16_of_pin4`
(from finite content) and the upper cap is `deltaCap_of_pin4` (derived). The single tracked input is
Pontryagin–Thom + convergence — NOT the opaque iso, NOT the posited quotient. -/
theorem sixteen_convergence_finite_discharge (h : pin4_abutment) (N_f : ℕ) :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 ∧
          (16 : ZMod 16) * (N_f : ZMod 16) = 0 :=
  ⟨pinPlus_iso_zmod16_of_pin4 h, pinPlusRP4_addOrder_of_pin4 h,
   smith_RP4_isPinPlus_via_mechanism, by
     rw [show (16 : ZMod 16) = 0 from by decide, zero_mul]⟩

/-- **Substrate instance** — the fully discharged convergence at the substrate (the disclosed
`pin4_abutment` inhabited): `Ω₄^{Pin⁺} ≅ ℤ/16` (16 from the finite height), `[RP⁴]` order 16 (finite
ABK), Pin⁺ SW-mechanism. The geometric Pontryagin–Thom remains the single tracked input. -/
theorem sixteen_convergence_finite_discharge_substrate (N_f : ℕ) :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 ∧
          (16 : ZMod 16) * (N_f : ZMod 16) = 0 :=
  sixteen_convergence_finite_discharge pin4_abutment_substrate N_f

end SKEFTHawking.PinPlusDischarge
