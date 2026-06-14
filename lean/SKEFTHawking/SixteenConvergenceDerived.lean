/-
# Phase 5q.F W7 — the 16-convergence with `SmithInflow`'s content REFINED (order derived, Smith SW-mechanized)

This is the Phase 5q.F capstone: it takes the conditional, opaque-`SmithInflow` 16-convergence of
`CommonOrigin.lean` (Phase 5q.E) and **refines the opaque hypothesis into transparent content** —
replacing the bare `SmithInflow` Lean binder with (a) the **constructed** Smith homomorphism `smithHom`
(`SpinZ4Bordism5.lean`), (b) the shared ℤ₁₆ generator's order **DERIVED from two independent bounds**
(`PinPlusExtBound.lean`: surface-ABK lower + Ext δ-cap upper), and (c) the Smith map's **Stiefel–Whitney
landing mechanism** `w₂(N)=0 ⟹ Pin⁺` (`SmithMechanism.lean`).

## What this IS, and what it is NOT (read before quoting — the 5q.E over-claim discipline)

**IS (a genuine refinement):** the capstone `sixteen_convergence_derived_substrate` states the
convergence with **no `SmithInflow` binder**, and its order-16 of `[RP⁴]` is no longer the substrate's
*posited* quotient relation (`pinPlusRP4_class_order_exact_sixteen`) — it is **pinched by two
independent, mostly-kernel-pure bounds**: the lower from the genuine surface ABK Gauss sum
(`β(RP²)=1` a unit ⟹ odd ⟹ order ≥ 16) and the upper from the Ext δ-truncation cap (height 4 ⟹
`16·[RP⁴]=0`). The Smith landing is backed by the actual SW obstruction arithmetic, not a content-free
ℤ₁₆ composite.

**IS NOT (do NOT quote as this):** "geometrically unconditional" or "`SmithInflow` discharged in the
geometric sense." The thin substrates `Omega4PinPlusBordism` / `Omega5SpinZ4Bordism` still **assign**
their invariants (`signature` / `daiFreed`) rather than computing them from manifolds; and the deep
topological landmarks — **Pontryagin–Thom** `Ω₄^{Pin⁺} ≅ π₄(MTPin⁺)`, **ABP splitting**, the **Campbell
δ-truncation** height-4 cap, the genuine **η-invariant** and **manifold-level bordism** construction —
remain **disclosed, cited Props** (the H1–H4 pattern of `ExtBordismBridge.lean`), Mathlib-absent, NOT
axioms. The refinement *decomposes the one opaque `SmithInflow`* into these named, individually-true
pieces (most built/derived, a few disclosed) — it does not eliminate the geometric tracked gap. Per
`[[project_phase5qE_sixteenconv]]`: the honest middle is "built where buildable, scoped precisely."

## The three new ingredients vs. `CommonOrigin`
  - order **derived**: `PinPlusExt.pinPlusRP4_addOrder_sixteen_substrate` (`addOrderOf [RP⁴] = 16`).
  - Smith **SW-mechanism**: `SymTFT.smith_RP4_isPinPlus_via_mechanism` (`IsPinPlusObstruction RP4`).
  - constructed Smith: `SymTFT.smithHom` (`SpinZ4Bordism5.lean`), already in `CommonOrigin` W6.

## References
  - `CommonOrigin.lean` (the conditional convergence this refines), `PinPlusExtBound.lean` (two-bounds
    pinch), `SymTFT/SmithMechanism.lean` (SW landing), `SymTFT/SpinZ4Bordism5.lean` (constructed Smith).
  - Campbell arXiv:1708.04264 Thm 6.7; Kirby–Taylor 1990; García-Etxebarria–Montero arXiv:1808.00009.
-/
import Mathlib
import SKEFTHawking.CommonOrigin
import SKEFTHawking.PinPlusExtBound
import SKEFTHawking.SymTFT.SmithMechanism

namespace SKEFTHawking.SixteenConvergenceDerived

open SKEFTHawking.SymTFT SKEFTHawking.CommonOrigin

/-- **The 16-convergence with `SmithInflow`'s content refined (Phase 5q.F capstone).** No `SmithInflow`
binder: the constructed `smithHom` carries the chain `SM → Ω₅^{Spin-ℤ₄} → Smith → Ω₄^{Pin⁺}`, and the
shared ℤ₁₆ generator `[RP⁴]` now has its order **pinned by two bounds** and its Pin⁺-landing
**SW-mechanized**:

1. **SM anomaly trivial** (`smithHom_sm_trivial`): the Dai–Freed class `16·N_f` lands at `0 ∈ Ω₄^{Pin⁺}`.
2. **Smith gen = `[RP⁴]`** (`smithHom_gen`): the Ω₅ generator maps to the Pin⁺ generator.
3. **order pinned by two bounds** (`pinPlusRP4_addOrder_sixteen_substrate`): `addOrderOf [RP⁴] = 16`
   from the surface-ABK lower bound (the genuine `β = 1` unit value) and the Ext δ-cap upper bound. Honest
   scope (PinPlusExtBound CRITICAL-2): for the *concrete* `[RP⁴]` the class `= 1` is fixed via the posited
   `signature = 1` and the ABK supplies the order-forcing value; the posit-free order-16 is the `∀ g` lemma.
4. **Smith SW-mechanism** (`smith_RP4_isPinPlus_via_mechanism`): `[RP⁴] = PD(α) ⊂ RP⁵` genuinely lands
   in Pin⁺ because `w₂(RP⁴) = 0` (Whitney `+` Spin-ℤ₄, Karoubi binomials).

**Scope:** a refinement of the opaque `SmithInflow` into transparent content, NOT a geometric discharge
(Pontryagin–Thom / ABP / δ-truncation / manifold bordism remain disclosed cited Props; see header). -/
theorem sixteen_convergence_derived_substrate (N_f : ℕ) :
    smithHom (Omega5SpinZ4Bordism.mk (smSpinZ4Class N_f)) = 0 ∧
      smithHom (Omega5SpinZ4Bordism.mk spinZ4Gen) = Omega4PinPlusBordism.mk pinPlusRP4 ∧
        addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
          IsPinPlusObstruction RP4 :=
  ⟨smithHom_sm_trivial N_f, smithHom_gen,
   PinPlusExt.pinPlusRP4_addOrder_sixteen_substrate, smith_RP4_isPinPlus_via_mechanism⟩

/-- **The conditional form** (still accepting a `SmithInflow S`, for the facet-pointwise readings that
need it), now *augmented* with the two new derived facts. Shows the refinement composes with
`CommonOrigin`'s pointwise Rokhlin = Kitaev reading: for the disclosed inflow `S`, the Kitaev generator
maps to `[RP⁴]`, which has **derived** order 16 and is **SW-mechanism** Pin⁺. -/
theorem sixteen_convergence_derived (S : SmithInflow) (N_f : ℕ) :
    S.smith (16 * (N_f : ZMod 16)) = 0 ∧
      S.smith (Kitaev16.kitaevClass 1) = Omega4PinPlusBordism.mk pinPlusRP4 ∧
        addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
          IsPinPlusObstruction RP4 :=
  ⟨sm_anomaly_trivial_in_bordism S N_f, kitaev_generator_is_bordism_generator S,
   PinPlusExt.pinPlusRP4_addOrder_sixteen_substrate, smith_RP4_isPinPlus_via_mechanism⟩

end SKEFTHawking.SixteenConvergenceDerived
