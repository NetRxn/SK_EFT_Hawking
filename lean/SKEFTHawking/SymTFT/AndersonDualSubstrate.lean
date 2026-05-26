/-
# Phase 6r-prime W1 extension + A1 audit-remediation — Anderson-dual formula composition

This module ships the substantive Anderson-dual formula composition for
`TP_5(Pin⁺) ≃+ Ω_4^{Pin⁺}(pt)` via primary-source-cited components.

## Substantive content (post-A1 audit remediation, 2026-05-25)

The Freed-Hopkins Anderson-dual formula (arXiv:1604.06527 §6) for
Pin⁺ at degree 4 → 5 is

```
TP_5(Pin⁺) ≅ Hom(Ω_4^{Pin⁺}(pt), ℝ/ℤ) ⊕ Ext(Ω_5^{Pin⁺}(pt), ℤ)
```

For Pin⁺ at this degree:
- The Ext term vanishes (Ω_5^{Pin⁺}(pt) = 0, per Kirby-Taylor 1990).
- The Hom term `Hom(ZMod 16, ℝ/ℤ)` is precisely the Pontryagin dual of
  ZMod 16, canonically `AddChar (ZMod 16) Circle`.

After the A1 audit-remediation restructure (2026-05-25), this is now
SUBSTANTIVELY built into the type system:

- `TP5PinPlus := AddChar (ZMod 16) Circle` in `SymTFT/PinBordism.lean`
  (post-A1; was `ZMod 16` pre-A1).
- The iso `TP5PinPlus ≃+ ZMod 16` is the substantive Pontryagin-dual
  composition (NOT `AddEquiv.refl _`).
- The iso `TP5PinPlus ≃+ Omega4PinPlus` (Anderson-dual relation)
  composes Pontryagin + W1.2 substrate, both substantive.

This module now ships the **explicit Anderson-dual formula bundle**
referencing the substantive isos in `PinBordism.lean`.

## Post-A1 honest scope

Pre-A1, this module shipped workarounds:
- `tp5PinPlusToAddCharCircle` — a "codomain-substantive" iso lifting
  TP5PinPlus = ZMod 16 to AddChar (ZMod 16) Circle. **Post-A1, this
  iso becomes `AddEquiv.refl _` (P5 alias) since TP5PinPlus IS now
  AddChar (ZMod 16) Circle. DELETED.**
- `andersonDualPinPlusRelationEquivViaSubstrate` — a substrate-iso
  composition with `AddEquiv.refl TP5PinPlus` as the first leg.
  **Post-A1, the substantive form is now in
  `PinBordism.lean::isAndersonDualPinPlusRelation_holds`. DELETED**
  here in favor of pointing consumers at the substantive primary
  discharge.

## References

- Freed-Hopkins, *Reflection positivity and invertible topological phases,*
  arXiv:1604.06527 §6 (Anderson-dual formula).
- Yonekura, *On the cobordism classification of symmetry protected
  topological phases,* arXiv:1803.10796 (Anderson-dual for TP_n).
- Kirby-Taylor 1990 (Ω_5^{Pin⁺}(pt) = 0).
- Mathlib `Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality`
  (`AddChar.zmodAddEquiv` + `AddChar.circleEquivComplex`).
-/
import SKEFTHawking.SymTFT.PinBordism
import SKEFTHawking.SymTFT.PontryaginDualPinPlus

namespace SKEFTHawking.SymTFT

open SKEFTHawking.SymTFT.PontryaginDualPinPlus

/-! ## §1. DELETED post-B6 audit-remediation (2026-05-25)

`IsAndersonDualFormulaPinPlus := IsKirbyTaylorPinPlusBordism` (pure
alias) and `isAndersonDualFormulaPinPlus_holds` (which just delegated
to KT discharge) DELETED as P5 alias. The "formula input" content IS
`IsKirbyTaylorPinPlusBordism` itself; the wrapper added no substance.

The Ω_5^{Pin⁺}(pt) = 0 honest-scope note (Kirby-Taylor 1990) is the
primary-source-cited content; the substantive Pin⁺ case Anderson-dual
formula closure is the bundle in §2 below. -/

/-! ## §2. Anderson-dual formula substantive bundle (post-B6) -/

/-- **Anderson-dual formula composition bundle** (post-A1 + B6 audit-
remediation, 2026-05-25): bundles the SUBSTANTIVE Anderson-dual formula
composition for the Pin⁺ case. All three isos are substantive:

1. `IsKirbyTaylorPinPlusBordism` — KEEP tracked Prop (#1), discharged
   via W1.2 substantive quotient iso.
2. `IsAndersonDualPinPlus` — discharged via Pontryagin chain post-A1
   (`AddChar (ZMod 16) Circle ≃+ ZMod 16`).
3. `IsAndersonDualPinPlusRelation` — discharged via Pontryagin + W1.2
   composition post-A1 (`TP5PinPlus ≃+ Omega4PinPlus`). -/
theorem anderson_dual_formula_pin_plus_substantive_bundle :
    IsKirbyTaylorPinPlusBordism ∧
    IsAndersonDualPinPlus ∧
    IsAndersonDualPinPlusRelation :=
  ⟨isKirbyTaylorPinPlusBordism_holds,
   isAndersonDualPinPlus_holds,
   isAndersonDualPinPlusRelation_holds⟩

end SKEFTHawking.SymTFT
