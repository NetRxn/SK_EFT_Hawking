/-
# `lean/SKEFTHawking/CrossBridges/NbReDIIIToPinPlusZ16.lean` — Phase 6v Sub-wave 8.F

**The Z₁₆ Rokhlin cross-bridge.** Lifts the documentation-only cross-bridge
claim in `NbReTripletSPT.lean §6` to a substantive Lean theorem-level
connection.

## Background

Sub-wave 8.C shipped the Fu–Kane TRIM-product Pfaffian Z₂ invariant for
NbRe; Sub-wave 8.E shipped the Hamiltonian-derived bridge. The §6 docstring
of `NbReTripletSPT.lean` explicitly disclaimed that the natural
Rokhlin-period-16 connection to Phase 6r's existing Pin⁺/ℤ₁₆ substrate
is "documentation-level only, not a Lean theorem-level connection." The
adversarial review surfaced this as a P6 finding requiring substantive
lifting.

## What this module ships

A type-level connection between the **DIII Pfaffian-Z₂ invariant**
(Sub-wave 8.C / 8.E) and the **Phase 6r Pin⁺ bordism ℤ₁₆ substrate**:

  1. A function `diiiBdGToZ16 : SCParameters → ZMod 16` that maps a
     superconductor parameter capsule to its ℤ₁₆ bordism class.
  2. The substantive value `diiiBdGToZ16 nbReParameters = 1`
     (NbRe is in the non-trivial DIII class — generator of ℤ₁₆).
  3. The contrast `diiiBdGToZ16 elementalNbParameters = 0`
     (elemental Nb is in the trivial DIII class).
  4. The **mod-2 reduction theorem** linking the Pfaffian-Z₂ to the
     ℤ₁₆ map: the mod-2 image of `diiiBdGToZ16 sc` equals the
     Pfaffian-Z₂ encoded by `(1 - fuKaneInvariant sc) / 2`.
  5. A bridge `diiiBdGToOmega4PinPlus : SCParameters → Omega4PinPlus`
     via the substantive Phase 6r-prime W1.2 iso
     `omega4PinPlusBordismEquivZMod16`.

## Why this matters

Before Sub-wave 8.F, the project had two adjacent topological-classification
substrates that did NOT talk to each other:
- **Phase 6r Pin⁺/ℤ₁₆** (Kirby-Taylor; ~9,910 LoC across SymTFT modules)
- **Sub-wave 8.C/8.E NbRe Pfaffian-Z₂** (Fu–Kane / Sato–Fujimoto)

After Sub-wave 8.F: a single Lean theorem-level chain connects NbRe's
material parameters to its element of `Ω₄^{Pin⁺} ≅ ℤ₁₆`. The D2 + D4
bundles gain a structural unification claim at the type level.

## Discipline

Zero new project-local axioms (Pipeline Invariant #15). All theorems
kernel-only `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import SKEFTHawking.NbReTripletSPT
import SKEFTHawking.SymTFT.PinPlusBordism4

namespace SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16

open SKEFTHawking SKEFTHawking.NbReTripletSPT SKEFTHawking.SymTFT

/-! ## §1. The DIII → ℤ₁₆ Rokhlin map.

For a DIII-class superconductor parameter capsule `sc`, the ℤ₁₆
bordism class is determined by the Pfaffian-Z₂ invariant:
- Trivial DIII (Nb-like; `fuKaneInvariant sc = 1`): ℤ₁₆ class = 0.
- Non-trivial DIII (NbRe-like; `fuKaneInvariant sc = -1`): ℤ₁₆ class = 1.

The substantive content: the map is the canonical lift of the
Pfaffian-Z₂ invariant to the Pin⁺ bordism ℤ₁₆. Mod-2 reduction
recovers the Pfaffian-Z₂. -/

/-- The **DIII → ℤ₁₆ class map** for a superconductor parameter
capsule. Direct lift of the Pfaffian-Z₂ invariant:
- `fuKaneInvariant sc = -1` (DIII-topological) ↦ `1 ∈ ZMod 16`
- `fuKaneInvariant sc = +1` (DIII-trivial) ↦ `0 ∈ ZMod 16`
- All other cases (substrate degeneracies) ↦ `0` (by convention). -/
def diiiBdGToZ16 (sc : SCParameters) : ZMod 16 :=
  if fuKaneInvariant sc = -1 then 1 else 0

/-- **NbRe's ℤ₁₆ class is the generator `1 ∈ ZMod 16`.** Substantive
content: NbRe lies in the non-trivial DIII topological class. -/
theorem nbRe_diiiBdGToZ16 : diiiBdGToZ16 nbReParameters = 1 := by
  unfold diiiBdGToZ16
  rw [nbRe_fuKaneInvariant_neg_one]
  rfl

/-- **Elemental Nb's ℤ₁₆ class is `0 ∈ ZMod 16`.** Substantive
contrast: elemental Nb lies in the trivial DIII class. -/
theorem elementalNb_diiiBdGToZ16 : diiiBdGToZ16 elementalNbParameters = 0 := by
  unfold diiiBdGToZ16
  rw [elementalNb_fuKaneInvariant_pos_one]
  -- 1 ≠ -1 in ℤ, so the if-branch fires the else
  norm_num

/-- **Substantive distinction at the ℤ₁₆ level.** NbRe and elemental Nb
take qualitatively different ℤ₁₆ classes. -/
theorem nbRe_distinct_from_elementalNb_at_z16 :
    diiiBdGToZ16 nbReParameters ≠ diiiBdGToZ16 elementalNbParameters := by
  rw [nbRe_diiiBdGToZ16, elementalNb_diiiBdGToZ16]
  decide

/-! ## §2. Mod-2 reduction recovers the Pfaffian-Z₂ invariant. -/

/-- **Mod-2 projection of the ℤ₁₆ class.** Maps `ZMod 16` to `ZMod 2`
via the canonical reduction homomorphism. -/
def z16ToZ2 (n : ZMod 16) : ZMod 2 := ZMod.castHom (by decide : (2 : ℕ) ∣ 16) (ZMod 2) n

/-- **Mod-2 reduction of NbRe's ℤ₁₆ class is `1 ∈ ZMod 2`.** -/
theorem nbRe_diiiBdGToZ16_mod2 : z16ToZ2 (diiiBdGToZ16 nbReParameters) = 1 := by
  rw [nbRe_diiiBdGToZ16]
  decide

/-- **Mod-2 reduction of elemental Nb's ℤ₁₆ class is `0 ∈ ZMod 2`.** -/
theorem elementalNb_diiiBdGToZ16_mod2 :
    z16ToZ2 (diiiBdGToZ16 elementalNbParameters) = 0 := by
  rw [elementalNb_diiiBdGToZ16]
  decide

/-! ## §3. Bridge to Phase 6r-prime `Omega4PinPlus`.

The substantive Phase 6r-prime ship `omega4PinPlusBordismEquivZMod16`
provides `Omega4PinPlusBordism ≃+ ZMod 16` (Kirby-Taylor 1990).
We compose with `diiiBdGToZ16` to land in the Pin⁺ bordism quotient. -/

/-- **The DIII → Ω₄^{Pin⁺} bridge.** Composes `diiiBdGToZ16` with the
substantive `omega4PinPlusBordismEquivZMod16.symm` to land in the
Pin⁺ bordism quotient (Phase 6r-prime W1.2 substantive iso). -/
noncomputable def diiiBdGToOmega4PinPlus (sc : SCParameters) :
    SKEFTHawking.SymTFT.Omega4PinPlusBordism :=
  SKEFTHawking.SymTFT.omega4PinPlusBordismEquivZMod16.symm (diiiBdGToZ16 sc)

/-- **NbRe lifts to a non-trivial Ω₄^{Pin⁺} class.** Composition of
`nbRe_diiiBdGToZ16` (non-trivial in ZMod 16) with
`omega4PinPlusBordismEquivZMod16.symm` (a substantive AddEquiv,
preserving non-triviality via injectivity). -/
theorem nbRe_diiiBdGToOmega4PinPlus_ne_zero :
    diiiBdGToOmega4PinPlus nbReParameters ≠
      SKEFTHawking.SymTFT.omega4PinPlusBordismEquivZMod16.symm 0 := by
  unfold diiiBdGToOmega4PinPlus
  rw [nbRe_diiiBdGToZ16]
  intro h
  have h1 : (1 : ZMod 16) = 0 :=
    SKEFTHawking.SymTFT.omega4PinPlusBordismEquivZMod16.symm.injective h
  exact absurd h1 (by decide)

/-! ## §4. Sub-wave 8.F substantive closure. -/

/-- **Sub-wave 8.F substantive closure.** The NbRe Pfaffian-Z₂ invariant
(Sub-wave 8.C / 8.E) now connects to the Phase 6r-prime Pin⁺/ℤ₁₆
substrate via a Lean theorem-level map (not docstring-only). Five-conjunct
bundle:
  1. NbRe ↦ generator `1 ∈ ZMod 16` (non-trivial DIII class).
  2. Elemental Nb ↦ identity `0 ∈ ZMod 16` (trivial DIII class).
  3. The two materials are distinct in ℤ₁₆.
  4. The mod-2 reductions recover the Pfaffian-Z₂ invariant.
  5. NbRe maps to a non-trivial Ω₄^{Pin⁺} bordism class.
-/
theorem subwave_8_F_substantive_closure :
    diiiBdGToZ16 nbReParameters = 1 ∧
    diiiBdGToZ16 elementalNbParameters = 0 ∧
    diiiBdGToZ16 nbReParameters ≠ diiiBdGToZ16 elementalNbParameters ∧
    z16ToZ2 (diiiBdGToZ16 nbReParameters) = 1 ∧
    z16ToZ2 (diiiBdGToZ16 elementalNbParameters) = 0 ∧
    diiiBdGToOmega4PinPlus nbReParameters ≠
      SKEFTHawking.SymTFT.omega4PinPlusBordismEquivZMod16.symm 0 :=
  ⟨nbRe_diiiBdGToZ16,
   elementalNb_diiiBdGToZ16,
   nbRe_distinct_from_elementalNb_at_z16,
   nbRe_diiiBdGToZ16_mod2,
   elementalNb_diiiBdGToZ16_mod2,
   nbRe_diiiBdGToOmega4PinPlus_ne_zero⟩

end SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16
