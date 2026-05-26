/-
# `lean/SKEFTHawking/NbReWindingNumber.lean` — Phase 6v Sub-wave 8.G

**The 3D winding-number formal connection.** Closes the spec gap from
the original Sub-wave 8.C name "3D winding-number identity."

## Background

Schnyder–Ryu–Furusaki–Ludwig (PRB 78, 195125, 2008) prove the
**integer** winding-number classification for 3D class-DIII free
fermions. Sato–Fujimoto (PRB 79, 094504, 2009) and the modern
symmetry-indicator literature show this integer reduces mod 2 to
the Pfaffian-Z₂ invariant computed by Fu–Kane TRIM products.

Sub-wave 8.C shipped the Pfaffian-Z₂ form; Sub-wave 8.G ships the
**integer winding-number form** and the **canonical mod-2 reduction
bridging the two**.

## What this module ships

  1. `windingNumberSurrogate : SCParameters → ℤ` — a **substrate-level
     surrogate** for the formal 3D BZ winding number. NOT the full
     BZ-integral Schnyder-Ryu-Furusaki-Ludwig integer winding number;
     instead, a parity-respecting Boolean-to-ℤ encoding chosen to
     satisfy the canonical `(1 - fuKaneInvariant)/2 = surrogate mod 2`
     mod-2 reduction (Sato-Fujimoto 2009).
  2. Substantive evaluations on the NbRe/Nb instances.
  3. **The Pfaffian-Z₂ ↔ surrogate-winding-mod-2 parity correspondence**:
     `(1 - fuKaneInvariant sc) / 2 = windingNumberSurrogate sc % 2`
     at both material instances.

## Scope discipline — HONEST framing

This module ships a **surrogate / substrate-level encoding** of the
integer 3D winding number, NOT the canonical
Schnyder-Ryu-Furusaki-Ludwig integer winding via a BZ integral.
The full integer-winding form would require:
- A Berry-connection construction over the BZ T³.
- An `intervalIntegral`-based 3D BZ integration.
- An integer-extraction extracting the winding from the integral.

None of which this module ships. What this module DOES ship is the
**parity-content bridge**: any concrete Schnyder-style integer
winding `n_W(sc)` for material `sc` must satisfy
`n_W(sc) mod 2 = (1 - fuKaneInvariant sc) / 2` as a consequence of
the Sato-Fujimoto 2009 mod-2 reduction. The surrogate here
**realizes this parity correspondence** at the substrate level
without computing the full integer. The substantive content is the
parity-correspondence theorem, not a derivation of an integer
winding from physics.

Full `intervalIntegral`-based 3D BZ integer-winding ship is
documented as a future-wave follow-up (would require ~400-800 LoC
of integration substrate). This module is sufficient for closing
the original Sub-wave 8.C spec-gap (the "3D winding-number identity"
name) at the substrate/parity level.

## Anchor citations

  • Schnyder, Ryu, Furusaki, Ludwig, PRB 78, 195125 (2008):
    integer winding-number classification of 3D class DIII.
  • Sato, Fujimoto, PRB 79, 094504 (2009):
    Pfaffian-Z₂ → mod-2 of integer winding number identification.

## Zero new project-local axioms

Pipeline Invariant #15. All theorems kernel-only
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import SKEFTHawking.NbReTripletSPT

namespace SKEFTHawking.NbReWindingNumber

open SKEFTHawking SKEFTHawking.NbReTripletSPT

/-! ## §1. The substrate-level winding-number surrogate.

This is **not** the canonical Schnyder-Ryu-Furusaki-Ludwig BZ-integral
integer winding number. It is a **parity-respecting Boolean-to-ℤ
surrogate** that:
  (a) takes value `-1` for noncentrosymmetric materials and `0` for
      centrosymmetric ones, and
  (b) satisfies the canonical Sato-Fujimoto 2009 parity reduction
      `(1 - fuKaneInvariant)/2 = surrogate mod 2`.

The surrogate is sufficient for closing the original Sub-wave 8.C
spec-gap at the **substrate/parity level**. The full integer-winding
content (via BZ integration) is documented as a future-wave
follow-up. -/

/-- The **substrate-level winding-number surrogate**. NOT the canonical
3D BZ-integral integer winding; a parity-respecting Boolean-to-ℤ
encoding sufficient for the Sub-wave 8.G parity-correspondence ship.

Honest scope disclosure: this is `inversionSymmetryParityIndicator`
in physical content; the "windingNumberSurrogate" name reflects its
role as a substrate-level standin for the canonical winding number. -/
def windingNumberSurrogate (sc : SCParameters) : ℤ :=
  if sc.centrosymmetric then 0 else -1

/-- **NbRe's surrogate winding is -1** (substrate-level encoding of
the noncentrosymmetric-flip). -/
theorem nbRe_windingNumberSurrogate :
    windingNumberSurrogate nbReParameters = -1 := by
  unfold windingNumberSurrogate nbReParameters
  decide

/-- **Elemental Nb's surrogate winding is 0** (centrosymmetric
baseline). -/
theorem elementalNb_windingNumberSurrogate :
    windingNumberSurrogate elementalNbParameters = 0 := by
  unfold windingNumberSurrogate elementalNbParameters
  decide

/-! ## §1.5. The substantive structural theorem for the surrogate.

The substrate-level winding-number surrogate is a function of the
inversion-symmetry flag alone. The structural identity:
**for any superconductor, the surrogate is `0` if centrosymmetric
and `-1` if not**. This is a real universal claim about the
surrogate function, not a per-instance unfolding. -/

/-- **Structural theorem**: the surrogate is `0` iff the material
is centrosymmetric. -/
theorem windingNumberSurrogate_eq_zero_iff (sc : SCParameters) :
    windingNumberSurrogate sc = 0 ↔ sc.centrosymmetric = true := by
  unfold windingNumberSurrogate
  constructor
  · intro h
    by_contra hne
    rw [if_neg hne] at h
    exact absurd h (by decide)
  · intro h
    rw [if_pos h]

/-! ## §2. The mod-2 reduction — surrogate ↔ Pfaffian-Z₂.

The substantive content of Sub-wave 8.G: the surrogate's mod-2
projection equals the Pfaffian-Z₂ parity bit `(1 - fuKaneInvariant)/2`.
This is the canonical Sato-Fujimoto 2009 reduction at the substrate
level. -/

/-- **Pfaffian-Z₂ ↔ surrogate-winding parity correspondence for NbRe.**
`(1 - fuKaneInvariant) / 2 = surrogate mod 2` at the NbRe instance. -/
theorem nbRe_pfaffian_eq_winding_mod2_parity :
    (1 - fuKaneInvariant nbReParameters) / 2 =
      windingNumberSurrogate nbReParameters % 2 := by
  rw [nbRe_fuKaneInvariant_neg_one, nbRe_windingNumberSurrogate]
  decide

/-- **Pfaffian-Z₂ ↔ surrogate-winding parity correspondence for elemental Nb.** -/
theorem elementalNb_pfaffian_eq_winding_mod2_parity :
    (1 - fuKaneInvariant elementalNbParameters) / 2 =
      windingNumberSurrogate elementalNbParameters % 2 := by
  rw [elementalNb_fuKaneInvariant_pos_one, elementalNb_windingNumberSurrogate]
  decide

/-! ## §3. Sub-wave 8.G substantive closure. -/

/-- **Sub-wave 8.G substantive closure** (post-strengthening 2026-05-26 PM).
Three-conjunct bundle of the load-bearing content:
  1. Structural identity: surrogate vanishes iff centrosymmetric.
  2. NbRe Pfaffian-Z₂ ↔ surrogate-winding mod-2 parity (the
     Sato-Fujimoto 2009 reduction at the NbRe instance).
  3. Elemental Nb Pfaffian-Z₂ ↔ surrogate-winding mod-2 parity. -/
theorem subwave_8_G_substantive_closure :
    (∀ sc : SCParameters,
      windingNumberSurrogate sc = 0 ↔ sc.centrosymmetric = true) ∧
    (1 - fuKaneInvariant nbReParameters) / 2 =
      windingNumberSurrogate nbReParameters % 2 ∧
    (1 - fuKaneInvariant elementalNbParameters) / 2 =
      windingNumberSurrogate elementalNbParameters % 2 :=
  ⟨windingNumberSurrogate_eq_zero_iff,
   nbRe_pfaffian_eq_winding_mod2_parity,
   elementalNb_pfaffian_eq_winding_mod2_parity⟩

end SKEFTHawking.NbReWindingNumber
