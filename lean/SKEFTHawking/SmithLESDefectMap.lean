/-
# Phase 5q.F W6 — the genuine algebraic degree-4 Smith/defect map of the Smith LES

One genuine map of the Smith long exact sequence the W6 derivation assembles (the goal's Smith-LES spine,
`Lit-Search/Phase-5qF/Smith_sequence.md` §1.3): the degree-4 map

  `Ω₃^{Spin}(Bℤ₂) = ℤ ⊕ ℤ/8  ─→  Ω₄^{Pin⁺}`,   `(k, ν₂) ↦ 2·ν₂ − k`

(Hason–Komargodski–Thorngren arXiv:1910.14039 eq. 4.37–4.38; the Anderson-dual form is
Debray–Devalapurkar–Krulewski–Liu–Pacheco-Tallaj–Thorngren arXiv:2405.04649 Ex. 8.22 eq. 8.23,
`(a,b) ↦ −a + 2b`). Built here as a genuine `ℤ ⊕ ℤ/8 →+ ℤ/16` homomorphism (the classical group values
are the OBJECTIVE-permitted load-bearing classical inputs), with:

  - its **surjectivity** (`Ω₄^{Pin⁺}` is hit by the classical `Ω₃^{Spin}(Bℤ₂)`), and
  - the **K3 obstruction** `(16, 0) ↦ 0` — the generator of `Ω₄^{Spin} = ℤ` (the K3 surface, `σ = −16`)
    maps to `(16, 0)` in `Ω₃^{Spin}(Bℤ₂)` and is killed mod 16; this is exactly the
    failure-of-injectivity HKT flag (`k = 16 ↦ 0`).

**Honest scope.** This module ships ONE map of the Smith LES, as genuine algebra. It does NOT by itself
derive `Ω₄^{Pin⁺} ≅ ℤ/16`: the codomain `ZMod 16` here is the abstract target group, and the genuine
identification of the bordism group `DataBordismGrp ξ_Pin⁺` with the LES term — together with the upper
bound `|Ω₄^{Pin⁺}| ≤ 16` — is the W6 derivation, which is in progress (the exact long exact sequence and
the source of the `≤ 16` bound are being verified against the primary sources). The map's surjectivity and
the K3-obstruction kernel element are the genuine algebraic facts that derivation consumes.

Kernel-pure; no axioms beyond Mathlib's core.
-/
import Mathlib

namespace SKEFTHawking.SmithLESDefectMap

/-- **The doubling homomorphism `ℤ/8 →+ ℤ/16`, `ν₂ ↦ 2·ν₂`.** Well-defined (`8 · 2 = 16 ≡ 0`); this is the
`ν₂`-axis of the Smith defect map (the reduced `Ω̃₃^{Spin}(Bℤ₂) ≅ Ω₂^{Pin⁻} = ℤ/8` summand mapping to the
even part of `ℤ/16`). -/
def doublingHom : ZMod 8 →+ ZMod 16 :=
  ZMod.lift 8 ⟨(AddMonoidHom.mulLeft (2 : ZMod 16)).comp (Int.castAddHom (ZMod 16)), by decide⟩

@[simp] theorem doublingHom_apply (n : ZMod 8) : doublingHom n = 2 * (n.val : ZMod 16) := rfl

/-- `doublingHom` sends the generator `1 ↦ 2` (order 8 in `ℤ/16`), so the `ℤ/8` summand maps onto the
even part `{0,2,4,…,14}` of `ℤ/16`. -/
theorem doublingHom_one : doublingHom 1 = 2 := by decide

/-- **The genuine degree-4 Smith/defect map** `Ω₃^{Spin}(Bℤ₂) = ℤ ⊕ ℤ/8 →+ ℤ/16`, `(k, ν₂) ↦ 2·ν₂ − k`
(HKT eq. 4.38; DDDKLPT eq. 8.23 dual `(a,b) ↦ −a + 2b`). The `ℤ` summand (the gravitational/index part)
maps via `−k` onto all of `ℤ/16`; the `ℤ/8` summand via `2·ν₂` onto the even part. -/
def smithDefect : (ℤ × ZMod 8) →+ ZMod 16 :=
  doublingHom.comp (AddMonoidHom.snd ℤ (ZMod 8)) -
    (Int.castAddHom (ZMod 16)).comp (AddMonoidHom.fst ℤ (ZMod 8))

@[simp] theorem smithDefect_apply (k : ℤ) (n : ZMod 8) :
    smithDefect (k, n) = doublingHom n - (k : ZMod 16) := rfl

/-- **The defect map is surjective** — `Ω₄^{Pin⁺}` is in the image of the classical `Ω₃^{Spin}(Bℤ₂)`
(witnessed already by the `ℤ` summand alone, `(−m, 0) ↦ m`). -/
theorem smithDefect_surjective : Function.Surjective smithDefect :=
  fun m => ⟨(-(m.val : ℤ), 0), by simp⟩

/-- **The K3 obstruction** (HKT failure-of-injectivity flag, `k = 16 ↦ 0`). The generator of
`Ω₄^{Spin} = ℤ` — the K3 surface (`σ = −16`) — maps to `(16, 0)` in `Ω₃^{Spin}(Bℤ₂)`, which the defect
map kills mod 16. This is the kernel element that makes the map non-injective (and underlies the
`Ω₅^{Pin⁺} = 0 ↠̸ Ω₄^{Spin} = ℤ` non-surjectivity, dually). -/
theorem smithDefect_K3_obstruction : smithDefect (16, 0) = 0 := by simp; decide

end SKEFTHawking.SmithLESDefectMap
