/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item D (M1) — `ZOmega` ring of integers of ℚ(ζ₈)

Ships the **runtime, native_decide-compatible** ring of integers of
ℚ(ζ₈) = ℚ(e^(iπ/4)) as a Lean 4 `structure` with four `ℤ` fields,
mirroring Selinger's Haskell `Omega Integer` design from `newsynth`
(reference only — GPL-3 source not copied; clean-room rebuild per the
Phase 6x Pre-Implementation Research Dossier §1.1).

## Multiplication table (verified by direct expansion using `ω⁴ = -1`)

`(a₁ω³ + b₁ω² + c₁ω + d₁) · (a₂ω³ + b₂ω² + c₂ω + d₂)` gives:

  * `ω³`-coef:  `a₁·d₂ + b₁·c₂ + c₁·b₂ + d₁·a₂`
  * `ω²`-coef:  `−a₁·a₂ + b₁·d₂ + c₁·c₂ + d₁·b₂`
  * `ω`-coef:   `−a₁·b₂ − b₁·a₂ + c₁·d₂ + d₁·c₂`
  * constant:   `−a₁·c₂ − b₁·b₂ − c₁·a₂ + d₁·d₂`

## Galois automorphisms

`Gal(ℚ(ζ_8)/ℚ) ≃ (ℤ/8)× = {1, 3, 5, 7}`. Non-identity:

  * `σ_3` : `ω → ω³`. `(a, b, c, d) ↦ (c, −b, a, d)`.
  * `σ_5` : `ω → ω⁵ = −ω`. `(a, b, c, d) ↦ (−a, b, −c, d)`.
  * `σ_7 = conj` : complex conjugation. `(a, b, c, d) ↦ (−c, −b, −a, d)`.

## Headline definitions

  * `ZOmega` — structure with `[ext]`-tagged auto-derivation.
  * `ZOmega.ω` — primitive 8th root of unity.
  * `instance : CommRing ZOmega` — via layered AddCommGroup → AddGroupWithOne → CommRing
    following the `Mathlib.NumberTheory.Zsqrtd.Basic` template exactly.
  * `ZOmega.conj`, `ZOmega.σ3`, `ZOmega.σ5` — Galois automorphisms.
  * `ZOmega.norm : ZOmega → ℤ` — algebraic field norm.

## Deferred to follow-ons (M2 ZOmegaSqrt2 + beyond)

  * `ZOmega.toComplex : ZOmega →+* ℂ` ring-hom + injectivity.
  * `ZOmega.lift : { r : R // r^4 = -1 } ≃ (ZOmega →+* R)` universal property.

## References

  * Pre-Implementation Research Dossier §1.1, §1.3, §1.4
    (`Lit-Search/Phase-6x/Ross-Selinger Clifford+T Synthesis- A Pre-Implementation Research Dossier.md`).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §2.
  * Ross-Selinger 2014 (arXiv:1403.2975).
  * Template: `Mathlib.NumberTheory.Zsqrtd.Basic` (the `ofInt`-based
    layered AddCommGroup → AddGroupWithOne → CommRing pattern).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import Mathlib.NumberTheory.Zsqrtd.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ## 1. Structure definition -/

/-- **The ring of integers of ℚ(ζ_8)**, represented as a 4-tuple of integers.

An element `⟨a, b, c, d⟩` stands for `a·ω³ + b·ω² + c·ω + d` where
`ω = ζ_8 = e^(iπ/4)`. The minimal polynomial of `ω` is `Φ₈ = X⁴ + 1`,
giving `ω⁴ = −1`. `@[ext]` enables `ZOmega.ext` + `ZOmega.ext_iff`
auto-derivation. -/
@[ext]
structure ZOmega : Type where
  /-- Coefficient of `ω³`. -/
  a : ℤ
  /-- Coefficient of `ω²` (= `i`). -/
  b : ℤ
  /-- Coefficient of `ω`. -/
  c : ℤ
  /-- Constant term. -/
  d : ℤ
  deriving DecidableEq, Repr

namespace ZOmega

/-! ## 2. Basic operations and `ofInt` -/

/-- Convert an integer to a `ZOmega` (constant element). -/
def ofInt (n : ℤ) : ZOmega := ⟨0, 0, 0, n⟩

@[simp] theorem ofInt_a (n : ℤ) : (ofInt n).a = 0 := rfl
@[simp] theorem ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl
@[simp] theorem ofInt_c (n : ℤ) : (ofInt n).c = 0 := rfl
@[simp] theorem ofInt_d (n : ℤ) : (ofInt n).d = n := rfl

instance : Zero ZOmega := ⟨ofInt 0⟩
instance : One ZOmega := ⟨ofInt 1⟩
instance : Inhabited ZOmega := ⟨0⟩

@[simp] theorem zero_a : (0 : ZOmega).a = 0 := rfl
@[simp] theorem zero_b : (0 : ZOmega).b = 0 := rfl
@[simp] theorem zero_c : (0 : ZOmega).c = 0 := rfl
@[simp] theorem zero_d : (0 : ZOmega).d = 0 := rfl

@[simp] theorem one_a : (1 : ZOmega).a = 0 := rfl
@[simp] theorem one_b : (1 : ZOmega).b = 0 := rfl
@[simp] theorem one_c : (1 : ZOmega).c = 0 := rfl
@[simp] theorem one_d : (1 : ZOmega).d = 1 := rfl

/-- **The primitive 8th root of unity** `ω = ζ_8 = e^(iπ/4)`. -/
def ω : ZOmega := ⟨0, 0, 1, 0⟩

@[simp] theorem ω_a : ω.a = 0 := rfl
@[simp] theorem ω_b : ω.b = 0 := rfl
@[simp] theorem ω_c : ω.c = 1 := rfl
@[simp] theorem ω_d : ω.d = 0 := rfl

instance : Add ZOmega := ⟨fun x y =>
  ⟨x.1 + y.1, x.2 + y.2, x.3 + y.3, x.4 + y.4⟩⟩

instance : Neg ZOmega := ⟨fun x => ⟨-x.1, -x.2, -x.3, -x.4⟩⟩

@[simp] theorem add_def (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ) :
    (⟨a₁, b₁, c₁, d₁⟩ + ⟨a₂, b₂, c₂, d₂⟩ : ZOmega)
      = ⟨a₁ + a₂, b₁ + b₂, c₁ + c₂, d₁ + d₂⟩ :=
  rfl

@[simp] theorem add_a (x y : ZOmega) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : ZOmega) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : ZOmega) : (x + y).c = x.c + y.c := rfl
@[simp] theorem add_d (x y : ZOmega) : (x + y).d = x.d + y.d := rfl

@[simp] theorem neg_a (x : ZOmega) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : ZOmega) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : ZOmega) : (-x).c = -x.c := rfl
@[simp] theorem neg_d (x : ZOmega) : (-x).d = -x.d := rfl

/-- **Multiplication on `ZOmega`** using `ω⁴ = -1`. See module doc. -/
instance : Mul ZOmega := ⟨fun x y => ⟨
  x.1 * y.4 + x.2 * y.3 + x.3 * y.2 + x.4 * y.1,
  -(x.1 * y.1) + x.2 * y.4 + x.3 * y.3 + x.4 * y.2,
  -(x.1 * y.2) - x.2 * y.1 + x.3 * y.4 + x.4 * y.3,
  -(x.1 * y.3) - x.2 * y.2 - x.3 * y.1 + x.4 * y.4⟩⟩

@[simp] theorem mul_a (x y : ZOmega) :
    (x * y).a = x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a := rfl
@[simp] theorem mul_b (x y : ZOmega) :
    (x * y).b = -(x.a * y.a) + x.b * y.d + x.c * y.c + x.d * y.b := rfl
@[simp] theorem mul_c (x y : ZOmega) :
    (x * y).c = -(x.a * y.b) - x.b * y.a + x.c * y.d + x.d * y.c := rfl
@[simp] theorem mul_d (x y : ZOmega) :
    (x * y).d = -(x.a * y.c) - x.b * y.b - x.c * y.a + x.d * y.d := rfl

/-! ## 3. `AddCommGroup` instance (layer 1) -/

instance addCommGroup : AddCommGroup ZOmega := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec ZOmega ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec ZOmega ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec ZOmega ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

/-! ## 4. `AddGroupWithOne` instance (layer 2) -/

instance addGroupWithOne : AddGroupWithOne ZOmega :=
  { ZOmega.addCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

/-! ## 5. `CommRing` instance (layer 3) -/

instance commRing : CommRing ZOmega := by
  refine
  { ZOmega.addGroupWithOne with
    npow := @npowRec ZOmega ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

/-! ## 6. `ω⁴ = -1` and related identities -/

theorem ω_sq : ω * ω = ⟨0, 1, 0, 0⟩ := by ext <;> simp

theorem ω_cubed : ω * ω * ω = ⟨1, 0, 0, 0⟩ := by ext <;> simp <;> ring

/-- **The defining relation**: `ω⁴ = −1`. -/
theorem ω_pow_four : ω ^ 4 = -1 := by
  show ω * (ω * (ω * (ω * 1))) = -1
  rw [mul_one]
  ext <;> simp <;> ring

/-! ## 7. Galois automorphisms -/

/-- **Complex conjugation** `σ_7 : ω ↦ ω⁷ = -ω³`.

In tuple form `(a, b, c, d) ↦ (-c, -b, -a, d)`. -/
def conj (x : ZOmega) : ZOmega := ⟨-x.c, -x.b, -x.a, x.d⟩

@[simp] theorem conj_a (x : ZOmega) : (conj x).a = -x.c := rfl
@[simp] theorem conj_b (x : ZOmega) : (conj x).b = -x.b := rfl
@[simp] theorem conj_c (x : ZOmega) : (conj x).c = -x.a := rfl
@[simp] theorem conj_d (x : ZOmega) : (conj x).d = x.d := rfl

@[simp] theorem conj_zero : conj 0 = 0 := by ext <;> simp
@[simp] theorem conj_one : conj 1 = 1 := by ext <;> simp
@[simp] theorem conj_add (x y : ZOmega) : conj (x + y) = conj x + conj y := by
  ext <;> simp <;> ring

@[simp] theorem conj_neg (x : ZOmega) : conj (-x) = -conj x := by ext <;> simp

theorem conj_mul (x y : ZOmega) : conj (x * y) = conj x * conj y := by
  ext <;> simp <;> ring

theorem conj_conj (x : ZOmega) : conj (conj x) = x := by ext <;> simp

/-- **The Galois automorphism** `σ_3 : ω ↦ ω³`. `(a, b, c, d) ↦ (c, -b, a, d)`. -/
def σ3 (x : ZOmega) : ZOmega := ⟨x.c, -x.b, x.a, x.d⟩

@[simp] theorem σ3_a (x : ZOmega) : (σ3 x).a = x.c := rfl
@[simp] theorem σ3_b (x : ZOmega) : (σ3 x).b = -x.b := rfl
@[simp] theorem σ3_c (x : ZOmega) : (σ3 x).c = x.a := rfl
@[simp] theorem σ3_d (x : ZOmega) : (σ3 x).d = x.d := rfl

@[simp] theorem σ3_zero : σ3 0 = 0 := by ext <;> simp
@[simp] theorem σ3_one : σ3 1 = 1 := by ext <;> simp
@[simp] theorem σ3_add (x y : ZOmega) : σ3 (x + y) = σ3 x + σ3 y := by
  ext <;> simp <;> ring

theorem σ3_mul (x y : ZOmega) : σ3 (x * y) = σ3 x * σ3 y := by
  ext <;> simp <;> ring

/-- **The Galois automorphism** `σ_5 : ω ↦ ω⁵ = -ω`. `(a, b, c, d) ↦ (-a, b, -c, d)`. -/
def σ5 (x : ZOmega) : ZOmega := ⟨-x.a, x.b, -x.c, x.d⟩

@[simp] theorem σ5_a (x : ZOmega) : (σ5 x).a = -x.a := rfl
@[simp] theorem σ5_b (x : ZOmega) : (σ5 x).b = x.b := rfl
@[simp] theorem σ5_c (x : ZOmega) : (σ5 x).c = -x.c := rfl
@[simp] theorem σ5_d (x : ZOmega) : (σ5 x).d = x.d := rfl

@[simp] theorem σ5_zero : σ5 0 = 0 := by ext <;> simp
@[simp] theorem σ5_one : σ5 1 = 1 := by ext <;> simp
@[simp] theorem σ5_add (x y : ZOmega) : σ5 (x + y) = σ5 x + σ5 y := by
  ext <;> simp <;> ring

theorem σ5_mul (x y : ZOmega) : σ5 (x * y) = σ5 x * σ5 y := by
  ext <;> simp <;> ring

/-- **Galois group orbit identity**: `σ_3 ∘ σ_5 = σ_7 = conj`. -/
theorem σ3_σ5_eq_conj (x : ZOmega) : σ3 (σ5 x) = conj x := by ext <;> simp

/-! ## 8. Algebraic field norm

`Norm(α) = α · σ_3(α) · σ_5(α) · σ_7(α)`. The product lies in the
fixed field ℚ. We project the constant term (`d` coefficient). -/

/-- **The algebraic field norm** `ZOmega → ℤ`. -/
def norm (x : ZOmega) : ℤ :=
  (x * σ3 x * σ5 x * conj x).d

@[simp] theorem norm_zero : norm 0 = 0 := by
  unfold norm
  simp

@[simp] theorem norm_one : norm 1 = 1 := by
  unfold norm
  simp

@[simp] theorem norm_ω : norm ω = 1 := by
  unfold norm
  simp only [mul_d, σ3_a, σ3_b, σ3_c, σ3_d, σ5_a, σ5_b, σ5_c, σ5_d,
             conj_a, conj_b, conj_c, conj_d, ω_a, ω_b, ω_c, ω_d,
             mul_a, mul_b, mul_c]
  ring

/-- **Norm is multiplicative**: `norm (x * y) = norm x * norm y`. -/
theorem norm_mul (x y : ZOmega) : norm (x * y) = norm x * norm y := by
  unfold norm
  rw [σ3_mul, σ5_mul, conj_mul]
  simp only [mul_d, σ3_a, σ3_b, σ3_c, σ3_d, σ5_a, σ5_b, σ5_c, σ5_d,
             conj_a, conj_b, conj_c, conj_d, mul_a, mul_b, mul_c]
  ring

end ZOmega
end SKEFTHawking.RossSelinger
