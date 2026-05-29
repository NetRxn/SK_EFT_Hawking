/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item E (M2) — `ZOmegaSqrt2 := ℤ[ω][1/√2]`

Ships the **computable runtime** representation of `ℤ[ω][1/√2]` as a
`Quotient` of fraction pairs, with the key arithmetic fact `√2² = 2`
discharged at the substrate level.

Per Pre-Implementation Research Dossier §1.7, there are two viable
representations:

  **(A) Localization.Away (clean theory):**
       `def ZOmegaSqrt2 := Localization.Away (sqrt2 : ZOmega)`
       Inherits `CommRing` from Mathlib automatically, but is
       **noncomputable** — blocks `native_decide` on gate arithmetic.

  **(B) Runtime quotient representation (SHIPPED HERE):**
       `def ZOmegaSqrt2 := Quotient ZOmegaSqrt2.Frac.setoid`, where
       `Frac` is a pair `(num : ZOmega, den : ℕ)` representing
       `num / √2^den`, modulo the equivalence
       `(z₁, k₁) ~ (z₂, k₂) iff z₁·√2^k₂ = z₂·√2^k₁`. **Computable** +
       `DecidableEq`, supporting `native_decide` on Clifford+T matrix
       arithmetic. The full `CommRing` instance is discharged by
       reducing each axiom to a representative-level `ZOmega` identity
       (via `mk_add`/`mk_mul`/`mk_eq_mk_iff`, closed by `ring`).

This file ships **(B)** — the computable runtime quotient. The
non-zero-divisor property of `√2` in `ZOmega` (proven via the
multiplication table below as `sqrt2_pow_mul_cancel`) is what makes the
equivalence relation transitive and the quotient well-defined.
Downstream consumers (KMM exact synthesis in Item F, the constructive
base finder in Item G) consume this runtime representation directly;
the theory-layer equivalence to Mathlib's `Localization.Away (sqrt2)`
is a separate (non-load-bearing) follow-on, not required by any
downstream `kmmReduce`/`compile` deliverable.

## Mathematical structure (verified by direct computation in M1)

`√2 = ω + ω⁻¹ = ω − ω³ = ⟨−1, 0, 1, 0⟩ : ZOmega`. Computation in M1's
multiplication table gives:

  `√2² = ⟨-1, 0, 1, 0⟩ · ⟨-1, 0, 1, 0⟩ = ⟨0, 0, 0, 2⟩ = 2`

So `√2 ∈ ZOmega` is a non-zero divisor (in fact a non-unit; norm 4), and
`Localization.Away (√2)` is the principal localization at this element.

## Headline definitions

  * `ZOmega.sqrt2 := ω − ω³ ∈ ZOmega` — the canonical square root of 2.
  * `ZOmega.sqrt2_sq : sqrt2 * sqrt2 = 2` — defining identity.
  * `ZOmega.sqrt2_pow_mul_cancel` — `√2^k` is a non-zero-divisor (makes
    the fraction equivalence well-defined).
  * `ZOmegaSqrt2.Frac` — the fraction-pair representative `(num, den)`.
  * `ZOmegaSqrt2 := Quotient ZOmegaSqrt2.Frac.setoid` — the computable
    runtime ring, with `DecidableEq` + full `CommRing`.
  * `ZOmegaSqrt2.mk z k` — the projection `z / √2^k`; `mk_eq_mk_iff`,
    `mk_add`, `mk_mul`, `mk_pad` the arithmetic API.
  * `ZOmegaSqrt2.sqrt2 / invSqrt2 : ZOmegaSqrt2` — `√2` and its inverse,
    with `sqrt2_mul_invSqrt2 : sqrt2 * invSqrt2 = 1` and `sqrt2_isUnit`.
  * `ZOmegaSqrt2.of / ofRingHom / Algebra ZOmega ZOmegaSqrt2` — the
    canonical computable embedding `z ↦ mk z 0`.

## Deferred to follow-ons (non-load-bearing)

  * `ZOmegaSqrt2.toComplex : ZOmegaSqrt2 →+* ℂ` (lifts the `ZOmega →+* ℂ`
    embedding through the universal property; used only for numerical
    cross-checks, not by `kmmReduce`/`compile`).
  * The ring isomorphism to Mathlib's `Localization.Away (sqrt2)`
    (theory-layer bridge; not required by any downstream deliverable).

## References

  * Pre-Implementation Research Dossier §1.7 (dual-representation design;
    this file ships representation (B), the runtime quotient).
  * Mathlib's `Mathlib.Data.Quot` (`Quotient`, `Quotient.lift₂`,
    `Quotient.sound`) — the well-definedness machinery.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmega

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-! ## 1. `sqrt2` element in ZOmega -/

/-- **`sqrt2 = ω - ω³` as a `ZOmega` element**.

In tuple form `(a, b, c, d) = (-1, 0, 1, 0)`. The defining equation
`sqrt2² = 2` is discharged by direct computation in M1's multiplication
table; the result is the constant `2 = (0, 0, 0, 2)`. -/
def sqrt2 : ZOmega := ⟨-1, 0, 1, 0⟩

@[simp] theorem sqrt2_a : sqrt2.a = -1 := rfl
@[simp] theorem sqrt2_b : sqrt2.b = 0 := rfl
@[simp] theorem sqrt2_c : sqrt2.c = 1 := rfl
@[simp] theorem sqrt2_d : sqrt2.d = 0 := rfl

/-- **The defining identity** `sqrt2² = 2`. -/
theorem sqrt2_sq : sqrt2 * sqrt2 = (2 : ZOmega) := by
  show sqrt2 * sqrt2 = (⟨0, 0, 0, 2⟩ : ZOmega)
  ext <;> simp

/-- **`sqrt2` is a non-zero element of `ZOmega`**. -/
theorem sqrt2_ne_zero : sqrt2 ≠ 0 := by decide

/-- **`sqrt2` multiplication table**: `sqrt2 * y` has explicit form
`(b - d, a + c, b + d, c - a)` for `y = (a, b, c, d)`. -/
theorem sqrt2_mul (y : ZOmega) :
    sqrt2 * y = ⟨y.b - y.d, y.a + y.c, y.b + y.d, y.c - y.a⟩ := by
  ext <;> simp <;> ring

/-- **`sqrt2` is a non-zero-divisor in ZOmega**: `sqrt2 * y = 0 → y = 0`.

Direct from the multiplication table: `sqrt2 * y = (b-d, a+c, b+d, c-a)`.
Setting all four components to zero gives `b = d`, `c = -a`, `b = -d`,
`a = c`, which forces `a = b = c = d = 0`. -/
theorem sqrt2_mul_eq_zero {y : ZOmega} (h : sqrt2 * y = 0) : y = 0 := by
  rw [sqrt2_mul] at h
  -- h : ⟨y.b - y.d, y.a + y.c, y.b + y.d, y.c - y.a⟩ = 0
  have h1 : y.b - y.d = 0 := congrArg ZOmega.a h
  have h2 : y.a + y.c = 0 := congrArg ZOmega.b h
  have h3 : y.b + y.d = 0 := congrArg ZOmega.c h
  have h4 : y.c - y.a = 0 := congrArg ZOmega.d h
  ext
  · show y.a = 0; omega
  · show y.b = 0; omega
  · show y.c = 0; omega
  · show y.d = 0; omega

/-- **Mul-left by sqrt2 cancels**: `sqrt2 * x = sqrt2 * y → x = y`. -/
theorem sqrt2_mul_cancel {x y : ZOmega} (h : sqrt2 * x = sqrt2 * y) : x = y := by
  have h1 : sqrt2 * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  exact sub_eq_zero.mp (sqrt2_mul_eq_zero h1)

/-- **`sqrt2 ^ k` is a non-zero-divisor for any `k`**.

By induction on `k`: base case is trivial; inductive step uses
`sqrt2_mul_cancel` to peel one `sqrt2` factor. -/
theorem sqrt2_pow_mul_cancel {x y : ZOmega} (k : ℕ)
    (h : sqrt2 ^ k * x = sqrt2 ^ k * y) : x = y := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    -- sqrt2^(n+1) * x = sqrt2 * (sqrt2^n * x)
    have heq : sqrt2 * (sqrt2 ^ n * x) = sqrt2 * (sqrt2 ^ n * y) := by
      have := h
      rw [pow_succ] at this
      calc sqrt2 * (sqrt2 ^ n * x)
          = sqrt2 ^ n * sqrt2 * x := by ring
        _ = sqrt2 ^ n * sqrt2 * y := this
        _ = sqrt2 * (sqrt2 ^ n * y) := by ring
    exact ih (sqrt2_mul_cancel heq)

/-- **Complex conjugation fixes `sqrt2`** (since `√2 = ω + ω⁻¹` is real).

The Galois automorphism `σ_7 = conj` fixes the real subfield `ℚ(√2)`
of `ℚ(ζ_8)`; `√2` lies in this subfield. -/
theorem conj_sqrt2 : conj sqrt2 = sqrt2 := by
  ext <;> simp

/-- **The `σ_3` Galois automorphism sends `sqrt2 ↦ -sqrt2`**.

`σ_3(ω) = ω³`, so `σ_3(√2) = σ_3(ω - ω³) = ω³ - ω⁹ = ω³ - ω = -√2`. -/
theorem σ3_sqrt2 : σ3 sqrt2 = -sqrt2 := by
  ext <;> simp

/-- **The `σ_5` Galois automorphism sends `sqrt2 ↦ -sqrt2`**.

`σ_5(ω) = -ω`, so `σ_5(√2) = σ_5(ω - ω³) = -ω - (-ω)³ = -ω + ω³ = -√2`. -/
theorem σ5_sqrt2 : σ5 sqrt2 = -sqrt2 := by
  ext <;> simp

end ZOmega

/-! ## 2. `ZOmegaSqrt2` as a computable quotient of `ZOmega × ℕ`

REPLACES the previous `Localization.Away`-based definition (which was
noncomputable). The new definition is a `Quotient` of pairs `(z, k)`
representing `z / √2^k`, with equivalence
`(z₁, k₁) ~ (z₂, k₂) iff z₁ · √2^k₂ = z₂ · √2^k₁`. The non-zero-divisor
property of `√2` (proven via the multiplication table above) makes the
equivalence reflexive, symmetric, and transitive (the latter requiring
`sqrt2_pow_mul_cancel`). `DecidableEq` follows from `ZOmega`'s
`DecidableEq` since the equivalence is decidable in this form.

The runtime representation enables `native_decide`-driven test queries
on Clifford+T matrix arithmetic (for the M4 KMM exact synthesis). The
theory-layer equivalence to the Mathlib `Localization.Away (sqrt2)` is
NOT shipped (deferred follow-on); downstream consumers (KMM, base
finder) consume this runtime representation directly. -/

namespace ZOmegaSqrt2

/-- **Fraction representative** `(z, k)` of an element `z / √2^k`. -/
structure Frac : Type where
  /-- Numerator. -/
  num : ZOmega
  /-- Denominator exponent. -/
  den : ℕ
  deriving DecidableEq, Repr

namespace Frac

/-- **Equivalence relation**: `(z₁, k₁) ~ (z₂, k₂) iff z₁ · √2^k₂ = z₂ · √2^k₁`. -/
def equiv (a b : Frac) : Prop :=
  a.num * ZOmega.sqrt2 ^ b.den = b.num * ZOmega.sqrt2 ^ a.den

/-- **Reflexivity**: any `Frac` is equivalent to itself. -/
@[refl] theorem equiv_refl (a : Frac) : equiv a a := rfl

/-- **Symmetry**: `equiv a b → equiv b a`. -/
theorem equiv_symm {a b : Frac} (h : equiv a b) : equiv b a := h.symm

/-- **Transitivity**: `equiv a b → equiv b c → equiv a c`.

The proof multiplies both equations together, rearranges, and cancels
`sqrt2^b.den` using `ZOmega.sqrt2_pow_mul_cancel` (sqrt2 is a non-zero-
divisor in ZOmega). -/
theorem equiv_trans {a b c : Frac} (h₁ : equiv a b) (h₂ : equiv b c) :
    equiv a c := by
  unfold equiv at *
  -- h₁ : a.num * sqrt2^b.den = b.num * sqrt2^a.den
  -- h₂ : b.num * sqrt2^c.den = c.num * sqrt2^b.den
  -- Want: a.num * sqrt2^c.den = c.num * sqrt2^a.den
  -- Strategy: show sqrt2^b.den * (a.num * sqrt2^c.den) = sqrt2^b.den * (c.num * sqrt2^a.den)
  -- then cancel sqrt2^b.den via sqrt2_pow_mul_cancel.
  apply ZOmega.sqrt2_pow_mul_cancel b.den
  calc ZOmega.sqrt2 ^ b.den * (a.num * ZOmega.sqrt2 ^ c.den)
      = (a.num * ZOmega.sqrt2 ^ b.den) * ZOmega.sqrt2 ^ c.den := by ring
    _ = (b.num * ZOmega.sqrt2 ^ a.den) * ZOmega.sqrt2 ^ c.den := by rw [h₁]
    _ = (b.num * ZOmega.sqrt2 ^ c.den) * ZOmega.sqrt2 ^ a.den := by ring
    _ = (c.num * ZOmega.sqrt2 ^ b.den) * ZOmega.sqrt2 ^ a.den := by rw [h₂]
    _ = ZOmega.sqrt2 ^ b.den * (c.num * ZOmega.sqrt2 ^ a.den) := by ring

/-- **Setoid instance** for `Frac`. -/
instance setoid : Setoid Frac := ⟨equiv, equiv_refl, equiv_symm, equiv_trans⟩

/-- **Decidable equivalence**: since `ZOmega` has `DecidableEq` and the
equivalence reduces to `z₁ · √2^k₂ = z₂ · √2^k₁` in `ZOmega`, the
relation is decidable. -/
instance decEquiv : DecidableRel (· ≈ · : Frac → Frac → Prop) :=
  fun a b => decEq _ _

end Frac

end ZOmegaSqrt2

/-- **The ring `ℤ[ω][1/√2]`** as the quotient of `ZOmegaSqrt2.Frac` by
the equivalence relation `(z₁, k₁) ~ (z₂, k₂) iff z₁ · √2^k₂ = z₂ · √2^k₁`.

Computable + `DecidableEq`-enabled, supporting `native_decide` on
small examples. Provides the runtime substrate for KMM exact synthesis
(`RossSelinger/KMM.lean`). -/
def ZOmegaSqrt2 : Type := Quotient ZOmegaSqrt2.Frac.setoid

namespace ZOmegaSqrt2

/-- **Decidable equality** on `ZOmegaSqrt2` via the decidable equivalence
on `Frac`. -/
instance : DecidableEq ZOmegaSqrt2 := fun a b =>
  Quotient.recOnSubsingleton₂ a b (fun x y =>
    decidable_of_iff (x ≈ y) Quotient.eq.symm)

/-- **The canonical map** from `Frac` to `ZOmegaSqrt2` (quotient projection). -/
def mk (z : ZOmega) (k : ℕ) : ZOmegaSqrt2 :=
  Quotient.mk Frac.setoid ⟨z, k⟩

@[simp] theorem mk_eq (z : ZOmega) (k : ℕ) :
    mk z k = Quotient.mk Frac.setoid ⟨z, k⟩ := rfl

/-- **Equality of `mk`**: `mk z₁ k₁ = mk z₂ k₂` iff the `Frac.equiv`
relation holds. -/
theorem mk_eq_mk_iff {z₁ z₂ : ZOmega} {k₁ k₂ : ℕ} :
    mk z₁ k₁ = mk z₂ k₂ ↔ z₁ * ZOmega.sqrt2 ^ k₂ = z₂ * ZOmega.sqrt2 ^ k₁ :=
  Quotient.eq

/-- **Padding lemma**: `mk z k = mk (z * sqrt2) (k + 1)` (multiplying top
and bottom by `sqrt2`). -/
theorem mk_pad (z : ZOmega) (k : ℕ) :
    mk z k = mk (z * ZOmega.sqrt2) (k + 1) := by
  rw [mk_eq_mk_iff]
  rw [pow_succ]
  ring

end ZOmegaSqrt2

/-! ## 3. Operations on `Frac` and `ZOmegaSqrt2` -/

namespace ZOmegaSqrt2.Frac

/-- **Addition of fractions**: common denominator `√2^(k₁+k₂)`,
numerator `z₁·√2^k₂ + z₂·√2^k₁`. -/
def add (a b : Frac) : Frac :=
  ⟨a.num * ZOmega.sqrt2 ^ b.den + b.num * ZOmega.sqrt2 ^ a.den, a.den + b.den⟩

/-- **Multiplication of fractions**: `(z₁/√2^k₁)·(z₂/√2^k₂) = (z₁z₂)/√2^(k₁+k₂)`. -/
def mul (a b : Frac) : Frac :=
  ⟨a.num * b.num, a.den + b.den⟩

/-- **Negation**: `-(z/√2^k) = (-z)/√2^k`. -/
def neg (a : Frac) : Frac := ⟨-a.num, a.den⟩

/-- **Zero fraction**: `0/√2^0`. -/
def zero : Frac := ⟨0, 0⟩

/-- **One fraction**: `1/√2^0`. -/
def one : Frac := ⟨1, 0⟩

/-- **`Add` respects the equivalence relation**.

If `a₁ ~ a₂` and `b₁ ~ b₂` then `add a₁ b₁ ~ add a₂ b₂`. The proof
expands both sides via the equivalence definitions and uses
`ZOmega.sqrt2` commutativity-with-itself + `ring`. -/
theorem add_respects {a₁ a₂ b₁ b₂ : Frac}
    (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) : add a₁ b₁ ≈ add a₂ b₂ := by
  unfold add
  show (a₁.num * ZOmega.sqrt2 ^ b₁.den + b₁.num * ZOmega.sqrt2 ^ a₁.den) *
        ZOmega.sqrt2 ^ (a₂.den + b₂.den)
      = (a₂.num * ZOmega.sqrt2 ^ b₂.den + b₂.num * ZOmega.sqrt2 ^ a₂.den) *
        ZOmega.sqrt2 ^ (a₁.den + b₁.den)
  -- ha : a₁.num * sqrt2^a₂.den = a₂.num * sqrt2^a₁.den
  -- hb : b₁.num * sqrt2^b₂.den = b₂.num * sqrt2^b₁.den
  have ha' : a₁.num * ZOmega.sqrt2 ^ a₂.den = a₂.num * ZOmega.sqrt2 ^ a₁.den := ha
  have hb' : b₁.num * ZOmega.sqrt2 ^ b₂.den = b₂.num * ZOmega.sqrt2 ^ b₁.den := hb
  -- LHS = a₁.num * sqrt2^(b₁.den + a₂.den + b₂.den) + b₁.num * sqrt2^(a₁.den + a₂.den + b₂.den)
  -- Substitute via ha' on first term, hb' on second.
  have h_pow_add : ∀ x y : ℕ, ZOmega.sqrt2 ^ (x + y) = ZOmega.sqrt2 ^ x * ZOmega.sqrt2 ^ y := by
    intros; exact pow_add _ _ _
  have key : (a₁.num * ZOmega.sqrt2 ^ b₁.den + b₁.num * ZOmega.sqrt2 ^ a₁.den) *
              ZOmega.sqrt2 ^ (a₂.den + b₂.den)
            = (a₁.num * ZOmega.sqrt2 ^ a₂.den) *
                (ZOmega.sqrt2 ^ b₁.den * ZOmega.sqrt2 ^ b₂.den)
              + (b₁.num * ZOmega.sqrt2 ^ b₂.den) *
                (ZOmega.sqrt2 ^ a₁.den * ZOmega.sqrt2 ^ a₂.den) := by
    repeat rw [h_pow_add]
    ring
  rw [key, ha', hb']
  -- After rewrite: (a₂.num * sqrt2^a₁.den) * (sqrt2^b₁.den * sqrt2^b₂.den)
  --              + (b₂.num * sqrt2^b₁.den) * (sqrt2^a₁.den * sqrt2^a₂.den)
  --             = (a₂.num * sqrt2^b₂.den + b₂.num * sqrt2^a₂.den) * sqrt2^(a₁.den + b₁.den)
  repeat rw [h_pow_add]
  ring

/-- **`Mul` respects the equivalence relation**. -/
theorem mul_respects {a₁ a₂ b₁ b₂ : Frac}
    (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) : mul a₁ b₁ ≈ mul a₂ b₂ := by
  unfold mul
  show (a₁.num * b₁.num) * ZOmega.sqrt2 ^ (a₂.den + b₂.den)
      = (a₂.num * b₂.num) * ZOmega.sqrt2 ^ (a₁.den + b₁.den)
  have ha' : a₁.num * ZOmega.sqrt2 ^ a₂.den = a₂.num * ZOmega.sqrt2 ^ a₁.den := ha
  have hb' : b₁.num * ZOmega.sqrt2 ^ b₂.den = b₂.num * ZOmega.sqrt2 ^ b₁.den := hb
  -- LHS = (a₁.num * a₂.den) * (b₁.num * b₂.den) ← rearrange
  have h_pow_add : ZOmega.sqrt2 ^ (a₂.den + b₂.den)
                  = ZOmega.sqrt2 ^ a₂.den * ZOmega.sqrt2 ^ b₂.den := pow_add _ _ _
  have h_pow_add' : ZOmega.sqrt2 ^ (a₁.den + b₁.den)
                  = ZOmega.sqrt2 ^ a₁.den * ZOmega.sqrt2 ^ b₁.den := pow_add _ _ _
  rw [h_pow_add, h_pow_add']
  calc (a₁.num * b₁.num) * (ZOmega.sqrt2 ^ a₂.den * ZOmega.sqrt2 ^ b₂.den)
      = (a₁.num * ZOmega.sqrt2 ^ a₂.den) * (b₁.num * ZOmega.sqrt2 ^ b₂.den) := by ring
    _ = (a₂.num * ZOmega.sqrt2 ^ a₁.den) * (b₂.num * ZOmega.sqrt2 ^ b₁.den) := by rw [ha', hb']
    _ = (a₂.num * b₂.num) * (ZOmega.sqrt2 ^ a₁.den * ZOmega.sqrt2 ^ b₁.den) := by ring

/-- **`Neg` respects the equivalence relation**. -/
theorem neg_respects {a₁ a₂ : Frac} (ha : a₁ ≈ a₂) : neg a₁ ≈ neg a₂ := by
  unfold neg
  show -a₁.num * ZOmega.sqrt2 ^ a₂.den = -a₂.num * ZOmega.sqrt2 ^ a₁.den
  have ha' : a₁.num * ZOmega.sqrt2 ^ a₂.den = a₂.num * ZOmega.sqrt2 ^ a₁.den := ha
  calc -a₁.num * ZOmega.sqrt2 ^ a₂.den
      = -(a₁.num * ZOmega.sqrt2 ^ a₂.den) := by ring
    _ = -(a₂.num * ZOmega.sqrt2 ^ a₁.den) := by rw [ha']
    _ = -a₂.num * ZOmega.sqrt2 ^ a₁.den := by ring

end ZOmegaSqrt2.Frac

namespace ZOmegaSqrt2

instance : Add ZOmegaSqrt2 :=
  ⟨Quotient.lift₂ (fun a b => Quotient.mk Frac.setoid (Frac.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Frac.add_respects ha hb))⟩

instance : Mul ZOmegaSqrt2 :=
  ⟨Quotient.lift₂ (fun a b => Quotient.mk Frac.setoid (Frac.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Frac.mul_respects ha hb))⟩

instance : Neg ZOmegaSqrt2 :=
  ⟨Quotient.lift (fun a => Quotient.mk Frac.setoid (Frac.neg a))
    (fun _ _ ha => Quotient.sound (Frac.neg_respects ha))⟩

instance : Zero ZOmegaSqrt2 := ⟨Quotient.mk Frac.setoid Frac.zero⟩
instance : One ZOmegaSqrt2 := ⟨Quotient.mk Frac.setoid Frac.one⟩
instance : Sub ZOmegaSqrt2 := ⟨fun a b => a + (-b)⟩

@[simp] theorem mk_add (z₁ z₂ : ZOmega) (k₁ k₂ : ℕ) :
    mk z₁ k₁ + mk z₂ k₂ =
      mk (z₁ * ZOmega.sqrt2 ^ k₂ + z₂ * ZOmega.sqrt2 ^ k₁) (k₁ + k₂) := rfl

@[simp] theorem mk_mul (z₁ z₂ : ZOmega) (k₁ k₂ : ℕ) :
    mk z₁ k₁ * mk z₂ k₂ = mk (z₁ * z₂) (k₁ + k₂) := rfl

@[simp] theorem mk_neg (z : ZOmega) (k : ℕ) : -(mk z k) = mk (-z) k := rfl

@[simp] theorem zero_def : (0 : ZOmegaSqrt2) = mk 0 0 := rfl
@[simp] theorem one_def : (1 : ZOmegaSqrt2) = mk 1 0 := rfl

/-! ## 4. CommRing instance via Quotient axiom-discharge

Each axiom reduces to a representative-level identity provable by
`ring` on `ZOmega` after combining `mk + mk → mk` and `mk * mk → mk`
via the `mk_add` / `mk_mul` simp lemmas, then `mk = mk` reduces to a
`ZOmega` equation via `mk_eq_mk_iff`. -/

/-- Convenience helper for the per-axiom proof shape: reduce a
ZOmegaSqrt2 equation to a ZOmega equation at the Frac level. -/
private theorem frac_eq {z₁ z₂ : ZOmega} {k₁ k₂ : ℕ}
    (h : z₁ * ZOmega.sqrt2 ^ k₂ = z₂ * ZOmega.sqrt2 ^ k₁) :
    mk z₁ k₁ = mk z₂ k₂ :=
  mk_eq_mk_iff.mpr h

instance : CommRing ZOmegaSqrt2 where
  add := (· + ·)
  add_assoc := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩ ⟨⟨c, kc⟩⟩
    show mk a ka + mk b kb + mk c kc = mk a ka + (mk b kb + mk c kc)
    simp only [mk_add]
    apply frac_eq
    simp only [pow_add]
    ring
  zero := 0
  zero_add := by
    rintro ⟨⟨a, ka⟩⟩
    show mk 0 0 + mk a ka = mk a ka
    simp only [mk_add]
    apply frac_eq
    simp
  add_zero := by
    rintro ⟨⟨a, ka⟩⟩
    show mk a ka + mk 0 0 = mk a ka
    simp only [mk_add]
    apply frac_eq
    simp
  neg := Neg.neg
  sub := fun a b => a + (-b)
  sub_eq_add_neg := fun _ _ => rfl
  neg_add_cancel := by
    rintro ⟨⟨a, ka⟩⟩
    show -(mk a ka) + mk a ka = 0
    rw [mk_neg]
    simp only [mk_add]
    apply frac_eq
    simp
  add_comm := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩
    show mk a ka + mk b kb = mk b kb + mk a ka
    simp only [mk_add]
    apply frac_eq
    rw [show ka + kb = kb + ka from Nat.add_comm _ _]
    ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul := (· * ·)
  mul_assoc := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩ ⟨⟨c, kc⟩⟩
    show mk a ka * mk b kb * mk c kc = mk a ka * (mk b kb * mk c kc)
    simp only [mk_mul]
    apply frac_eq
    rw [show ka + kb + kc = ka + (kb + kc) from by omega]
    ring
  one := 1
  one_mul := by
    rintro ⟨⟨a, ka⟩⟩
    show mk 1 0 * mk a ka = mk a ka
    simp only [mk_mul]
    apply frac_eq
    simp
  mul_one := by
    rintro ⟨⟨a, ka⟩⟩
    show mk a ka * mk 1 0 = mk a ka
    simp only [mk_mul]
    apply frac_eq
    simp
  left_distrib := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩ ⟨⟨c, kc⟩⟩
    show mk a ka * (mk b kb + mk c kc) = mk a ka * mk b kb + mk a ka * mk c kc
    simp only [mk_add, mk_mul]
    apply frac_eq
    simp only [pow_add]
    ring
  right_distrib := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩ ⟨⟨c, kc⟩⟩
    show (mk a ka + mk b kb) * mk c kc = mk a ka * mk c kc + mk b kb * mk c kc
    simp only [mk_add, mk_mul]
    apply frac_eq
    simp only [pow_add]
    ring
  zero_mul := by
    rintro ⟨⟨a, ka⟩⟩
    show mk 0 0 * mk a ka = 0
    simp only [mk_mul]
    apply frac_eq
    simp
  mul_zero := by
    rintro ⟨⟨a, ka⟩⟩
    show mk a ka * mk 0 0 = 0
    simp only [mk_mul]
    apply frac_eq
    simp
  mul_comm := by
    rintro ⟨⟨a, ka⟩⟩ ⟨⟨b, kb⟩⟩
    show mk a ka * mk b kb = mk b kb * mk a ka
    simp only [mk_mul]
    apply frac_eq
    rw [show ka + kb = kb + ka from Nat.add_comm _ _]
    ring
  npow := npowRec
  intCast n := mk (n : ZOmega) 0
  natCast n := mk (n : ZOmega) 0
  intCast_ofNat n := by
    show mk ((n : ℤ) : ZOmega) 0 = mk ((n : ℕ) : ZOmega) 0
    push_cast
    rfl
  intCast_negSucc n := by
    show mk ((Int.negSucc n : ℤ) : ZOmega) 0 = -(mk ((n + 1 : ℕ) : ZOmega) 0)
    rw [mk_neg]
    apply frac_eq
    push_cast
    ring
  natCast_zero := by
    show mk ((0 : ℕ) : ZOmega) 0 = mk 0 0
    push_cast
    rfl
  natCast_succ n := by
    show mk ((n + 1 : ℕ) : ZOmega) 0 = mk ((n : ℕ) : ZOmega) 0 + mk 1 0
    simp only [mk_add]
    apply frac_eq
    push_cast
    ring

/-! ## 5. `sqrt2`, `invSqrt2`, units, and `algebraMap ZOmega ZOmegaSqrt2` -/

/-- **`sqrt2` lifted to `ZOmegaSqrt2`**: the element `ZOmega.sqrt2 / √2^0`. -/
def sqrt2 : ZOmegaSqrt2 := mk ZOmega.sqrt2 0

@[simp] theorem sqrt2_def : sqrt2 = mk ZOmega.sqrt2 0 := rfl

/-- **The multiplicative inverse of `sqrt2`** in `ZOmegaSqrt2`. Defined
as `1 / √2^1 = ⟦(1, 1)⟧`. -/
def invSqrt2 : ZOmegaSqrt2 := mk 1 1

@[simp] theorem invSqrt2_def : invSqrt2 = mk 1 1 := rfl

/-- **Defining identity**: `sqrt2 * invSqrt2 = 1`. -/
theorem sqrt2_mul_invSqrt2 : sqrt2 * invSqrt2 = 1 := by
  show mk ZOmega.sqrt2 0 * mk 1 1 = mk 1 0
  rw [mk_mul]
  apply frac_eq
  simp

/-- **Defining identity (other direction)**: `invSqrt2 * sqrt2 = 1`. -/
theorem invSqrt2_mul_sqrt2 : invSqrt2 * sqrt2 = 1 := by
  rw [mul_comm]
  exact sqrt2_mul_invSqrt2

/-- **`sqrt2` is a unit in `ZOmegaSqrt2`**. -/
theorem sqrt2_isUnit : IsUnit (sqrt2 : ZOmegaSqrt2) :=
  ⟨⟨sqrt2, invSqrt2, sqrt2_mul_invSqrt2, invSqrt2_mul_sqrt2⟩, rfl⟩

/-- **The canonical algebra map** `ZOmega → ZOmegaSqrt2`: `z ↦ mk z 0`. -/
def of (z : ZOmega) : ZOmegaSqrt2 := mk z 0

@[simp] theorem of_def (z : ZOmega) : of z = mk z 0 := rfl

@[simp] theorem of_zero : of 0 = 0 := by show mk 0 0 = mk 0 0; rfl
@[simp] theorem of_one : of 1 = 1 := by show mk 1 0 = mk 1 0; rfl

theorem of_add (z₁ z₂ : ZOmega) : of (z₁ + z₂) = of z₁ + of z₂ := by
  show mk (z₁ + z₂) 0 = mk z₁ 0 + mk z₂ 0
  simp only [mk_add]
  apply frac_eq
  simp

theorem of_mul (z₁ z₂ : ZOmega) : of (z₁ * z₂) = of z₁ * of z₂ := by
  show mk (z₁ * z₂) 0 = mk z₁ 0 * mk z₂ 0
  rw [mk_mul]

theorem of_neg (z : ZOmega) : of (-z) = -(of z) := by
  show mk (-z) 0 = -(mk z 0)
  rw [mk_neg]

/-- **`of` is a ring homomorphism**. -/
def ofRingHom : ZOmega →+* ZOmegaSqrt2 where
  toFun := of
  map_one' := of_one
  map_mul' := of_mul
  map_zero' := of_zero
  map_add' := of_add

@[simp] theorem ofRingHom_apply (z : ZOmega) : ofRingHom z = of z := rfl

/-- **`Algebra ZOmega ZOmegaSqrt2`** instance via `ofRingHom`. -/
instance : Algebra ZOmega ZOmegaSqrt2 where
  smul z x := of z * x
  algebraMap := ofRingHom
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

@[simp] theorem algebraMap_eq_of (z : ZOmega) :
    algebraMap ZOmega ZOmegaSqrt2 z = of z := rfl

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
