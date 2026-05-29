/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — computable √2-adic valuation + `sde` substrate

Ships the **computable** primitives the KMM exact-synthesis algorithm
needs to compute the *smallest denominator exponent* (`sde`) of a
Clifford+T matrix over the runtime ring `ZOmegaSqrt2` (DR §1.7 rep B):

  * `ZOmega.dividesSqrt2 z` — decidable predicate `√2 ∣ z` in `ZOmega`.
  * `ZOmega.divSqrt2 z` — the quotient `z / √2` (correct when `√2 ∣ z`).
  * `ZOmega.lowestDenExp z k` — the **lowest-terms denominator exponent**
    of the fraction `z / √2^k`, computed by dividing out `√2` (up to `k`
    times) by structural recursion on the fuel `k`.

These are all plain (computable) `def`s, so `decide` / `#eval` reduce
them in the kernel. They are the substrate for the per-entry denominator
exponent of a `ZOmegaSqrt2` element, and hence for the matrix `sde` that
makes `kmmReduce` terminate (`termination_by sde`).

## The divisibility criterion (KMM §3, derived from the `√2` mul table)

`√2 = ω − ω³ = ⟨−1, 0, 1, 0⟩`, and (from `ZOmega.sqrt2_mul`)

  `√2 · w = ⟨w.b − w.d, w.a + w.c, w.b + w.d, w.c − w.a⟩`.

Solving `z = √2 · w` component-wise:

  `w.a = (z.b − z.d)/2`,  `w.b = (z.a + z.c)/2`,
  `w.c = (z.b + z.d)/2`,  `w.d = (z.c − z.a)/2`.

These are integers iff `z.a ≡ z.c (mod 2)` and `z.b ≡ z.d (mod 2)` —
the `dividesSqrt2` criterion. When it holds, `divSqrt2 z` is the unique
`w` with `√2 · w = z` (`divSqrt2_spec`).

## References

  * Pre-Implementation Research Dossier §1.7, §3.3.
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3 (sde structure).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmegaSqrt2

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-! ## 1. Divisibility by `√2` in `ZOmega` -/

/-- **Decidable criterion for `√2 ∣ z`**: `z.a ≡ z.c (mod 2)` and
`z.b ≡ z.d (mod 2)`. Derived from the `√2` multiplication table (see
module docstring). -/
def dividesSqrt2 (z : ZOmega) : Prop := z.a % 2 = z.c % 2 ∧ z.b % 2 = z.d % 2

instance (z : ZOmega) : Decidable (dividesSqrt2 z) := by
  unfold dividesSqrt2; infer_instance

/-- **The quotient `z / √2`** (the unique `w` with `√2 · w = z` when
`√2 ∣ z`; junk value otherwise). -/
def divSqrt2 (z : ZOmega) : ZOmega :=
  ⟨(z.b - z.d) / 2, (z.a + z.c) / 2, (z.b + z.d) / 2, (z.c - z.a) / 2⟩

@[simp] theorem divSqrt2_a (z : ZOmega) : (divSqrt2 z).a = (z.b - z.d) / 2 := rfl
@[simp] theorem divSqrt2_b (z : ZOmega) : (divSqrt2 z).b = (z.a + z.c) / 2 := rfl
@[simp] theorem divSqrt2_c (z : ZOmega) : (divSqrt2 z).c = (z.b + z.d) / 2 := rfl
@[simp] theorem divSqrt2_d (z : ZOmega) : (divSqrt2 z).d = (z.c - z.a) / 2 := rfl

/-- **`divSqrt2` is a genuine left-inverse of `√2 ·`** when `√2 ∣ z`:
`√2 · divSqrt2 z = z`. -/
theorem divSqrt2_spec {z : ZOmega} (h : dividesSqrt2 z) :
    sqrt2 * divSqrt2 z = z := by
  obtain ⟨h1, h2⟩ := h
  rw [sqrt2_mul]
  ext <;> simp only [divSqrt2_a, divSqrt2_b, divSqrt2_c, divSqrt2_d] <;> omega

/-- **`√2` always divides `√2 · w`**. -/
theorem dividesSqrt2_sqrt2_mul (w : ZOmega) : dividesSqrt2 (sqrt2 * w) := by
  rw [sqrt2_mul]
  constructor <;> simp only [] <;> omega

/-- **`divSqrt2` recovers `w` from `√2 · w`**: `divSqrt2 (√2 · w) = w`. -/
theorem divSqrt2_sqrt2_mul (w : ZOmega) : divSqrt2 (sqrt2 * w) = w := by
  rw [sqrt2_mul]
  ext <;> simp only [divSqrt2_a, divSqrt2_b, divSqrt2_c, divSqrt2_d] <;> omega

/-! ## 2. Lowest-terms denominator exponent -/

/-- **Lowest-terms denominator exponent** of the fraction `z / √2^k`.

Divides out `√2` from the numerator as long as the numerator is `√2`-
divisible and fuel remains, returning the residual denominator exponent.
Structural recursion on the fuel `k` (so it terminates trivially and is
`decide`/`#eval`-reducible). -/
def lowestDenExp (z : ZOmega) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if dividesSqrt2 z then lowestDenExp (divSqrt2 z) k else k + 1

@[simp] theorem lowestDenExp_zero (z : ZOmega) : lowestDenExp z 0 = 0 := rfl

theorem lowestDenExp_succ (z : ZOmega) (k : ℕ) :
    lowestDenExp z (k + 1)
      = if dividesSqrt2 z then lowestDenExp (divSqrt2 z) k else k + 1 := rfl

/-- **Peeling a `√2` factor leaves the exponent unchanged**: the lowest-
terms denominator exponent of `(√2 · w) / √2^(k+1)` equals that of
`w / √2^k`. This is the well-definedness engine for the fraction `sde`:
multiplying numerator and denominator by `√2` (the `Frac` equivalence)
does not change the result. -/
theorem lowestDenExp_sqrt2_mul (w : ZOmega) (k : ℕ) :
    lowestDenExp (sqrt2 * w) (k + 1) = lowestDenExp w k := by
  rw [lowestDenExp_succ, if_pos (dividesSqrt2_sqrt2_mul w), divSqrt2_sqrt2_mul]

/-- **The lowest-terms denominator exponent never exceeds the fuel**. -/
theorem lowestDenExp_le (z : ZOmega) (k : ℕ) : lowestDenExp z k ≤ k := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [lowestDenExp_succ]
    split
    · exact Nat.le_succ_of_le (ih (divSqrt2 z))
    · exact Nat.le_refl _

/-- **Iterated peel**: `lowestDenExp (√2^n · w) (k + n) = lowestDenExp w k`.
Multiplying numerator and denominator by `√2^n` does not change the
lowest-terms denominator exponent. -/
theorem lowestDenExp_sqrt2_pow_mul (w : ZOmega) (n k : ℕ) :
    lowestDenExp (sqrt2 ^ n * w) (k + n) = lowestDenExp w k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hpow : sqrt2 ^ (m + 1) * w = sqrt2 * (sqrt2 ^ m * w) := by ring
    have hnat : k + (m + 1) = (k + m) + 1 := by omega
    rw [hpow, hnat, lowestDenExp_sqrt2_mul, ih]

/-! ## 3a. Lowest-terms reduction (numerator + exponent) -/

/-- **Lowest-terms reduction** of the fraction `z / √2^k`: returns the
reduced `(numerator, exponent)` pair. Same recursion as `lowestDenExp`
but carrying the numerator, so that the achievability bridge can name
the resulting `ZOmega`-valued numerator. -/
def reduceFrac (z : ZOmega) : ℕ → ZOmega × ℕ
  | 0 => (z, 0)
  | k + 1 => if dividesSqrt2 z then reduceFrac (divSqrt2 z) k else (z, k + 1)

/-- **The reduced exponent equals `lowestDenExp`**. -/
theorem reduceFrac_snd (z : ZOmega) (k : ℕ) :
    (reduceFrac z k).2 = lowestDenExp z k := by
  induction k generalizing z with
  | zero => rfl
  | succ n ih =>
    show (if dividesSqrt2 z then reduceFrac (divSqrt2 z) n else (z, n + 1)).2
       = if dividesSqrt2 z then lowestDenExp (divSqrt2 z) n else n + 1
    split
    · exact ih (divSqrt2 z)
    · rfl

end ZOmega

namespace ZOmegaSqrt2

/-- **Reduction preserves the fraction**: `mk z k = mk z' e` where
`(z', e) = reduceFrac z k`. Each peel multiplies numerator and
denominator by `√2`, which the `Frac` equivalence absorbs. -/
theorem mk_reduceFrac (z : ZOmega) (k : ℕ) :
    mk z k = mk (ZOmega.reduceFrac z k).1 (ZOmega.reduceFrac z k).2 := by
  induction k generalizing z with
  | zero => rfl
  | succ n ih =>
    show mk z (n + 1)
       = mk (if ZOmega.dividesSqrt2 z then ZOmega.reduceFrac (ZOmega.divSqrt2 z) n
              else (z, n + 1)).1
            (if ZOmega.dividesSqrt2 z then ZOmega.reduceFrac (ZOmega.divSqrt2 z) n
              else (z, n + 1)).2
    split
    · next h =>
      rw [← ih (ZOmega.divSqrt2 z), mk_eq_mk_iff]
      have hs := ZOmega.divSqrt2_spec h
      calc z * ZOmega.sqrt2 ^ n
          = (ZOmega.sqrt2 * ZOmega.divSqrt2 z) * ZOmega.sqrt2 ^ n := by rw [hs]
        _ = ZOmega.divSqrt2 z * ZOmega.sqrt2 ^ (n + 1) := by ring
    · rfl

/-! ## 3. The per-element denominator exponent on the quotient ring

`denExp x` is the lowest-terms `√2`-denominator exponent of `x`, lifted
from `Frac` representatives. Well-definedness (independence of
representative) is exactly `ZOmega.lowestDenExp_sqrt2_pow_mul`: two
representatives `(z₁, k₁) ~ (z₂, k₂)` satisfy `z₁·√2^k₂ = z₂·√2^k₁`, and
peeling the shared `√2` powers shows both give the same exponent. -/

/-- **Per-element lowest-terms `√2`-denominator exponent** on `ZOmegaSqrt2`,
well-defined on the quotient. -/
def denExp : ZOmegaSqrt2 → ℕ :=
  Quotient.lift (fun f => ZOmega.lowestDenExp f.num f.den) (by
    rintro a b hab
    show ZOmega.lowestDenExp a.num a.den = ZOmega.lowestDenExp b.num b.den
    have E : a.num * ZOmega.sqrt2 ^ b.den = b.num * ZOmega.sqrt2 ^ a.den := hab
    have hz : ZOmega.sqrt2 ^ b.den * a.num = ZOmega.sqrt2 ^ a.den * b.num := by
      rw [mul_comm (ZOmega.sqrt2 ^ b.den) a.num, E, mul_comm]
    rw [(ZOmega.lowestDenExp_sqrt2_pow_mul a.num b.den a.den).symm,
        (ZOmega.lowestDenExp_sqrt2_pow_mul b.num a.den b.den).symm,
        show a.den + b.den = b.den + a.den from Nat.add_comm _ _, hz])

@[simp] theorem denExp_mk (z : ZOmega) (k : ℕ) :
    denExp (mk z k) = ZOmega.lowestDenExp z k := rfl

/-- **`denExp` of a `ZOmega`-valued element is `0`** (no denominator). -/
@[simp] theorem denExp_of (z : ZOmega) : denExp (of z) = 0 := by
  rw [of_def, denExp_mk]
  rfl

@[simp] theorem denExp_zero : denExp (0 : ZOmegaSqrt2) = 0 := by
  rw [zero_def, denExp_mk]; rfl

@[simp] theorem denExp_one : denExp (1 : ZOmegaSqrt2) = 0 := by
  rw [one_def, denExp_mk]; rfl

/-! ## 4. Achievability: clearing the denominator -/

/-- **`sqrt2^e` in `ZOmegaSqrt2` is `ZOmega.sqrt2^e` over denominator 0**. -/
theorem sqrt2_pow_eq (e : ℕ) : (sqrt2 : ZOmegaSqrt2) ^ e = mk (ZOmega.sqrt2 ^ e) 0 := by
  induction e with
  | zero => rw [pow_zero, pow_zero, one_def]
  | succ n ih => rw [pow_succ, ih, sqrt2_def, mk_mul, Nat.add_zero, pow_succ]

/-- **Achievability (denominator clearing)**: multiplying `x` by
`sqrt2^(denExp x)` lands in the image of `ZOmega` (i.e. clears the
denominator to lowest terms). This is the achievability half of the
`sde ↔ sde_le` bridge: `denExp x` denominators suffice. -/
theorem exists_of_sqrt2_pow_smul (x : ZOmegaSqrt2) :
    ∃ w : ZOmega, (sqrt2 : ZOmegaSqrt2) ^ denExp x * x = of w := by
  induction x using Quotient.inductionOn with
  | _ f =>
    obtain ⟨z, d⟩ := f
    refine ⟨(ZOmega.reduceFrac z d).1, ?_⟩
    show (sqrt2 : ZOmegaSqrt2) ^ denExp (mk z d) * mk z d = of (ZOmega.reduceFrac z d).1
    rw [denExp_mk, mk_reduceFrac z d, ZOmega.reduceFrac_snd, sqrt2_pow_eq, mk_mul, Nat.zero_add,
        of_def, mk_eq_mk_iff]
    ring

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
