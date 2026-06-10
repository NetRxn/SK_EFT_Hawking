/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(b) — `ℤ[ω] = ℤ[ζ₈]` is a Euclidean domain

The Ross–Selinger Diophantine theory (arXiv:1403.2975v3 Appendix C) rests on `ℤ`, `ℤ[√2]`, and
`ℤ[ω]` all being Euclidean domains ("A fundamental property…", asserted there without proof; the
gcd computations of Lemmas C.18–C.20 consume it). `ℤ[√2]` shipped in `Zsqrt2EuclideanDomain.lean`;
**Mathlib has no Euclidean instance for `ℤ[ζ₈]`** (only `GaussianInt`), so this file builds it.

## The proof — Gaussian-pair rounding with the perpendicular-corner rescue

`ℤ[ω]` is FREE OF RANK 2 over `ℤ[i]`: `⟨a,b,c,d⟩ = aω³ + bω² + cω + d = γ + δ·ω` with
`γ = d + b·i`, `δ = c + a·i` (`ω² = i`, `ω³ = iω`). NOTE this is sharper than `ℤ[√2][i]`, which is
only an index-2 subring (paper Lemma 5.5) and — being non-integrally-closed — can never be a UFD.

The relative conjugation `ω ↦ −ω` is the existing `σ5`; the relative norm `t·σ5 t = γ² − i·δ²`
lands in `ℤ[i]` (its `a`/`c` coordinates vanish), and the absolute norm factors through it:
`norm t = ((t·σ5 t).d)² + ((t·σ5 t).b)²` — manifestly a **sum of two squares**, so `norm ≥ 0`.

Division: Gaussian-round both `ℤ[i]`-coordinates of `x·σ5 y / (y·σ5 y)`. Each rounding remainder
`e = e₁ + e₂i` has `|e₁|, |e₂| ≤ 1/2`, and the descent needs
`|eγ² − i·eδ²|² = (e₁²−e₂²+2f₁f₂)² + (2e₁e₂−f₁²+f₂²)² < 1`. The triangle bound gives only `≤ 1`
(tight when all four remainders are `±1/2`) — but at the corners `eγ²` is purely imaginary while
`i·eδ²` is purely real, so the two contributions are PERPENDICULAR and the value drops to `1/2`.
Algebraically the whole inequality is the explicit identity
`A² + B² = S² − 2·(e₁(f₁−f₂) + e₂(f₁+f₂))²` with `S = e₁²+e₂²+f₁²+f₂² ≤ 1`, plus the
all-corners case `S = 1 ⟹ A² + B² = 1/2`.

## Consequences

`EuclideanDomain ZOmega` ⟹ `IsPrincipalIdealRing`/`UniqueFactorizationMonoid`/`gcd` for `ℤ[ω]`
(via Mathlib's general instances) — the engine for the paper's Lemma C.20 gcd arguments
(`t = gcd(ξ, u + i)`), i.e. Track 1(c)'s even-power relative-norm criterion.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C (esp. C.18–C.21).
  * Mathlib `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` (the `ℤ[i]` template).
  * `Zsqrt2EuclideanDomain.lean` (the project's `ℤ[√2]` template this mirrors).
-/

import SKEFTHawking.FKLW.RossSelinger.ZOmega
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace ZOmega

/-! ### Subtraction coordinates -/

@[simp] theorem sub_a (x y : ZOmega) : (x - y).a = x.a - y.a := by
  show (x + -y).a = _; simp [sub_eq_add_neg]
@[simp] theorem sub_b (x y : ZOmega) : (x - y).b = x.b - y.b := by
  show (x + -y).b = _; simp [sub_eq_add_neg]
@[simp] theorem sub_c (x y : ZOmega) : (x - y).c = x.c - y.c := by
  show (x + -y).c = _; simp [sub_eq_add_neg]
@[simp] theorem sub_d (x y : ZOmega) : (x - y).d = x.d - y.d := by
  show (x + -y).d = _; simp [sub_eq_add_neg]

/-! ### The `ℤ[i]`-graded structure through `σ5` -/

/-- The relative norm `t·σ5 t` has vanishing `ω³`-coordinate: it lies in `ℤ[i] = ℤ⟨1, ω²⟩`. -/
theorem mul_σ5_self_a (t : ZOmega) : (t * σ5 t).a = 0 := by simp; ring

/-- The relative norm `t·σ5 t` has vanishing `ω`-coordinate: it lies in `ℤ[i] = ℤ⟨1, ω²⟩`. -/
theorem mul_σ5_self_c (t : ZOmega) : (t * σ5 t).c = 0 := by simp; ring

/-- Rational coordinate of the relative norm: `(t·σ5 t).d = 2ac + d² − b²`. -/
theorem mul_σ5_self_d (t : ZOmega) : (t * σ5 t).d = 2 * t.a * t.c + t.d ^ 2 - t.b ^ 2 := by
  simp; ring

/-- `i`-coordinate of the relative norm: `(t·σ5 t).b = a² − c² + 2bd`. -/
theorem mul_σ5_self_b (t : ZOmega) : (t * σ5 t).b = t.a ^ 2 - t.c ^ 2 + 2 * t.b * t.d := by
  simp; ring

/-- The absolute norm is Galois-invariant under `σ5`. -/
theorem norm_σ5 (t : ZOmega) : norm (σ5 t) = norm t := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [norm, σ5, conj, σ3, mul_a, mul_b, mul_c, mul_d]
  ring

/-- **The Gauss-norm form of the absolute norm**: `norm t = ((t·σ5 t).d)² + ((t·σ5 t).b)²`,
the `ℤ[i]`-norm of the relative norm — manifestly a sum of two squares. -/
theorem norm_eq_gauss (t : ZOmega) : norm t = (t * σ5 t).d ^ 2 + (t * σ5 t).b ^ 2 := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [norm, σ5, conj, σ3, mul_a, mul_b, mul_c, mul_d]
  ring

/-- The absolute norm is nonnegative. -/
theorem norm_nonneg (t : ZOmega) : 0 ≤ norm t := by
  rw [norm_eq_gauss]; positivity

/-- The `ℤ[√2]`-factored form of the absolute norm (Ross thesis Def 3.1.4). -/
theorem norm_eq_sq_sub_two_sq (a b c d : ℤ) :
    norm ⟨a, b, c, d⟩
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 - 2 * (a * b - a * d + c * b + c * d) ^ 2 := by
  simp only [norm, σ5, conj, σ3, mul_a, mul_b, mul_c, mul_d]
  ring

/-- **The absolute norm vanishes only at `0`** (via the `ℤ[√2]`-descent `A² = 2B² ⟹ A = B = 0`,
delegated to `Zsqrtd.norm_eq_zero` on the shipped non-square witness `two_ne_sq`). -/
theorem norm_eq_zero_iff {t : ZOmega} : norm t = 0 ↔ t = 0 := by
  constructor
  · intro h
    obtain ⟨a, b, c, d⟩ := t
    rw [norm_eq_sq_sub_two_sq] at h
    set A : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 with hA
    set B : ℤ := a * b - a * d + c * b + c * d with hB
    have hz : Zsqrtd.norm (⟨A, B⟩ : Zsqrtd 2) = 0 := by
      rw [Zsqrtd.norm_def]
      push_cast
      linarith [h]
    have h0 : (⟨A, B⟩ : Zsqrtd 2) = 0 := (Zsqrtd.norm_eq_zero two_ne_sq _).mp hz
    have hA0 : A = 0 := congrArg Zsqrtd.re h0
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    ext <;> simp [ha, hb, hc, hd]
  · rintro rfl
    exact norm_zero

instance : Nontrivial ZOmega := ⟨0, 1, by decide⟩

instance : NoZeroDivisors ZOmega where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have hn : norm x * norm y = 0 := by rw [← norm_mul, h, norm_zero]
    rcases mul_eq_zero.mp hn with h1 | h1
    · exact Or.inl (norm_eq_zero_iff.mp h1)
    · exact Or.inr (norm_eq_zero_iff.mp h1)

/-- **`ℤ[ω]` is an integral domain.** -/
instance : IsDomain ZOmega := NoZeroDivisors.to_isDomain _

/-! ### Multiplication by an `ℤ[i]`-element preserves the `{1, ω}`-grading -/

theorem gauss_mul_d {n q : ZOmega} (ha : n.a = 0) (hc : n.c = 0) :
    (n * q).d = n.d * q.d - n.b * q.b := by simp [ha, hc]; ring

theorem gauss_mul_b {n q : ZOmega} (ha : n.a = 0) (hc : n.c = 0) :
    (n * q).b = n.d * q.b + n.b * q.d := by simp [ha, hc]; ring

theorem gauss_mul_c {n q : ZOmega} (ha : n.a = 0) (hc : n.c = 0) :
    (n * q).c = n.d * q.c - n.b * q.a := by simp [ha, hc]; ring

theorem gauss_mul_a {n q : ZOmega} (ha : n.a = 0) (hc : n.c = 0) :
    (n * q).a = n.d * q.a + n.b * q.c := by simp [ha, hc]; ring

/-! ### The rounded `ℤ[i]`-pair division -/

/-- **Rounded division in `ℤ[ω]`**: Gaussian-round both `ℤ[i]`-coordinates of the exact quotient
`x·σ5 y / (y·σ5 y)`. With `w = x·σ5 y` and `n = y·σ5 y ∈ ℤ[i]`, the `{1, ω}`-graded Gaussian
divisions are `γ_w·n̄/N(n)` and `δ_w·n̄/N(n)`; the four rounded ℚ-coordinates are assembled in
`⟨a,b,c,d⟩` order (`a` = δ-im, `b` = γ-im, `c` = δ-re, `d` = γ-re). -/
def divAux (x y : ZOmega) : ZOmega :=
  ⟨round ((((x * σ5 y).a * (y * σ5 y).d - (x * σ5 y).c * (y * σ5 y).b : ℤ) : ℚ)
      / (((y * σ5 y).d ^ 2 + (y * σ5 y).b ^ 2 : ℤ) : ℚ)),
   round ((((x * σ5 y).b * (y * σ5 y).d - (x * σ5 y).d * (y * σ5 y).b : ℤ) : ℚ)
      / (((y * σ5 y).d ^ 2 + (y * σ5 y).b ^ 2 : ℤ) : ℚ)),
   round ((((x * σ5 y).c * (y * σ5 y).d + (x * σ5 y).a * (y * σ5 y).b : ℤ) : ℚ)
      / (((y * σ5 y).d ^ 2 + (y * σ5 y).b ^ 2 : ℤ) : ℚ)),
   round ((((x * σ5 y).d * (y * σ5 y).d + (x * σ5 y).b * (y * σ5 y).b : ℤ) : ℚ)
      / (((y * σ5 y).d ^ 2 + (y * σ5 y).b ^ 2 : ℤ) : ℚ))⟩

instance : Div ZOmega := ⟨divAux⟩

theorem div_def (x y : ZOmega) : x / y = divAux x y := rfl

instance : Mod ZOmega := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ZOmega) : x % y = x - y * (x / y) := rfl

/-! ### The Gaussian-pair rounding bound (the crux) -/

/-- **The crux inequality**: for Gaussian rounding remainders `|e₁|,|e₂|,|f₁|,|f₂| ≤ 1/2`,
`|eγ² − i·eδ²|² < 1`. The triangle bound is tight (`= 1`) only when all four are `±1/2`, but
there `eγ²` is purely imaginary and `i·eδ²` purely real — perpendicular — and the value is `1/2`.
Algebraic skeleton: `A² + B² = S² − 2(e₁(f₁−f₂) + e₂(f₁+f₂))²` with `S = e₁²+e₂²+f₁²+f₂²`. -/
theorem gauss_pair_bound {e₁ e₂ f₁ f₂ : ℚ} (he₁ : |e₁| ≤ 1 / 2) (he₂ : |e₂| ≤ 1 / 2)
    (hf₁ : |f₁| ≤ 1 / 2) (hf₂ : |f₂| ≤ 1 / 2) :
    (e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2 + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2 < 1 := by
  have he₁' := abs_le.mp he₁
  have he₂' := abs_le.mp he₂
  have hf₁' := abs_le.mp hf₁
  have hf₂' := abs_le.mp hf₂
  have hq₁ : e₁ ^ 2 ≤ 1 / 4 := by nlinarith [he₁'.1, he₁'.2]
  have hq₂ : e₂ ^ 2 ≤ 1 / 4 := by nlinarith [he₂'.1, he₂'.2]
  have hq₃ : f₁ ^ 2 ≤ 1 / 4 := by nlinarith [hf₁'.1, hf₁'.2]
  have hq₄ : f₂ ^ 2 ≤ 1 / 4 := by nlinarith [hf₂'.1, hf₂'.2]
  have hkey : (e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2 + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2
      = (e₁ ^ 2 + e₂ ^ 2 + f₁ ^ 2 + f₂ ^ 2) ^ 2
        - 2 * (e₁ * (f₁ - f₂) + e₂ * (f₁ + f₂)) ^ 2 := by ring
  by_cases hlt : e₁ ^ 2 + e₂ ^ 2 + f₁ ^ 2 + f₂ ^ 2 < 1
  · have hS0 : 0 ≤ e₁ ^ 2 + e₂ ^ 2 + f₁ ^ 2 + f₂ ^ 2 := by positivity
    nlinarith [sq_nonneg (e₁ * (f₁ - f₂) + e₂ * (f₁ + f₂))]
  · -- all four remainders are at the corners: the perpendicular case, value 1/2
    have hS1 : e₁ ^ 2 + e₂ ^ 2 + f₁ ^ 2 + f₂ ^ 2 = 1 :=
      le_antisymm (by linarith) (not_lt.mp hlt)
    have hc₁ : e₁ ^ 2 = 1 / 4 := by linarith
    have hc₂ : e₂ ^ 2 = 1 / 4 := by linarith
    have hc₃ : f₁ ^ 2 = 1 / 4 := by linarith
    have hc₄ : f₂ ^ 2 = 1 / 4 := by linarith
    have hval : (e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2 + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2
        = 4 * (f₁ ^ 2 * f₂ ^ 2) + 4 * (e₁ ^ 2 * e₂ ^ 2) := by
      rw [show e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂ = 2 * f₁ * f₂ by rw [hc₁, hc₂]; ring,
        show 2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2 = 2 * e₁ * e₂ by rw [hc₃, hc₄]; ring]
      ring
    rw [hval, hc₁, hc₂, hc₃, hc₄]
    norm_num

/-! ### Euclidean descent -/

/-- **The Euclidean descent for `ℤ[ω]`**: `norm (x % y) < norm y` for `y ≠ 0`. -/
theorem norm_mod_lt (x : ZOmega) {y : ZOmega} (hy : y ≠ 0) : norm (x % y) < norm y := by
  have hNpos : 0 < norm y :=
    lt_of_le_of_ne (norm_nonneg y) fun h => hy (norm_eq_zero_iff.mp h.symm)
  set n : ZOmega := y * σ5 y with hn
  set w : ZOmega := x * σ5 y with hw
  have hna : n.a = 0 := mul_σ5_self_a y
  have hnc : n.c = 0 := mul_σ5_self_c y
  have hNy : norm y = n.d ^ 2 + n.b ^ 2 := norm_eq_gauss y
  -- the exact ℚ-quotient coordinates and their rounding remainders
  set Nq : ℚ := ((n.d ^ 2 + n.b ^ 2 : ℤ) : ℚ) with hNq
  have hNqpos : 0 < Nq := by
    rw [hNq]
    exact_mod_cast hNy ▸ hNpos
  have hNQ : ((n.d : ℚ)) ^ 2 + ((n.b : ℚ)) ^ 2 ≠ 0 := by
    have h0 : (0 : ℚ) < (n.d : ℚ) ^ 2 + (n.b : ℚ) ^ 2 := by exact_mod_cast hNy ▸ hNpos
    exact ne_of_gt h0
  set u₁ : ℚ := ((w.d * n.d + w.b * n.b : ℤ) : ℚ) / Nq with hu₁
  set u₂ : ℚ := ((w.b * n.d - w.d * n.b : ℤ) : ℚ) / Nq with hu₂
  set v₁ : ℚ := ((w.c * n.d + w.a * n.b : ℤ) : ℚ) / Nq with hv₁
  set v₂ : ℚ := ((w.a * n.d - w.c * n.b : ℤ) : ℚ) / Nq with hv₂
  set e₁ : ℚ := u₁ - round u₁ with he₁
  set e₂ : ℚ := u₂ - round u₂ with he₂
  set f₁ : ℚ := v₁ - round v₁ with hf₁
  set f₂ : ℚ := v₂ - round v₂ with hf₂
  -- the quotient's coordinates are exactly those rounds
  have hqa : (x / y).a = round v₂ := rfl
  have hqb : (x / y).b = round u₂ := rfl
  have hqc : (x / y).c = round v₁ := rfl
  have hqd : (x / y).d = round u₁ := rfl
  -- the remainder relation transported through σ5: (x % y)·σ5 y = w − n·(x/y)
  have hfact : (x % y) * σ5 y = w - n * (x / y) := by
    rw [mod_def, hw, hn]; ring
  -- the round-free exact-quotient identities: `n · (quotient pair) = w` per ℤ[i]-coordinate
  have hud : (n.d : ℚ) * u₁ - (n.b : ℚ) * u₂ = ((w.d : ℤ) : ℚ) := by
    rw [hu₁, hu₂, hNq]
    push_cast
    field_simp
    ring
  have hub : (n.d : ℚ) * u₂ + (n.b : ℚ) * u₁ = ((w.b : ℤ) : ℚ) := by
    rw [hu₁, hu₂, hNq]
    push_cast
    field_simp
    ring
  have hvc : (n.d : ℚ) * v₁ - (n.b : ℚ) * v₂ = ((w.c : ℤ) : ℚ) := by
    rw [hv₁, hv₂, hNq]
    push_cast
    field_simp
    ring
  have hva : (n.d : ℚ) * v₂ + (n.b : ℚ) * v₁ = ((w.a : ℤ) : ℚ) := by
    rw [hv₁, hv₂, hNq]
    push_cast
    field_simp
    ring
  -- the four ℚ-coordinate identities of the transported remainder (`round` stays an atom)
  have hrd : (((w - n * (x / y)).d : ℤ) : ℚ) = n.d * e₁ - n.b * e₂ := by
    rw [sub_d, gauss_mul_d hna hnc, hqd, hqb]
    push_cast
    rw [he₁, he₂]
    linear_combination -hud
  have hrb : (((w - n * (x / y)).b : ℤ) : ℚ) = n.d * e₂ + n.b * e₁ := by
    rw [sub_b, gauss_mul_b hna hnc, hqd, hqb]
    push_cast
    rw [he₁, he₂]
    linear_combination -hub
  have hrc : (((w - n * (x / y)).c : ℤ) : ℚ) = n.d * f₁ - n.b * f₂ := by
    rw [sub_c, gauss_mul_c hna hnc, hqc, hqa]
    push_cast
    rw [hf₁, hf₂]
    linear_combination -hvc
  have hra : (((w - n * (x / y)).a : ℤ) : ℚ) = n.d * f₂ + n.b * f₁ := by
    rw [sub_a, gauss_mul_a hna hnc, hqc, hqa]
    push_cast
    rw [hf₁, hf₂]
    linear_combination -hva
  -- assemble: norm (x % y) · norm y = Nq² · (A² + B²)
  have hprod : ((norm (x % y) : ℤ) : ℚ) * ((norm y : ℤ) : ℚ)
      = Nq ^ 2 * ((e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2
          + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2) := by
    have h2 : norm (x % y) * norm y = norm (w - n * (x / y)) := by
      rw [← norm_σ5 y, ← norm_mul, hfact]
    have h3 : norm (w - n * (x / y))
        = (2 * (w - n * (x / y)).a * (w - n * (x / y)).c
            + (w - n * (x / y)).d ^ 2 - (w - n * (x / y)).b ^ 2) ^ 2
          + ((w - n * (x / y)).a ^ 2 - (w - n * (x / y)).c ^ 2
            + 2 * (w - n * (x / y)).b * (w - n * (x / y)).d) ^ 2 := by
      rw [norm_eq_gauss, mul_σ5_self_d, mul_σ5_self_b]
    have hcast : ((norm (x % y) : ℤ) : ℚ) * ((norm y : ℤ) : ℚ)
        = (((norm (w - n * (x / y)) : ℤ) : ℚ)) := by
      rw [← h2]; push_cast; ring
    rw [hcast, h3]
    push_cast
    rw [hrd, hrb, hrc, hra]
    rw [hNq]
    push_cast
    ring
  -- the crux bound
  have hcrux : (e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2
      + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2 < 1 :=
    gauss_pair_bound (he₁ ▸ abs_sub_round u₁) (he₂ ▸ abs_sub_round u₂)
      (hf₁ ▸ abs_sub_round v₁) (hf₂ ▸ abs_sub_round v₂)
  -- conclude: norm(x%y)·norm y < Nq² = (norm y)², cancel norm y > 0
  have hNqy : Nq = ((norm y : ℤ) : ℚ) := by rw [hNq, hNy]
  have hlt : ((norm (x % y) : ℤ) : ℚ) * ((norm y : ℤ) : ℚ)
      < ((norm y : ℤ) : ℚ) * ((norm y : ℤ) : ℚ) := by
    calc ((norm (x % y) : ℤ) : ℚ) * ((norm y : ℤ) : ℚ)
        = Nq ^ 2 * ((e₁ ^ 2 - e₂ ^ 2 + 2 * f₁ * f₂) ^ 2
            + (2 * e₁ * e₂ - f₁ ^ 2 + f₂ ^ 2) ^ 2) := hprod
      _ < Nq ^ 2 * 1 := mul_lt_mul_of_pos_left hcrux (pow_pos hNqpos 2)
      _ = ((norm y : ℤ) : ℚ) * ((norm y : ℤ) : ℚ) := by rw [hNqy]; ring
  have hyQ : (0 : ℚ) < ((norm y : ℤ) : ℚ) := by exact_mod_cast hNpos
  have : ((norm (x % y) : ℤ) : ℚ) < ((norm y : ℤ) : ℚ) :=
    lt_of_mul_lt_mul_right hlt (le_of_lt hyQ)
  exact_mod_cast this

/-- Division by zero yields zero. -/
theorem div_zero' (x : ZOmega) : x / 0 = 0 := by
  rw [div_def, divAux]
  have h5 : σ5 (0 : ZOmega) = 0 := by ext <;> simp [σ5]
  ext <;> simp [h5]

/-- natAbs-level descent for the Euclidean structure. -/
theorem natAbs_norm_mod_lt (x : ZOmega) {y : ZOmega} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  have h := norm_mod_lt x hy
  have h0 := norm_nonneg (x % y)
  omega

/-- Multiplying by a nonzero element does not decrease the norm measure. -/
theorem natAbs_norm_le_mul_left (x : ZOmega) {y : ZOmega} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  have h1 : (norm y).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr fun h => hy (norm_eq_zero_iff.mp h)
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h1)

/-- **`ℤ[ω] = ℤ[ζ₈]` is a Euclidean domain** — hence a PID and a UFD, with computable `gcd`:
the engine for the Ross–Selinger Appendix-C Diophantine theory (Lemmas C.18–C.21). -/
noncomputable instance : EuclideanDomain ZOmega :=
  { (inferInstance : CommRing ZOmega),
    (inferInstance : Nontrivial ZOmega) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := div_zero'
    quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
    r := fun a b => (norm a).natAbs < (norm b).natAbs
    r_wellFounded := (measure fun a : ZOmega => (norm a).natAbs).wf
    remainder_lt := fun a b hb => natAbs_norm_mod_lt a hb
    mul_left_not_lt := fun a b hb => not_lt.mpr (natAbs_norm_le_mul_left a hb) }

end ZOmega
end SKEFTHawking.RossSelinger
