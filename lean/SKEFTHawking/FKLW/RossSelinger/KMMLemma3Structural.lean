/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, site 4/4 — the structural KMM Lemma 3 (T-pairing calculus)

Toward eliminating the `kmm_lemma3_alg2` `native_decide` (a ~16.7M-pair `(ZMod 8)⁴`² sweep):
the statement depends on the residues only through the 8-tuple
`(P(x), Q(x), P(y), Q(y), T₀, T₁, T₂, T₃)` where `Tₖ = B(x, ωᵏy)` is the `P`-polarization
pairing (`B(x,z) = Σ xᵢzᵢ`):

  * `P`/`Q` are `ω`-invariant; `Tₖ₊₄ = −Tₖ`;
  * `P(x + ωᵏy) = P(x) + P(y) + 2Tₖ`; `Q(x + ωᵏy) = Q(x) + Q(y) + (Tₖ₊₁ − Tₖ₊₃)`
    (indices signed-folded);
  * **reachability** (numerically validated, 0/36864 failures): the conjugate product
    satisfies `x·ȳ = ⟨T₃, T₂, T₁, T₀⟩` exactly, so norm multiplicativity
    `|x·ȳ|² = |x|²·|y|²` descends to the two `ZMod 8` polynomial identities
    `P(x)P(y) + 2Q(x)Q(y) = T₀²+T₁²+T₂²+T₃²` and
    `P(x)Q(y) + Q(x)P(y) = T₃T₂+T₂T₁+T₁T₀−T₃T₀` — and WITH these two constraints the
    quantified master lemma over `(pX, qX, pY, qY, T₀..T₃)` holds (the free-`T` version
    fails: the constraints are load-bearing).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only; master chunked to the
  kernel budget). **#15**: no new axioms. No `native_decide` in this file.
  Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.KMMLemma3
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.KMM

open Coord4

namespace Coord4

/-- The `P`-polarization pairing `B(x,z) = Σ xᵢzᵢ` (so `P(x+z) = P(x) + P(z) + 2B(x,z)`). -/
def Bform (x z : Coord4) : ZMod 8 :=
  x.1 * z.1 + x.2.1 * z.2.1 + x.2.2.1 * z.2.2.1 + x.2.2.2 * z.2.2.2

/-- `gde` factors through `(P, Q)`. -/
def gdePQ (p q : ZMod 8) : ℕ :=
  min 4 (2 * min (vtwo p) (vtwo q) + (if vtwo p > vtwo q then 1 else 0))

theorem gde_eq_gdePQ (x : Coord4) : gde x = gdePQ (Pform x) (Qform x) := rfl

/-! ### The T-calculus: update formulas and reachability identities (polynomial, `ring`) -/

/-- `P` of a translate: `P(x + z) = P(x) + P(z) + 2·B(x,z)`. -/
theorem Pform_add (x z : Coord4) : Pform (add x z) = Pform x + Pform z + 2 * Bform x z := by
  obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, h⟩ := z
  simp only [Pform, add, Bform]; ring

/-- `Q` of a translate: `Q(x + z) = Q(x) + Q(z) + (B(x, ωz) − B(x, ω³z))`. -/
theorem Qform_add (x z : Coord4) :
    Qform (add x z) = Qform x + Qform z
      + (Bform x (mulOmegaPow 1 z) - Bform x (mulOmegaPow 3 z)) := by
  obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, h⟩ := z
  simp only [Qform, add, Bform, mulOmegaPow, mulOmega]; ring

/-- `P` is `ω`-invariant. -/
theorem Pform_mulOmega (z : Coord4) : Pform (mulOmega z) = Pform z := by
  obtain ⟨e, f, g, h⟩ := z; simp only [Pform, mulOmega]; ring

/-- `Q` is `ω`-invariant. -/
theorem Qform_mulOmega (z : Coord4) : Qform (mulOmega z) = Qform z := by
  obtain ⟨e, f, g, h⟩ := z; simp only [Qform, mulOmega]; ring

/-- The pairing's `ω⁴`-antiperiod: `B(x, ω⁴z) = −B(x, z)`. -/
theorem Bform_mulOmega_four (x z : Coord4) :
    Bform x (mulOmegaPow 4 z) = -Bform x z := by
  obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, h⟩ := z
  simp only [Bform, mulOmegaPow, mulOmega]; ring

/-- **Reachability identity 1** (rational part of `|x·ȳ|² = |x|²·|y|²`):
`P(x)P(y) + 2Q(x)Q(y) = T₀² + T₁² + T₂² + T₃²`. -/
theorem reach_P (x y : Coord4) :
    Pform x * Pform y + 2 * (Qform x * Qform y)
      = Bform x y ^ 2 + Bform x (mulOmegaPow 1 y) ^ 2
        + Bform x (mulOmegaPow 2 y) ^ 2 + Bform x (mulOmegaPow 3 y) ^ 2 := by
  obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, h⟩ := y
  simp only [Pform, Qform, Bform, mulOmegaPow, mulOmega]; ring

/-- **Reachability identity 2** (`√2`-part of `|x·ȳ|² = |x|²·|y|²`):
`P(x)Q(y) + Q(x)P(y) = T₃T₂ + T₂T₁ + T₁T₀ − T₃T₀`. -/
theorem reach_Q (x y : Coord4) :
    Pform x * Qform y + Qform x * Pform y
      = Bform x (mulOmegaPow 3 y) * Bform x (mulOmegaPow 2 y)
        + Bform x (mulOmegaPow 2 y) * Bform x (mulOmegaPow 1 y)
        + Bform x (mulOmegaPow 1 y) * Bform x y
        - Bform x (mulOmegaPow 3 y) * Bform x y := by
  obtain ⟨a, b, c, d⟩ := x; obtain ⟨e, f, g, h⟩ := y
  simp only [Pform, Qform, Bform, mulOmegaPow, mulOmega]; ring

/-! ### The k-sweep update tables -/

/-- The `P`-update of the `k`-th rotation: `P(x + ωᵏy) = P(x) + P(y) + pUpd k`. -/
def pUpd (t0 t1 t2 t3 : ZMod 8) : Fin 4 → ZMod 8
  | 0 => 2 * t0
  | 1 => 2 * t1
  | 2 => 2 * t2
  | 3 => 2 * t3

/-- The `Q`-update of the `k`-th rotation: `Q(x + ωᵏy) = Q(x) + Q(y) + qUpd k`
(`Tₖ₊₁ − Tₖ₊₃` with the `Tₖ₊₄ = −Tₖ` signed fold). -/
def qUpd (t0 t1 t2 t3 : ZMod 8) : Fin 4 → ZMod 8
  | 0 => t1 - t3
  | 1 => t2 + t0
  | 2 => t3 + t1
  | 3 => t2 - t0

end Coord4

/-! ### The master sweeps (kernel `decide` over the reachable `(P,Q,T)`-data)

`qY = −qX` is forced exactly (`Q(x)+Q(y) = 0`), so the translated `Q`-base is `0`;
`2(P(x)+P(y)) = 0` leaves `pY ∈ {−pX, 4−pX}` (translated `P`-base `0` or `4`) — one
master per branch. The two reachability hypotheses are the norm-multiplicativity
constraints (`reach_P`/`reach_Q`); WITHOUT them the sweep is false. -/

set_option maxRecDepth 8000 in
/-- **Master sweep, branch `pY = −pX`** (`P`-base `0`). -/
theorem kmm_master_a : ∀ pX qX t0 t1 t2 t3 : ZMod 8, ∀ j : Fin 2,
    gdePQ pX qX = j.val → gdePQ (-pX) (-qX) = j.val →
    pX * (-pX) + 2 * (qX * (-qX)) = t0 ^ 2 + t1 ^ 2 + t2 ^ 2 + t3 ^ 2 →
    pX * (-qX) + qX * (-pX) = t3 * t2 + t2 * t1 + t1 * t0 - t3 * t0 →
    ∀ s : Fin 3, ∃ k : Fin 4,
      gdePQ (0 + pUpd t0 t1 t2 t3 k) (0 + qUpd t0 t1 t2 t3 k) = (s.val + 1) + j.val := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- **Master sweep, branch `pY = 4 − pX`** (`P`-base `4`). -/
theorem kmm_master_b : ∀ pX qX t0 t1 t2 t3 : ZMod 8, ∀ j : Fin 2,
    gdePQ pX qX = j.val → gdePQ (4 - pX) (-qX) = j.val →
    pX * (4 - pX) + 2 * (qX * (-qX)) = t0 ^ 2 + t1 ^ 2 + t2 ^ 2 + t3 ^ 2 →
    pX * (-qX) + qX * (4 - pX) = t3 * t2 + t2 * t1 + t1 * t0 - t3 * t0 →
    ∀ s : Fin 3, ∃ k : Fin 4,
      gdePQ (4 + pUpd t0 t1 t2 t3 k) (0 + qUpd t0 t1 t2 t3 k) = (s.val + 1) + j.val := by
  decide +kernel

end SKEFTHawking.RossSelinger.KMM
