/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM Lemma 3 via Algorithm 2 (the finite decide)

KMM Lemma 3 (arXiv:1206.5236 v4, p. 6; proof = **Algorithm 2**, p. 14) is the
sde-reduction existence lemma:

> For a unit column `(z,w)ᵀ` over `ℤ[1/√2,i]` with `sde(|z|²) ≥ 4`, and each
> `s ∈ {−1,0,1}`, there is `k ∈ {0,1,2,3}` with
> `sde(|(z+wωᵏ)/√2|²) − sde(|z|²) = s`.

After clearing denominators (`x = z·√2^m`, `y = w·√2^m`; `gde(|x|²)=gde(|y|²)=j∈{0,1}`
by Lemma 4) the statement becomes (KMM Eq. 14): for `(x,y)` with `|x|²+|y|²=2^m`,
`gde(x)=gde(y)=j` and each `s∈{1,2,3}`, `∃k: gde(|x+ωᵏy|²) = s+j`.

**KMM's proof is NOT a closed-form `k`-selector / `𝔭`-adic case split** (the DR
established no such proof is published). It is an **exhaustive computer check**
over the residues `ℤ[ω]/(2³)`: `gde(|·|²)` capped at `4` is determined by the
coordinates `mod 8` (verified — only the zero residue is ambiguous, and it has
`gde > 1` so is excluded from the `j∈{0,1}` base), and the squared modulus is
`|x|² = P(x) + √2·Q(x)` with `P, Q` the two quadratic forms below; `gde(|·|²)` is
then read off `(v₂(P), v₂(Q))` via KMM Prop 1. Running Algorithm 2 over all
residue pairs satisfying the necessary congruences `P(x)+P(y) ≡ 0 ∨ 4` and
`Q(x)+Q(y) ≡ 0 (mod 8)` and `gde = gde = j` returns **true** — this file ships
the residue vocabulary (`Coord4`, `Pform`, `Qform`, `mulOmega`, `vtwo`, `gde`);
the theorem itself (`kmm_lemma3_alg2`) lives in `KMMLemma3Alg2.lean`, proved
**structurally** (Phase 6AO Track 3, 2026-06-10): the former ~16.7M-pair
`native_decide` was eliminated via the T-pairing calculus + the two 262k-tuple
kernel master sweeps of `KMMLemma3Structural.lean`.

**The `P+P ∈ {0,4}` disjunction covers the whole reduction regime `sde(|z|²) ≥ 4`.**
The cleared column satisfies `|x|²+|y|² = 2^m` with `m = s_c` the column clearing
exponent, and `sde(|z|²) = 2·s_c − gde(|x|²) = 2·m − j`. Thus `sde ≥ 4` splits as:
`m ≥ 3` (sde ≥ 5; `2^m ≡ 0`) and `m = 2` (sde = 4, `j = 0`; `2^m = 4`). Both the
`P+P ≡ 0` and `P+P ≡ 4` residue classes are required, and both are computer-checked
true here (786432 pairs, 0 fails — `scripts/kmm_zomega_reference_oracle.py` residue
mode). An earlier `P+P ≡ 0`-only statement silently dropped the `sde = 4` boundary
case the algorithm passes through on every descent `… → 5 → 4 → 3`.

All formulas were cross-validated against `scripts/kmm_zomega_reference_oracle.py`
in the project's `ZOmega ⟨a,b,c,d⟩ = a·ω³+b·ω²+c·ω+d` convention (0 mismatches
over the 65535 nonzero residues; Algorithm 2 `FAILS=0` over 393216 pairs):
`P(x)=a²+b²+c²+d²`, `Q(x)=ab+bc+cd−ad` (`= (|x|²).d, (|x|²).c`), and the
`ω`-action `⟨a,b,c,d⟩ ↦ ⟨b,c,d,−a⟩` (the project `ZOmega.mul` by `ω`, which differs
from the DR's loose `mulOmega` formula — the oracle pins the correct one).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected. No `native_decide` —
  kernel-pure `{propext, Classical.choice, Quot.sound}`.

-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.KMM

/-- A `ℤ[ω]/(2³)` residue: the four integer coordinates `⟨a,b,c,d⟩` taken `mod 8`. -/
abbrev Coord4 : Type := ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8

namespace Coord4

/-- `P(x) = a² + b² + c² + d²` — the rational part of `|x|²` (`= (|x|²).d`). -/
def Pform (x : Coord4) : ZMod 8 := x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2

/-- `Q(x) = ab + bc + cd − ad` — the `√2`-part of `|x|²` (`= (|x|²).c`). -/
def Qform (x : Coord4) : ZMod 8 :=
  x.1 * x.2.1 + x.2.1 * x.2.2.1 + x.2.2.1 * x.2.2.2 - x.1 * x.2.2.2

/-- Multiplication by `ω` on coordinates: `⟨a,b,c,d⟩ ↦ ⟨b,c,d,−a⟩` (the project
`ZOmega.mul` by `ω`, oracle-verified). -/
def mulOmega (x : Coord4) : Coord4 := (x.2.1, x.2.2.1, x.2.2.2, -x.1)

/-- `ωᵏ · x`. -/
def mulOmegaPow : ℕ → Coord4 → Coord4
  | 0, x => x
  | n + 1, x => mulOmega (mulOmegaPow n x)

/-- Coordinatewise addition. -/
def add (x y : Coord4) : Coord4 :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)

/-- `2`-adic valuation of a `ZMod 8` value (`v₂` capped at `3` for `≡ 0`). -/
def vtwo (r : ZMod 8) : ℕ :=
  if r = 0 then 3 else if r = 4 then 2 else if r = 2 ∨ r = 6 then 1 else 0

/-- `gde(|x|², √2)` capped at `4`, read off `(v₂(P), v₂(Q))` via KMM Prop 1:
`gde = 2·min(v₂P, v₂Q) + [v₂P > v₂Q]`. Determined by the residue `mod 8`
(verified against the peel-based gde, 0 mismatches over all nonzero residues). -/
def gde (x : Coord4) : ℕ :=
  let vA := vtwo (Pform x)
  let vB := vtwo (Qform x)
  min 4 (2 * min vA vB + (if vA > vB then 1 else 0))

end Coord4

open Coord4


end SKEFTHawking.RossSelinger.KMM
