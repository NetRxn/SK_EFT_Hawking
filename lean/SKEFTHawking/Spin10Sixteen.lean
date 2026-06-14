/-
# Phase 5q.E Wave 2 — Spin(10) Weyl spinor = 16, branching 16 → 10 ⊕ 5̄ ⊕ 1

The facet-1 ↔ facet-2 *algebraic half* of the "16 convergence" (see
`docs/SIXTEEN_CONVERGENCE_STATUS.md`): the SM "16 Weyl fermions per generation" is the
**16 of Spin(10)** (the irreducible Weyl/half-spinor), and the actual SM multiplet content
realizes the Georgi–Glashow SU(5) branching `16 → 10 ⊕ 5̄ ⊕ 1`. This module makes that
realization machine-checked at the level of **representation dimensions** and the explicit
SM-fermion assignment, grounded in `SMFermionData.lean`.

## The genuine content (vs a literal "16")

The three SU(5) multiplets are the **even exterior powers** `Λ⁰, Λ², Λ⁴` of the SU(5)
fundamental `5` (this is *why* the Spin(10) Weyl spinor decomposes the way it does):

  * `1  = Λ⁰`, `dim = C(5,0) = 1`   (the singlet — `ν̄_R`)
  * `10 = Λ²`, `dim = C(5,2) = 10`  (`Q_L, ū_R, ē_R`)
  * `5̄  = Λ⁴ ≅ 5̄`, `dim = C(5,4) = 5` (`d̄_R, L`)

and `C(5,0) + C(5,2) + C(5,4) = 2^(5-1) = 16` is the rep-theoretic identity behind the "16"
(`weyl_spinor_as_even_exterior`). Every "16", "10", "5", "1" here is a computed binomial /
spinor-dimension, not a hard-coded numeral; the branching theorems are falsified by any wrong
SU(5) assignment (e.g. placing `ē_R` in the 5̄ breaks a dimension sum).

## What this is NOT (honesty — keep in any paper)

This is the **branching-rule realization** at the dimension/assignment level, NOT a
construction of the Spin(10) spinor module. Building the irreducible Weyl spinor of Spin(10)
via `CliffordAlgebra`, the embedding `SU(5) ⊂ Spin(10)`, and the branching as a
representation-theory theorem is Mathlib-absent (generational; Phase 5q.E roadmap §"Walls").
A shared "16" **constrains, it does not derive** the SM. The 3-generation headline is
independent and does not import this module.

## References
  - Georgi–Glashow, Phys. Rev. Lett. 32, 438 (1974) — SU(5).
  - Fritzsch–Minkowski, Ann. Phys. 93, 193 (1975) — SO(10) and the 16.
  - `SMFermionData.lean` — the one-generation SM fermion content (`components`,
    `total_components_with_nu_R = 16`).
  - `docs/SIXTEEN_CONVERGENCE_STATUS.md` §3 (facet 1).
-/

import Mathlib
import SKEFTHawking.SMFermionData

namespace SKEFTHawking.Spin10

/-! ## §1. The SU(5) irreps in the spinor branching, as even exterior powers -/

/-- The three SU(5) irreps in the Spin(10) Weyl-spinor branching `16 → 10 ⊕ 5̄ ⊕ 1`.
Each is an even exterior power `Λᵏ` of the SU(5) fundamental `5`: `1 = Λ⁰`, `10 = Λ²`,
`5̄ = Λ⁴`. -/
inductive SU5Irrep | ten | fivebar | one
  deriving DecidableEq, Fintype

/-- Dimension of each SU(5) irrep as the genuine dimension of the corresponding even
exterior power `Λᵏ(ℂ⁵)`, namely `C(5,k)`: `dim Λ²(5) = C(5,2) = 10`,
`dim Λ⁴(5) = C(5,4) = 5` (and `Λ⁴(5) ≅ 5̄`), `dim Λ⁰(5) = C(5,0) = 1`. -/
def su5dim : SU5Irrep → ℕ
  | .ten => Nat.choose 5 2
  | .fivebar => Nat.choose 5 4
  | .one => Nat.choose 5 0

/-- The three irrep dimensions are `10, 5, 1` (computed from `C(5,k)`, not asserted). -/
theorem su5dim_values : su5dim .ten = 10 ∧ su5dim .fivebar = 5 ∧ su5dim .one = 1 := by decide

/-- **The Weyl spinor = even exterior powers.** The Spin(10) Weyl (half-)spinor has
dimension `2^(5-1) = 16`, realized as `Λ⁰ ⊕ Λ² ⊕ Λ⁴` of the SU(5) fundamental:
`C(5,0) + C(5,2) + C(5,4) = 2^4`. This is the representation-theoretic identity behind the
"16" — two independent computations of 16 (binomial sum and spinor-dimension formula). -/
theorem weyl_spinor_as_even_exterior :
    su5dim .one + su5dim .ten + su5dim .fivebar = 2 ^ (5 - 1) := by decide

/-! ## §2. The Georgi–Glashow SU(5) assignment of the SM fermions -/

/-- The Georgi–Glashow SU(5) embedding: the physically-correct multiplet of each SM fermion.
`10 ⊃ {Q_L, ū_R, ē_R}`, `5̄ ⊃ {d̄_R, L}`, `1 = ν̄_R`. -/
def su5Multiplet : SMFermion → SU5Irrep
  | .Q_L => .ten | .u_R_bar => .ten | .e_R_bar => .ten
  | .d_R_bar => .fivebar | .L => .fivebar | .nu_R_bar => .one

/-- Every SM fermion lies in exactly one of the three multiplets: the assignment is a genuine
partition of the one-generation content, not a relabeling that drops or double-counts. -/
theorem su5_partition_exhaustive (f : SMFermion) :
    su5Multiplet f = .ten ∨ su5Multiplet f = .fivebar ∨ su5Multiplet f = .one := by
  cases f <;> simp [su5Multiplet]

/-! ## §3. Branching realization — components per multiplet = irrep dimension -/

/-- **Branching realization (10).** The SM fermion components assigned to the SU(5) `10`
sum to its dimension: `components(Q_L)+components(ū_R)+components(ē_R) = 6+3+1 = 10 = dim Λ²`. -/
theorem su5_branching_ten :
    (∑ f ∈ Finset.univ.filter (fun f => su5Multiplet f = .ten), components f) = su5dim .ten := by
  decide

/-- **Branching realization (5̄).** `components(d̄_R)+components(L) = 3+2 = 5 = dim Λ⁴`. -/
theorem su5_branching_fivebar :
    (∑ f ∈ Finset.univ.filter (fun f => su5Multiplet f = .fivebar), components f)
      = su5dim .fivebar := by
  decide

/-- **Branching realization (1).** `components(ν̄_R) = 1 = dim Λ⁰` — the singlet is the
right-handed neutrino. -/
theorem su5_branching_one :
    (∑ f ∈ Finset.univ.filter (fun f => su5Multiplet f = .one), components f) = su5dim .one := by
  decide

/-- **The full decomposition `16 → 10 ⊕ 5̄ ⊕ 1`.** The SM one-generation component count
(`total_components_with_nu_R = 16`) equals the sum of the three SU(5) multiplet dimensions
(`= 2^4`, the Spin(10) Weyl-spinor dimension). Routes through the real SM count, not a
literal 16. -/
theorem spinor16_decomposition :
    components .Q_L + components .u_R_bar + components .d_R_bar +
      components .L + components .e_R_bar + components .nu_R_bar
      = su5dim .ten + su5dim .fivebar + su5dim .one := by
  rw [total_components_with_nu_R]; decide

/-! ## §4. Module summary

Genuine Spin(10)-spinor branching content (the facet-1 ↔ facet-2 algebraic half):
  - `su5dim` grounds `10, 5, 1` as `C(5,2), C(5,4), C(5,0)` (even exterior powers Λ⁰,Λ²,Λ⁴).
  - `weyl_spinor_as_even_exterior` — `C(5,0)+C(5,2)+C(5,4) = 2^4`, the "16" as half-spinor dim.
  - `su5Multiplet` + `su5_partition_exhaustive` — the Georgi–Glashow assignment is a partition.
  - `su5_branching_{ten,fivebar,one}` — components per multiplet = irrep dimension (falsified
    by any wrong assignment).
  - `spinor16_decomposition` — SM 16 = 10 + 5̄ + 1, via `total_components_with_nu_R`.

Wall (documented): constructing the Spin(10) spinor module / SU(5) ⊂ Spin(10) / the branching
as a rep-theory theorem is Mathlib-absent. All proofs kernel-pure (`decide` / `simp`); no
axiom / sorry / native_decide.
-/

end SKEFTHawking.Spin10
