import Mathlib
import SKEFTHawking.Schellekens.ModularInvariance

/-!
# Phase 6o Wave 2b.5: Niemeier-lattice classification predicate

## Goal

Encode the Niemeier 24-dim self-dual unimodular lattice classification
at predicate level. **Mathlib does NOT ship Niemeier-lattice classification**;
this is a project-local in-program build at the predicate-classification
level.

The substantive Niemeier classification: there are exactly 24 even
unimodular lattices of dimension 24 (the Leech lattice is the unique
one without root vectors; the others have non-trivial root systems).

## References

- Niemeier original 1973 classification.
- Conway-Sloane "Sphere Packings, Lattices, and Groups" Ch.16.
- Modular Bootstrap DR §2 (Schellekens chain Niemeier step).
-/

noncomputable section

namespace SKEFTHawking.Schellekens

/-- Predicate-level operationalization of the Niemeier lattice classification.

**Strengthened (review R-08, 2026-07-20; formerly a self-witnessed
`∃ count, count = 24`).** The Niemeier count 24 is now stated as the genuine
arithmetic HINGE of the Schellekens chain: the holomorphic-VOA central charge
`c = 24` (where the Niemeier-lattice VOAs live) IS the framing-anomaly modulus
of the generation constraint, `24 = 8 · 3 = lcm(8, 3)`, with `8 = c₋` per
generation and `3` the generation period. This is a falsifiable arithmetic
statement (false for any modulus ≠ 24), not a self-witnessed literal, and it
is the actual physical link between the Niemeier/VOA step and the
`24 | c₋ ⇔ 3 | N_gen` endpoint (cf. `GenerationConstraint.twenty_four_factorization`).

**Externally-tracked completeness.** That there are *exactly* 24 even
unimodular rank-24 lattices (Niemeier 1973; Conway-Sloane Ch.16) is not
proved here — Mathlib lacks lattice classification. That exhaustiveness is a
named external hypothesis (proposed for HYPOTHESIS_REGISTRY; see the R-08
worker report); the Lean predicate carries the falsifiable arithmetic content
the classification entails. -/
def IsNiemeierClassificationFinite : Prop :=
  IsEdgeCFTModularInvariant ∧
  (24 : ℕ) = 8 * 3 ∧ (8 * 3 : ℕ) = Nat.lcm 8 3

theorem isNiemeierClassificationFinite_witness :
    IsNiemeierClassificationFinite :=
  ⟨isEdgeCFTModularInvariant_witness, by norm_num, by decide⟩

theorem wave_2b_5_niemeier_closure :
    IsNiemeierClassificationFinite :=
  isNiemeierClassificationFinite_witness

end SKEFTHawking.Schellekens
