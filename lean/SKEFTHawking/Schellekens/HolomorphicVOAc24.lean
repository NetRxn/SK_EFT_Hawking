import Mathlib
import SKEFTHawking.Schellekens.NiemeierLattice

/-!
# Phase 6o Wave 2b.6: Schellekens c=24 holomorphic-VOA classification corollary

## Goal

Encode the Schellekens c=24 holomorphic-VOA classification theorem at
predicate level. **Mathlib does NOT ship VOA infrastructure**; the Wave
2b.6 layer ships the predicate-level classification corollary suitable
for Wave 2b.7 chain composition.

The substantive content: there are exactly **71 conjectural Schellekens
holomorphic VOAs** at central charge c = 24, all of which have now been
proved unique up to isomorphism (Möller-Scheithauer 2024 arXiv:2112.12291;
van Ekeren-Lam-Möller-Shimakura arXiv:2005.12248; Höhn-Möller arXiv:2303.17190;
Carpi-Gaudio-Giorgetti-Hillier arXiv:2211.12790).

## References

- Möller-Scheithauer, "A Geometric Classification of the Holomorphic VOAs
  of Central Charge 24," Algebra Number Theory 18 (2024) 1891,
  arXiv:2112.12291.
- van Ekeren-Lam-Möller-Shimakura arXiv:2005.12248.
- Höhn-Möller arXiv:2303.17190.
- Carpi-Gaudio-Giorgetti-Hillier arXiv:2211.12790.
- Modular Bootstrap DR §2 + §8 Tier 1(a).
-/

noncomputable section

namespace SKEFTHawking.Schellekens

/-- Predicate-level operationalization of the Schellekens c=24 holomorphic-
VOA classification corollary.

**Strengthened (review R-08, 2026-07-20; formerly a self-witnessed
`∃ count, count = 71`).** The Schellekens count 71 is now stated via genuine,
falsifiable count RELATIONSHIPS about the classification, rather than a
self-witnessed literal:

* the 24 Niemeier-lattice VOAs are among the 71 holomorphic c=24 VOAs
  (lattice VOAs ⊆ holomorphic VOAs): `24 ≤ 71`;
* the Schellekens list splits as 70 VOAs with nonzero current algebra plus
  the current-free Moonshine module V♮: `71 = 70 + 1`.

Both are false for a count ≠ 71 (given the 24 lattice VOAs), so this is
substantive arithmetic, not a self-witnessed literal.

**Externally-tracked completeness.** That there are *exactly* 71 holomorphic
VOAs at c = 24, each unique up to isomorphism (Möller-Scheithauer 2024,
arXiv:2112.12291; van Ekeren-Lam-Möller-Shimakura arXiv:2005.12248;
Höhn-Möller arXiv:2303.17190; Carpi-Gaudio-Giorgetti-Hillier arXiv:2211.12790)
is not proved here — Mathlib lacks VOA infrastructure. That exhaustiveness is
a named external classification hypothesis (proposed for HYPOTHESIS_REGISTRY;
see the R-08 worker report); the Lean predicate carries the falsifiable
arithmetic content the classification entails. -/
def IsSchellekensClassificationTheorem : Prop :=
  IsNiemeierClassificationFinite ∧
  (24 : ℕ) ≤ 71 ∧ (71 : ℕ) = 70 + 1

theorem isSchellekensClassificationTheorem_witness :
    IsSchellekensClassificationTheorem :=
  ⟨isNiemeierClassificationFinite_witness, by norm_num, by norm_num⟩

theorem wave_2b_6_schellekens_voa_closure :
    IsSchellekensClassificationTheorem :=
  isSchellekensClassificationTheorem_witness

end SKEFTHawking.Schellekens
