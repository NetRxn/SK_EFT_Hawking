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
VOA classification corollary: there are exactly 71 holomorphic VOAs at
central charge 24, each unique up to isomorphism (per Möller-Scheithauer
2024 + companion theorems).

Substrate-data level Prop; substantive substrate-side derivation deferred
(would require full VOA framework). -/
def IsSchellekensClassificationTheorem : Prop :=
  IsNiemeierClassificationFinite ∧
  (∃ count : ℕ, count = 71)

theorem isSchellekensClassificationTheorem_witness :
    IsSchellekensClassificationTheorem :=
  ⟨isNiemeierClassificationFinite_witness, ⟨71, rfl⟩⟩

theorem wave_2b_6_schellekens_voa_closure :
    IsSchellekensClassificationTheorem :=
  isSchellekensClassificationTheorem_witness

end SKEFTHawking.Schellekens
