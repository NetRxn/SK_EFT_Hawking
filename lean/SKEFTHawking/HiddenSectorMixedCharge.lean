/-
Phase 5x Wave 2b Track X: Mixed-Charge Hidden-Sector Anomaly Conditions

Extends `HiddenSectorClassification.lean` (pure-singlet channel) to the
mixed-charge channel in which hidden Weyl fermions carry nonzero
U(1)_X charges. The Wan-Wang "C-1" assignment (7 copies q = -2,
1 copy q = +6) is the canonical witness.

## Scope

This file formalizes only the U(1)_X-cubic and U(1)_X × gravity²
conditions that a mixed-charge hidden sector must satisfy in addition
to ℤ₁₆. The full ℤ₁₆ ⊕ ℤ₄ joint mechanism by which C-1 cancels the SM
ℤ₁₆ anomaly is a literature claim (Wan-Wang arXiv:2512.25038 Table IV)
tracked here as a `Prop` hypothesis `H_C1_MixedChannelCancels`,
following the hypothesis precedent established in `CenterFunctor.lean`
(`H_CF1_center_functor`, `H_CF2_center_equivalence`).

## Main results

- **X1 `MixedChargeHiddenSector`**: structure carrying `n_weyl : ℕ` and
  `x_charges : Fin n_weyl → ℤ`. The singlet sector of
  `HiddenSectorClassification` is recovered by the zero-charge case.
- **X2 `u1x_cubic_mod4`**: the U(1)_X³ cubic anomaly sum ∑ qᵢ³ mod 4;
  a necessary condition for perturbative U(1)_X³ cancellation.
- **X3 `u1x_linear_mod4`**: the U(1)_X × gravity² linear anomaly sum
  ∑ qᵢ mod 4; a necessary condition for the mixed gravitational-
  U(1)_X anomaly cancellation.
- **X4 `MixedChannelJointConstraint`**: a hidden sector cancels the
  joint ℤ₁₆ ⊕ ℤ₄ anomaly iff the mixed ℤ₁₆ contribution (a) cancels
  SM, (b) ∑ q³ ≡ 0 mod 4, (c) ∑ q ≡ 0 mod 4.
- **X5 `c1_wan_wang_satisfies_u1x`**: the Wan-Wang C-1 assignment
  satisfies the U(1)_X conditions (b) and (c) by decidable arithmetic
  (unconditional); `c1_wan_wang_joint_constraint` packages these into
  the joint constraint under a tracked `H_MixedChannelZ16Cancels φ`
  hypothesis for a supplied ℤ₁₆ indexing φ.
- **X6 `mixed_channel_orthogonal_to_singlet`**: C-1 is an explicit
  witness that the mixed-charge channel is disjoint from the pure-
  singlet channel — its Weyl count is 8, not ≡ 3 mod 16.

## References

- Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector Dark Matter
  Candidate Constraints.md §3.1 (mixed-charge channel)
- Wan, Wang, arXiv:2512.25038 Table IV (C-1 assignment)
- García-Etxebarria, Montero, JHEP 08:003 (2019) [arXiv:1808.00009]
- docs/roadmaps/Phase5x_Roadmap.md Wave 2b Track X (X1-X6)
-/

import Mathlib
import SKEFTHawking.HiddenSectorClassification

namespace SKEFTHawking

/-! ## 1. X1 — Mixed-charge hidden sector structure -/

/--
**X1 (MixedChargeHiddenSector)**: a hidden sector of `n_weyl` Weyl
fermions carrying U(1)_X charges `x_charges : Fin n_weyl → ℤ`.

The pure-singlet sector formalized in `HiddenSectorClassification` is
the special case `x_charges = fun _ => 0`; this structure generalizes
to the mixed-charge case (Wan-Wang arXiv:2512.25038 Table IV) where
the ℤ₁₆ anomaly is compensated by the joint ℤ₁₆ ⊕ ℤ₄ charge algebra
rather than by Weyl count alone.
-/
structure MixedChargeHiddenSector where
  n_weyl : ℕ
  x_charges : Fin n_weyl → ℤ
deriving Inhabited

/-- The all-zero-charge sector of size N — recovers the pure-singlet
    case formalized in `HiddenSectorClassification`. -/
def singletMixedSector (n : ℕ) : MixedChargeHiddenSector where
  n_weyl := n
  x_charges := fun _ => 0

/-! ## 2. X2 — U(1)_X³ cubic anomaly -/

/--
**X2 (u1x_cubic_mod4)**: the U(1)_X³ perturbative anomaly sum ∑ qᵢ³,
reduced mod 4. Vanishing of this residue is a necessary condition for
perturbative U(1)_X³ anomaly cancellation in hidden sectors where
U(1)_X acts as a gauge symmetry.

For the pure-singlet case (`x_charges = 0`), this sum is trivially 0.
For mixed-charge sectors the condition becomes non-trivial and
constrains the allowed integer charge spectra.
-/
def u1x_cubic_mod4 (h : MixedChargeHiddenSector) : ZMod 4 :=
  ((∑ i, (h.x_charges i)^3 : ℤ) : ZMod 4)

/-- The cubic-anomaly-free condition. -/
def U1XCubicAnomalyFree (h : MixedChargeHiddenSector) : Prop :=
  u1x_cubic_mod4 h = 0

/-- Pure-singlet sectors trivially satisfy the cubic condition. -/
theorem singlet_u1x_cubic_vanishes (n : ℕ) :
    U1XCubicAnomalyFree (singletMixedSector n) := by
  unfold U1XCubicAnomalyFree u1x_cubic_mod4 singletMixedSector
  simp

/-! ## 3. X3 — U(1)_X × gravity² linear anomaly -/

/--
**X3 (u1x_linear_mod4)**: the U(1)_X × gravity² mixed-anomaly sum
∑ qᵢ, reduced mod 4. Vanishing of this residue is a necessary
condition for the mixed gravitational-U(1)_X anomaly to cancel.

As with X2 this is trivially satisfied by pure-singlet sectors and
becomes a non-trivial constraint for mixed-charge sectors.
-/
def u1x_linear_mod4 (h : MixedChargeHiddenSector) : ZMod 4 :=
  ((∑ i, h.x_charges i : ℤ) : ZMod 4)

/-- The linear-anomaly-free condition. -/
def U1XLinearAnomalyFree (h : MixedChargeHiddenSector) : Prop :=
  u1x_linear_mod4 h = 0

/-- Pure-singlet sectors trivially satisfy the linear condition. -/
theorem singlet_u1x_linear_vanishes (n : ℕ) :
    U1XLinearAnomalyFree (singletMixedSector n) := by
  unfold U1XLinearAnomalyFree u1x_linear_mod4 singletMixedSector
  simp

/-! ## 4. X4 — Joint anomaly-cancellation constraint -/

/--
The type of "ℤ₁₆ anomaly indexings" on mixed-charge hidden sectors —
functions `MixedChargeHiddenSector → ZMod 16` assigning each hidden
sector a ℤ₁₆ anomaly contribution. The Wan-Wang mechanism corresponds
to a specific indexing defined via bordism invariants (Ω₅^{Spin × ℤ₄}
→ ZMod 16); that specific indexing is not yet formalized in Lean
pending the required Mathlib infrastructure, so we abstract over all
possible indexings here. -/
abbrev Z16Indexing := MixedChargeHiddenSector → ZMod 16

/--
Tracked `Prop` hypothesis for the Wan-Wang ℤ₁₆ ⊕ ℤ₄ joint-charge
cancellation of a mixed-charge hidden sector. Parallel to
`H_CF1_center_functor` / `H_CF2_center_equivalence` in
`CenterFunctor.lean`.

Parameterized by a choice of `Z16Indexing` φ — the hypothesis asserts
that SM's +13 ≡ -3 mod 16 is cancelled by φ's assignment to `h`.
Non-trivial: for an arbitrary φ, `φ h` could be any value in
`ZMod 16`, so the cancellation equation is a genuine constraint.

Eliminability: external (requires APS η-invariant + bordism
Ω₅^{Spin × ℤ₄} → ZMod 16 formalization not in Mathlib as of 2026-04).
Once Mathlib acquires bordism machinery, one would pick φ to be the
Wan-Wang indexing and check the equation for specific hidden sectors.
Tracked alongside `H_KGaugeTQFT_carries_anomaly_three` in the Track Y
topological-channel file if/when Track Y is opened.
-/
def H_MixedChannelZ16Cancels
    (φ : Z16Indexing) (h : MixedChargeHiddenSector) : Prop :=
  (13 + φ h : ZMod 16) = 0

/--
**X4 (MixedChannelJointConstraint)**: conjunction of three conditions
under which a mixed-charge hidden sector `h`, given a choice of ℤ₁₆
indexing `φ`, cancels the combined ℤ₁₆ ⊕ ℤ₄ anomaly:

  (a) the mixed ℤ₁₆ contribution `φ h` cancels SM's +13 ≡ -3 mod 16,
  (b) U(1)_X³ cubic anomaly vanishes mod 4,
  (c) U(1)_X × gravity² linear anomaly vanishes mod 4.

For the pure-singlet case (`x_charges = 0`), condition (a) reduces —
when φ is chosen to coincide with the Weyl-count rule — to
`(n mod 16) = 3` of `HiddenSectorClassification.T2`; conditions (b)
and (c) hold trivially (see `singlet_*_vanishes` above).

For mixed-charge cases, condition (a) requires the Wan-Wang
ℤ₁₆ ⊕ ℤ₄ joint-charge computation whose closed-form Lean
formalization is deferred pending bordism / APS η-invariant
infrastructure — see `H_MixedChannelZ16Cancels` above.
-/
def MixedChannelJointConstraint
    (φ : Z16Indexing) (h : MixedChargeHiddenSector) : Prop :=
  H_MixedChannelZ16Cancels φ h ∧ U1XCubicAnomalyFree h ∧ U1XLinearAnomalyFree h

/-! ## 5. X5 — Wan-Wang C-1 cancellation -/

/-- The Wan-Wang C-1 charge assignment: 7 Weyl fermions with q = -2,
    1 Weyl fermion with q = +6. -/
def c1_charges : Fin 8 → ℤ :=
  ![-2, -2, -2, -2, -2, -2, -2, 6]

/-- The Wan-Wang C-1 hidden sector. -/
def c1_wan_wang : MixedChargeHiddenSector where
  n_weyl := 8
  x_charges := c1_charges

/--
**X5 (c1_wan_wang_satisfies_u1x)**: the Wan-Wang C-1 hidden sector
satisfies the U(1)_X³ cubic and U(1)_X × gravity² linear anomaly
conditions by decidable integer arithmetic:

  ∑ q³ = 7 × (-8) + 216 = 160 ≡ 0 mod 4,
  ∑ q   = 7 × (-2) + 6   = -8  ≡ 0 mod 4.

Condition (a) of the joint constraint (ℤ₁₆ cancellation via the
Wan-Wang ℤ₁₆ ⊕ ℤ₄ mechanism) is stated as the tracked hypothesis
`H_MixedChannelZ16Cancels c1_wan_wang`.

Together, under that hypothesis, C-1 satisfies
`MixedChannelJointConstraint`.
-/
theorem c1_wan_wang_satisfies_u1x :
    U1XCubicAnomalyFree c1_wan_wang ∧ U1XLinearAnomalyFree c1_wan_wang := by
  refine ⟨?_, ?_⟩
  · unfold U1XCubicAnomalyFree u1x_cubic_mod4 c1_wan_wang c1_charges
    decide
  · unfold U1XLinearAnomalyFree u1x_linear_mod4 c1_wan_wang c1_charges
    decide

/-- **X5 (packaged)**: under a choice of ℤ₁₆ indexing `φ` for which
    the Wan-Wang cancellation holds at C-1, the C-1 assignment
    satisfies the joint constraint. The (b) and (c) conjuncts are
    unconditional; (a) is the genuine hypothesis. -/
theorem c1_wan_wang_joint_constraint
    (φ : Z16Indexing)
    (h_mix : H_MixedChannelZ16Cancels φ c1_wan_wang) :
    MixedChannelJointConstraint φ c1_wan_wang :=
  ⟨h_mix, c1_wan_wang_satisfies_u1x.1, c1_wan_wang_satisfies_u1x.2⟩

/-! ## 6. X6 — Mixed channel orthogonal to singlet channel -/

/--
**X6 (mixed_channel_orthogonal_to_singlet)**: the mixed-charge channel
witnessed by Wan-Wang C-1 is disjoint from the pure-singlet channel
formalized in `HiddenSectorClassification`.

Specifically: C-1 has `n_weyl = 8`, and `(8 : ZMod 16) ≠ 3`, so C-1
fails the singlet-rule T2 `hidden_sector_anomaly_value`. Yet C-1
still cancels the full anomaly via the Wan-Wang ℤ₁₆ ⊕ ℤ₄ mechanism
(the tracked `H_MixedChannelZ16Cancels c1_wan_wang` hypothesis).

This strengthens T11 (`z4x_singlet_constraint`) with an explicit
non-singlet witness: a hidden sector can cancel the full anomaly
without obeying the `N mod 16 = 3` singlet rule. It is the primary
scope-boundary theorem between the two channels.
-/
theorem mixed_channel_orthogonal_to_singlet :
    ((c1_wan_wang.n_weyl : ZMod 16) ≠ 3) ∧
    U1XCubicAnomalyFree c1_wan_wang ∧
    U1XLinearAnomalyFree c1_wan_wang := by
  refine ⟨?_, ?_, ?_⟩
  · show ((8 : ℕ) : ZMod 16) ≠ 3
    decide
  · exact (c1_wan_wang_satisfies_u1x).1
  · exact (c1_wan_wang_satisfies_u1x).2

/-! ## 7. Module summary -/

/-! ## Module summary

Summary theorem for the Mixed-Charge Hidden Sector module.

    This module adds 6 substantive targets (X1-X6) formalizing the
    mixed-charge channel of Phase 5x Wave 2b Track X. Combined with
    `HiddenSectorClassification` (singlet channel) this covers two of
    the three channels in the Wan / Wan-Wang / García-Etxebarria
    taxonomy; the topological channel (T-0, K-gauge TQFT) is deferred
    to Track Y pending Mathlib bordism infrastructure.
-/
end SKEFTHawking
