/-
# Phase 6q Wave 1b.3 — DKM Transport Bootstrap: no-crossing structural finding

The Phase 6o Wave 1c Obstruction (II) discussion motivates the comparison. The Phase 6o
NO-GO writeup (`temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`
§2.2) identified the absence of a doubled-contour analog for s/t/u
crossing as the second structural obstruction. The DR Wave 1a.1 §1 row
(2) re-reads CHHK 2509.18255 and finds: **CHHK never invokes crossing.**
The bootstrap is "vertical" — it operates on low-ω vs high-ω data:
low-ω from the DKM functional form (CHHK arXiv:2509.18255v2 Eq. (4)),
high-ω from the bounded-local nested-commutator estimate (Eq. (31)).
The Stirling estimate (Eq. (32)) yields the spectral bound in Eq. (33).

CHHK's published derivation uses low- and high-frequency constraints
without an s/t/u crossing input. The Lean record operations reflect the
absence of a crossing field.

The Lean declarations assemble and project the legacy fields without
a crossing relation. Global F1 and pointwise F2 remain incompatible
near the diffusion origin. A physical witness needs a finite-window
match and the actual microscopic bounds.

References:
- Phase 6o Wave 1c NO-GO §2.2: no doubled-contour crossing
- DR Wave 1a.1 §1 row (2): CLEARED — CHHK never invokes crossing
- CHHK §2 / §3: vertical (low-ω / high-ω) architecture, no crossing
- Abanin–De Roeck–Huveneers PRL 115, 256803 (arXiv:1507.01474):
  nested-commutator high-ω bound
- Parker–Cao–Avdoshkin–Scaffidi–Altman PRX 9, 041017 (arXiv:1812.08657):
  universal operator-growth hypothesis (CHHK §6 future-strengthening)
-/
import SKEFTHawking.DKMBootstrap.AxiomSet

namespace SKEFTHawking.DKMBootstrap

/-! ## §1. The vertical-bootstrap predicate.

CHHK's bootstrap is *vertical* in the sense that its substantive content
is partitioned into:
- a low-ω section (F1 + F2): the DKM functional form at low frequencies +
  the integrated lattice f-sum rule, AND
- a high-ω section (F3 + Stirling): the nested-commutator operator-
  growth bound + the factorial-vs-power Stirling estimate.

The Lean interface groups legacy global F1, pointwise F2 and
standalone F3 for a supplied sequence. -/

/-- Groups the three legacy predicates without a channel relation. The
field names reflect the source's low- and high-frequency split. -/
structure IsVerticalBootstrap
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) : Prop where
  /-- Legacy F1: global DKM functional form. -/
  low_omega_dkm_form : IsDKMTransportCorrelator G p
  /-- Legacy F2: uniform pointwise bound on the divided spectrum. -/
  low_omega_f_sum_rule : HasFSumRule G boundData
  /-- High-ω F3: nested-commutator operator-growth bound. -/
  high_omega_operator_growth :
      HasOperatorGrowthBound commutatorNorm p.ε n0Norm

/-! ## §2. The structural theorem — verticality bypasses crossing.

The proof assembles a record from the supplied vertical fields and
the supplied F4, legacy F5 and F6 witnesses. -/

/-- Assemble `IsDKMAxiomSet` from the six supplied legacy fields. -/
theorem vertical_bootstrap_bypasses_crossing
    {G : Correlator} {p : DKMParameters}
    {commutatorNorm : ℕ → ℝ} {n0Norm boundData : ℝ}
    (vb : IsVerticalBootstrap G p commutatorNorm n0Norm boundData)
    (h4 : IsImGRetardedNonneg G)
    (h5 : IsUpperHalfPlaneAnalytic G)
    (h6 : HasParityTimeReversal G) :
    IsDKMAxiomSet G p commutatorNorm n0Norm boundData where
  dkm_form := vb.low_omega_dkm_form
  f_sum_rule := vb.low_omega_f_sum_rule
  operator_growth := vb.high_omega_operator_growth
  positivity := h4
  uhp_analytic := h5
  pt_symmetry := h6

/-! ## §3. The reverse direction for the legacy bundle.

Confirms the architecture is **operationally equivalent** to the
vertical decomposition: every `IsDKMAxiomSet` witness gives a
vertical-bootstrap witness for free, by projection. -/

/-- Project the first three fields from the supplied legacy bundle. -/
theorem dkm_axiom_set_is_vertical
    {G : Correlator} {p : DKMParameters}
    {commutatorNorm : ℕ → ℝ} {n0Norm boundData : ℝ}
    (h : IsDKMAxiomSet G p commutatorNorm n0Norm boundData) :
    IsVerticalBootstrap G p commutatorNorm n0Norm boundData where
  low_omega_dkm_form := h.dkm_form
  low_omega_f_sum_rule := h.f_sum_rule
  high_omega_operator_growth := h.operator_growth

/-! ## §4. Roundtrip and equivalence.

The equivalence adds the three supplied F4, legacy F5 and F6 fields
to the vertical record. -/

/-- **Equivalence at the bundled level.** The conjunction of
`IsVerticalBootstrap` with the (F4, F5, F6) trio is equivalent to
`IsDKMAxiomSet` — both directions established by §2 and §3. -/
theorem dkm_axiom_set_iff_vertical_plus_f4f5f6
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) :
    IsDKMAxiomSet G p commutatorNorm n0Norm boundData ↔
    (IsVerticalBootstrap G p commutatorNorm n0Norm boundData ∧
     IsImGRetardedNonneg G ∧
     IsUpperHalfPlaneAnalytic G ∧
     HasParityTimeReversal G) := by
  constructor
  · intro h
    refine ⟨dkm_axiom_set_is_vertical h, h.positivity, h.uhp_analytic, h.pt_symmetry⟩
  · rintro ⟨vb, h4, h5, h6⟩
    exact vertical_bootstrap_bypasses_crossing vb h4 h5 h6

/-! ## §5. Closure summary — Wave 1b.3 no-crossing.

This module ships:
- **`IsVerticalBootstrap`** predicate capturing CHHK's (low-ω F1+F2,
  high-ω F3) architecture, explicitly without any s/t/u channel
  constraint.
- **`vertical_bootstrap_bypasses_crossing`** — structural theorem:
  vertical + F4 + legacy F5 + F6 assemble the legacy record without
  invoking crossing.
- **`dkm_axiom_set_is_vertical`** — reverse direction: every full
  legacy bundle supplies the vertical fields.
- **`dkm_axiom_set_iff_vertical_plus_f4f5f6`** — equivalence at the
  bundled level (substantive structural identity).

The Phase 6o question motivates comparing the interfaces. The Lean
proofs package and project supplied legacy fields without a
doubled-contour crossing input.

An `IsDKMAxiomSet` witness supplies a vertical-bootstrap witness by
projection. The normalized examples do not establish the hypotheses for
a physical graphene, BEC or polariton model. -/

end SKEFTHawking.DKMBootstrap
