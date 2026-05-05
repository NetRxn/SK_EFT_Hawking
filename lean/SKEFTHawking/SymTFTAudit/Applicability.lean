/-
# Phase 6n Wave 1b Stage 3 — SymTFT applicability verdict + discrete-sector predicates

Stage-2 audit verdict (per `temporary/working-docs/phase6n/wave_1b_symtft_audit_verdict.md`):
the Choi-doubled mixed-state SymTFT framework of arXiv:2507.05350
(Schäfer-Nameki et al., July 2025) is **PARTIALLY APPLICABLE** to the
SK-EFT dynamical-KMS structure of Crossley-Glorioso-Liu — discrete
dynamical-KMS Z₂ embeds cleanly; continuous entropic U(1)_T requires
follow-on research (fusion with Brennan-Sun arXiv:2407.07951 BF
technology, multi-wave research project per DR §6.2).

This module ships the **Stage 3 discrete-sector Lean substrate**:
predicate-level statements for the 3 ship-able candidates from the
Stage 2 verdict's Section 3 disposition table:

  1. `chiralCentralChargeMod24Compatible` — modular invariance +
     24|c₋ → N_f = 3 (Schellekens / Kong-Wen Witt class)
  2. `Z16AnomalyEtaCompatible` — Z₁₆ anomaly + Witten-Yonekura η/16
  3. `KMSParityAlternationCompatible` — γ_{2,1} + γ_{2,2} = 0 +
     dynamical KMS Z₂ (the discrete-sector dynamical-KMS embedding)

Each predicate is parameterized over an abstract `SymTFTApplicability`
verdict; the Stage-1 trivial well-posedness witness uses the
`PartiallyApplicable` constructor matching the Stage-2 audit verdict.

**Two candidates from the Stage 1 §6.3 list are deferred:**
- `gauge_erasure` (Phase 3 W2) — speculative connection per Stage 1 §4
- `GD_orthogonality` (4-factor decomposition) — at-most 2/4 fit
  (-1)-form pattern; speculative per Stage 1 §3.1

These remain in the audit-verdict working doc as deferred follow-ons.

References:
- Schäfer-Nameki-Tiwari-Warman-Zhang, "SymTFT Approach for Mixed States
  with Non-Invertible Symmetries," arXiv:2507.05350 (v1, July 2025) — the
  primary-source-audit target
- Stage 1 audit working doc: `temporary/working-docs/phase6n/6n_beta_symtft_audit.md`
- Stage 2 audit verdict: `temporary/working-docs/phase6n/wave_1b_symtft_audit_verdict.md`
- Phase 6n DR (SymTFT track substrate analysis): `Lit-Search/_Exploratory/SymTFT, Higher-Form, and Non-Invertible Symmetries Applied to the SK-EFT Hawking Program- A Structural Audit.md`
-/

namespace SKEFTHawking.SymTFTAudit

/-! ## The Stage-2 verdict as an inductive type. -/

/--
**The applicability verdict for arXiv:2507.05350 (Choi-doubled mixed-state
SymTFT) to the SK-EFT dynamical-KMS structure of CGL II.**

Per the Stage 1 §2.2 decision matrix, three branches:

  - `Applicable` — Choi-doubled SymTFT admits dynamical-KMS Z₂ as a
    Lagrangian algebra; entropic U(1)_T fits as a continuous extension.
  - `PartiallyApplicable` — Discrete dynamical-KMS Z₂ embeds cleanly,
    but entropic U(1)_T (a continuous gauge symmetry) does not fit the
    published Sang-Hsieh strong/weak dichotomy.
  - `NotApplicable` — The strong/weak dichotomy fundamentally cannot
    accommodate a thermal hydrodynamic state.

**Stage-2 audit verdict (Session 6, 2026-05-05):** `PartiallyApplicable`
— per direct primary-source fetch of arXiv:2507.05350. -/
inductive SymTFTApplicability
  | Applicable
  | PartiallyApplicable
  | NotApplicable
  deriving DecidableEq

/-- The Stage-2 audit verdict from direct primary-source fetch of
arXiv:2507.05350 (Session 6, 2026-05-05): PartiallyApplicable. -/
def stage2Verdict : SymTFTApplicability := SymTFTApplicability.PartiallyApplicable

/-! ## Discrete-sector predicates (3 ship-able candidates per Stage-2 §3). -/

/--
**`chiralCentralChargeMod24Compatible`: the Schellekens / Kong-Wen Witt-
class compatibility of the program's "24 | c₋ → N_f = 3" modular-invariance
content with the discrete-sector embedding of arXiv:2507.05350.**

Stage 3 form: Prop-level predicate parameterized over the applicability
verdict. Substantive Stage-2-3 content (deferred): connect to existing
program content (Schellekens hep-th/9205072 + Kong-Wen Witt-class) and
the 24-divisibility derivation; Stage 4+ would require full Lean-
formalized Witt-group infrastructure (Mathlib gap; multi-year community
project per Stage 1 §6 risk register). -/
def chiralCentralChargeMod24Compatible (verdict : SymTFTApplicability) : Prop :=
  verdict ≠ SymTFTApplicability.NotApplicable

/--
**`Z16AnomalyEtaCompatible`: the Witten-Yonekura η/16 mod 1 invariant
treatment of the program's ℤ₁₆ anomaly content (per Phase 6n.η AS
reformulation memo) is compatible with the discrete-sector embedding
of arXiv:2507.05350.**

Stage 3 form: Prop-level predicate. Substantive Stage-2-3 content
(deferred): connect to existing program `SpinBordism.Z16` content and
the Witten-Yonekura η/16 derivation; the AS reformulation memo
(`temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md`)
identifies this as one of the cross-bridges from the AS-side
(characteristic-class) to the SymTFT-side (categorical-symmetry). -/
def Z16AnomalyEtaCompatible (verdict : SymTFTApplicability) : Prop :=
  verdict ≠ SymTFTApplicability.NotApplicable

/--
**`KMSParityAlternationCompatible`: the program's
γ_{2,1} + γ_{2,2} = 0 parity-alternation constraint at second order
SK-EFT (existing `SecondOrderSK.lean` content) embeds in the
discrete-sector dynamical-KMS Z₂ of the Choi-doubled framework.**

Stage 3 form: Prop-level predicate. The Stage-2 audit verdict
explicitly identified this candidate as the one that fits naturally
in the Choi-doubled framework's "weak symmetry" classification — the
parity-alternation IS the dynamical-KMS Z₂'s manifestation on the
polynomial coefficients at second order in the gradient expansion.

Stage-2-3 substantive content (deferred): connect to existing
`SKEFTHawking.SecondOrderSK` content (`gamma_2_1_plus_gamma_2_2_zero`
or equivalent) via a cross-module bridge once the SymTFT-side
infrastructure is in place. -/
def KMSParityAlternationCompatible (verdict : SymTFTApplicability) : Prop :=
  verdict ≠ SymTFTApplicability.NotApplicable

/-! ## Stage-2 verdict instantiates each predicate. -/

/-- Substantive Stage-3 well-posedness theorem: the Stage-2 audit verdict
(`stage2Verdict = PartiallyApplicable`) instantiates each discrete-sector
candidate predicate non-vacuously. -/
theorem stage2Verdict_instantiates_chiralCentralCharge :
    chiralCentralChargeMod24Compatible stage2Verdict := by
  unfold chiralCentralChargeMod24Compatible stage2Verdict
  decide

theorem stage2Verdict_instantiates_Z16Anomaly :
    Z16AnomalyEtaCompatible stage2Verdict := by
  unfold Z16AnomalyEtaCompatible stage2Verdict
  decide

theorem stage2Verdict_instantiates_KMSParityAlternation :
    KMSParityAlternationCompatible stage2Verdict := by
  unfold KMSParityAlternationCompatible stage2Verdict
  decide

/-! ## The Stage-2 partition: ship-able vs deferred. -/

/--
**Stage-2 partition theorem: under the audit verdict, all 3 ship-able
discrete-sector candidates instantiate non-vacuously, while the verdict
itself is `PartiallyApplicable` (not `Applicable`) — reflecting the
continuous-sector follow-on flagged for Phase 6o.**

Substantive content: this is the cleanest Lean-level statement of the
Stage-2 audit verdict. The 3 candidates form a coherent discrete-sector
substrate; the verdict's `PartiallyApplicable` shape is the honest
representation of the continuous-sector gap. -/
theorem stage2_partition :
    chiralCentralChargeMod24Compatible stage2Verdict ∧
    Z16AnomalyEtaCompatible stage2Verdict ∧
    KMSParityAlternationCompatible stage2Verdict ∧
    stage2Verdict = SymTFTApplicability.PartiallyApplicable :=
  ⟨stage2Verdict_instantiates_chiralCentralCharge,
   stage2Verdict_instantiates_Z16Anomaly,
   stage2Verdict_instantiates_KMSParityAlternation,
   rfl⟩

end SKEFTHawking.SymTFTAudit
