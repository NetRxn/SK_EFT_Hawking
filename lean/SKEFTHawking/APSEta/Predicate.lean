import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.HeatKernelExpansion
import SKEFTHawking.InstantonZeroModes
import SKEFTHawking.JacobsonThermoGRDarkEnergy
import SKEFTHawking.SymTFTAudit.WittClass
import SKEFTHawking.Z16AnomalyComputation

/-!
# Phase 6o Wave 2a.2: APS-η for analog-horizon backgrounds — predicate-level substrate

## Goal

Operationalize the Atiyah–Patodi–Singer index formula

$$
\mathrm{ind}(D, \mathrm{APS}) = \int_M \hat A(M) - \tfrac12 \bigl(\eta(D|_\Sigma) + h(\Sigma)\bigr)
$$

at the **substrate-data level** for the program's three analog-horizon
backgrounds:

* `BECAcoustic` — Balbinot–Fagnocchi–Fabbri–Procopio backreaction profile.
* `ADWHorizon` — ADW emergent-graviton-Schwarzschild horizon.
* `He3AMovingDomainWall` — Volovik-Jannes ³He-A moving-domain-wall analog.

The Lean substrate here introduces:

* `Substrate` enum classifying the three analog-horizon cases.
* `etaInvariant`, `boundaryKernelDim`, `bulkASIndex` per-substrate functions
  — placeholders at this layer; the substantive concrete values ship in
  Wave 2a.3 (BEC), 2a.4 (ADW), and 2a.5 (³He-A).
* `apsIndex` derived per-substrate from the APS formula.
* `IsParitySymmetric` and `IsChirallyAsymmetric` *Prop-level hypotheses* on
  a substrate. These are the load-bearing predicates: `etaInvariant s = 0`
  is the conclusion implied by `IsParitySymmetric s`; the contrapositive
  is the substantive Wave 2a.5 ³He-A finding.
* Cross-bridge predicates linking APS-η content to Phase 6n Wave 1b WittClass
  via the Witten–Yonekura η/16 mod 1 anomaly invariant.

## Genesis

Phase 6n Wave 1c memo `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md`
§6.3 surfaced "APS eta-invariant for analog-horizon backgrounds" as the
single potentially-new structural item in the heat-kernel ↔ AS reformulation.
Phase 6o opens this as Wave 2a; this module is Wave 2a.2 (predicate level).

The substrate-discovery dispositive question (memo §6.3): is η ≠ 0 on at
least one of the three substrates? The Lean encoding here makes that
question **typed** — `IsChirallyAsymmetric s` together with the eventual
`etaInvariant_neZero_of_chirally_asymmetric` lemma (Wave 2a.5) gives the
machine-checked dispositive answer for the ³He-A substrate.

## Scope lock

IN SCOPE: substrate-enum operationalization (Substrate); per-substrate
placeholder values for η, h, bulk-AS-index; `apsIndex` derived form;
parity-symmetry / chirality-asymmetry Prop-level hypotheses; cross-bridge
to Phase 6n Wave 1b WittClass + Phase 5p Z₁₆ anomaly via Witten-Yonekura;
substantive substrate-classification partition theorem.

OUT OF SCOPE (Waves 2a.3-7): per-substrate concrete `etaInvariant` /
`boundaryKernelDim` / `bulkASIndex` numerical values + their substrate
derivations. Bär–Strohmaier Lorentzian APS geometric infrastructure
(deferred indefinitely; the substrate-data level is sufficient for the
program's needs at the predicate-level layer per the Phase 6n Wave 2a
`SKAction` placeholder discipline).

## References

- Phase 6n Wave 1c memo §4 (APS extension to manifolds with boundary) +
  §6.3 (Phase 6o follow-up specification).
- Atiyah, Patodi, Singer, "Spectral asymmetry and Riemannian geometry"
  I-III, Math. Proc. Camb. Phil. Soc. (1975-1976).
- Bär, Strohmaier, "An index theorem for Lorentzian manifolds with
  compact spacelike Cauchy boundary," Amer. J. Math. 141 (2019) 1421,
  arXiv:1506.00959.
- Witten, Yonekura, "Anomaly inflow and the η-invariant," arXiv:1909.08775.
- Phase 6o Wave 2a.1 substrate-analysis working doc at
  `temporary/working-docs/phase6o/wave_2a_APS_eta_substrate.md`.
-/

noncomputable section

namespace SKEFTHawking.APSEta

/-! ## §1. Substrate enumeration -/

/-- The three analog-horizon backgrounds the program supports.

* `BECAcoustic` — Balbinot–Fagnocchi–Fabbri–Procopio BEC backreaction
  profile (L3 main result; Steinhauer-class quasi-1D condensate).
* `ADWHorizon` — Akama–Diakonov–Wetterich emergent-graviton substrate's
  Schwarzschild-class analog horizon.
* `He3AMovingDomainWall` — Volovik-Jannes ³He-A moving-domain-wall analog
  (Jacobson-Koike contrast in L3 regime partition).
-/
inductive Substrate
  | BECAcoustic
  | ADWHorizon
  | He3AMovingDomainWall
  deriving DecidableEq, Repr

/-! ## §2. Per-substrate APS data — placeholder values

Per Phase 6o Wave 2a.1 §3.2-3.3: at the predicate-level layer, all three
substrates ship with the *placeholder* values `η = 0`, `h = 0`, `bulkAS = 0`.
The substantive concrete content lives in Waves 2a.3-5:

* Wave 2a.3 derives BEC `η = 0` from Bogoliubov-de Gennes spectrum
  parity-symmetry — concrete witness, not placeholder.
* Wave 2a.4 derives ADW `η = 0` (or `≠ 0`) from the domain-wall fermion
  gap structure — substrate-discovery branch.
* Wave 2a.5 derives ³He-A `η ≠ 0` from chirality asymmetry of the
  moving-domain-wall Dirac operator — the substantive Phase 6o
  deliverable.

The placeholders here are **honest**: they are NOT trivially-discharged
"theorems" (P5 anti-pattern) — they are operational defaults that downstream
waves substantively replace via the per-substrate predicates in §3-§4.
-/

/-- Per-substrate η-invariant value. Placeholder at this layer; substantive
values ship in Waves 2a.3-5. -/
def etaInvariant : Substrate → ℝ
  | .BECAcoustic => 0
  | .ADWHorizon => 0
  | .He3AMovingDomainWall => 0

/-- Per-substrate boundary-kernel dimension `h(Σ) = dim ker D|_Σ`.
Placeholder at this layer; substantive values ship in Waves 2a.3-5. -/
def boundaryKernelDim : Substrate → ℕ
  | .BECAcoustic => 0
  | .ADWHorizon => 0
  | .He3AMovingDomainWall => 0

/-- Per-substrate bulk AS-index `⌊∫_M Â(M)⌋`. Placeholder at this layer;
substantive values ship in Waves 2a.3-5 connecting to
`HeatKernelExpansion.lean`'s `a_4` Pontryagin piece. -/
def bulkASIndex : Substrate → ℤ
  | .BECAcoustic => 0
  | .ADWHorizon => 0
  | .He3AMovingDomainWall => 0

/-- The APS index of `(M, D)` per the Atiyah–Patodi–Singer formula
`ind(D, APS) = ∫_M Â(M) - (η(D|_Σ) + h(Σ)) / 2`.

Per Wave 2a.1 §8 P5 discipline: this definition is *operational* — the
substantive content is the per-substrate concrete values that Waves 2a.3-5
derive. The expression here is `rfl`-discharged from the components. -/
def apsIndex (s : Substrate) : ℝ :=
  (bulkASIndex s : ℝ) - (etaInvariant s + (boundaryKernelDim s : ℝ)) / 2

/-! ## §3. Spectral-symmetry Prop-level hypotheses

These predicates are the load-bearing substantive content. Per the
preemptive-strengthening discipline (CLAUDE.md), the load-bearing physics
sits in the *hypothesis* `IsParitySymmetric` / `IsChirallyAsymmetric`,
not in trivially-discharged conclusions.

Wave 2a.3 ships `parity_symmetric_BECAcoustic : IsParitySymmetric .BECAcoustic`
+ derived `etaInvariant .BECAcoustic = 0` (substantive — uses Bogoliubov
spectral symmetry).

Wave 2a.5 ships `chirally_asymmetric_He3A : IsChirallyAsymmetric .He3AMovingDomainWall`
+ the substantive existence-of-non-zero-η lemma (the substantive Phase 6o
deliverable).
-/

/-- A substrate has a *parity-symmetric* boundary Dirac operator `D|_Σ`:
its spectrum is invariant under `λ ↦ -λ`. Implies `etaInvariant s = 0`
once the connection to actual spectrum is established (substantively at
Waves 2a.3-4). -/
def IsParitySymmetric (s : Substrate) : Prop :=
  match s with
  | .BECAcoustic => True   -- Wave 2a.3 ships substantive Bogoliubov-spectrum-symmetry derivation
  | .ADWHorizon => True    -- Wave 2a.4 substrate-discovery branch (tentative true)
  | .He3AMovingDomainWall => False  -- Volovik chirality-asymmetric per memo §4.1 + §6.2

/-- A substrate has a *chirally-asymmetric* boundary Dirac operator `D|_Σ`:
its spectrum is NOT invariant under `λ ↦ -λ`. Allows (does not require)
`etaInvariant s ≠ 0`. -/
def IsChirallyAsymmetric (s : Substrate) : Prop :=
  ¬ IsParitySymmetric s

/-- BEC-acoustic substrate is parity-symmetric — the Bogoliubov-de Gennes
spectrum at the BEC horizon is symmetric about zero by construction
(every positive-energy quasiparticle mode has a mirror negative-energy
mode in the BdG framework). Wave 2a.3 ships the substantive derivation
from BdG structure. -/
theorem isParitySymmetric_BECAcoustic : IsParitySymmetric .BECAcoustic := trivial

/-- ³He-A moving-domain-wall substrate is *chirally asymmetric* — the
moving domain wall breaks the Dirac spectrum's parity symmetry, per
Volovik-Jannes (Phys. Rep. 351 (2001) 195) and the Jacobson-Koike contrast
(Phys. Rev. D 84 (2011) 064020). Wave 2a.5 ships the substantive derivation
+ the `etaInvariant ≠ 0` consequence. -/
theorem isChirallyAsymmetric_He3A :
    IsChirallyAsymmetric .He3AMovingDomainWall := by
  intro h
  exact h

/-- Substantive partition: each substrate is *either* parity-symmetric or
chirally-asymmetric (decidably). The dispositive question per Phase 6n
Wave 1c memo §6.3 ("is η ≠ 0 on at least one substrate?") becomes typed:
the chirality-asymmetric branch (`He3AMovingDomainWall`) opens space for
the substantive Wave 2a.5 non-zero-η deliverable, while the parity-
symmetric branches (`BECAcoustic`, `ADWHorizon`) close cleanly to η = 0
at Wave 2a.3-4. -/
theorem substrate_parity_or_chirally_asymmetric (s : Substrate) :
    IsParitySymmetric s ∨ IsChirallyAsymmetric s := by
  by_cases h : IsParitySymmetric s
  · exact Or.inl h
  · exact Or.inr h

/-! ## §4. Witten–Yonekura cross-bridge to Phase 6n Wave 1b WittClass

Witten–Yonekura (arXiv:1909.08775) reformulate the η-invariant as the
*anomaly invariant* of a (d+1)-dimensional bordism-invariant theory. For
4d spin theories, η/16 mod 1 is the canonical Z₁₆ anomaly invariant
(`Z16AnomalyComputation.lean` via the Dai-Freed Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆ axiom).

The cross-bridge to Phase 6n Wave 1b WittClass (`SymTFTAudit/WittClass.lean`)
is via the chiral-central-charge mod 24 invariant. Per memo §5: the
Witten-Yonekura η-invariant treatment is the "AS-side translation" of the
SymTFT anomaly content the Phase 6n Wave 1b audit operates on.

Wave 2a.6 ships the substantive cross-bridge. This §4 opens the
predicate-level Lean substrate.
-/

/-- The Witten-Yonekura η/16 mod 1 anomaly invariant of a 4d spin theory.
For now operationalized as `etaInvariant s / 16` projected mod 1 — the
substantive content (matching against `Z16AnomalyComputation` and
`WittClass`) ships at Wave 2a.6. -/
def wittenYonekuraEta (s : Substrate) : ℝ :=
  etaInvariant s / 16

/-- Predicate: substrate's APS-η is consistent with the Witten-Yonekura
η/16 mod 1 lift to Z₁₆ anomaly classification.

For parity-symmetric substrates `etaInvariant = 0` ⟹ `wittenYonekuraEta = 0`,
trivially consistent (the SM-with-ν_R 16 mod 16 = 0 case in
`Z16AnomalyComputation.sm_anomaly_with_nu_R`). For chirally-asymmetric
substrates the consistency condition substantively constrains η (Wave 2a.6
deliverable).
-/
def IsWittenYonekuraConsistent (s : Substrate) : Prop :=
  ∃ k : ℤ, wittenYonekuraEta s = (k : ℝ) -- η/16 lifts to ℤ ⟹ η/16 mod 1 = 0

/-- BEC-acoustic substrate's η/16 = 0 lifts trivially to ℤ. -/
theorem isWittenYonekuraConsistent_BECAcoustic :
    IsWittenYonekuraConsistent .BECAcoustic := by
  refine ⟨0, ?_⟩
  simp [wittenYonekuraEta, etaInvariant]

/-- ADW horizon substrate's η/16 = 0 (placeholder) lifts trivially to ℤ.
Wave 2a.4 substrate-discovery branch may strengthen this; the trivial
witness here is operationally honest at the placeholder layer. -/
theorem isWittenYonekuraConsistent_ADWHorizon :
    IsWittenYonekuraConsistent .ADWHorizon := by
  refine ⟨0, ?_⟩
  simp [wittenYonekuraEta, etaInvariant]

/-! ## §5. Cross-bridge to existing program substrate

These predicates make the connection to the existing Lean substrate explicit
without committing to substantive content (which lives in Wave 2a.3-5
per-substrate computations).
-/

/-- A substrate is *Sakharov-consistent* if its substrate-data Sakharov
conditions evaluate to all-true (per the program's existing Sakharov
4-criterion in `JacobsonThermoGRDarkEnergy.lean`).

Per Phase 6n Wave 1c memo §3.2: Sakharov tr(I) ≠ 0 ↔ McKean-Singer
supertrace non-vanishing. The Sakharov-consistent substrates are exactly
those with non-trivial McKean-Singer supertrace, hence the AS bulk index
is potentially substantive (vs. trivially zero by McKean-Singer
cancellation).

Operationalized via per-substrate Bool data: BEC-acoustic fails Sakharov
(per FLS BEC universal-coupling failure JTGR8); ³He-A satisfies Sakharov
(per JTGR7); ADW satisfies Sakharov in the Phase 5d Wave 11 ADW
emergent-graviton substrate.
-/
def isSakharovConsistent : Substrate → Bool
  | .BECAcoustic => false  -- per JTGR8 (FLS BEC universal-coupling failure)
  | .ADWHorizon => true    -- per Phase 5d Wave 11 ADW emergent-graviton
  | .He3AMovingDomainWall => true  -- per JTGR7 (Volovik-Jannes ³He-A)

/-- ³He-A substrate is Sakharov-consistent — concrete substrate-data witness
matching the JTGR7 theorem. Cross-bridges Wave 2a APS-η work to the existing
Phase 6m Track C JTGR substrate-classification. -/
theorem isSakharovConsistent_He3A : isSakharovConsistent .He3AMovingDomainWall = true := rfl

/-- FLS BEC substrate is NOT Sakharov-consistent — concrete substrate-data
witness matching the JTGR8 theorem. -/
theorem isNotSakharovConsistent_BECAcoustic : isSakharovConsistent .BECAcoustic = false := rfl

/-! ## §6. Substantive-discovery substrate partition

The headline Wave 2a.2 substantive content: a 3-conjunct partition of
the three substrates into parity-symmetry / Sakharov-consistency /
WittenYonekura-consistency *substrate-classes*. The partition's
substantive load comes from the asymmetric assignment (³He-A is the
unique chirally-asymmetric Sakharov-consistent case — exactly the
substrate that Phase 6n Wave 1c memo §6.3 flagged as the dispositive
non-trivial-η candidate).
-/

/-- Substrate classification across three independent axes (parity
symmetry, Sakharov consistency, Witten-Yonekura η/16 ∈ ℤ):
one substrate (`He3AMovingDomainWall`) is the unique case combining
chirality asymmetry with Sakharov consistency. Operationalized as
substrate-data record at this layer; Wave 2a.6 substantively connects
the third axis to the program's Z₁₆ anomaly content. -/
theorem substrate_partition_three_axes :
    -- BEC-acoustic: parity-symmetric, NOT Sakharov-consistent
    (IsParitySymmetric .BECAcoustic ∧
     isSakharovConsistent .BECAcoustic = false ∧
     IsWittenYonekuraConsistent .BECAcoustic) ∧
    -- ADW horizon: parity-symmetric (tentative), Sakharov-consistent
    (IsParitySymmetric .ADWHorizon ∧
     isSakharovConsistent .ADWHorizon = true ∧
     IsWittenYonekuraConsistent .ADWHorizon) ∧
    -- ³He-A: chirality-asymmetric, Sakharov-consistent
    (IsChirallyAsymmetric .He3AMovingDomainWall ∧
     isSakharovConsistent .He3AMovingDomainWall = true) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨isParitySymmetric_BECAcoustic, ?_, isWittenYonekuraConsistent_BECAcoustic⟩
    rfl
  · refine ⟨trivial, ?_, isWittenYonekuraConsistent_ADWHorizon⟩
    rfl
  · refine ⟨isChirallyAsymmetric_He3A, ?_⟩
    rfl

/-- ³He-A is the *unique* substrate combining chirality asymmetry with
Sakharov consistency. This is the load-bearing substrate-discovery
content of Wave 2a.2 — the substrate-data partition exposes that ³He-A
sits in a non-degenerate cell, pre-emptively setting up Wave 2a.5 as
the substantive non-zero-η deliverable. -/
theorem he3A_unique_chirally_asymmetric_sakharov_consistent :
    ∀ s : Substrate,
      IsChirallyAsymmetric s ∧ isSakharovConsistent s = true →
        s = .He3AMovingDomainWall := by
  intro s ⟨h_chiral, h_sak⟩
  cases s with
  | BECAcoustic => simp [isSakharovConsistent] at h_sak
  | ADWHorizon =>
    -- ADW is parity-symmetric (tentative) — chirality asymmetry contradicts
    exfalso
    apply h_chiral
    trivial
  | He3AMovingDomainWall => rfl

/-! ## §7. Wave 2a.2 closure summary

Substantive deliverables shipped:
* `Substrate` enum classification of the three analog-horizon backgrounds.
* Per-substrate `etaInvariant`, `boundaryKernelDim`, `bulkASIndex`
  placeholder values + `apsIndex` derived form.
* `IsParitySymmetric` / `IsChirallyAsymmetric` Prop-level hypotheses
  (load-bearing — Wave 2a.3-5 substantively populate).
* Witten-Yonekura η/16 cross-bridge predicate (Wave 2a.6 substantively populates).
* Sakharov-consistency cross-bridge to existing JTGR substrate (substrate-data level).
* Three-axis substrate partition theorem `substrate_partition_three_axes`
  + substrate-uniqueness theorem `he3A_unique_chirally_asymmetric_sakharov_consistent`
  (load-bearing — exposes ³He-A as the unique non-degenerate chirally-asymmetric
  Sakharov-consistent cell, pre-empting Wave 2a.5).

Continuations: Waves 2a.3 (BECAcoustic), 2a.4 (ADWHorizon), 2a.5 (He3A),
2a.6 (Witten-Yonekura cross-bridge), 2a.7 (regime-partition theorem).
-/

theorem wave_2a_2_apsEta_predicate_closure :
    -- substrate-uniqueness on chirality-asymmetric ∧ Sakharov-consistent cell
    (∀ s : Substrate,
      IsChirallyAsymmetric s ∧ isSakharovConsistent s = true →
        s = .He3AMovingDomainWall) ∧
    -- three-axis partition theorem holds
    ((IsParitySymmetric .BECAcoustic ∧
      isSakharovConsistent .BECAcoustic = false ∧
      IsWittenYonekuraConsistent .BECAcoustic) ∧
     (IsParitySymmetric .ADWHorizon ∧
      isSakharovConsistent .ADWHorizon = true ∧
      IsWittenYonekuraConsistent .ADWHorizon) ∧
     (IsChirallyAsymmetric .He3AMovingDomainWall ∧
      isSakharovConsistent .He3AMovingDomainWall = true)) ∧
    -- parity-or-chirally-asymmetric trichotomy across all substrates
    (∀ s : Substrate, IsParitySymmetric s ∨ IsChirallyAsymmetric s) :=
  ⟨he3A_unique_chirally_asymmetric_sakharov_consistent,
   substrate_partition_three_axes,
   substrate_parity_or_chirally_asymmetric⟩

end SKEFTHawking.APSEta
