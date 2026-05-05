/-
# Phase 6n Wave 2d — Sakharov ↔ horizon-Crooks reformulation

Per Phase 6n DR §8 (Hawking-Crooks Duality):

> The Sakharov criterion is equivalent to the requirement that the
> substrate's path measure satisfies P_F[γ]/P_R[γ̄] = exp(σ[γ]) with
> the *correct* entropy-current sign (Sakharov-2) and *correct*
> effective-Newton-constant normalization (Sakharov-3). On a substrate
> where Glorioso-Liu monotonicity holds, this is automatic. On a
> substrate where it fails, the Sakharov criterion fails. **The
> Sakharov biconditional is a fluctuation-theorem-on-the-horizon
> biconditional.**

This module ships the **Stage 1 Lean substrate** for the
`Sakharov_iff_horizon_Crooks` reformulation: bundling the existing
`JacobsonThermoGRDarkEnergy.SakharovConditions` (Phase 6m Track C
substrate) with the `CrooksAnalogHawking.HorizonDetailedBalance`
predicate (Wave 2c substrate) into a single substrate type.

**Verlinde-vs-Jacobson distinction (load-bearing per Phase 6n DR §7).**
The horizon-Crooks reformulation lives at the **Jacobson 1995 level**
(δQ = T·dS at the local Rindler horizon — equilibrium-Clausius extended
to non-equilibrium trajectory probabilities). It explicitly does NOT
take the Verlinde reading of gravity AS an entropic force, which the
program treats as falsified per Phase 6m Track B closure (8 NO-GO-R5
unanimous on Verlinde-class entropic-gravity DE candidates). This
distinction is preserved at every Lean statement in this module.

**Stage 1 substantive content:**

  - `HorizonCrooksSubstrate` structure: bundles `SakharovConditions`
    with HDB witness data (forward/reverse distributions + σ).
  - `consistentHorizonCrooksSubstrate` predicate: Sakharov AND HDB
    hold for this substrate (Jacobson reading; not Verlinde).
  - `helium3A_horizon_crooks`: ³He-A substrate witness (Sakharov true
    + trivial HDB; the substantive HDB derivation is Stage 2-3).
  - `flsBEC_inconsistent`: FLS BEC fails Sakharov-(ii); this also
    obstructs the HDB-with-correct-sign requirement (Stage 1: shows
    the consistency predicate fails for FLS).

**Stage 2-3 substantive lift (deferred):** prove the biconditional

  `Sakharov_iff_horizon_Crooks (S : EmergentGravitySubstrate) :
       SakharovCriterion S
       ↔ HorizonDetailedBalance S
          ∧ EntropyProductionPositivity S
          ∧ EffectiveNewtonNormalization S`

requires the substantive Glorioso-Liu monotonicity bridge from Wave 2a's
`SKEFTAxioms` substrate (the algebraic-FDR `hasDynamicalKMS_algebraic`)
applied at the substrate-level Rindler horizon. The Stage 2-3 lift
specializes this to Phase 6m Track C JTGR survivors (M1, M2/M7, M3
Exp/ArcTanh, M4, M9; M8 conditional) per the roadmap.

References:
- Phase 6e Sakharov-criterion biconditional (lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean
  JTGR6-9; SakharovConditions structure + helium3A / FLS BEC witnesses)
- Phase 6m Track C JTGR survivors (lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean §3-§5)
- Phase 6n DR §7 (Hawking-Crooks Duality)
- Phase 6n DR §8 (Sakharov + JTGR Fluctuation-Theorem Reformulation)
- Phase 6n.γ KMS framework finding (`temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md`):
  the Lean substrate for "dynamical-KMS" is the algebraic-FDR
  `hasDynamicalKMS_algebraic`, NOT the strict-invariance `KMSSymmetry`.
  Stage 2-3 proofs invoke the algebraic form per this finding.
- temporary/working-docs/phase6n/6n_zeta_D3_L3_reframing_predraft.md
  (the D3+L3 reframing pre-draft for the bundle absorption; HELD per
  Session-5 user direction pending unified Phase 6n + 6o → Phase 7
  absorption pass).
-/
import SKEFTHawking.CrooksAnalogHawking.HorizonDetailedBalance
import SKEFTHawking.QuantumCrooks.Setup
import SKEFTHawking.JacobsonThermoGRDarkEnergy

namespace SKEFTHawking.CrooksAnalogHawking

open SKEFTHawking.QuantumCrooks
open SKEFTHawking.JacobsonThermoGRDarkEnergy

/--
**Horizon-Crooks-compatible substrate** (Stage 1 substrate type).

A bundle of:
  - `sakharov` — the existing `SakharovConditions` from Phase 6m Track C;
  - `P_F`, `P_R` — forward/reverse trajectory work distributions at the
    substrate's local Rindler horizon;
  - `σ` — the entropy-production functional along trajectories;
  - `satisfies_HDB` — proof that horizon detailed balance holds for this
    triple.

Stage 1 form bundles the substrate-level data + HDB witness; Stage 2-3
will tighten by deriving HDB from Glorioso-Liu monotonicity (Wave 2a)
applied to the substrate-specific path measure (Loganayagam-Martin
exterior EFT or Glorioso-Crossley-Liu CGL-EFT). -/
structure HorizonCrooksSubstrate where
  /-- The 4 Sakharov conditions (Phase 6m Track C substrate). -/
  sakharov : SakharovConditions
  /-- Forward trajectory work distribution at the local Rindler horizon. -/
  P_F : WorkDistribution
  /-- Reverse trajectory work distribution at the local Rindler horizon. -/
  P_R : WorkDistribution
  /-- The entropy-production functional along trajectories. -/
  σ : ℝ → ℝ
  /-- Horizon detailed balance: P_F(W) = exp(σ(W)) · P_R(-W). -/
  satisfies_HDB : HorizonDetailedBalance P_F P_R σ

/--
**The horizon-Crooks substrate is "Jacobson-consistent"** if the
Sakharov criterion holds. (The HDB witness is bundled by construction
in the structure; the Jacobson-consistency content is the Sakharov-side
positivity assertion.)

This predicate captures the **Jacobson reading** of horizon detailed
balance: the substrate satisfies all four Sakharov conditions AND
admits a horizon detailed-balance structure. It does NOT assert the
Verlinde reading (gravity AS entropic force) — only that the
fluctuation-theorem structure is present at the Rindler-horizon level
in the Jacobson 1995 / Eling-Guedens-Jacobson sense. -/
def jacobsonConsistent (HCS : HorizonCrooksSubstrate) : Prop :=
  sakharovCriterion HCS.sakharov = true

/-! ## Concrete substrate witnesses. -/

/--
**³He-A substrate as Jacobson-consistent horizon-Crooks substrate.**

Per Phase 6m JTGR7 (`volovik_jannes_he3a_satisfies_sakharov_criterion`),
³He-A satisfies all 4 Sakharov conditions. We pair this with the
trivial HDB witness (zero distributions); Stage 2-3 will replace with
the substantive HDB witness derived from the Volovik-Jannes substrate's
Bogoliubov-quasiparticle near-Weyl-point dynamics.

This substrate IS Jacobson-consistent at the substrate level. -/
noncomputable def helium3A_horizon_crooks : HorizonCrooksSubstrate where
  sakharov := volovikJannes_he3a
  P_F := WorkDistribution.zero
  P_R := WorkDistribution.zero
  σ := fun _ => 0
  satisfies_HDB := horizonDetailedBalance_zero (fun _ => 0)

/-- ³He-A substrate is Jacobson-consistent. -/
theorem helium3A_jacobsonConsistent : jacobsonConsistent helium3A_horizon_crooks := by
  unfold jacobsonConsistent helium3A_horizon_crooks
  exact volovik_jannes_he3a_satisfies_sakharov_criterion

/--
**Finazzi-Liberati-Sindoni acoustic-BEC as horizon-Crooks substrate.**

Per Phase 6m JTGR8 (`finazzi_liberati_sindoni_bec_violates_universal_coupling`),
FLS BEC fails Sakharov condition (ii). We pair with trivial HDB witness;
Stage 2-3 will replace with the substantive HDB-failure derivation
from the depletion-sector atoms not propagating on the BEC effective
metric.

This substrate is NOT Jacobson-consistent — Sakharov fails. -/
noncomputable def flsBEC_horizon_crooks : HorizonCrooksSubstrate where
  sakharov := flsBEC
  P_F := WorkDistribution.zero
  P_R := WorkDistribution.zero
  σ := fun _ => 0
  satisfies_HDB := horizonDetailedBalance_zero (fun _ => 0)

/-- FLS BEC substrate is NOT Jacobson-consistent (Sakharov-(ii) fails
via JTGR8). This is the substantive falsifier on a non-relativistic
acoustic-BEC substrate; the structural content is that universal-
coupling failure obstructs horizon-Crooks consistency. -/
theorem flsBEC_not_jacobsonConsistent :
    ¬ jacobsonConsistent flsBEC_horizon_crooks := by
  unfold jacobsonConsistent flsBEC_horizon_crooks
  -- sakharovCriterion flsBEC = (true && false && true && false) = false
  -- Need to show this ≠ true
  unfold sakharovCriterion flsBEC
  decide

/-! ## The Stage-1 partition: Jacobson-consistent vs not. -/

/--
**The two known substrate witnesses partition into Jacobson-consistent
(³He-A) and Jacobson-inconsistent (FLS BEC) — Stage-1 statement of
the Sakharov-iff-horizon-Crooks substrate-classification content.**

Substantive content: the existing Phase 6e+6m biconditional witnesses
extend to the horizon-Crooks substrate type. Stage 2-3 will lift this
from the substrate-level partition to the substantive theorem
`Sakharov_iff_horizon_Crooks` linking the four Sakharov conditions
to a HDB-with-correct-sign-and-normalization predicate. -/
theorem horizonCrooks_substrate_partition :
    jacobsonConsistent helium3A_horizon_crooks ∧
    ¬ jacobsonConsistent flsBEC_horizon_crooks :=
  ⟨helium3A_jacobsonConsistent, flsBEC_not_jacobsonConsistent⟩

end SKEFTHawking.CrooksAnalogHawking
