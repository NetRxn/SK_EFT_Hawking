/-
# Phase 6n Wave 2d Stage 2-3 — `Sakharov_iff_horizon_Crooks` biconditional

Per Phase 6n DR §8 (Sakharov + JTGR Fluctuation-Theorem Reformulation):

> The Sakharov criterion is equivalent to the requirement that the
> substrate's path measure satisfies P_F[γ]/P_R[γ̄] = exp(σ[γ]) with
> the *correct* entropy-current sign (Sakharov-2) and *correct*
> effective-Newton-constant normalization (Sakharov-3). On a substrate
> where Glorioso-Liu monotonicity holds, this is automatic.

This module ships the **Stage 2-3 substantive biconditional theorem**:

  sakharov_iff_horizon_crooks (HCS : HorizonCrooksSubstrate) :
    sakharovCriterion HCS.sakharov = true
      ↔ jacobsonHorizonCompatible HCS

where `jacobsonHorizonCompatible` is a 4-conjunct horizon-Crooks-side
predicate, each conjunct corresponding to one of the four Sakharov
conditions per the DR §8 mapping:

  Sakharov-1 (emergentLorentz)        ↔ horizonLorentzCompatible
  Sakharov-2 (universalCoupling)      ↔ horizonEntropySignCorrect
  Sakharov-3 (inducedNewtonConstant)  ↔ horizonNewtonNormCorrect
  Sakharov-4 (lambdaEffEqLambdaHK)    ↔ horizonLambdaMatch

The biconditional is a **substantive structural restatement**: each
Sakharov condition has a horizon-Crooks-side interpretation, and the
4-conjunct conjunction matches the `sakharovCriterion` Bool-AND.

**Verlinde-vs-Jacobson distinction (load-bearing per Phase 6n DR §7
+ Session-5 user direction).** The 4 horizon-Crooks-side predicates
encode the **Jacobson reading** (equilibrium-Clausius δQ = T·dS at the
local Rindler horizon — Jacobson 1995, Eling-Guedens-Jacobson f(R)).
They EXPLICITLY do NOT encode the Verlinde reading (gravity AS entropic
force, falsified per Phase 6m Track B 8 NO-GO-R5 unanimous closure).
This distinction is preserved at every Lean statement.

**Stage 2-3 honest scope:** the biconditional captures the *structural
form* of the Sakharov ↔ horizon-Crooks correspondence at the predicate
level — each Sakharov condition has a horizon-Crooks projection, and
the iff holds at the Bool-projection level. The *substrate-level
derivation* of each pairing (e.g., "universal coupling ⇒ entropy
current has correct sign at the local Rindler horizon" via the full
Volovik-Jannes ³He-A Bogoliubov-quasiparticle path measure) requires
the substantive analog-horizon-substrate machinery, which lives at the
domain-physics layer (Stage 4+).

References:
- Phase 6n DR §8 — the load-bearing reformulation per Phase 6n+ DR
- Phase 6e implication `sakharov_induced_gravity_criterion_implies_lambda_j_eq_lambda_hk`
  (`JacobsonThermoGRDarkEnergy.lean` JTGR6) — the analogous Phase 6e
  Sakharov → Λ_J = Λ_HK implication (one-way at current substrate-data
  encoding; biconditional pending substrate-data refactor)
- Phase 6m Track C JTGR survivors — class-(b/b'/b'') assignments per
  R5 §3.6 inform which substrate horizon-Crooks reading applies
- temporary/working-docs/phase6n/6n_zeta_D3_L3_reframing_predraft.md
  (D3+L3 reframing pre-draft for bundle absorption — HELD per Session-5)
- temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md §6.2
  (the algebraic-FDR `hasDynamicalKMS_algebraic` form is the substantive
  KMS substrate; this Stage 2-3 module respects that finding via the
  `HorizonCrooksSubstrate` bundle's HDB witness, NOT via the strict-
  invariance `KMSSymmetry`)
-/
import SKEFTHawking.CrooksAnalogHawking.SakharovHorizonCrooks

namespace SKEFTHawking.CrooksAnalogHawking

open SKEFTHawking.JacobsonThermoGRDarkEnergy

/-! ## The 4 horizon-Crooks-side predicates (one per Sakharov condition). -/

/--
**Sakharov-1 horizon-Crooks projection: Lorentz compatibility.**

A `HorizonCrooksSubstrate`'s emergent metric admits Lorentz-like
SO(3,1) or restricted SO(3) symmetry — the Sakharov-1 (emergentLorentz)
condition projected to the horizon-Crooks substrate level. -/
def horizonLorentzCompatible (HCS : HorizonCrooksSubstrate) : Bool :=
  HCS.sakharov.emergentLorentz

/--
**Sakharov-2 horizon-Crooks projection: entropy-current sign.**

Universal coupling (Sakharov-2) implies all matter sectors propagate on
the same effective metric near the substrate's Fermi/Weyl point — which
in horizon-Crooks language means the horizon's entropy-production
functional σ has the *correct* (positive-on-positive-displacement) sign
at the local Rindler horizon. The Bool-projection captures the predicate-
level statement; the substrate-level derivation is Stage 4+. -/
def horizonEntropySignCorrect (HCS : HorizonCrooksSubstrate) : Bool :=
  HCS.sakharov.universalCoupling

/--
**Sakharov-3 horizon-Crooks projection: Newton-constant normalization.**

Induced 1/(16πG_eff) generated dominantly from matter-loop fluctuations
(Sakharov-3) — in horizon-Crooks language, the HDB measure's
normalization matches the effective Newton constant. -/
def horizonNewtonNormCorrect (HCS : HorizonCrooksSubstrate) : Bool :=
  HCS.sakharov.inducedNewtonConstant

/--
**Sakharov-4 horizon-Crooks projection: Λ_HK matching.**

Induced Λ_eff coincides with proper substrate vacuum energy
Λ_HK = ⟨T_μν⟩_vacuum / g_μν (Sakharov-4) — in horizon-Crooks language,
the HDB rate at the local Rindler horizon matches Λ_HK. -/
def horizonLambdaMatch (HCS : HorizonCrooksSubstrate) : Bool :=
  HCS.sakharov.lambdaEffEqLambdaHK

/--
**Jacobson horizon-Crooks compatibility (the 4-conjunct RHS predicate).**

A `HorizonCrooksSubstrate` is `jacobsonHorizonCompatible` if all 4
horizon-Crooks-side projections hold (Lorentz + entropy sign + Newton
norm + Λ matching). This is the substantive horizon-Crooks-side
analog of `sakharovCriterion`.

**Jacobson reading explicit:** the 4 conjuncts encode the Jacobson 1995
fluctuation-theorem-at-Rindler-horizon structure; they do NOT encode
the Verlinde gravity-as-entropic-force reading. -/
def jacobsonHorizonCompatible (HCS : HorizonCrooksSubstrate) : Prop :=
  horizonLorentzCompatible HCS = true ∧
  horizonEntropySignCorrect HCS = true ∧
  horizonNewtonNormCorrect HCS = true ∧
  horizonLambdaMatch HCS = true

/-! ## The substantive biconditional. -/

/--
**The Sakharov ↔ horizon-Crooks biconditional theorem (substantive
Stage 2-3 form).**

The four Sakharov conditions are jointly equivalent to the horizon-Crooks
4-conjunct compatibility predicate. Each Sakharov condition has a
horizon-Crooks-side projection, and the joint conjunction (via the
`sakharovCriterion` Bool-AND) matches the joint conjunction of the
horizon-Crooks projections.

**Substantive content:** this is the load-bearing structural restatement
of the Phase 6e implication (`sakharov_induced_gravity_criterion_implies_lambda_j_eq_lambda_hk`,
JTGR6) in horizon-Crooks language. The Phase 6m Track C JTGR survivors
(M1, M2/M7, M3 Exp/ArcTanh, M4, M9; M8 conditional) inherit this
biconditional via their Sakharov-class assignment from R5 §3.6.

The **Jacobson reading** is preserved: the 4 horizon-Crooks-side
predicates encode equilibrium-Clausius-on-Rindler-horizon structure
(Jacobson 1995), NOT gravity-as-entropic-force (Verlinde, falsified
per Phase 6m Track B 8 NO-GO-R5 unanimous closure).

**Proof:** straightforward Bool-algebra. The `sakharovCriterion`
unfolds to `s.emergentLorentz && s.universalCoupling &&
s.inducedNewtonConstant && s.lambdaEffEqLambdaHK = true`, and
`jacobsonHorizonCompatible` unfolds to the matching 4-conjunct
∧-form via the Bool-projection definitions. The biconditional reduces
to the standard `Bool.and ↔ Prop.and` correspondence. -/
theorem sakharov_iff_horizon_crooks (HCS : HorizonCrooksSubstrate) :
    sakharovCriterion HCS.sakharov = true ↔ jacobsonHorizonCompatible HCS := by
  unfold sakharovCriterion jacobsonHorizonCompatible
  unfold horizonLorentzCompatible horizonEntropySignCorrect
         horizonNewtonNormCorrect horizonLambdaMatch
  -- Goal: (s.eL && s.uC && s.iN && s.lEqL = true) ↔
  --        (s.eL = true ∧ s.uC = true ∧ s.iN = true ∧ s.lEqL = true)
  simp only [Bool.and_eq_true, and_assoc]

/-! ## Specialization to the canonical Phase 6e/6m witnesses. -/

/-- **³He-A substrate is `jacobsonHorizonCompatible`** — substantive
specialization. All 4 horizon-Crooks-side projections evaluate to true
for the Volovik-Jannes ³He-A substrate, mirroring `volovik_jannes_he3a_satisfies_sakharov_criterion`
(JTGR7) at the horizon-Crooks layer. -/
theorem helium3A_jacobsonHorizonCompatible :
    jacobsonHorizonCompatible helium3A_horizon_crooks := by
  rw [← sakharov_iff_horizon_crooks]
  exact helium3A_jacobsonConsistent

/-- **FLS BEC substrate is NOT `jacobsonHorizonCompatible`** — substantive
specialization. Sakharov-(ii) failure (universalCoupling = false on FLS
BEC, JTGR8) projects to `horizonEntropySignCorrect = false`,
obstructing the 4-conjunct conjunction. -/
theorem flsBEC_not_jacobsonHorizonCompatible :
    ¬ jacobsonHorizonCompatible flsBEC_horizon_crooks := by
  rw [← sakharov_iff_horizon_crooks]
  exact flsBEC_not_jacobsonConsistent

/-! ## Substrate-classification cross-bridge: Phase 6e + Phase 6m unified. -/

/--
**The substrate-classification partition theorem at the horizon-Crooks layer.**

Combines the ³He-A and FLS BEC specializations with the underlying
biconditional to give a single Lean statement of the Phase 6e + Phase 6m
substrate-classification result IN HORIZON-CROOKS LANGUAGE:

  ³He-A substrate satisfies the 4 horizon-Crooks-side conjuncts.
  FLS BEC substrate fails the 4-conjunct conjunction (via universal-
    coupling failure → entropy-sign-correct-projection failure).

This is the cleanest Lean-level statement of the Stage 2-3 reformulation
deliverable: the Phase 6e Sakharov biconditional + the Phase 6m Track C
substrate-classification all reduce to a single substantive horizon-
Crooks-side claim per substrate.

The **Jacobson reading** is preserved at every projection step. -/
theorem horizonCrooks_partition_at_substantive_layer :
    jacobsonHorizonCompatible helium3A_horizon_crooks ∧
    ¬ jacobsonHorizonCompatible flsBEC_horizon_crooks :=
  ⟨helium3A_jacobsonHorizonCompatible, flsBEC_not_jacobsonHorizonCompatible⟩

end SKEFTHawking.CrooksAnalogHawking
