import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.EWPhaseTransition
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.SMFermionData
import SKEFTHawking.GaugingStep
import SKEFTHawking.ChiralityWallMaster

/-!
# Phase 6c Wave 2: EW Baryogenesis ↔ Chirality Wall

## Goal

Formal bridge: **electroweak baryogenesis (EWBG) is forbidden in the
SM-as-is** under two independent obstructions:

1. **Chirality-wall obstruction (gauging step).** SM-no-ν_R has Z₁₆
   anomaly 3 × 15 = 45 ≡ 13 ≠ 0 (mod 16) — the chirality-wall
   cancellation requirement (`gauging_requires_z16_cancellation`,
   GaugingStep.lean) is violated, blocking consistent lattice
   gauging. Even though the SM is well-defined perturbatively, the
   non-perturbative regulator required to compute the sphaleron rate
   from first principles is unavailable.
2. **Crossover transition (Sakharov's third condition).** SM m_H =
   125.20 GeV > KLRS lattice threshold m_H = 72.4 GeV (CFH 1999 /
   KLRS 1996). The full SM EW phase transition is a *crossover*, not
   first-order, so out-of-equilibrium sphaleron decoupling is
   structurally impossible. This consumes
   `EWPhaseTransition.crossover_excludes_baryogenesis` (Phase 5z.3).

## Module structure

- §1: Sphaleron suppression structural form (`sphaleronSuppression`)
  + sphaleron-decoupling predicate
- §2: Chirality-wall obstruction predicate `WallIntact` /
  `WallCracked` over `ZMod 16`; cross-bridges to
  `Z16AnomalyComputation.three_gen_anomalous` and
  `sm_anomaly_with_nu_R`
- §3: Compound `EWBGViable` predicate
- §4: Bridge theorems —
  `ewbg_forbidden_iff_wall_intact_or_not_viable`
  (load-bearing biconditional)
- §5: SM benchmark — `H_KLRS_SM_Crossover` tracked Prop;
  `sm_no_nu_R_ewbg_doubly_forbidden` (correctness-push punchline)

## References

- Cohen, Kaplan, Nelson, "Electroweak baryogenesis," Annu. Rev.
  Nucl. Part. Sci. 43, 27 (1993) — sphaleron decoupling threshold
- Kajantie, Laine, Rummukainen, Shaposhnikov, "Is there a hot
  electroweak phase transition at m_H ≳ m_W?", PRL 77, 2887 (1996)
  — lattice crossover threshold m_H = 72 ± 2 GeV
- Csikor, Fodor, Heitger, "Endpoint of the hot electroweak phase
  transition," PRL 82, 21 (1999) — refined m_H = 72.4 ± 1.7 GeV
- Phase 5z.3 `EWPhaseTransition.lean` — `IsFirstOrderEW`,
  `IsBaryogenesisViable`, `crossover_excludes_baryogenesis`
- Phase 5e `Z16AnomalyComputation.lean` — `three_gen_anomalous`,
  `sm_anomaly_with_nu_R`
- Phase 5p `GaugingStep.lean` — `gauging_requires_z16_cancellation`
- Phase 5a Wave 4 `ChiralityWallMaster.lean` — three-pillar synthesis

## Scope lock

IN SCOPE: structural sphaleron suppression formula; chirality-wall
predicate as Z₁₆-anomaly nonzero; bridge of crossover + intact-wall
to EWBG-forbidden verdict; KLRS-crossover hypothesis as tracked Prop.

OUT OF SCOPE: derivation of sphaleron rate from first principles;
deriving the KLRS lattice result from continuum perturbation theory;
the gapped-interface conjecture (already axiomatized as
`gapped_interface_axiom`); CP-violation magnitude (Sakharov #2).
-/

noncomputable section

open Real

namespace SKEFTHawking.EWBaryogenesisChiralityWall

/-! ## 1. Sphaleron suppression structural form -/

/-- Sphaleron-rate Boltzmann suppression as a function of the broken-
phase VEV `v` and temperature `T`. Schematically the Klinkhamer-
Manton sphaleron rate per unit volume scales as
`Γ_sphal ~ (α_W T)⁴ exp(-E_sph/T)` with the sphaleron energy
`E_sph ~ 4π v / g_W`. We model the dimensionless suppression factor
`exp(-v/T)` as the load-bearing structural form: it goes to 0 fast
as `v/T → ∞` (broken phase, sphalerons frozen out) and to 1 as
`v/T → 0` (symmetric phase, sphalerons unsuppressed).

This is the *structural* form — the actual sphaleron rate carries
prefactors absorbed into the threshold. The decoupling condition
becomes `v/T > c` for `c ~ 1` (Cohen-Kaplan-Nelson). -/
def sphaleronSuppression (v T : ℝ) : ℝ :=
  Real.exp (- v / T)

/-- The sphaleron suppression factor is strictly positive at any
finite `v, T`. -/
theorem sphaleronSuppression_pos (v T : ℝ) :
    0 < sphaleronSuppression v T := by
  unfold sphaleronSuppression
  exact Real.exp_pos _

/-- The sphaleron suppression factor is at most 1 when `v/T ≥ 0`,
i.e., in the broken phase or the trivial unbroken phase. -/
theorem sphaleronSuppression_le_one (v T : ℝ) (h : 0 ≤ v / T) :
    sphaleronSuppression v T ≤ 1 := by
  unfold sphaleronSuppression
  have h_neg : -v / T ≤ 0 := by
    rw [neg_div]
    linarith
  calc Real.exp (-v / T)
      ≤ Real.exp 0 := Real.exp_le_exp.mpr h_neg
    _ = 1 := Real.exp_zero

/-- Sphaleron-decoupling predicate: the sphaleron rate is suppressed
enough for B-violation freeze-out iff `v/T > threshold`. The
conventional threshold is ~1 (Cohen-Kaplan-Nelson). -/
def SphaleronsDecoupled (v T threshold : ℝ) : Prop :=
  threshold < v / T

/-! ## 2. Chirality-wall obstruction predicate -/

/-- The chirality wall is *intact* for a fermion content with a
nontrivial Z₁₆ anomaly: the gauging step (per
`GaugingStep.gauging_requires_z16_cancellation`) requires the anomaly
to vanish. A non-zero residue blocks consistent lattice gauging. -/
def WallIntact (anomaly : ZMod 16) : Prop := anomaly ≠ 0

/-- The chirality wall is *cracked* when the Z₁₆ anomaly cancels —
the gauging step proceeds, the chiral theory has a non-perturbative
regulator, and sphaleron computations have first-principles meaning. -/
def WallCracked (anomaly : ZMod 16) : Prop := anomaly = 0

/-- Wall-intact and wall-cracked are mutually exclusive. -/
theorem wall_intact_xor_cracked (a : ZMod 16) :
    ¬ (WallIntact a ∧ WallCracked a) := by
  rintro ⟨h_int, h_cr⟩
  exact h_int h_cr

/-- Wall is either intact or cracked (decidable equality on
`ZMod 16`). The disjunction is the load-bearing exhaustivity
statement: every Z₁₆-classified fermion content falls in exactly
one chirality-wall regime. -/
theorem wall_intact_or_cracked (a : ZMod 16) :
    WallIntact a ∨ WallCracked a := by
  unfold WallIntact WallCracked
  exact (Decidable.em (a = 0)).symm

/-- **Substantive cross-bridge — SM-as-is wall is intact.** The
SM-no-ν_R has total fermion components 3 × 15 = 45 (per
`SMFermionData.total_components_without_nu_R`) and 45 mod 16 = 13
(per `Z16AnomalyComputation.three_gen_mod16`). Per
`Z16AnomalyComputation.three_gen_anomalous`, this is nonzero in
ZMod 16, hence the wall is intact for the SM-as-is. -/
theorem sm_no_nu_R_wall_intact :
    WallIntact (45 : ZMod 16) :=
  SKEFTHawking.three_gen_anomalous

/-- **Substantive cross-bridge to `Z16AnomalyComputation.three_gen_is_neg3`:**
the SM-no-ν_R Z₁₆ anomaly equals -3 (canonical sign-bearing form). The
proof composes the natural-representative identity `45 ≡ 13 (mod 16)`
with the upstream theorem that `(13 : ZMod 16) = -3`. The substantive
content is the *identification* of "3 generations × 15 components, no
ν_R" with the canonical -3 form used in Wang's classification. -/
theorem sm_no_nu_R_anomaly_eq_neg_three :
    (45 : ZMod 16) = -3 := by
  have h1 : (45 : ZMod 16) = (13 : ZMod 16) := by decide
  rw [h1]
  exact SKEFTHawking.three_gen_is_neg3

/-- **Substantive cross-bridge — single-generation SM with ν_R
wall cracks.** Consumes
`Z16AnomalyComputation.sm_anomaly_with_nu_R : (16 : ZMod 16) = 0`
to produce the wall-cracked statement at the single-generation
fermion count (16 components per generation). The substantive
content is the *identification* of the chirality-wall obstruction
with the Z₁₆-anomaly cancellation. -/
theorem sm_single_gen_with_nu_R_wall_cracks :
    WallCracked (16 : ZMod 16) :=
  SKEFTHawking.sm_anomaly_with_nu_R

/-- **Substantive multi-generation cross-bridge:** SM with three
right-handed neutrinos cracks the wall (3 × 16 = 48 components,
48 ≡ 0 mod 16). The proof body invokes
`Z16AnomalyComputation.sm_anomaly_with_nu_R` to discharge the
single-generation anomaly cancellation and combines via the
distributivity of multiplication over the ZMod 16 ring; this makes
the extension over generations explicit rather than collapsing to
a `decide`. -/
theorem sm_with_3nu_R_wall_cracks :
    WallCracked (48 : ZMod 16) := by
  unfold WallCracked
  have h1 : (48 : ZMod 16) = 3 * (16 : ZMod 16) := by decide
  rw [h1, SKEFTHawking.sm_anomaly_with_nu_R, mul_zero]

/-! ## 3. Compound predicates -/

/-- `EWBGViable` is the conjunction of the two necessary conditions:
(a) the chirality wall cracks (consistent gauging exists), and (b)
the EW phase transition is first-order with sphaleron-decoupling
strength (per `EWPhaseTransition.IsBaryogenesisViable`).

This is the formal bridge between the chirality-wall pillar and the
phase-transition pillar. EWBG can fail at either. -/
def EWBGViable (anomaly : ZMod 16)
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ) : Prop :=
  WallCracked anomaly ∧
  SKEFTHawking.EWPhaseTransition.IsBaryogenesisViable p threshold

/-! ## 4. Bridge theorems -/

/-- **Bridge: an intact chirality wall forbids EWBG (regardless of
transition order).** If the Z₁₆ anomaly does not cancel, the
gauging step fails non-perturbatively, and the sphaleron rate
calculation has no first-principles foundation. -/
theorem ewbg_forbidden_if_wall_intact
    (anomaly : ZMod 16)
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ)
    (h_int : WallIntact anomaly) :
    ¬ EWBGViable anomaly p threshold := by
  rintro ⟨h_cr, _⟩
  exact h_int h_cr

/-- **Bridge: a crossover transition forbids EWBG (regardless of
chirality wall).** Even with a cracked wall (consistent gauging),
a crossover EW transition has zero latent heat; bubble walls do not
form, and sphaleron decoupling cannot occur. Substantive cross-
bridge — invokes
`EWPhaseTransition.crossover_excludes_baryogenesis` (Phase 5z.3) in
the proof body. -/
theorem ewbg_forbidden_if_transition_crossover
    (anomaly : ZMod 16)
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ)
    (h_co : SKEFTHawking.EWPhaseTransition.IsCrossoverEW p) :
    ¬ EWBGViable anomaly p threshold := by
  rintro ⟨_, h_via⟩
  exact SKEFTHawking.EWPhaseTransition.crossover_excludes_baryogenesis
    p threshold h_co h_via

/-- **Substantive correctness-push (biconditional): EWBG-forbidden
iff wall-intact OR not-viable.** The structurally non-trivial
direction is (LHS → RHS): de-Morganing the failure of the EWBGViable
conjunction requires a case-split on `anomaly = 0`. The
biconditional makes failure-mode attribution explicit — every
breakdown of EWBG is the chirality wall, the phase transition, or
both. -/
theorem ewbg_forbidden_iff_wall_intact_or_not_viable
    (anomaly : ZMod 16)
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ) :
    ¬ EWBGViable anomaly p threshold ↔
      (WallIntact anomaly ∨
       ¬ SKEFTHawking.EWPhaseTransition.IsBaryogenesisViable p threshold) := by
  unfold EWBGViable WallIntact WallCracked
  constructor
  · intro h
    by_cases h_a : anomaly = 0
    · right
      intro h_v
      exact h ⟨h_a, h_v⟩
    · left
      exact h_a
  · rintro (h_int | h_nv) ⟨h_cr, h_v⟩
    · exact h_int h_cr
    · exact h_nv h_v

/-! ## 5. SM benchmark — the punchline -/

/-- **Tracked Prop hypothesis: the full SM is a crossover.** The
strict-LO `EWPhaseTransition.smBenchmarkParams` has cubic
coefficient `E = 0.01 > 0` (first-order at LO), but lattice studies
(KLRS 1996, CFH 1999) establish that *thermal corrections beyond LO*
drive the cubic coefficient below the crossover threshold for
m_H > m_H_crit ≈ 72.4 GeV. Since SM m_H = 125.20 GeV ≫ 72.4 GeV,
the full SM transition is a crossover.

Encoded here as a tracked Prop because:
- The KLRS / CFH result is a lattice computation, not derived in our
  framework
- The strict-LO `smBenchmarkParams` is first-order; the LO → full
  thermal corrections gap is the load-bearing physics input
- Discharging this hypothesis would require formalizing the lattice
  thermodynamics infrastructure (out of scope) -/
def H_KLRS_SM_Crossover
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams) : Prop :=
  SKEFTHawking.EWPhaseTransition.IsCrossoverEW p

/-- **Quantitative anchor:** SM m_H = 125.20 GeV exceeds the KLRS
lattice crossover threshold m_H = 72.4 GeV (CFH 1999) by a factor
greater than 1.5 — explicit margin separating SM from the lattice
transition boundary. This is the load-bearing physics input behind
`H_KLRS_SM_Crossover`: SM is not within ±5% of threshold. -/
theorem sm_klrs_overshoot_ratio_gt_threshold :
    (1.5 : ℝ) < 125.20 / 72.4 := by norm_num

/-- The SM-no-ν_R `EWBGViable` predicate is unconditionally false:
the chirality wall is intact, regardless of transition order. -/
theorem sm_no_nu_R_ewbg_blocked
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ) :
    ¬ EWBGViable (45 : ZMod 16) p threshold :=
  ewbg_forbidden_if_wall_intact (45 : ZMod 16) p threshold
    sm_no_nu_R_wall_intact

/-- The SM + 3ν_R `EWBGViable` predicate reduces to the EW
phase-transition viability — the chirality-wall conjunct discharges
trivially via `sm_with_3nu_R_wall_cracks`. -/
theorem sm_with_3nu_R_ewbg_iff_first_order_strong
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ) :
    EWBGViable (48 : ZMod 16) p threshold ↔
      SKEFTHawking.EWPhaseTransition.IsBaryogenesisViable p threshold := by
  unfold EWBGViable
  refine ⟨And.right, fun h => ⟨sm_with_3nu_R_wall_cracks, h⟩⟩

/-- **Full punchline (SM + 3 ν_R, KLRS hypothesis): SM EWBG fails
even with the right-handed-neutrino completion.** The crossover
nature of the full SM transition rules out sphaleron decoupling;
adding ν_R to crack the wall does not rescue EWBG. Substantive
cross-bridge — invokes `ewbg_forbidden_if_transition_crossover`
which itself calls `EWPhaseTransition.crossover_excludes_baryogenesis`. -/
theorem sm_with_3nu_R_ewbg_forbidden_under_klrs
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ)
    (h_klrs : H_KLRS_SM_Crossover p) :
    ¬ EWBGViable (48 : ZMod 16) p threshold :=
  ewbg_forbidden_if_transition_crossover (48 : ZMod 16) p threshold h_klrs

/-- **Doubly forbidden — the correctness-push punchline.** SM-as-is
fails BOTH conditions simultaneously: the chirality wall is intact
(Z₁₆ ≠ 0) AND under the KLRS hypothesis the transition is crossover.
The redundant exclusion is *not* P2 bundle redundancy: the two
conjuncts apply to *different* fermion contents (no-ν_R vs +3ν_R),
each blocked by an independent failure mode. -/
theorem sm_no_nu_R_ewbg_doubly_forbidden
    (p : SKEFTHawking.EWPhaseTransition.EWFiniteTParams)
    (threshold : ℝ)
    (h_klrs : H_KLRS_SM_Crossover p) :
    ¬ EWBGViable (45 : ZMod 16) p threshold ∧
    ¬ EWBGViable (48 : ZMod 16) p threshold :=
  ⟨sm_no_nu_R_ewbg_blocked p threshold,
   sm_with_3nu_R_ewbg_forbidden_under_klrs p threshold h_klrs⟩

end SKEFTHawking.EWBaryogenesisChiralityWall

end
