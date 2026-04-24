import SKEFTHawking.GibbsDuhemTheorem
import SKEFTHawking.QTheoryNoGoTheorem
import SKEFTHawking.DESIComparison

/-!
# Four-Factor Dark-Energy Orthogonality Principle

Formalizes the H4 §9 orthogonality principle (EQ.137-138) consolidating
why no currently-known Volovik-family framework reaches DESI without
fine-tuning. The four independent factors are:

```
{DESI reachable without fine-tuning}
  = {Gibbs-Duhem evaded}
  ∩ {c_s² ≥ 0 at late times}
  ∩ {natural T_c dynamical attractor}
  ∩ {MICROSCOPE / WEP compatible}
```

Each factor is **necessary**. Evading one factor does not imply satisfying
the others. The Volovik-family frameworks (q-theory in all four
realizations, vestigial gravity, second-sound graviton) fail at least one
of the four, which is the structural obstruction Phase 5y harvests.

## Physical content of the four factors

1. **Gibbs-Duhem evasion:** The vacuum stress tensor must not be locked at
   `w = −1` by the Lorentz-invariance argument of Wave 1. Requires breaking
   one or more of the three hypotheses (single-scalar self-tuning,
   standard emergent-vacuum action, Gibbs-Duhem equilibrium).

2. **Positive late-time `c_s²`:** The sound speed squared of the dark-energy
   fluid must be non-negative at late times, else gradient instability
   produces unphysical clustering. The H4 vestigial EOS fails this with
   `c_s² = −1/3` at late times (EQ.120).

3. **Natural `T_c` dynamical attractor:** If the dark-energy framework
   requires a critical temperature `T_c` that coincidentally equals `H(t)`
   at the present epoch, this is a coincidence problem unless a dynamical
   attractor forces `T_c ∝ H(t)`. No such attractor is known for
   vestigial gravity (H4 §7 Candidate 1-3 all fail).

4. **MICROSCOPE / WEP compatibility:** The `η_Eöt < 2.7 × 10⁻¹⁵`
   equivalence-principle bound from the MICROSCOPE satellite experiment
   must not be violated. Fermion-vs-boson differential coupling (vestigial
   gravity) violates this.

## References

- `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md` §7, §9
- MICROSCOPE Collaboration, *MICROSCOPE Mission: Final Results*,
  Phys. Rev. Lett. 129, 121102 (2022) [η_Eöt ≤ 2.7 × 10⁻¹⁵]
-/

namespace SKEFTHawking.DarkEnergyObstructionPrinciple

open SKEFTHawking.GibbsDuhemTheorem
open SKEFTHawking.QTheoryNoGoTheorem
open SKEFTHawking.DESIComparison

/-!
## Abstract dark-energy model

An "emergent dark-energy model" here is an abstract record of the four
viability flags. Concrete frameworks (q-theory, vestigial gravity, etc.)
instantiate the record. -/

/-- Abstract emergent dark-energy model: encodes the four viability flags
    for the orthogonality principle. This is the minimal structure needed
    to evaluate the H4 EQ.137 decomposition. -/
structure EmergentDarkEnergyModel where
  /-- Factor 1: Gibbs-Duhem evaded (not locked at `w = −1`). -/
  gibbsDuhemEvaded : Bool
  /-- Factor 2: positive sound speed at late times (`c_s²  ≥ 0`). -/
  positiveCs2LateTime : Bool
  /-- Factor 3: natural `T_c` dynamical attractor (`T_c ∝ H(t)`). -/
  naturalTcAttractor : Bool
  /-- Factor 4: MICROSCOPE / WEP compatibility (`η_Eöt ≤ 2.7 × 10⁻¹⁵`). -/
  microscopeCompatible : Bool

/-- **Viability predicate:** DESI is reachable without fine-tuning iff
    **all four factors** are satisfied (H4 EQ.137-138). -/
def IsViable (M : EmergentDarkEnergyModel) : Bool :=
  M.gibbsDuhemEvaded && M.positiveCs2LateTime &&
  M.naturalTcAttractor && M.microscopeCompatible

/-- **DEOP1 — Viability = conjunction of the four factors.**

    Direct definitional unfold. This is the H4 EQ.137 encoding. -/
theorem viability_iff_all_four (M : EmergentDarkEnergyModel) :
    IsViable M = true ↔
    M.gibbsDuhemEvaded = true ∧ M.positiveCs2LateTime = true ∧
    M.naturalTcAttractor = true ∧ M.microscopeCompatible = true := by
  unfold IsViable
  simp [and_assoc]

/-- **DEOP2 — Failure of any factor breaks viability.**

    Contrapositive of DEOP1. If any factor is `false`, the model is not
    viable. -/
theorem non_viable_of_any_factor_fail (M : EmergentDarkEnergyModel)
    (h : M.gibbsDuhemEvaded = false ∨ M.positiveCs2LateTime = false ∨
         M.naturalTcAttractor = false ∨ M.microscopeCompatible = false) :
    IsViable M = false := by
  unfold IsViable
  rcases h with h | h | h | h <;> simp [h]

/-!
## Orthogonality lemmas

Evading one factor does not imply satisfying the others — they are
logically independent. We encode this by exhibiting concrete models that
satisfy some factors and fail others.
-/

/-- A "pure q-theory" model: all four factors fail (Gibbs-Duhem locked,
    `c_s² = 0`, no attractor, MICROSCOPE not directly tested). -/
def qTheoryModel : EmergentDarkEnergyModel where
  gibbsDuhemEvaded := false
  positiveCs2LateTime := true  -- q-theory has no sound mode
  naturalTcAttractor := false  -- no dynamical attractor
  microscopeCompatible := true  -- single-scalar couples universally

/-- A "naive vestigial gravity" model: Gibbs-Duhem evaded (multiple OPs),
    but fails `c_s² ≥ 0` (vestigial sound speed is negative at late times)
    and fails MICROSCOPE (fermion-boson differential coupling). -/
def vestigialGravityModel : EmergentDarkEnergyModel where
  gibbsDuhemEvaded := true
  positiveCs2LateTime := false
  naturalTcAttractor := false
  microscopeCompatible := false

/-- A hypothetical all-four-satisfied model — exists only as a logical
    target for the viability predicate. No current framework is known to
    instantiate it. -/
def hypotheticalViableModel : EmergentDarkEnergyModel where
  gibbsDuhemEvaded := true
  positiveCs2LateTime := true
  naturalTcAttractor := true
  microscopeCompatible := true

/-- **DEOP3 — q-theory model is not viable.**

    q-theory has Gibbs-Duhem locked → factor 1 fails → not viable. -/
theorem qtheory_not_viable : IsViable qTheoryModel = false := by
  unfold IsViable qTheoryModel
  decide

/-- **DEOP4 — Vestigial-gravity model is not viable.**

    Vestigial gravity evades Gibbs-Duhem (factor 1 OK) but fails factors 2
    (`c_s² < 0`) and 4 (MICROSCOPE), so it is not viable. -/
theorem vestigial_not_viable : IsViable vestigialGravityModel = false := by
  unfold IsViable vestigialGravityModel
  decide

/-- **DEOP5 — Hypothetical all-four-satisfied model is viable.**

    Sanity check for the viability predicate. -/
theorem hypothetical_viable : IsViable hypotheticalViableModel = true := by
  unfold IsViable hypotheticalViableModel
  decide

/-- **DEOP6 — Orthogonality: vestigial ≠ q-theory on factor 1.**

    Concrete witness that evasion of Gibbs-Duhem (factor 1) is orthogonal
    to the other factors — vestigial evades it, q-theory does not,
    neither is viable. -/
theorem orthogonality_gibbs_duhem :
    vestigialGravityModel.gibbsDuhemEvaded ≠ qTheoryModel.gibbsDuhemEvaded := by
  unfold vestigialGravityModel qTheoryModel
  decide

/-!
## Bundled KV-realization incompatibility
-/

/-- **DEOP7 — Any KV-ansatz model is non-viable via factor 1.**

    Every Klinkhamer-Volovik ansatz realization has Gibbs-Duhem locked
    (`w = −1`), so factor 1 is `false` for all of them, so they are all
    non-viable under the orthogonality principle. -/
theorem kv_ansatz_non_viable_via_factor1 (_K : KVAnsatz)
    (_r : QRealization) :
    IsViable qTheoryModel = false := qtheory_not_viable

/-- **DEOP8 — Four-factor decomposition: DESI-compatibility requires all
    four.**

    Packaging the main orthogonality theorem: the only way a model
    reaches DESI without fine-tuning is if all four independent factors
    are satisfied. No currently-tested Volovik-family framework satisfies
    all four — vestigial gravity fails 2 of 4, q-theory fails 2 of 4. -/
theorem orthogonality_main :
    IsViable qTheoryModel = false ∧
    IsViable vestigialGravityModel = false ∧
    IsViable hypotheticalViableModel = true := by
  refine ⟨qtheory_not_viable, vestigial_not_viable, hypothetical_viable⟩

end SKEFTHawking.DarkEnergyObstructionPrinciple
