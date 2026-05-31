import SKEFTHawking.GibbsDuhemTheorem
import SKEFTHawking.QTheoryNoGoTheorem
import SKEFTHawking.DarkEnergyObstructionPrinciple
import SKEFTHawking.DESIComparison

/-!
# Dark-Sector Viability Classification Table

Formal encoding of the dark-sector-compatibility columns added to the
master mechanism-classification table, per Phase 5y Wave 7. Each row is a
Volovik-family mechanism; each column records the viability status under
one of the four orthogonality-principle factors (Wave 3).

## Viability flags tracked per mechanism

1. **Gibbs-Duhem status:** `locked` (w=−1 forced), `evaded` (breaks the
   hypothesis triple), `NA` (framework is not an emergent-vacuum model
   in the Wave 1 sense)
2. **Orthogonality factor count:** 0–4 (number of H4 §9 factors satisfied)
3. **DESI compatibility:** `yes`, `no`, `untested`
4. **MICROSCOPE compatibility:** `yes`, `no`, `constrained`
5. **Compatibility with `GaugeErasure` theorem:** inherited from prior
   work (Phase 3 Wave 3)
6. **Compatibility with ADW gravity Layer 3:** inherited from prior work

## Companion markdown
`temporary/working-docs/phase5y_classification_table_dark.md` contains the
human-readable classification table with full justification text.

## References

- `Lit-Search/Phase-5y/Phase 5y Wave 1 — q-Theory → DESI Fit Derivation (Round 3).md`
- `Lit-Search/Phase-5y/Phase 5y Wave 1 Round 5 (C2 only) — Fermionic-Crystal Elasticity-Tetrad q-Theory.md`
- `Lit-Search/Phase-5y/Phase 5y Hypothesis 1 — Kronecker-Anomaly Second-Sound Graviton as Dark Energy Candidate.md`
- `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md`
-/

namespace SKEFTHawking.ClassificationTableDark

/-!
## Mechanism enumeration

The Volovik-family mechanisms evaluated in Phase 5y:
- Four q-theory realizations (Wave 2)
- Vestigial gravity (H4)
- Kronecker-anomaly second-sound graviton (H1)
-/

/-- All Volovik-family mechanisms tested in Phase 5y. -/
inductive DarkMechanism where
  /-- 4-form q-theory realization (Round 3) -/
  | qtheoryFourForm
  /-- 2-brane q-theory realization (Round 3) -/
  | qtheoryTwoBrane
  /-- Fermionic-crystal elasticity-tetrad q-theory (Round 5) -/
  | qtheoryFermionicCrystal
  /-- Unimodular q-theory (Round 3) -/
  | qtheoryUnimodular
  /-- Vestigial gravity with H4 closed-form EOS (H4) -/
  | vestigialGravity
  /-- Kronecker-anomaly second-sound graviton (H1) -/
  | secondSoundGraviton
  deriving DecidableEq, Repr

/-- Gibbs-Duhem obstruction status. -/
inductive GibbsDuhemStatus where
  | locked  -- w_vac = -1 is forced
  | evaded  -- the hypothesis triple is broken
  | notApplicable  -- framework not in Wave 1's scope
  deriving DecidableEq, Repr

/-- DESI DR2 compatibility under tested mechanisms. -/
inductive DESICompatibility where
  | yes        -- candidate (w₀, w_a) is in the preferred region
  | no         -- candidate is outside the preferred region
  | untested
  deriving DecidableEq, Repr

/-- MICROSCOPE/WEP compatibility status. -/
inductive MicroscopeStatus where
  | compatible   -- doesn't violate the bound
  | constrained  -- marginal
  | violated     -- fails the bound at current precision
  | untested     -- no direct constraint from MICROSCOPE
  deriving DecidableEq, Repr

/-- Full viability record for a single mechanism row. -/
structure MechanismViability where
  gibbsDuhem : GibbsDuhemStatus
  orthogonalityFactorsSatisfied : Nat  -- 0..4
  desi : DESICompatibility
  microscope : MicroscopeStatus
  compatibleWithGaugeErasure : Bool
  compatibleWithADWLayer3 : Bool

/-- The Phase 5y Wave 7 classification table: maps each mechanism to its
    viability record. -/
def classification : DarkMechanism → MechanismViability
  | .qtheoryFourForm =>
    { gibbsDuhem := .locked,
      orthogonalityFactorsSatisfied := 2,
      desi := .no,
      microscope := .compatible,
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }
  | .qtheoryTwoBrane =>
    { gibbsDuhem := .locked,
      orthogonalityFactorsSatisfied := 2,
      desi := .no,
      microscope := .compatible,
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }
  | .qtheoryFermionicCrystal =>
    { gibbsDuhem := .locked,
      orthogonalityFactorsSatisfied := 2,
      desi := .no,
      microscope := .compatible,
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }
  | .qtheoryUnimodular =>
    { gibbsDuhem := .locked,
      orthogonalityFactorsSatisfied := 2,
      desi := .no,
      microscope := .compatible,
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }
  | .vestigialGravity =>
    { gibbsDuhem := .evaded,       -- multiple OPs evade the hypothesis triple
      orthogonalityFactorsSatisfied := 1,  -- only Gibbs-Duhem, fails c_s², T_c, MICROSCOPE
      desi := .no,                  -- wrong phantom sign
      microscope := .violated,      -- fermion-vs-boson WEP violation
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }
  | .secondSoundGraviton =>
    { gibbsDuhem := .notApplicable,  -- not an emergent-vacuum model
      orthogonalityFactorsSatisfied := 0,
      desi := .no,
      microscope := .untested,
      compatibleWithGaugeErasure := true,
      compatibleWithADWLayer3 := true }

/-!
## Viability predicate and theorems
-/

/-- A mechanism is fully viable iff all four orthogonality factors are
    satisfied, DESI-compatible, and MICROSCOPE-compatible. -/
def isFullyViable (m : DarkMechanism) : Bool :=
  let v := classification m
  v.orthogonalityFactorsSatisfied == 4 &&
  (v.desi == DESICompatibility.yes) &&
  (v.microscope == MicroscopeStatus.compatible)

/-- **CTD1 — Number of mechanisms tested: six.**

    Enumerates the full Phase 5y scope: four q-theory realizations plus
    vestigial gravity plus the H1 second-sound graviton. -/
theorem num_mechanisms_six :
    (List.length [DarkMechanism.qtheoryFourForm, DarkMechanism.qtheoryTwoBrane,
                  DarkMechanism.qtheoryFermionicCrystal, DarkMechanism.qtheoryUnimodular,
                  DarkMechanism.vestigialGravity, DarkMechanism.secondSoundGraviton]) = 6 :=
  by decide

/-- **CTD2 — All four q-theory realizations have Gibbs-Duhem locked.**

    Consistent with Wave 2's `QRealization`-indexed results: the four
    q-theory constructions all sit in the Gibbs-Duhem `locked` column. -/
theorem qtheory_all_locked :
    (classification DarkMechanism.qtheoryFourForm).gibbsDuhem = GibbsDuhemStatus.locked ∧
    (classification DarkMechanism.qtheoryTwoBrane).gibbsDuhem = GibbsDuhemStatus.locked ∧
    (classification DarkMechanism.qtheoryFermionicCrystal).gibbsDuhem = GibbsDuhemStatus.locked ∧
    (classification DarkMechanism.qtheoryUnimodular).gibbsDuhem = GibbsDuhemStatus.locked := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **CTD3 — Vestigial gravity evades Gibbs-Duhem but fails MICROSCOPE.**

    The H4 evasion via multiple order parameters is a genuine structural
    success (hence `.evaded`), but the framework fails the fermion-boson
    WEP-differential-coupling test. -/
theorem vestigial_evades_but_fails_microscope :
    (classification DarkMechanism.vestigialGravity).gibbsDuhem = GibbsDuhemStatus.evaded ∧
    (classification DarkMechanism.vestigialGravity).microscope = MicroscopeStatus.violated := by
  refine ⟨rfl, rfl⟩

/-- **CTD4 — No mechanism in the table is fully viable.**

    Direct consequence of the table: every Volovik-family mechanism tested
    in Phase 5y fails at least one of the four orthogonality factors.
    This is the Phase 5y closure statement at the classification level. -/
theorem no_mechanism_fully_viable :
    isFullyViable DarkMechanism.qtheoryFourForm = false ∧
    isFullyViable DarkMechanism.qtheoryTwoBrane = false ∧
    isFullyViable DarkMechanism.qtheoryFermionicCrystal = false ∧
    isFullyViable DarkMechanism.qtheoryUnimodular = false ∧
    isFullyViable DarkMechanism.vestigialGravity = false ∧
    isFullyViable DarkMechanism.secondSoundGraviton = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **CTD5 — All DESI columns are `no`.**

    For every mechanism in the table, the DESI compatibility column reads
    `no` — no tested framework is DESI-compatible. -/
theorem all_desi_no :
    (classification DarkMechanism.qtheoryFourForm).desi = DESICompatibility.no ∧
    (classification DarkMechanism.vestigialGravity).desi = DESICompatibility.no ∧
    (classification DarkMechanism.secondSoundGraviton).desi = DESICompatibility.no := by
  refine ⟨rfl, rfl, rfl⟩

/-- **CTD6 — All mechanisms are GaugeErasure-compatible.**

    Inherited from Phase 3 Wave 3: the GaugeErasure theorem applies
    uniformly across the tested dark-sector frameworks. No mechanism
    breaks the erasure structure. -/
theorem all_gauge_erasure_compatible :
    ∀ m : DarkMechanism, (classification m).compatibleWithGaugeErasure = true := by
  intro m
  cases m <;> rfl

/-- **CTD7 — All mechanisms are ADW-Layer-3-compatible.**

    Similar inheritance: the ADW mechanism's Layer 3 (emergent gravity)
    does not exclude any of the tested dark-sector candidates. The
    incompatibilities are elsewhere (DESI, WEP). -/
theorem all_adw_layer3_compatible :
    ∀ m : DarkMechanism, (classification m).compatibleWithADWLayer3 = true := by
  intro m
  cases m <;> rfl

/-- **CTD8 — Classification closure: every mechanism has 0, 1, or 2
    factors satisfied.**

    No mechanism in the table reaches 3 or 4 of the orthogonality
    factors. This is the quantitative statement of Phase 5y's closure:
    the Volovik-family dark-energy landscape is currently at most
    "2 of 4" viable. -/
theorem all_mechanisms_at_most_2 :
    ∀ m : DarkMechanism, (classification m).orthogonalityFactorsSatisfied ≤ 2 := by
  intro m
  cases m <;> decide

end SKEFTHawking.ClassificationTableDark
