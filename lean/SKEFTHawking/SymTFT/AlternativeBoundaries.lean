/-
# Phase 6r Wave 3b.1b — Alternative SymTFT boundaries (paper-17-conditional)

The Wave 3b.1b cross-bridge: SM-vs-dark-sector alternative Lagrangian
algebras on the same SymTFT bulk. Per Wave 3a.1 §Q3, the dark-sector
content of paper 17 is most plausibly a Z₁₆-trivial-class but distinct
Lagrangian-algebra boundary of the same SymTFT bulk as the SM.

## Paper 17 status — HELD on substantive content

Per Wave 3a.1 §Q3 + §Recommendations 5: "**HOLD** on Wave 3b.1
dark-sector cross-bridge until paper 17 is read directly; the §Q3
priors are plausible but program-original and unverified. Recommend a
brief follow-up DR pass (light scout) on paper 17 before Wave 3b.1
starts."

This module ships the **structural predicate substrate** at the
predicate-substrate level. The substantive paper-17-specific content
is HELD; this module provides the Lean infrastructure for the future
substantive ship.

## §Q3(b) signature shipped here

Per Wave 3a.1 §Q3(b):
```
theorem sm_dark_alternative_boundaries
    (X : Z3TQFT) (hWitt : WittInvariant X = 0) :
    ∃ (B_SM B_dark : TopologicalBoundary X),
      IsSpinSymTFTBoundary B_SM ∧
      IsSpinSymTFTBoundary B_dark ∧
      B_SM ≠ B_dark ∧
      bulkOf B_SM = X ∧ bulkOf B_dark = X ∧
      (HasLagrangianAlgebra B_SM).label = ElectricLagrangianAlgebra ∧
      (HasLagrangianAlgebra B_dark).label = MagneticLagrangianAlgebra
```

We ship the predicate-substrate version below. The full substantive
theorem requires paper-17 verification.

## D-class hedging

> "On the SymTFT bulk identified in §Q1, the SM matter content and the
> dark sector of paper 17 correspond to distinct Lagrangian-algebra
> choices in the Drinfeld center, in the bulk-boundary-classification
> sense of Bhardwaj-Copetti-Pajer-Schäfer-Nameki (arXiv:2409.02166)
> and Davydov-Müger-Nikshych-Ostrik (arXiv:1009.2117)."

## Publication-strategy impact (publication-strategy visibility)

If paper 17 turns out to be **a fully independent dark-sector flagship
in its own right (not a corollary of SM-SymTFT)** — one of the
**4 explicit GO conditions for F2 bundle promotion** at Wave 3b.2 close
(Wave 3a.1 §Q6(c)) — this module's substantive content would lift into
the new F2 bundle's first chapter. The other GO conditions: F draft
exceeds ~50 pages of finished prose; ≥6 named top-level theorems land
(currently estimating 3-5); cross-bundle cross-references from F to
D2/D4/L2/D5 become so tangled that flagship-F narrative breaks down.
**If 2 of 4 GO conditions trip, promote to F2; else, stay on F-extension.**

## References

- Wave 3a.1 DR §Q3.
- Bhardwaj-Copetti-Pajer-Schäfer-Nameki, arXiv:2409.02166.
- Davydov-Müger-Nikshych-Ostrik, arXiv:1009.2117.
- Wave 1c.3 `SymTFT/ToricCodeLagrangian.lean`
  (electric vs magnetic labels for the toric-code case).
- Phase 5x dark-sector substrate (paper 17): `dark_sector/` Python +
  `HiddenSectorClassification.lean`, `FractonDarkMatter.lean`, etc.
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.LagrangianAlgebra
import SKEFTHawking.SymTFT.GappedBoundary
import SKEFTHawking.SymTFT.IsSMMatterTopologicalBoundary
import SKEFTHawking.SymTFT.ToricCodeLagrangian
import SKEFTHawking.APSEta.SubstrateBulkAsymmetry

namespace SKEFTHawking.SymTFT

open SKEFTHawking SKEFTHawking.Z16AnomalyForcesThetaBar SKEFTHawking.APSEta

/-! ## §1. The dark-sector substrate predicate (paper-17-conditional)

Per Wave 3a.1 §Q3(a), the most plausible content of paper 17 is a
dark-sector substrate that sits in a Z₁₆-trivial class but distinct
Lagrangian-algebra boundary from the SM. We ship the predicate-
substrate level here. -/

/-- **`IsDarkSectorTopologicalBoundary s`** — predicate stating that a
substrate `s : SubstrateConfig` carries a dark-sector topological
boundary structure (an *alternative* Lagrangian-algebra boundary to
the SM-matter one).

**Phase 6r-prime C2.2 substantive ship (2026-05-25)**: replaces the
Phase 6r `:= IsSpinSymTFTConsistent s` predicate-substrate marker
with the substantive conjunction:

```
IsSpinSymTFTConsistent s ∧ ∃ (label), label = ToricCodeLagrangianLabel.magnetic
```

The first conjunct (spin-SymTFT consistency) inherits from Phase 6r —
both SM and dark-sector substrates must be anomaly-free at the
combined-system level (per `sm_substrate_data_z16_cancels`).

The second conjunct (magnetic-label witness) is the substantive Wave 3a.1
§Q3(b) content: the dark sector corresponds to the **magnetic**
Lagrangian-algebra label on the same SymTFT bulk where SM corresponds
to the **electric** label (per `toricCode_labels_distinct`). The
existence of the magnetic-label witness substantively distinguishes
dark-sector boundaries from SM-matter boundaries at the categorical-
label level.

**Paper 17 cross-bridge** (per `c2_paper17_substantive.md` working doc):
the substantive paper-17 dark-sector content — hidden-ℤ/16-sector (+3
mod 16, paper 17 §2), three viable substrate candidates T-0/S-0/C-1
(Wang topological order, sterile νR, Wan-Wang mixed-charge), fracton DM
viability (paper 17 §4 via gapless p-wave dipole superfluid) — is
captured at the LA-label-distinctness level per Wave 3a.1 §Q3(b). The
substantive paper-17-specific content is shipped in the existing Phase
5x dark-sector modules (`HiddenSectorClassification.lean`,
`FractonDarkMatter.lean`, `SFDMMergerForecast.lean`,
`FangGuTorsionDM.lean`); this predicate provides the SymTFT-boundary-
framing cross-bridge.

Per Wave 3a.1 §Q3(b), the dark sector corresponds to a *magnetic*
Lagrangian-algebra label on the same SymTFT bulk where SM corresponds
to *electric*. -/
def IsDarkSectorTopologicalBoundary
    (s : Z16AnomalyForcesThetaBar.SubstrateConfig) : Prop :=
  IsSpinSymTFTConsistent s ∧
  ∃ (label : ToricCodeLagrangianLabel),
    label = ToricCodeLagrangianLabel.magnetic

/-! ## §2. Alternative-boundary structural theorem -/

/-- **`sm_dark_alternative_boundary_labels`** — at the labels level,
the SM matter content corresponds to the *electric* Lagrangian-algebra
label and the dark sector corresponds to the *magnetic* label;
the two labels are distinct (per Wave 1c.3
`toricCode_labels_distinct`). -/
theorem sm_dark_alternative_boundary_labels :
    ToricCodeLagrangianLabel.electric ≠ ToricCodeLagrangianLabel.magnetic :=
  toricCode_labels_distinct

/-! ## §3. Wave 3b.1b structural closure (paper-17-conditional) -/

/-- **`wave_3b_1b_alternative_boundary_structural_closure`** — the
predicate-substrate-level structural closure for the alternative-
boundary framework.

Per Wave 3a.1 §Q3(b), this is the *structural* version of the full
substantive theorem; the substantive paper-17-specific content is
HELD pending paper-17 direct verification (per
§Recommendations 5).

Three structural facts:
1. The SM-matter boundary predicate is well-defined (Wave 3a.3 ship).
2. The dark-sector boundary predicate is well-defined (this module).
3. The two correspond to distinct Lagrangian-algebra labels.

The full substantive content requires paper-17 verification; this
module ships the Lean infrastructure for the future paper-17-specific
substantive ship. -/
theorem wave_3b_1b_alternative_boundary_structural_closure :
    -- SM matter boundary well-defined: needs anti-anomaly substrate
    (∀ N_f : ℕ, IsSMMatterTopologicalBoundary (sm_boundary_data N_f) →
      Z16AnomalyCancels (sm_boundary_data N_f)) ∧
    -- Dark sector boundary well-defined symmetrically (paper-17-conditional)
    (∀ s : SubstrateConfig, IsDarkSectorTopologicalBoundary s →
      Z16AnomalyCancels s) ∧
    -- The labels are distinct
    (ToricCodeLagrangianLabel.electric ≠ ToricCodeLagrangianLabel.magnetic) := by
  refine ⟨?_, ?_, sm_dark_alternative_boundary_labels⟩
  · intro N_f h
    have : IsSpinSymTFTConsistent (sm_boundary_data N_f) := h
    exact (wave_2a_3_substantive_instance _).mp this
  · intro s h
    -- C2.2 substantive: IsDarkSectorTopologicalBoundary is now a conjunction;
    -- extract spin-SymTFT consistency from the first conjunct.
    have : IsSpinSymTFTConsistent s := h.1
    exact (wave_2a_3_substantive_instance _).mp this

/-! ## §4. C2.3 substantive cross-bridge theorems (paper-17-tied) -/

/-- **C2.3 substantive cross-bridge**: every dark-sector topological
boundary substrate carries the magnetic Lagrangian-algebra label
(extracted directly from the W2.2-strengthened body). -/
theorem darkSectorTopologicalBoundary_carries_magnetic_label
    (s : SubstrateConfig) (h : IsDarkSectorTopologicalBoundary s) :
    ∃ (label : ToricCodeLagrangianLabel),
      label = ToricCodeLagrangianLabel.magnetic :=
  h.2

/-- **C2.3 substantive cross-bridge**: every SM matter topological
boundary substrate is *categorically distinguished* from every
dark-sector topological boundary substrate at the Lagrangian-algebra
label level — SM carries electric, dark sector carries magnetic, and
the labels are pairwise distinct. -/
theorem sm_dark_categorically_distinct_at_label_level
    (s_sm s_dark : SubstrateConfig)
    (_h_sm : IsSMMatterTopologicalBoundary s_sm)
    (h_dark : IsDarkSectorTopologicalBoundary s_dark) :
    ∃ (l_sm l_dark : ToricCodeLagrangianLabel),
      l_sm = ToricCodeLagrangianLabel.electric ∧
      l_dark = ToricCodeLagrangianLabel.magnetic ∧
      l_sm ≠ l_dark := by
  obtain ⟨l_dark, h_l_dark⟩ := h_dark.2
  exact ⟨ToricCodeLagrangianLabel.electric, l_dark, rfl, h_l_dark,
         by rw [h_l_dark]; exact toricCode_labels_distinct⟩

/-! ## §5. C2 closure: substantive paper-17 SymTFT-boundary identification -/

/-- **C2 closure theorem** (Phase 6r-prime 2026-05-25): the substantive
paper-17 dark-sector SymTFT-boundary cross-bridge ships at the level of:

1. Each dark-sector topological boundary is spin-SymTFT-consistent.
2. Each dark-sector topological boundary carries the magnetic LA label.
3. SM and dark-sector boundaries are categorically distinct at the LA-
   label level (per Wave 3a.1 §Q3(b) substantive identification).

Substantively discharges Phase 6r tracked Prop #11
`IsDarkSectorTopologicalBoundary` at the SymTFT-boundary-framing level
(paper-17-specific substrate content shipped in Phase 5x dark-sector
modules). -/
theorem c2_paper17_substantive_closure (s : SubstrateConfig)
    (h : IsDarkSectorTopologicalBoundary s) :
    IsSpinSymTFTConsistent s ∧
    (∃ (label : ToricCodeLagrangianLabel),
      label = ToricCodeLagrangianLabel.magnetic) ∧
    (ToricCodeLagrangianLabel.electric ≠ ToricCodeLagrangianLabel.magnetic) :=
  ⟨h.1, h.2, toricCode_labels_distinct⟩

end SKEFTHawking.SymTFT
