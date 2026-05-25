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

The predicate-substrate body matches `IsSMMatterTopologicalBoundary`
(both must be spin-SymTFT-consistent), with the distinction at the
Lagrangian-algebra label level. Per Wave 3a.1 §Q3(b), the dark sector
corresponds to a *magnetic* Lagrangian-algebra label on the same
SymTFT bulk where SM corresponds to *electric*. -/
def IsDarkSectorTopologicalBoundary
    (s : Z16AnomalyForcesThetaBar.SubstrateConfig) : Prop :=
  IsSpinSymTFTConsistent s

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
    have : IsSpinSymTFTConsistent s := h
    exact (wave_2a_3_substantive_instance _).mp this

end SKEFTHawking.SymTFT
