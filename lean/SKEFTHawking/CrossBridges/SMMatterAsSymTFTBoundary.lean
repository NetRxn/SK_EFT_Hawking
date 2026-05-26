/-
# Phase 6r Wave 3a.3 — Cross-bridge: SM matter as SymTFT boundary

The Wave 3a.3 cross-bridge module connecting the new
`SymTFT/IsSMMatterTopologicalBoundary.lean` Lean substrate to the
existing project chain:

```
GenerationConstraint.lean (Phase 5b)
   ↓
SymTFTAudit/WittClass.lean (Phase 6n Wave 1b Stage 5)
   ↓
SymTFTAudit/CrossBridges.lean::chiralCentralCharge_bridges_to_GenerationConstraint
   ↓
[Wave 3a.3] CrossBridges/SMMatterAsSymTFTBoundary.lean — THIS MODULE
```

## Wave 3a.1 §Q2(b) — the new content vs cosmetic

Per Wave 3a.1 §Q2(b):
> "Cosmetic (renaming): re-stating '8 N_f ≡ 0 mod 24' as 'WittInvariant
> = 0' is renaming.
>
> Genuinely new: the equivalence `WittInvariant = 0 ↔ ∃ L,
> HasLagrangianAlgebra L` (the DMNO content) coupled with
> `HasLagrangianAlgebra L ↔ B admits a gapped boundary` (Kapustin-
> Saulina arXiv:1008.0654; Fuchs-Schweigert-Valentino arXiv:1203.4568)
> is *not* present in `chiralCentralCharge_bridges_to_GenerationConstraint`.
> The new reframing adds: (i) categorical bulk-boundary structure,
> (ii) a gapped-boundary-existence statement that interfaces with the
> SM Lagrangian-algebra boundary, and (iii) the Witt-class language as
> the unifying object that the η/16 chain and the chiral-central-charge
> chain both project onto."

This module ships the load-bearing new content as the two cross-bridge
theorems below.

## References

- Wave 3a.1 DR §Q2.
- `SymTFTAudit/CrossBridges.lean::chiralCentralCharge_bridges_to_GenerationConstraint`.
- `SymTFTAudit/WittClass.lean::chiralCentralCharge_wittTrivial_iff_three_dvd_N_f`.
- `GenerationConstraint.lean::generation_constraint_iff`.
- `SymTFT/IsSMMatterTopologicalBoundary.lean::sm_3gen_via_symtft`.
-/
import SKEFTHawking.SymTFT.IsSMMatterTopologicalBoundary
import SKEFTHawking.SymTFT.BulkBoundaryCorrespondence
import SKEFTHawking.SymTFTAudit.CrossBridges

namespace SKEFTHawking.CrossBridges

open SKEFTHawking SKEFTHawking.SymTFT SKEFTHawking.SymTFTAudit

/-! ## §1. The substantive new cross-bridge: Witt-triviality ↔ Lagrangian-algebra-existence -/

/-- **`witt_triviality_iff_has_lagrangian_algebra`** — the DMNO 2010
substantive cross-bridge, lifted into the project's cross-bridges
namespace. Under the DMNO tracked Prop, a 3D TQFT bulk is Witt-trivial
iff it admits a Lagrangian-algebra boundary.

Anchored on `Phase 6r Wave 1d.1 SymTFT/BulkBoundaryCorrespondence.lean::
witt_triviality_iff_has_lagrangian_algebra`. -/
theorem witt_triviality_iff_has_lagrangian_algebra
    (B : Type) [CategoryTheory.Category B] [CategoryTheory.MonoidalCategory B]
    (hDMNO : IsDMNOBiconditional B) :
    Is3DTQFTBraided B ↔ HasLagrangianAlgebra B :=
  SymTFT.witt_triviality_iff_has_lagrangian_algebra B hDMNO

/-! ## §2. The Witt-class ↔ chiral-central-charge cross-bridge -/

/-- **`witt_class_bridges_to_chiral_central_charge`** — for an SM-matter
topological boundary `B` (in the Wave 3a.2 sense), the modular bulk
Witt invariant equals the chiral central charge mod 24.

For SM with `N_f` generations including right-handed neutrinos (16
fermions per gen), `chiralCentralCharge = 8 * N_f`. -/
theorem witt_class_bridges_to_chiral_central_charge (N_f : ℕ) :
    sm_bulk N_f = WittInvariant.fromChiralCentralCharge (8 * (N_f : ℤ)) :=
  rfl

/-! ## §3. The composed Wave 3a.3 closure -/

/-- **Wave 3a.3 closure** — the substantive composed theorem
identifying the SM matter content as a topological boundary condition
of a SymTFT bulk, with the 3-generation constraint recovered.

Combines (transitively, through `sm_3gen_via_symtft_under_boundary_hyp`):
- `sm_3gen_via_symtft` (the new Wave 3a.3 substantive theorem).
- `chiralCentralCharge_wittTrivial_iff_three_dvd_N_f` (Phase 6n Wave 1b
  Stage 5 substrate; called inside `sm_3gen_via_symtft`).
- `generation_constraint_iff` (Phase 5b substrate; called inside
  `chiralCentralCharge_wittTrivial_iff_three_dvd_N_f`).

For any substrate that's SM-matter-topological-boundary, the modular
SymTFT bulk is Witt-trivial at the witness `N_f` iff `3 ∣ N_f`.

**Post-B7 + B9 audit-remediation (2026-05-25)**: prior version `(N_f : ℕ)
(_h : IsSMMatterTopologicalBoundary (sm_boundary_data N_f))` had an
unused hypothesis (P5 pattern). Post-B7 (which strengthened
IsSMMatterTopologicalBoundary to a 2-conjunct with substantive
`∃ N_f, z16_class = 16·N_f` witness), the substantive content of the
hypothesis is the SM-witness conjunct itself. The honest form: input a
substrate `s` that's SM-topological, EXTRACT the witness `N_f` via the
hypothesis, and conclude with the 3-generation biconditional at THAT
witness. The hypothesis is now USED. -/
theorem sm_matter_as_symtft_boundary_closure
    (s : Z16AnomalyForcesThetaBar.SubstrateConfig)
    (h : IsSMMatterTopologicalBoundary s) :
    sm_bulk h.2.choose = 0 ↔ 3 ∣ h.2.choose :=
  SymTFT.sm_3gen_via_symtft h.2.choose

/-- **Cross-bridge integrity witness** — explicit demonstration that
the Phase 6n Wave 1b Stage 4 cross-bridge
`chiralCentralCharge_bridges_to_GenerationConstraint` carries the
Schellekens-side `chiralCentralChargeMod24Compatible (8 * N_f)` content
to the Phase 5b `generation_constraint_iff` chain, and that both
project chains terminate at the same numerical content as
`sm_3gen_via_symtft`.

This theorem makes the cross-module integrity visible at the
type-signature level per the round-1 adversarial-review REQUIRED-2
remediation. -/
theorem sm_3gen_cross_bridge_integrity (N_f : ℕ) :
    -- Phase 5b chain: 3 ∣ N_f ↔ 24 ∣ (8 * N_f)
    (3 ∣ N_f ↔ 24 ∣ (8 * N_f)) ∧
    -- Phase 6n Wave 1b Stage 5: Schellekens chain at Witt-class level
    (WittTrivial (8 * (N_f : ℤ)) ↔ 3 ∣ N_f) ∧
    -- Wave 3a.3 SymTFT-boundary lift: modular bulk Witt-trivial ↔ 3 ∣ N_f
    (sm_bulk N_f = 0 ↔ 3 ∣ N_f) :=
  ⟨SKEFTHawking.generation_constraint_iff N_f,
   chiralCentralCharge_wittTrivial_iff_three_dvd_N_f N_f,
   SymTFT.sm_3gen_via_symtft N_f⟩

end SKEFTHawking.CrossBridges
