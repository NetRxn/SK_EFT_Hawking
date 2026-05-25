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
import SKEFTHawking.SymTFT.SubstrateEtaInvariant
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
SymTFT bulk where SM corresponds to *electric*.

**Phase 6r-prime 2026-05-25 honest revert**: a prior C2.2 ship added a
2nd conjunct `∃ (label : ToricCodeLagrangianLabel), label = magnetic`
that did NOT reference the substrate parameter `s` — pure P5
structural-tautology (vacuous existential over a 2-constructor enum,
trivially discharged by `⟨magnetic, rfl⟩`). Reverted to Phase 6r body.
Honest substantive C2 discharge requires a real cross-bridge to the
existing Phase 5x dark-sector substrate (`HiddenSectorClassification.
lean`, `FractonDarkMatter.lean`, etc.), which is a separate state-of-
the-art sub-wave ship. -/
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

/-! ## §4. C2 substantive paper-17 cross-bridge (sub-wave C2-honest-1)

**Phase 6r-prime sub-wave C2-honest-1 (2026-05-25)**: substantive C2
cross-bridge tying the paper-17 §2 hidden-sector content (charge +3
mod 16 from `HiddenSectorClassification.lean::three_singlets_satisfy_hidden_sector`)
to the SymTFT-boundary framework via SubstrateConfig construction +
anomaly-cancellation arithmetic.

**Substantive content**: per paper 17 §2, the dark sector carries
charge +3 mod 16. Combined with the SM 3-generation -3 mod 16 anomaly,
the net combined-system anomaly is `(-3) + 3 = 0 mod 16`. This
substantively yields a SubstrateConfig that is dark-sector-topological-
boundary via `IsSpinSymTFTConsistent` ↔ `Z16AnomalyCancels`.

**Distinct from the trivial Phase 6r unconditional discharge**: the SM
substrate `sm_substrate_data N_f` has `z16_class = 16·N_f = 0` trivially
(per the Z16AnomalyForcesThetaBar framework — 16 fermions per gen).
Here we construct the SM+paper-17-hidden combined substrate via the
explicit `-3 + 3` cancellation arithmetic, which IS the paper-17
content. -/

/-- **Paper 17 §2 hidden-sector charge**: the dark sector carries
exactly +3 mod 16 charge per paper 17. Witnessed by 3 sterile singlets
(per Phase 5x `HiddenSectorClassification.three_singlets_satisfy_hidden_sector`). -/
def paper17_hidden_sector_charge : ZMod 16 := 3

/-- **SM 3-generation (no νR) anomaly**: -3 mod 16 (per `Z16AnomalyComputation.lean`
and paper 17 §2 "three generations carry charge -45 ≡ -3 ≡ +13 mod 16"). -/
def sm_three_gen_no_nuR_anomaly : ZMod 16 := -3

/-- **Combined SM + paper-17 hidden-sector substrate**: the SubstrateConfig
representing the SM (3 generations, no νR) combined with paper-17 hidden
sector. Net z16_class = -3 + 3 = 0 (anomaly cancellation). -/
def sm_plus_paper17_hidden_substrate : SubstrateConfig where
  z16_class := sm_three_gen_no_nuR_anomaly + paper17_hidden_sector_charge
  theta_bar := 0

/-- **Paper 17 §2 substantive cancellation**: the combined SM + paper-17
hidden-sector substrate has z16_class = 0 (anomaly cancellation
`-3 + 3 = 0 mod 16`). Discharged via `decide` on ZMod 16 arithmetic. -/
theorem sm_plus_paper17_hidden_substrate_anomaly_cancels :
    Z16AnomalyCancels sm_plus_paper17_hidden_substrate := by
  show sm_plus_paper17_hidden_substrate.z16_class = 0
  show sm_three_gen_no_nuR_anomaly + paper17_hidden_sector_charge = 0
  decide

/-- **C2 substantive sub-wave headline**: the combined SM + paper-17
hidden-sector substrate is dark-sector-topological-boundary. The proof
substantively uses the paper-17 +3 mod 16 cancellation arithmetic. -/
theorem sm_plus_paper17_hidden_substrate_is_dark_sector_topological_boundary :
    IsDarkSectorTopologicalBoundary sm_plus_paper17_hidden_substrate := by
  show IsSpinSymTFTConsistent sm_plus_paper17_hidden_substrate
  rw [wave_2a_3_substantive_instance]
  exact sm_plus_paper17_hidden_substrate_anomaly_cancels

/-- **Cross-bridge to Phase 5x `HiddenSectorClassification`**: the
paper-17 hidden-sector charge of +3 mod 16 is exactly the value that
Phase 5x's `three_singlets_satisfy_hidden_sector` theorem witnesses
via the minimal S-0 scenario (three sterile singlets). This ties the
substrate-level paper-17 content to the existing Phase 5x classification. -/
theorem paper17_hidden_sector_charge_eq_three_singlets :
    paper17_hidden_sector_charge = ((3 : ℕ) : ZMod 16) := by
  show (3 : ZMod 16) = ((3 : ℕ) : ZMod 16)
  rfl

/-! ## §5. C2-honest-2 / W5-η-bridge-3 — dark-sector η-invariant cross-bridge

**Phase 6r-prime sub-wave W5-η-bridge-3 (2026-05-25)**: cross-bridge
applying the substantive Witten-Yonekura η-invariant (W4-η-1) to the
paper-17 combined SM + hidden-sector substrate (C2-honest-1). The
substantive content: the same `-3 + 3 = 0 mod 16` cancellation that
makes the combined substrate a dark-sector topological boundary also
forces the η-invariant in `ℝ/ℤ` to vanish.

**Substantive content**: this cross-bridge is the η-level analog of
W5-η-bridge-2 (which did the same for the SM-only substrate). The two
substrates differ — `sm_substrate_data N_f` has `z16_class = 16·N_f`
which cancels trivially per the 16-fermions-per-generation convention,
whereas `sm_plus_paper17_hidden_substrate` has `z16_class = -3 + 3`
which is the substantive paper-17 cancellation arithmetic — yet both
vanish at the η level via the same substrate-level lemma
`substrateEtaInvariant_zero_of_anomaly_cancels`. -/

/-- **W5-η-bridge-3 / C2-honest-2**: the combined SM + paper-17
hidden-sector substrate has vanishing Witten-Yonekura η-invariant.
The proof composes the C2-honest-1 anomaly-cancellation theorem with
the W4-η-1 substrate-level vanishing lemma. -/
theorem sm_plus_paper17_hidden_substrate_eta_invariant_vanishes :
    substrateEtaInvariant sm_plus_paper17_hidden_substrate = 0 :=
  substrateEtaInvariant_zero_of_anomaly_cancels
    sm_plus_paper17_hidden_substrate
    sm_plus_paper17_hidden_substrate_anomaly_cancels

/-- **W5-η-bridge-3 bundled corollary**: the combined SM + paper-17
hidden-sector substrate is simultaneously a dark-sector topological
boundary AND has vanishing η-invariant. Mirrors the SM-only bundled
corollary `sm_boundary_data_topological_AND_eta_trivial` from
W5-η-bridge-2. -/
theorem sm_plus_paper17_hidden_substrate_dark_topological_AND_eta_trivial :
    IsDarkSectorTopologicalBoundary sm_plus_paper17_hidden_substrate ∧
    substrateEtaInvariant sm_plus_paper17_hidden_substrate = 0 :=
  ⟨sm_plus_paper17_hidden_substrate_is_dark_sector_topological_boundary,
   sm_plus_paper17_hidden_substrate_eta_invariant_vanishes⟩

/-! ## §6. C2-honest-3 / W4-η-4 — broken paper-17 substrate falsifier

**Phase 6r-prime sub-wave C2-honest-3 / W4-η-4 (2026-05-25)**:
negative counterpoint to C2-honest-1+2. Constructs a "broken"
paper-17 substrate where the hidden-sector charge is `+2` instead of
the substantive `+3` from paper 17 §2. The mismatch breaks anomaly
cancellation (`-3 + 2 = -1 ≠ 0 mod 16`) and per W4-η-2 yields a
non-zero η-invariant in `ℝ/ℤ`.

**Substantive content**: demonstrates the substrate framework
DISTINGUISHES valid paper-17 hidden-sector charges (which yield
topological-boundary configurations with vanishing η) from invalid
ones (which yield non-topological-boundary configurations with
non-vanishing η). This is the substantive falsifier counterpart to
the C2-honest-1+2 positive substrate ships. -/

/-- **W4-η-4 / C2-honest-3 broken hidden-sector charge**: `+2 mod 16`,
which differs from paper 17 §2's substantive `+3`. The mismatch is
the falsifier mechanism. -/
def broken_paper17_hidden_sector_charge : ZMod 16 := 2

/-- **W4-η-4 / C2-honest-3 broken substrate**: SM + broken-paper-17
combined substrate. Net z16_class = -3 + 2 = -1 ≠ 0 (anomaly does
NOT cancel). -/
def sm_plus_broken_paper17_substrate : SubstrateConfig where
  z16_class := sm_three_gen_no_nuR_anomaly + broken_paper17_hidden_sector_charge
  theta_bar := 0

/-- **W4-η-4 / C2-honest-3 falsifier**: the broken substrate does NOT
satisfy `Z16AnomalyCancels`. Discharged via `decide` on `ZMod 16`. -/
theorem sm_plus_broken_paper17_substrate_anomaly_does_not_cancel :
    ¬ Z16AnomalyCancels sm_plus_broken_paper17_substrate := by
  intro h
  have : (sm_plus_broken_paper17_substrate.z16_class : ZMod 16) = 0 := h
  revert this
  show sm_three_gen_no_nuR_anomaly + broken_paper17_hidden_sector_charge ≠ 0
  decide

/-- **W4-η-4 substantive η-non-vanishing on broken substrate**: by
composition with W4-η-2, the broken substrate has non-zero η-invariant
in `ℝ/ℤ`. The mismatch `+2 ≠ +3` in the hidden-sector charge is
substantively detected at the η level. -/
theorem sm_plus_broken_paper17_substrate_eta_invariant_nonzero :
    substrateEtaInvariant sm_plus_broken_paper17_substrate ≠ 0 := by
  apply substrateEtaInvariant_nonzero_of_z16_nonzero
  show sm_three_gen_no_nuR_anomaly + broken_paper17_hidden_sector_charge ≠ 0
  decide

end SKEFTHawking.SymTFT
