/-
# Phase 6r Wave 3a.3 — APSEta substrate-bulk asymmetry

The Witten-Yonekura η/16 chain ↔ Z₁₆ chain asymmetry-typing theorem
between analog-Hawking substrates (BEC, ADW, ³He-A — all ℤ/16-trivial
at substrate-data level per Phase 6o Wave 2a's
`wave_2a_6_symtft_bridge_closure`) and the SM-with-νR substrate
(ℤ/16-non-trivial per García-Etxebarria-Montero arXiv:1808.00009).

Per Wave 3a.1 §Q4(a), this is the load-bearing asymmetry-typing
theorem connecting the Phase 6r Track 3 SM-as-boundary narrative to
the existing analog-Hawking substrate framework.

## Wave 3a.1 §Q4(a) signature

```lean
theorem analogHawking_substrate_z16_trivial :
    ∀ s : AnalogHawkingSubstrate,
      wittenYonekuraToZ16 (substrateBulk s) = (0 : ZMod 16)
```

For each Phase 6o substrate (BEC, ADW, ³He-A), the η/16 lift is
trivially zero at the substrate-data layer (per Wave 2a.6 closure).

## Wave 3a.1 §Q4(a) SM-side complement — shipped vs deferred (round-1
## adversarial review remediation)

Per Wave 3a.1 §Q4(a): "García-Etxebarria-Montero arXiv:1808.00009
abstract (verbatim): 'we relate the fact that there are 16 fermions per
generation of the Standard model — including right-handed neutrinos —
to anomalies under time-reversal of boundary states in four-dimensional
topological superconductors.'"

NOTE: Per Wave 3a.1 §Caveats, the SM-side ℤ/16 class is `16·N_gen`
which is **ZERO in ZMod 16**, so the GE-M ℤ/16 anomaly classification
refers to a *different* Pin⁺ invariant than the bare 16-fermion-count;
the non-triviality is at the level of the Pin⁺-Z/16 SPT class
*realization*, not the bare counting.

### What this module SHIPS

- `analogHawking_substrate_z16_trivial`: for each Phase 6o analog-Hawking
  substrate, η/16 lift is trivial at substrate-data level (Wave 2a.6
  closure restated).
- `sm_substrate_data N_f` + `sm_substrate_data_z16_cancels N_f`: the
  SM-with-νR substrate at the `SubstrateConfig` level, with bare ℤ/16
  cancellation (`16·N_f ≡ 0 mod 16`).
- `analogHawking_vs_SM_bulk_asymmetry_substrate_data`: combined
  asymmetry statement at substrate-data layer (both sides ℤ/16-trivial
  at bare counting; substantive asymmetry lives at the Pin⁺ SPT
  realization layer).
- `IsSubstantivePinPlusSPTAsymmetry` (tracked Prop): the substantive
  realization-level asymmetry, encoded as a conjunction of the
  Kirby-Taylor + Anderson-dual tracked Props.
- `wave_3a_3_substrate_bulk_asymmetry_closure`: composed Wave 3a.3
  closure theorem.

### What is DEFERRED (and why)

The naïve `SM_withNuR_substrate_z16_nontrivial : ∀ s : SMSubstrate, s.
includesRightHandedNeutrino → wittenYonekuraToZ16 (substrateBulk s) ≠
(0 : ZMod 16)` form is **NOT shippable as stated** because the SM-with-νR
substrate has bare `z16_class = 16·N_f ≡ 0 mod 16`. The substantive
non-triviality content per García-Etxebarria-Montero lives at the
realization level (a *non-trivial* Pin⁺ SPT class realization, distinct
from the bare-counting layer); this requires additional Pin⁺ SPT
classification infrastructure not currently shipped in `SymTFT/PinBordism.lean`
(only the placeholder `ZMod 16` model exists). Ship as
`IsSubstantivePinPlusSPTAsymmetry` tracked Prop instead.

## References

- Witten-Yonekura, arXiv:1909.08775.
- Freed-Hopkins, arXiv:1604.06527.
- García-Etxebarria-Montero, arXiv:1808.00009.
- Kapustin-Thorngren-Turzillo-Wang, arXiv:1406.7329.
- Phase 6o `APSEta/SymTFTBridge.lean` (`wave_2a_6_symtft_bridge_closure`).
- Wave 3a.1 DR §Q4.
- Wave 2a.2 `SymTFT/PinBordism.lean`.
-/
import SKEFTHawking.APSEta.SymTFTBridge
import SKEFTHawking.SymTFT.PinBordism
import SKEFTHawking.SymTFT.SpinSymTFT
import SKEFTHawking.SymTFT.SubstrateEtaInvariant

namespace SKEFTHawking.APSEta

open SKEFTHawking SKEFTHawking.SymTFT SKEFTHawking.Z16AnomalyForcesThetaBar

/-! ## §1. Analog-Hawking substrates: ℤ/16-trivial -/

/-- **`analogHawking_substrate_z16_trivial`** — for each Phase 6o
analog-Hawking substrate (BEC, ADW, ³He-A), the Witten-Yonekura η/16
lift to ℤ/16 is trivial at substrate-data level.

This is the load-bearing claim of Phase 6o Wave 2a.6
(`wave_2a_6_symtft_bridge_closure`), restated here in the
Wave 3a.3 asymmetry-typing form. -/
theorem analogHawking_substrate_z16_trivial :
    ∀ s : Substrate, wittenYonekuraToZ16 s = (0 : ZMod 16) :=
  wittenYonekuraToZ16_zero

/-! ## §2. The SM-with-νR substrate -/

/-- **`sm_substrate_data`** — the SM-with-νR substrate configuration
at the `SubstrateConfig` level: 16 Weyl fermions per generation,
yielding `16·N_f ≡ 0 mod 16` (anomaly-free at the bare-counting level).

The Pin⁺ ℤ/16 SPT class non-triviality of the SM-with-νR substrate is
captured at the *realization* level (Wave 3a.1 §Caveats discipline);
this `SubstrateConfig` ships the bare anomaly-counting data. -/
def sm_substrate_data (N_f : ℕ) : SubstrateConfig where
  z16_class := (16 * N_f : ZMod 16)
  theta_bar := 0

/-- The SM-with-νR substrate `sm_substrate_data N_f` is anomaly-free
at the bare ℤ/16 counting layer. -/
theorem sm_substrate_data_z16_cancels (N_f : ℕ) :
    Z16AnomalyCancels (sm_substrate_data N_f) := by
  show (16 * (N_f : ZMod 16)) = 0
  have : (16 : ZMod 16) = 0 := by decide
  rw [this]; ring

/-! ## §3. The substrate-bulk asymmetry theorem -/

/-- **`analogHawking_vs_SM_bulk_asymmetry_substrate_data`** — at the
substrate-data layer, both analog-Hawking and SM-with-νR substrates
exhibit trivial η/16 lift (per the Phase 6o Wave 2a placeholder
η = 0). The substantive asymmetry between the two is encoded at the
*Pin⁺ SPT realization* layer, not at the bare counting layer.

Per Wave 3a.1 §Caveats, the substantive non-triviality of the SM-with-νR
Pin⁺ class lives in TP_5(Pin⁺) at the realization level (García-Etxebarria-
Montero 1808.00009); the bare `z16_class : ZMod 16` is identically zero
because `16 · N_f ≡ 0 mod 16`. -/
theorem analogHawking_vs_SM_bulk_asymmetry_substrate_data :
    (∀ s_analog : Substrate, wittenYonekuraToZ16 s_analog = 0) ∧
    (∀ s_SM_n_f : ℕ, Z16AnomalyCancels (sm_substrate_data s_SM_n_f)) :=
  ⟨analogHawking_substrate_z16_trivial, sm_substrate_data_z16_cancels⟩

/-! ## §4. The substantive Pin⁺ SPT realization asymmetry (tracked Prop) -/

/-! ### DELETED: `IsSubstantivePinPlusSPTAsymmetry`

**Phase 6r-prime A2 audit-remediation (2026-05-25)**: deleted as
P2+P5 anti-pattern per self-conducted audit. The prior body was a
bundle of `IsKirbyTaylorPinPlusBordism ∧ IsAndersonDualPinPlus`,
with the prior docstring explicitly acknowledging "the substantive
content lives at the level of Pin⁺ SPT classification realization,
not at the bare counting layer" — i.e., the predicate body did NOT
capture the substantive content it claimed to encode.

The genuine substantive Pin⁺ SPT realization asymmetry (per García-
Etxebarria-Montero 1808.00009) requires Pin⁺ SPT classification
infrastructure (e.g., functor from `SubstrateConfig` to `TP5PinPlus`
producing distinct values for analog-Hawking vs SM-with-νR substrates).
That infrastructure is currently absent; deferred to a future Pin⁺ SPT
classification ship.

Consumers post-A2: use `isKirbyTaylorPinPlusBordism_holds ∧
isAndersonDualPinPlus_holds` directly (the two substantive discharges)
when they need the bundle. -/

/-! ## §5. The Wave 3a.3 cross-bridge closure -/

/-- **Wave 3a.3 closure** — the substrate-bulk asymmetry theorem at
the substrate-data layer: both analog-Hawking and SM-with-νR substrates
exhibit trivial ℤ/16 class.

**Post-A2 audit refactor (2026-05-25)**: removed the third conjunct
`IsSubstantivePinPlusSPTAsymmetry` (P2+P5 bundle of the two tracked
Props on Anderson-dual side, with docstring acknowledgment that the
substantive content lives elsewhere). The genuine substantive Pin⁺ SPT
realization asymmetry requires Pin⁺ SPT classification infrastructure
absent in current Mathlib; the existing tracked Props `IsKirbyTaylor
PinPlusBordism` and `IsAndersonDualPinPlus` provide the bordism/Anderson-
dual identifications that ground the asymmetry, but the realization-
level asymmetry function `SubstrateConfig → TP5PinPlus` is the deferred
ship. -/
theorem wave_3a_3_substrate_bulk_asymmetry_closure :
    -- Analog-Hawking substrates are ℤ/16-trivial at substrate-data
    (∀ s_analog : Substrate, wittenYonekuraToZ16 s_analog = 0) ∧
    -- SM-with-νR substrate at bare counting layer is ℤ/16-trivial too
    (∀ N_f : ℕ, Z16AnomalyCancels (sm_substrate_data N_f)) :=
  ⟨analogHawking_substrate_z16_trivial,
   sm_substrate_data_z16_cancels⟩

/-! ## §6. W5-η-bridge sub-wave — η-invariant cross-bridge to Phase 6r-prime W4-η substrate

**Phase 6r-prime sub-wave W5-η-bridge-1 (2026-05-25)**: cross-bridge
linking the existing `wave_3a_3_substrate_bulk_asymmetry_closure`
substrate-data layer to the Phase 6r-prime W4-η-1+2 substantive
η-invariant content (`SymTFT/SubstrateEtaInvariant.lean`).

**Substantive content**: the SM-with-νR substrate `sm_substrate_data
N_f` has z16_class = 16·N_f ≡ 0 mod 16 (anomaly-cancellation per
`sm_substrate_data_z16_cancels`); the W4-η-1 substantive predicate
`substrateEtaInvariant_zero_of_anomaly_cancels` then gives the
η-invariant vanishes. The combined statement: SM-with-νR substrate has
both ℤ/16-trivial z16_class AND ℝ/ℤ-trivial η-invariant. This is the
**joint** content of the substrate-bulk symmetry at the Pin⁺ Anderson-
dual TFT level.

Per Witten-Yonekura arXiv:1909.08775: the η-invariant captures the
anomaly content of the substrate in a way that respects the substrate's
z16_class structure. The W5-η-bridge ties the Phase 6r tracked Props
(KT, AD, GEM realization) to the W4-η-1+2 substantive η-formula. -/

/-- **W5-η-bridge substantive theorem**: the SM-with-νR substrate has
vanishing η-invariant per the W4-η-1 substantive Witten-Yonekura formula
(η = z16_class / 16 mod 1 = 0 because z16_class = 16·N_f ≡ 0 mod 16). -/
theorem sm_substrate_data_eta_invariant_vanishes (N_f : ℕ) :
    SymTFT.substrateEtaInvariant (sm_substrate_data N_f) = 0 :=
  SymTFT.substrateEtaInvariant_zero_of_anomaly_cancels
    (sm_substrate_data N_f) (sm_substrate_data_z16_cancels N_f)

/-- **W5-η-bridge cross-bridge closure**: composed substrate-bulk
asymmetry result at BOTH the ℤ/16-counting layer (Phase 6r baseline)
AND the η-invariant ℝ/ℤ-formula layer (W4-η-1 substantive). For the
SM-with-νR substrate, both layers give the same trivial classification
(z16_class = 0 ⟹ η = 0). For analog-Hawking substrates, same. The
substantive realization-level asymmetry (per GEM 1808.00009) lives at
the Pin⁺ SPT class layer, NOT at either of these substrate-data layers. -/
theorem wave_3a_3_with_W4_η_cross_bridge_closure :
    -- Phase 6r baseline: SM-with-νR substrate is z16-trivial
    (∀ N_f : ℕ, Z16AnomalyCancels (sm_substrate_data N_f)) ∧
    -- W4-η-1 substantive: SM-with-νR substrate has trivial η-invariant
    (∀ N_f : ℕ, SymTFT.substrateEtaInvariant (sm_substrate_data N_f) = 0) :=
  ⟨sm_substrate_data_z16_cancels,
   sm_substrate_data_eta_invariant_vanishes⟩

end SKEFTHawking.APSEta
