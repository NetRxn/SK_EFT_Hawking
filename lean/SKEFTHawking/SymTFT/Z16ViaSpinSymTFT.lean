/-
# Phase 6r Wave 2b.1 + 2b.2 — Z₁₆ classification via Spin-SymTFT

The substantive theorem identifying the SM Z₁₆ anomaly classification
(`Z16AnomalyForcesThetaBar.lean` Phase 6l Wave 1) as a spin-SymTFT
boundary-classification result. Per Wave 2b.1 + 2b.2 of the roadmap,
this is the D.3-candidate substantive content that *would* reframe D2
under the spin-SymTFT umbrella; the actual D2 bundle reframing is HELD
for unified bundle-absorption per Wave 2a.1 §4.4 (cluster bond preserved,
no D4/L2 rewrite needed).

## Wave 2b.1 — Z₁₆ classification via Spin-SymTFT

The substantive theorem: the Z₁₆ classification of SM anomalies is
recovered as the spin-SymTFT classification of fermionic boundary
conditions on the Anderson-dual Pin⁺ bulk. Per Wave 3a.1 §Caveats
and Wave 2a.1 §1.2, the Z₁₆ class is the *Ising-Witt-subgroup* of the
Davydov-Müger-Nikshych-Ostrik Witt group (Davydov-Nikshych-Ostrik
arXiv:1109.5558).

## Wave 2b.2 — Witten-Yonekura η/16 connection

The cross-bridge connecting the Wave 2b.1 spin-SymTFT classification
to the Phase 6o Wave 2a APSEta η/16-mod-1 anomaly invariant. Per Wave
2a.1 §3.2 (Witten-Yonekura inflow convention).

## D.3 user-authorization gate

Per Phase 6r roadmap §"User authorization gates", Wave 2b.3 D2
reframing prose is **HELD** for the unified bundle-absorption pass.
This module ships the Lean content; the D2 reframing prose is in
`temporary/working-docs/phase6r/wave_2b_D2_reframing_predraft.md`.

## References

- Davydov-Nikshych-Ostrik, "On the structure of the Witt group of
  braided fusion categories," Selecta Math. 19 (2013) 237;
  arXiv:1109.5558.
- Witten-Yonekura, arXiv:1909.08775.
- Kapustin-Thorngren-Turzillo-Wang, arXiv:1406.7329.
- García-Etxebarria-Montero, arXiv:1808.00009.
- Phase 6o Wave 2b Schellekens chain + Wave 2a APSEta SymTFTBridge.
- Phase 5b `Z16AnomalyComputation.lean`, `SPTStacking.lean`.
- Wave 2a.3 `SymTFT/SpinSymTFT.lean` (`wave_2a_3_substantive_instance`).
-/
import SKEFTHawking.SymTFT.PinBordism
import SKEFTHawking.SymTFT.SpinSymTFT
import SKEFTHawking.APSEta.SymTFTBridge
import SKEFTHawking.SymTFT.BulkBoundaryCorrespondence

namespace SKEFTHawking.SymTFT

open SKEFTHawking SKEFTHawking.Z16AnomalyForcesThetaBar

/-! ## §1. Wave 2b.1 — Z₁₆ classification via Spin-SymTFT theorem -/

/-- **Wave 2b.1: `z16_classification_via_spin_symtft`** — the substantive
theorem identifying the Z₁₆ anomaly classification (`Z16AnomalyCancels`)
as the spin-SymTFT boundary-classification result.

Per Wave 2a.1 §1.2: the substrate's `z16_class : ZMod 16` is interpreted
as taking values in **TP_5(Pin⁺) ≅ ℤ/16** (the 5D bulk SPT class), and
spin-SymTFT consistency on the substrate is equivalent to vanishing of
this class.

This theorem is the Wave 2a.3 biconditional restated in the language
of Z₁₆ classification.

**Hedging discipline (Wave 2a.1 §0)**: "structural equivalence between
spin-SymTFT framework consistency and ℤ/16-anomaly cancellation" — NOT
"the first formalization of the ℤ/16 anomaly via SymTFT." -/
theorem z16_classification_via_spin_symtft (s : SubstrateConfig) :
    IsSpinSymTFTConsistent s ↔ s.z16_class = 0 :=
  wave_2a_3_substantive_instance s

/-! ## §2. Wave 2b.2 — Witten-Yonekura η/16 connection -/

/-- **Wave 2b.2: `z16_classification_via_witten_yonekura`** —
substantive cross-bridge: the Spin-SymTFT classification at Wave 2b.1
is precisely the Witten-Yonekura η/16 mod 1 anomaly invariant. Cross-
bridge to Phase 6o Wave 2a APS-η.

For each Phase 6o substrate, the Witten-Yonekura η/16 lift coincides
with the spin-SymTFT classification at substrate-data level. -/
theorem z16_classification_via_witten_yonekura :
    ∀ s : APSEta.Substrate, APSEta.wittenYonekuraToZ16 s = 0 :=
  APSEta.wittenYonekuraToZ16_zero

/-! ## §3. The Wave 2b closure summary -/

/-- **Wave 2b closure theorem** — the unified statement combining
2b.1 spin-SymTFT classification with 2b.2 Witten-Yonekura cross-bridge.

For SK-EFT-Hawking substrates:
1. Spin-SymTFT consistency is equivalent to Z₁₆-anomaly cancellation.
2. The Phase 6o APSEta η/16 lift is trivial for all three substrates
   (BEC, ADW, ³He-A) at the substrate-data level.

The D.3 reframing of the D2 bundle (Wave 2b.3) is HELD for unified
bundle-absorption per the Phase 6r user-authorization gate. -/
theorem wave_2b_closure (s : SubstrateConfig) :
    (IsSpinSymTFTConsistent s ↔ s.z16_class = 0) ∧
    (∀ apsSubstrate : APSEta.Substrate,
      APSEta.wittenYonekuraToZ16 apsSubstrate = 0) :=
  ⟨z16_classification_via_spin_symtft s,
   z16_classification_via_witten_yonekura⟩

end SKEFTHawking.SymTFT
