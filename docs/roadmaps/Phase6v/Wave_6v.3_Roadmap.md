# Wave 6v.3 — DKM F3 polariton occupancy bound (Phase 6q follow-on)

## Current scientific status — 2026-10-17

**Physical platform placement: OPEN BUILD.** The dated ship below records the photon-energy/count implementation, conditional growth implication and normalized MIR witnesses. It does not derive an intracavity per-mode hard occupation bound from incident mean pulse energy, an actual Hamiltonian/open-generator commutator bound, physical transport parameters or an exclusive platform classification. The original physical-resolution goal remains owed; the inclusive bimodal OR is not an exclusive physical partition.

Next substantive successor: construct one source-qualified pumped-mode model with explicit state, coupling, loss and occupation-support/tail estimate, then derive its growth bound and physical transport map. Separately construct the actual BEC Hamiltonian/observable growth sequence, rather than prescribe factorial growth. Link the existing OPEN finding `review:2026-08-15-e1-stage10-redraft:E1:2.3` and Phase6q Wave2b.4/B.3; do not duplicate the same physical work as paper-local prose tickets. Independent physics/operator-bound review must check the nonempty carrier, units, domains, invariant cutoff or controlled leakage, and counterexamples before native admission. Current N D5's conditional disclosure is real delivered source correction, not this BUILD's completion.

**Scientific construction owner:** Physics Publication Remediation, explicitly accepted in the primary publication-remediation notebook r40 (2026-10-17). This is current author acceptance, not a historic assignment or a native lease. Completion requires the actual construction, independent scientific review and the existing recorded closure; ROOT retains shared-primary/native admission, integration and protected Git/main authority. No target reduction or deferral is granted.


**Bundle targets:** D5 §"substrate constraints by platform" + E1 §"polariton platform regime structure" (additive scope paragraphs).

**Historical delivery status:** ✅ SHIPPED 2026-05-26. **Current physical construction: OPEN BUILD**, as specified above.

**Wave goal.** Determine the physical polariton/BEC operator-growth and transport regime required for the DKM uniqueness or sharpened-NO-GO conclusion. `PlatformBimodalOutcome` is an inclusive disjunction. Existing normalized MIR witnesses and the prescribed BEC growth sequence do not classify physical platforms exclusively. The required pump/state-to-growth and actual BEC Hamiltonian-to-growth constructions remain OPEN BUILD.

## Physical input — incident pulse photon count

Using the supplied Wang et al. 2026 switching-pulse energy and photon energy, the incident photon count is

```
n_per_pulse = E_pulse / (ℏω)
            = (4 × 10⁻¹⁵ J) / (1.736 eV × 1.602176634×10⁻¹⁹ J/eV)
            ≈ 1.44 × 10⁴ incident photons per pulse.
```

Incident count alone supplies no per-mode intracavity support, occupation tail or commutator bound. Construct the state, coupling, drive/loss/reservoir evolution and observation interval first, then derive the actual growth constants in the relevant norm/domain. A finite-mean bosonic state can have unbounded occupation support. The existing `IsBoundedByPolaritonPumpScale` predicate assumes the full growth bound; the pump-threshold predicate does not derive it. The numerical 10⁶ proxy is not an established physical F3 boundary. The Phase6q physical question remains OPEN BUILD.

## Key parameters (LLM-verified against Wang et al. 2026 / Falque 2025)

| Symbol | Value | Unit | Source | Use |
|---|---:|---|---|---|
| ℏω_cav (Penn resonance energy) | 1.736 | eV | Wang et al. 2026 | Photon count derivation. |
| E_pulse (Penn switching threshold) | 4 | fJ | Wang et al. 2026 | Incident pulse-energy input; cavity occupation requires coupling/state dynamics. |
| n_per_pulse | ≈ 1.44 × 10⁴ | incident photons/pulse | supplied-energy conversion | Not a per-mode occupation-support bound. |
| τ_LP (Penn polariton lifetime) | ≈ 366 | fs | Wang et al. 2026 (= ℏ/γ_LP) | Per-mode steady-state setting. |
| ℏω_LP (Paris-LKB polariton energy) | ≈ 1.485 | eV | Falque 2025 (working point) | Cross-check on Paris-LKB. |
| n_threshold (adopted proxy) | 10⁶ | nominal occupation | DR Wave 2a.1 §1 BEC row | Physical F3 boundary unestablished; do not infer a platform branch. |

## Dated implementation record (2026-05-26)

The table records the historical source, tests and manuscript delivery, including claims subsequently corrected. Its SHIPPED marks do not certify the current physical BUILD, a fresh kernel/runtime run or publication readiness. Current acceptance must use the actual source and independent review.

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap doc (this file). | ✅ SHIPPED |
| 2 | Added Python canonical formula `polariton_mode_occupation_per_pulse(pulse_energy_J, photon_energy_eV)` to `src/core/formulas.py` with Lean reference `polariton_dkm_f3_holds_at_pump_below_threshold`. | ✅ SHIPPED |
| 3a | (a) New Python module `src/dkm_polariton/` (`__init__.py` + `polariton_occupation_bound.py`) — wraps the canonical formula and ships `penn_tmd_occupation_at_switching_threshold()` (= 1.438×10⁴) + `paris_lkb_occupation_at_typical_pump()` (= 3.36×10⁻²) + `is_below_dkm_f3_threshold(n, threshold=10⁶)`. (b) New Lean module `lean/SKEFTHawking/DKMBootstrap/PolaritonF3Bound.lean` (~240 LoC kernel-only) — definitions `polaritonOperatorGrowthScale`, `IsBoundedByPolaritonPumpScale`, `IsPolaritonPumpBelowThreshold`; theorems `polariton_dkm_f3_holds_at_pump_below_threshold` (contrapositive of `sharpened_no_go_super_factorial`, ~10 LoC), `horizon_transport_uniqueness_polariton_witness_one_half`, `polariton_inherits_graphene_uniqueness_result` (LEFT branch of bimodal outcome), `polariton_mir_witness_eq_graphene_mir_witness` (substrate parity). Module imported in `lean/SKEFTHawking.lean`. | ✅ SHIPPED |
| 3b | None — 3a closed via direct constructive proofs. | SKIP |
| 4 | (not needed) — Aristotle fallback not invoked. | SKIP |
| 5 | `lake env lean SKEFTHawking/DKMBootstrap/PolaritonF3Bound.lean` clean (exit 0). MCP diagnostic returns zero errors. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_polariton_dkm_f3_bound.py` (12 tests, all PASS): canonical-formula identity, ℏ-conversion sanity, error-rejection on negative pump / non-positive photon energy, Penn TMD per-pulse occupation in [1.40e4, 1.50e4] range, Paris-LKB negligible-occupation check, 70× headroom + 10⁷× headroom assertions, linear-scaling sanity, threshold-predicate boundary tests, both-platforms-on-positive-branch bimodal-resolution sanity. | ✅ SHIPPED |
| 7 | `validate.py` checks: `formulas` PASS, `parameter_provenance` PASS (205 params), `citation_primary_sources_present` PASS (419 bibkeys cited / 290 cached), `paper_provenance` PASS, `provenance_doi_in_registry` PASS. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no new figures. | SKIP |
| 10 | E1 §2 paragraph "DKM F3 holds at device-operating pump energies — polariton inherits the graphene positive-uniqueness branch" added with Eq. \\eqref{eq:n_per_pulse_penn} (the 1.44×10⁴ per-pulse count) + direct references to `polariton_dkm_f3_holds_at_pump_below_threshold` and `polariton_inherits_graphene_uniqueness_result`. D5 §13 paragraph "Polariton substrate placement — bimodal-branch resolution" added cross-referencing the Lean theorem and noting closure of the Phase 6q open question. New bibitems for Yin-Lucas 2022 + Kuwahara-Saito 2021 added to E1 thebibliography. CITATION_REGISTRY `used_in` updated for both. 2-pass pdflatex of E1 clean (4 pages, 411 KB); 2-pass pdflatex of D5 clean. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | (a) `Phase6v_Roadmap.md` wave-status update. (b) This per-wave roadmap finalized. (c) Phase-level stakeholder docs DEFERRED to Phase 6v close. (d) Inventory_Index DEFERRED. | ✅ SHIPPED (per-wave portion) |
| 13 | Stage 13 adversarial review — DEFERRED to end of Phase 6v per user directive. | DEFERRED |
| 14 | QI — none identified in this wave. | ✅ NO-FINDINGS |

## Notes on infrastructure adjustment

Wave 6v.3 added the bibkeys `YinLucas2022LiebRobinsonBosons` and `KuwaharaSaito2021LiebRobinsonBosons` to `papers/E1/paper_draft.tex` `used_in` list. This surfaced the previously-latent fact that *bundle keys* (D1–D5, L1–L3, F, I1–I3, E1, E2) are not registered in `PAPER_TO_PHASE`. An attempt to add 14 bundle→phase mappings broke 69 pre-existing routes (those bibkeys' cache files were already placed in `Phase-1-and-Background/primary-sources/` per the previous FALLBACK behavior). The mappings were reverted and a one-line comment in `PAPER_TO_PHASE` documents the convention: bundle-cited bibkey primary sources live in `Lit-Search/Phase-1-and-Background/primary-sources/` until a future infrastructure wave re-routes them with backwards-compatible cache migration.

## Substrate touched

- **New files:** `src/dkm_polariton/__init__.py`, `src/dkm_polariton/polariton_occupation_bound.py`, `lean/SKEFTHawking/DKMBootstrap/PolaritonF3Bound.lean`, `tests/test_polariton_dkm_f3_bound.py`.
- **Modified files:** `src/core/formulas.py` (one helper), `src/core/provenance.py` (1 derived-quantity entry for the 1.44×10⁴ per-pulse occupation), `papers/D5/paper_draft.tex` and `papers/E1/paper_draft.tex` (one paragraph each), `docs/roadmaps/Phase6v_Roadmap.md` (status).

## Historical cross-wave dependencies (2026-05-26)

- **Predecessors:** Wave 6v.4 (Penn TMD parameter pass already in place; this wave consumes the Wang et al. 2026 4 fJ + 1.736 eV anchor).
- **Historical successors entry:** none in Phase 6v — this is the second of the polariton pair.
- **Current scientific successors (2026-10-17):** physical pump/occupation, dynamics/F3, transport and BEC constructions above remain OPEN under the existing Phase6q/E1:2.3 lineage.
- **Phase 6q bridge:** the dated implementation recorded a physical-closure claim, but the conditional growth theorem and normalized witnesses do not close the physical question. Current pump/state, growth, transport/uniqueness and actual BEC constructions above remain OPEN BUILD.

## No-axiom discipline

The delivered source adds no project-local axiom or tracked Prop. Given positive n_max AND the full assumed `IsBoundedByPolaritonPumpScale` growth bound, the theorem excludes `IsSuperFactorialUnbounded`. The separate LEFT-arm witness uses normalized MIR parameters; the inclusive disjunction does not establish exclusive physical classification. Incident pulse count or finite mean occupation alone supplies neither the growth premise/constants nor physical platform uniqueness. Construct those missing bridges under the original OPEN BUILD objective.
