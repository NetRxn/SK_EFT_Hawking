# Wave 6v.3 — DKM F3 polariton occupancy bound (Phase 6q follow-on)

**Bundle targets:** D5 §"substrate constraints by platform" + E1 §"polariton platform regime structure" (additive scope paragraphs).

**Status:** ✅ SHIPPED 2026-05-26.

**Wave goal.** Resolve the Phase 6q open question: where does the polariton platform fall on the DKM positive-uniqueness ↔ sharpened-NO-GO bimodal outcome? Phase 6q's `PlatformBimodalOutcome` is a disjunction; graphene is the positive-uniqueness witness, BEC Bogoliubov is the sharpened-NO-GO witness. Wave 6v.3 ships the polariton resolution: **polariton, under a finite-pump-energy operating constraint, takes the POSITIVE branch — inheriting the graphene uniqueness result via a finite per-mode occupation bound that keeps the commutator-norm sequence factorially bounded (not super-factorial unbounded).**

## Physical anchor — per-mode occupation under sub-nW pump

The UPenn nanocavity-polariton platform (Wang et al. 2026, Wave 6v.4) demonstrates all-optical switching at pulse energies as low as 4 fJ on picosecond timescales. The photon count per switching pulse is

```
n_per_pulse = E_pulse / (ℏω)
            = (4 × 10⁻¹⁵ J) / (1.736 eV × 1.602176634×10⁻¹⁹ J/eV)
            ≈ 1.44 × 10⁴ photons per mode per pulse.
```

This is the *device-operating* mode occupation. For the DKM F3 (operator-growth) axiom to break on a bosonic substrate via Yin-Lucas / Kuwahara-Saito Lieb-Robinson-for-bosons, the mode occupation needs to grow super-factorially (per `IsSuperFactorialUnbounded` in `DKMBootstrap/HorizonTransportBootstrap.lean`). At `n ≈ 1.5×10⁴`, the polariton operator growth is bounded by a factorial-power product with a finite ε proportional to `√(n_max)·g/ℏ`, NOT super-factorial — so F3 holds.

The cleanest formulation: **polariton occupation below `n_threshold = 10⁶` implies bounded operator growth**, which puts polariton on the same positive-uniqueness branch as graphene (whose commutator norm is identically zero in the substrate witness — the strongest possible bound).

This **resolves the explicit open question** left in Phase 6q's `project_phase6q_complete_2026_05_23.md` memory.

## Key parameters (LLM-verified against Wang et al. 2026 / Falque 2025)

| Symbol | Value | Unit | Source | Use |
|---|---:|---|---|---|
| ℏω_cav (Penn resonance energy) | 1.736 | eV | Wang et al. 2026 | Photon count derivation. |
| E_pulse (Penn switching threshold) | 4 | fJ | Wang et al. 2026 | Per-pulse mode occupation. |
| n_per_pulse | ≈ 1.44 × 10⁴ | photons/mode | derived | Device-operating occupation. |
| τ_LP (Penn polariton lifetime) | ≈ 366 | fs | Wang et al. 2026 (= ℏ/γ_LP) | Per-mode steady-state setting. |
| ℏω_LP (Paris-LKB polariton energy) | ≈ 1.485 | eV | Falque 2025 (working point) | Cross-check on Paris-LKB. |
| n_threshold (F3-break onset) | 10⁶ | photons/mode | DR Wave 2a.1 §1 BEC row | Polariton stays well below. |

## Deliverables (14-stage pipeline)

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

## Cross-wave dependencies

- **Predecessors:** Wave 6v.4 (Penn TMD parameter pass already in place; this wave consumes the Wang et al. 2026 4 fJ + 1.736 eV anchor).
- **Successors:** none in Phase 6v — this is the second of the polariton pair.
- **Phase 6q bridge:** closes the open question in `project_phase6q_complete_2026_05_23.md` memory.

## No-axiom discipline

Zero new project-local axioms; zero tracked Props. The polariton-bounded-commutator-norm proof is a contrapositive of the existing `sharpened_no_go_super_factorial`: by the existing predicate's negation, polariton's finite-n mode occupation gives a finite super-factorial bound, putting it OUTSIDE `IsSuperFactorialUnbounded` — and hence on the LEFT (positive-uniqueness) branch of `PlatformBimodalOutcome`.
