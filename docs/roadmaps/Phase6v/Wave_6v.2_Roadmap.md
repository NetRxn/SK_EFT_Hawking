# Wave 6v.2 — Shor T-gate counts for ECC-256 (D6 §5)

**Bundle targets:** D6 §5 (primary) + D4 (cross-bridge) + I1 (verification-methodology sidebar).

**Status:** ✅ SHIPPED 2026-05-26.

**Source paper (canonical, primary-source cached):**
R. Babbush, A. Zalcman, C. Gidney, M. Broughton, T. Khattar, H. Neven, T. Bergamaschi, J. Drake, D. Boneh, "Securing Elliptic Curve Cryptocurrencies against Quantum Vulnerabilities: Resource Estimates and Mitigations," arXiv:2603.28846 (v2 2026-04-15). Primary-source cache: `Lit-Search/Phase-1-and-Background/primary-sources/GoogleShorECC256_2026.pdf` (1.9 MB, downloaded 2026-05-26). Bibkey: `BabbushGidneyEtAl2026ECC256Shor`.

**Wave goal.** Lift the Google 2026 ECC-256 Shor resource estimate into a kernel-verified T-gate-count upper bound for `shor_ecc256_tgate_count_le`. The substantive content: the Bravyi-Kitaev exact-ancilla-free Toffoli-to-T decomposition gives 7 T-gates per Toffoli, so the Babbush-Gidney-et-al. headline `< 90M Toffoli` translates to `< 630M T-gates`. The Lean substrate encodes this as a *non-trivial bound*: ANY ECC-256 Shor circuit fitting in the Babbush-et-al. Toffoli budget, after BK decomposition, fits in 7× the corresponding T budget. The companion `bk_decomposition_optimal_factor` theorem witnesses the substantive 7× factor.

## Key parameters

| Symbol | Value | Source | Use |
|---|---:|---|---|
| `n_qubits_config_1200` | 1200 | Babbush et al. 2026 abstract | qubit-count anchor (config A) |
| `n_qubits_config_1450` | 1450 | Babbush et al. 2026 abstract | qubit-count anchor (config B) |
| `Toffoli budget (config A)` | 90 × 10⁶ | Babbush et al. 2026 abstract | upper bound on Toffoli gates |
| `Toffoli budget (config B)` | 70 × 10⁶ | Babbush et al. 2026 abstract | upper bound on Toffoli gates |
| `Bravyi-Kitaev T per Toffoli` | 7 | Bravyi-Kitaev 2005 PRA 71, 022316 | exact ancilla-free factor |
| `T-gate bound (config A)` | 630 × 10⁶ | derived: 7 × 90M | upper bound on T gates |
| `T-gate bound (config B)` | 490 × 10⁶ | derived: 7 × 70M | upper bound on T gates |

## Deliverables

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap + PDF cache. Bibkeys `BabbushGidneyEtAl2026ECC256Shor` + `BravyiKitaev2005MagicState` added. | ✅ SHIPPED |
| 2 | (skip) — no new Python formulas (Toffoli-count facts are integer arithmetic). | SKIP |
| 3a | Ship Lean `lean/SKEFTHawking/FaultTolerance/ShorTGateCount.lean` (~140 LoC, kernel-only): `bravyiKitaevToffoliT`, `bkDecomposition_eq_seven_times`, `googleShorECC256ToffoliBound`, `googleShorECC256TGateBound`, `shor_ecc256_tgate_count_le` (the headline theorem), substantive contrast `shor_ecc256_falls_within_megagate_envelope_at_1G` (a falsifier-style claim: the 1-G T-gate envelope ENCLOSES the Google ECC-256 budget, with concrete margin). | ✅ SHIPPED |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean` clean. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_shor_tgate_count.py` regression. | ✅ SHIPPED |
| 7 | `validate.py` checks: citation_primary_sources_present + parameter_provenance. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | D6 §5 populated with Wave-6v.2 substantive content. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | Phase6v_Roadmap.md status + per-wave roadmap finalized; Inventory_Index + stakeholder docs DEFERRED to Phase 6v close. | ✅ SHIPPED |
| 13 | DEFERRED. | DEFERRED |
| 14 | QI — none. | ✅ NO-FINDINGS |

## Cross-wave dependencies

- **Predecessor:** Wave 6v.1 (D6 bundle created); the D6 §5 lift requires the bundle to exist.
- **Substrate consumer:** Wave 6v.2 builds on Phase 6t SK substrate conceptually (per-non-Clifford-rotation compile cost) but the Lean theorem is at integer-arithmetic level — no direct SK theorem call.

## No-axiom discipline

Zero new project-local axioms. The bound is integer arithmetic discharged by `decide`.
