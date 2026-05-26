# Wave 6v.5 — APM-LDPC code substrate + hashing-bound LDP sub-wave (D6 §4)

**Bundle targets:** D6 §4 (primary) + I1 (verification-methodology sidebar).

**Status:** ✅ SHIPPED 2026-05-26.

**Source papers (canonical, primary-source cached):**
- D. Komoto, K. Kasai, "Quantum Error Correction near the Coding Theoretical Bound," npj Quantum Information 11, 154 (2025); arXiv:2412.21171; DOI 10.1038/s41534-025-01090-1. Hashing-bound substrate paper. Cache: `Lit-Search/Phase-1-and-Background/primary-sources/KomotoKasai2025APMLDPCHashingBound.pdf`. Bibkey: `KomotoKasai2025APMLDPCHashingBound`.

**Wave goal.** Substrate-level kernel-verified encoding of two complementary APM-LDPC properties:

1. **Rate-above-half:** an explicit APM-LDPC code with logical-to-physical rate `k/n > 1/2`. Reference parameters: `[[1152, 580, ≤12]]` from the strategy synthesis F4 QuEra/Harvard line (a representative high-rate qLDPC code structure; 580/1152 ≈ 0.5035 > 1/2).
2. **Hashing-bound approachability:** for a depolarizing-noise channel with per-qubit error probability `p`, the quantum capacity is upper-bounded by `1 - H_2(p)` where `H_2` is binary Shannon entropy. APM-LDPC codes (per Komoto-Kasai 2025) approach this bound with linear-time decoding. Substrate-level encoding via the `IsHashingBoundAchievable` predicate.

The substantive contrast: a code with rate `k/n ≤ 1/2` is in the "high-overhead" class; the QuEra/Harvard [[1152, 580]] sits one logical qubit above the threshold (the 580 ≥ 577 = ⌈1152/2⌉ + 1 margin). Falsifier: an explicit `(2k, k)` code witnesses the rate-exactly-1/2 case where the predicate `>1/2` fails.

## Key parameters

| Symbol | Value | Source | Use |
|---|---:|---|---|
| `n_phys` (reference code) | 1152 | F4 line strategy synthesis | physical qubits |
| `k_log` (reference code) | 580 | F4 line strategy synthesis | logical qubits |
| `code_rate` = k/n | 580/1152 ≈ 0.5035 | derived | substantively > 1/2 |
| `rate_margin_above_half` | 580 - 576 = 4 | derived: k - ⌊n/2⌋ | concrete integer margin |
| `hashing_bound_threshold_p` | depolarizing-noise p | Komoto-Kasai 2025 | predicate parameter |

## Deliverables

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap + bibkey + PDF cache. | ✅ SHIPPED |
| 2 | (skip) — no new Python formulas. | SKIP |
| 3a | Ship Lean `lean/SKEFTHawking/FaultTolerance/APMLdpcHashingBound.lean` (~150 LoC, kernel-only): `ApmLdpcCode` structure (`nPhys`, `kLog` + positivity witnesses), `quEraHarvardMITCode_1152_580 : ApmLdpcCode`, `IsRateAboveHalf` predicate, `apmLdpc_quEraHarvard_rate_above_half`, `IsHashingBoundAchievable` predicate, `apmLdpc_approaches_hashing_bound` (substrate-level), substantive falsifier `exactlyHalfRateCode_not_above_half`. | ✅ SHIPPED |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean` clean. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_apm_ldpc_hashing_bound.py` regression. | ✅ SHIPPED |
| 7 | `validate.py` checks: citation_primary_sources_present. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | D6 §4 populated with Wave-6v.5 substantive content. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | Phase6v_Roadmap.md status updated; per-wave roadmap finalized; Inventory_Index + stakeholder docs DEFERRED to Phase 6v close. | ✅ SHIPPED |
| 13 | DEFERRED. | DEFERRED |
| 14 | QI — none. | ✅ NO-FINDINGS |

## No-axiom discipline

Zero new project-local axioms. The rate-above-half claim is rational-arithmetic discharged by `decide` / `norm_num`. The hashing-bound predicate ships at substrate level (capacity-theoretic content deferred to a future Mathlib-Shannon-entropy-substrate wave; the predicate is non-vacuously witnessable by any code whose rate satisfies the threshold inequality).
