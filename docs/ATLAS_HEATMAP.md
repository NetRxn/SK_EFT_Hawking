# Atlas Heatmap — derived proof-landscape surface (ADR-005 Phase 3)

> **Auto-generated** by `scripts/atlas_heatmap.py` from `atlas_view.build_atlas()` — a VIEW over `lean_deps.json` ∪ `HYPOTHESIS_REGISTRY`. Do not hand-edit; regenerate with `uv run python scripts/atlas_heatmap.py --write`.

_Source: 26355 theorem nodes, 48 tracked open assumptions, 72 IMPLIES edges._

## Landscape

| | count |
|---|---:|
| ✅ TRUE (proved) | 25947 |
| ⛔ OBSTRUCTION (no-go) | 408 |
| ❓ open (tracked assumptions) | 48 |
| ★ apex (headline open targets) | 1 |

## Open frontier by track ("separate areas")

Each open assumption belongs to a TRACK (`tier`); `gating` is the Σ of how many decls each node in the track immediately gates (reverse proof-dep edges).

| track | open | gating (Σ impact) | apex |
|---|---:|---:|---:|
| `discharge_future` | 16 | 12 |  |
| `external_boundary` | 14 | 23 |  |
| `headline` | 1 | 0 | 1 |
| `local` | 6 | 0 |  |

## Apex (headline) targets

| target | eliminability | gating |
|---|---|---:|
| `hyp:H_PMNSAnglesFromExactSubstrate` | hard | 0 |

## Most-gating open assumptions (top 15)

"Which open node, if discharged, unlocks the most." Swarm schedulers read this frontier (from `lean/atlas_view.json`, DB-free) to fan out provable work — ADR-005 D-I.

| gating | open node | track | eliminability | status |
|---:|---|---|---|---|
| 11 | `hyp:rokhlin_sigma_mod_16` | external_boundary | very_hard | STATED |
| 6 | `hyp:intH2_basis_datum` | discharge_future | very_hard | PLANNED |
| 4 | `hyp:H_RT_Formula_Valid` | external_boundary | open | STATED |
| 3 | `hyp:intOrientation_datum` | discharge_future | very_hard | PLANNED |
| 3 | `hyp:spin_bordism_iso_Z` | external_boundary | very_hard | PLANNED |
| 2 | `hyp:H_KLRS_SM_Crossover` | external_boundary | hard | STATED |
| 2 | `hyp:H_ScalarChannelIsTetradBifurcationOutput` | discharge_future | hard | PLANNED |
| 2 | `hyp:modular_invariance_framing` | external_boundary | hard | STATED |
| 1 | `hyp:abp_splitting_degree4_spin_bordism` | discharge_future | very_hard | PLANNED |
| 1 | `hyp:c_minus_equals_8Nf` | external_boundary | algebraic | STATED |
| 0 | `hyp:H_BilocalPointlikeLimit` | local | hard | STATED |
| 0 | `hyp:H_CFZ2_sq_a` | local | hard | STATED |
| 0 | `hyp:H_CFZ2_sq_e` | local | hard | STATED |
| 0 | `hyp:H_CasiniHuerta_Bound_Valid` | external_boundary | hard | STATED |
| 0 | `hyp:H_DESICompatibility` | discharge_future | hard | PLANNED |

