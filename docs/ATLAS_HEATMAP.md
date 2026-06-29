# Atlas Heatmap — derived proof-landscape surface (ADR-005 Phase 3)

> **Auto-generated** by `scripts/atlas_heatmap.py` from `atlas_view.build_atlas()` — a VIEW over `lean_deps.json` ∪ `HYPOTHESIS_REGISTRY`. Do not hand-edit; regenerate with `uv run python scripts/atlas_heatmap.py --write`.

_Source: 14224 theorem nodes, 33 tracked open assumptions, 35 IMPLIES edges._

## Landscape

| | count |
|---|---:|
| ✅ TRUE (proved) | 14014 |
| ⛔ OBSTRUCTION (no-go) | 210 |
| ❓ open (tracked assumptions) | 33 |
| ★ apex (headline open targets) | 4 |

## Open frontier by track ("separate areas")

Each open assumption belongs to a TRACK (`tier`); `gating` is the Σ of how many decls each node in the track immediately gates (reverse proof-dep edges).

| track | open | gating (Σ impact) | apex |
|---|---:|---:|---:|
| `discharge_future` | 8 | 14 |  |
| `external_boundary` | 15 | 21 |  |
| `headline` | 4 | 0 | 4 |
| `local` | 6 | 0 |  |

## Apex (headline) targets

| target | eliminability | gating |
|---|---|---:|
| `hyp:H_Fib_NonCentralConjugateWitness` | hard | 0 |
| `hyp:H_Fib_TwoLITangents` | hard | 0 |
| `hyp:H_Fib_v4_witness` | hard | 0 |
| `hyp:H_PMNSAnglesFromExactSubstrate` | hard | 0 |

## Most-gating open assumptions (top 15)

"Which open node, if discharged, unlocks the most." Swarm schedulers read this frontier (from `lean/atlas_view.json`, DB-free) to fan out provable work — ADR-005 D-I.

| gating | open node | track | eliminability | status |
|---:|---|---|---|---|
| 12 | `hyp:smith_inflow_z16` | discharge_future | very_hard | PLANNED |
| 11 | `hyp:rokhlin_sigma_mod_16` | external_boundary | very_hard | STATED |
| 4 | `hyp:H_RT_Formula_Valid` | external_boundary | open | STATED |
| 2 | `hyp:H_KLRS_SM_Crossover` | external_boundary | hard | STATED |
| 2 | `hyp:H_ScalarChannelIsTetradBifurcationOutput` | discharge_future | hard | PLANNED |
| 2 | `hyp:modular_invariance_framing` | external_boundary | hard | STATED |
| 1 | `hyp:c_minus_equals_8Nf` | external_boundary | algebraic | STATED |
| 1 | `hyp:characteristic_square_mod_8` | external_boundary | hard | STATED |
| 0 | `hyp:H_BilocalPointlikeLimit` | local | hard | STATED |
| 0 | `hyp:H_CFZ2_sq_a` | local | hard | STATED |
| 0 | `hyp:H_CFZ2_sq_e` | local | hard | STATED |
| 0 | `hyp:H_CasiniHuerta_Bound_Valid` | external_boundary | hard | STATED |
| 0 | `hyp:H_DESICompatibility` | discharge_future | hard | PLANNED |
| 0 | `hyp:H_DecouplingBoundDim6` | local | hard | STATED |
| 0 | `hyp:H_Fib_NonCentralConjugateWitness` ★ | headline | hard | STATED |

