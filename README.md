# SK-EFT Hawking

SK-EFT Hawking is an open research project on analog horizons, effective field
theory, and the mathematics that connects condensed matter, gravity, and quantum
information. It began with Schwinger–Keldysh effective field theory for
dissipative corrections to analog Hawking radiation. It now includes a Lean 4
library, numerical models, and a portfolio of working papers.

The research asks which features of a microscopic model survive in an effective
description and where that description breaks down. Lean checks each formal
theorem against its stated hypotheses. Python and Rust support numerical and
computational work. Physical modeling, experimental identification, and
manuscript review have their own evidence requirements.

## Research areas

| Area | Where to look |
| :--- | :--- |
| Analog horizons and transport | [E1](papers/E1/) and [E2](papers/E2/) cover analog-horizon predictions and detector models. The [transport study](docs/roadmaps/Phase6v/Wave_6v.10_Roadmap.md#scope-of-the-operator-and-transport-results) is a worked example of checking where an effective model applies. |
| Emergent gravity and field theory | [Research map by claim chain](docs/RESEARCH_STATUS_OVERVIEW.md#how-to-read-this-document) and the [predictive scope](docs/ARCHITECTURE_SCOPE.md) trace the proposed mechanisms, conditional results, and obstructions. |
| Topological phases and quantum computation | [D4](papers/D4/), [D6](papers/D6/), [D7](papers/D7/), and [D8](papers/D8/) cover related work on topological quantum computation, fault tolerance, classical simulability, and gate synthesis. |
| Formal methods and reproducibility | The [Lean library](lean/SKEFTHawking/), [tracked hypotheses](docs/PERMANENT_TRACKED_HYPOTHESES.md), and [provenance graph](docs/KNOWLEDGE_GRAPH.md) connect formal statements, code, sources, and draft claims. |

For a nontechnical introduction, start with the
[Educational Companion Guide](docs/stakeholder/companion_guide.md).
For the full paper roster and scope of each bundle, see the
[bundle summary](docs/PAPER_STRATEGY.md#6-summary-table).

## Publication readiness

Each row is a working manuscript bundle. The cells report the repository's
[readiness evaluator](scripts/readiness_gates.py), whose categories and criteria
are documented in [Readiness Gates](docs/READINESS_GATES.md). Publication also
requires manuscript review and human sign-off.

**🟢 Passed · 🔴 Blocked · 🟡 Open or in review · 🟡 ↻ Needs recheck · ⚪ Unmeasured**

Snapshot evaluated on 2026-11-26 from [`9b5556b7`](https://github.com/NetRxn/SK_EFT_Hawking/commit/9b5556b7df2efb04c2c124b0929f213ae916c2a7).

| Bundle | Citations | Consistency | Parameters | Computation | Lean proofs | Assumptions | Narrative | Run health | Freshness | First claims | Fixes |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| [F](papers/F/) | 🟢 | 🟢 | 🟡 | 🟡 | 🔴 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🔴 |
| [D1](papers/D1/) | 🟢 | 🟢 | 🟡 | 🟡 | 🔴 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🔴 |
| [D2](papers/D2/) | 🔴 | 🟢 | 🟢 | 🟡 | 🔴 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [D3](papers/D3/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [D4](papers/D4/) | 🟢 | 🟢 | 🟡 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🔴 |
| [D5](papers/D5/) | 🟢 | 🟡 ↻ | 🟡 | 🟡 | 🔴 | 🟢 | 🔴 | 🟢 | 🟡 ↻ | 🟡 ↻ | 🔴 |
| [D6](papers/D6/) | 🟢 | 🟢 | 🟡 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🟢 |
| [D7](papers/D7/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ |
| [D8](papers/D8/) | 🟡 | 🟢 | 🟢 | 🟡 | 🔴 | 🟢 | 🔴 | 🟢 | 🟢 | 🟡 ↻ | 🔴 |
| [D9](papers/D9/) | 🟢 | 🟡 ↻ | 🟡 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🟢 |
| [D10](papers/D10/) | 🟡 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🔴 | 🟢 | 🟢 | 🟡 ↻ | 🟡 ↻ |
| [D11](papers/D11/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ |
| [D12](papers/D12/) | 🟢 | 🟢 | 🔴 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [L1](papers/L1/) | 🟢 | 🟢 | 🟡 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🔴 |
| [L2](papers/L2/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [L3](papers/L3/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [I1](papers/I1/) | 🟢 | 🟢 | 🟢 | 🟡 | 🔴 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [I2](papers/I2/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ |
| [I3](papers/I3/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ |
| [E1](papers/E1/) | 🟢 | 🟢 | 🟢 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🟢 | 🔴 |
| [E2](papers/E2/) | 🟢 | 🟢 | 🟡 | 🟡 | 🟢 | 🟢 | 🟢 | 🟢 | 🟡 ↻ | 🟢 | 🟡 ↻ |

The table is a commit-pinned snapshot. For current gate evidence and blockers,
run the [provenance dashboard](docs/architecture/DASHBOARD.md#quick-start) and open
[Readiness](http://localhost:8050/?tab=readiness) on your local instance.
The [Stage 13 review heatmap](docs/BUNDLE_READINESS_HEATMAP.md) tracks
review findings. The [gate topology](docs/architecture/VALIDATION_GATE_TOPOLOGY.md)
explains what the readiness checks measure.

<details>
<summary>Regenerate the snapshot from a clean checkout</summary>

Set up the repository and its source corpus as described in the
[dashboard guide](docs/architecture/DASHBOARD.md#quick-start). The commands below print a
replacement snapshot using the current bundle roster and gate evaluator.
A stale Lean declaration map stops the refresh.

```sh
uv run python -B scripts/extract_lean_deps.py --check &&
PYTHONPATH=scripts uv run python -B - <<'PYTHON'
from datetime import date
from itertools import product
from subprocess import check_output

from build_graph import extract_readiness_gate_nodes
from bundle_registry import BUNDLE_CODES, bundle_sort_key
from readiness_gates import GATES

bundles = sorted(BUNDLE_CODES, key=bundle_sort_key)
gates = [name for name, _, _ in GATES]
labels = {
    "CitationIntegrity": "Citations", "CrossPaperConsistency": "Consistency",
    "ParameterProvenance": "Parameters", "ComputationCorrectness": "Computation",
    "LeanProofSubstance": "Lean proofs", "AssumptionDisclosure": "Assumptions",
    "NarrativeGrounding": "Narrative", "ProductionRunHealth": "Run health",
    "NumericalFreshness": "Freshness", "FirstClaimVerification": "First claims",
    "FixPropagation": "Fixes",
}
icons = {"passed": "🟢", "blocked": "🔴", "open": "🟡",
         "in-review": "🟡", "needs-recheck": "🟡 ↻"}
cells = {}
for node in extract_readiness_gate_nodes():
    row = node["meta"]
    if row["paper"] not in bundles:
        continue
    key = (row["paper"], row["gate"])
    if key in cells:
        raise ValueError(f"Duplicate readiness cell {key}")
    cells[key] = icons[row["state"]] if row["measured"] else "⚪"

if not bundles or not gates or cells.keys() != set(product(bundles, gates)):
    raise ValueError("Incomplete bundle readiness matrix")

sha = check_output(["git", "rev-parse", "HEAD"], text=True).strip()
print(f"Snapshot evaluated on {date.today()} from "
      f"[`{sha[:8]}`](https://github.com/NetRxn/SK_EFT_Hawking/commit/{sha}).")
print()
print("| Bundle | " + " | ".join(labels.get(gate, gate) for gate in gates) + " |")
print("| :--- | " + " | ".join(":---:" for _ in gates) + " |")
for bundle in bundles:
    print(f"| [{bundle}](papers/{bundle}/) | " +
          " | ".join(cells[bundle, gate] for gate in gates) + " |")
PYTHON
```

</details>

## Work with the repository

The [contributor guide](CONTRIBUTING.md) shows how to inspect a checked theorem
and find work in the proof atlas, numerics, or manuscripts.

Use Python 3.14 or later with `uv`, and install the Lean toolchain pinned
in [`lean/lean-toolchain`](lean/lean-toolchain).

```sh
uv sync
uv run python -m pytest -q
(cd lean && lake build SKEFTHawking.ExtractDeps)
uv run python scripts/provenance_dashboard.py
```

- [Contributor guidance](AGENTS.md) and the [wave execution pipeline](docs/WAVE_EXECUTION_PIPELINE.md)
- [Current library and code counts](docs/counts.json) and the [module census](docs/MODULE_CENSUS.md)
- [Research roadmaps](docs/roadmaps/) and [attribution](ATTRIBUTION.md)
