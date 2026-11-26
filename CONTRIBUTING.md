# Contributing to SK-EFT Hawking

You can contribute with a Lean editor, the command line, or an agent-assisted
workflow. Start with a specific theorem, computation, or manuscript claim so
reviewers can trace what the change affects.

## Inspect a checked result

Install [Elan](https://github.com/leanprover/elan) and clone the repository.
Open the `lean/` directory in a Lean-enabled editor. Elan selects the version
in [`lean/lean-toolchain`](lean/lean-toolchain). Package revisions are recorded
in [`lean/lake-manifest.json`](lean/lake-manifest.json).

From the repository root, build the library with `(cd lean && lake build)`.
Then try the following in a scratch Lean file. It shows
the statement and axiom dependencies of a theorem about the receiver kernel:

```lean
import SKEFTHawking.DKMBootstrap.ReceiverKernel

#check SKEFTHawking.DKMBootstrap.receiverKernel_integral
#print axioms SKEFTHawking.DKMBootstrap.receiverKernel_integral
```

For build and validation commands, see the repository's
[Build & run guide](CLAUDE.md#build--run). Python and Rust support the numerical
and validation work. The Lean editor route is enough to begin reading and
inspecting proofs.

## Choose a contribution

| If you want to work on | Start here |
| :--- | :--- |
| Lean proofs | Use the [proof atlas](docs/ATLAS_HEATMAP.md#open-frontier-by-track-separate-areas) to find open assumptions and the [negative frontier](docs/adrs/ADR-007-kernel-nogo-ledger-and-negative-frontier.md) to understand routes that have already been ruled out. |
| Numerical work | Start with the [module census](docs/MODULE_CENSUS.md) and the relevant [notebook](notebooks/). Trace inputs and outputs in the [provenance graph](docs/KNOWLEDGE_GRAPH.md). |
| Manuscripts and evidence | Pick an entry in the [bundle summary](docs/PAPER_STRATEGY.md#6-summary-table) and check the [readiness matrix](README.md#publication-readiness). Give the exact draft location and backing evidence in any proposed correction. |

Discuss substantial changes in an issue or pull request so maintainers can
point to related work. Include the relevant declaration, check, or source
location and the validation you ran. The
[repository guidance](AGENTS.md) and
[wave execution pipeline](docs/WAVE_EXECUTION_PIPELINE.md) define the current
proof, review, and handoff procedures.
