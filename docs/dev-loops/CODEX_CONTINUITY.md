# Codex dispatch and recovery

Status: explicit packet recovery is implemented and rehearsed. Native desktop compaction delivery and final integration remain unverified; broad autonomous swarming is not yet released. See [rehearsal evidence](../audits/2026-09-08-codex-continuity/RESULTS.md).

The primary lead uses the existing remediation planner (`scripts/orchestrate.py`) for finding-driven work, and the atlas for additional development context. The lead remains free to choose its execution graph. The wave pipeline owns review and closure; ADR-008 owns slots and builds. ADR-017 specifies this Codex connection.

Each assignment records the task and parent, objective, assigned files, exact candidate state, role, notebook's absolute primary-checkout path, its designated writer, owning roadmap, required evidence and acceptance reviewer. These are handoff data, not a duplicate progress ledger. One writer curates each notebook; workers read and report. Notebook files remain gitignored and machine-local.

Before dispatch, after interruption or compaction, and before accepting a returned result, compare the packet with live repository and governing-file state. Changed state means reconcile: read current owners, inspect the change and refresh the assignment deliberately. A matching packet is not proof that tests passed, a lease remains active, or a task is complete. Read the existing live probe and atlas for structural orientation; leaf workers must not act on root-only build or repair suggestions.

Root verifies live slot admission through the current controller before leasing or delegating Lean work. Leaf workers do not integrate, repair caches, build, or write shared registries/notebooks. Reviewers receive the candidate and original acceptance requirement and report independently. A new research result can reopen affected work; do not silently treat a returned result for an old contract as current.

A source-level check or synthetic event does not establish native lifecycle delivery. Until native compaction recovery is demonstrated, the explicit recovery procedure remains mandatory and unattended compaction continuity is unverified. Record rehearsal evidence and residual requirements in the process increment's owning record.

Expected worker edits also make a snapshot stale. The lead reviews the resulting diff and issues a new packet after reconciling it; workers never refresh away their own discrepancy as evidence of acceptance.

## Explicit command sequence

The adapter is `scripts/codex_continuity.py`. From the assigned checkout, the lead calls `packet` with `--repo`, `--task`, `--parent`, `--role`, `--owner`, `--writer`, `--objective`, `--reviewer`, `--evidence`, `--roadmap`, `--notebook`, repeated `--owned` files, and an ignored primary-local `--output`. Use `--help` for the exact argument contract. Supply additional `--authority` inputs when work depends on other process or research decisions, including governing files outside the selected repository. These read-only references supplement mandatory base guidance; they never replace it. A downstream repository must explicitly include its upstream governing documents.

Packet revisions live in the primary checkout's gitignored `.codex/continuity/` directory. These local snapshots may contain absolute paths. The adapter refuses tracked or nonignored output, existing output and invalid inputs; use a new revision filename for deliberate reissue.

The assigned worker's first action and explicit recovery action are:

```bash
python3 scripts/codex_continuity.py check /absolute/primary/local/packet.json
```

A nonzero result returns work to the lead for reconciliation. On a match, read the referenced roadmap, notebook and authorities, then verify live role/slot authority separately. Reports include the packet revision, candidate diff, commands actually run, results, open questions and required re-review. The lead checks current evidence and uses the existing closure writer for accepted findings; a new packet is never a substitute for closure.

For finding-driven work, generate the plan with `python3 scripts/orchestrate.py --json` and consume its groups, gates and refusal reasons. Its output does not prove slot availability. Source observation and planning do not need a new runtime hook. Hook installation or runtime reload is a separate transition with event evidence; editing agent profiles does not reload an already-running worker.
