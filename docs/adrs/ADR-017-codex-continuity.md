# ADR-017 — Codex continuity at dispatch and recovery

Status: explicit adapter implemented and independently reviewed; interrupted-reader rehearsal passed. Native lifecycle acceptance and merged-wave certification remain pending. Evidence: [rehearsal results](../audits/2026-09-08-codex-continuity/RESULTS.md).

## Context

ADR-012's `scripts/orchestrate.py` already derives eligible repair groups and worker profiles. ADR-008 owns leases, builds and integration. `scripts/repo_state_probe.py` and the derived atlas supply live orientation; local notebooks preserve decisions. Codex worker contracts need an explicit connection to these owners across interrupted execution.

## Decisions

D1. Keep routing, completion records and scientific state in their current owners. A handoff packet is a disposable local snapshot, not another task registry or a certificate.

D2. Bind each packet to a task, parent, role, designated notebook writer, primary repository, assigned paths, roadmap and notebook. Fingerprint the governing documents and source state. A recovery check reports changed or unavailable inputs; it never silently refreshes an obsolete packet or authorizes a lease.

D3. Reuse the existing planner on fresh context when the task consumes findings. Preserve its profile gates. Slot discovery does not grant admission; the primary orchestrator checks current controller state and ownership before dispatch.

D4. Resume from current authorities and the notebook's decisions. Preserve one writer per notebook; workers return evidence. Manual recovery is supported independently of lifecycle-hook delivery. Do not claim automatic compaction coverage without a native runtime event test.

D5. Validate stale source, same-status dirty edits, changed authority, missing notebook, and fresh-reader recovery. An interrupted task must reconcile a changed contract before continuing. Synthetic tests and real agent rehearsal are distinct evidence. Broad autonomous swarming remains gated until the required runtime evidence is filed.

D6. Claude configuration and lifecycle remain outside this change. Broad transcript harvesting and deeper hierarchical supervision are subsequent work, not implicit dependencies of a basic handoff.

## Ownership and plan

The operator contract lives in `docs/dev-loops/CODEX_CONTINUITY.md`; the adapter belongs beside existing scripts and calls existing owners rather than copying their decision logic. Codex bootstrap references the contract. Existing source and review gates retain acceptance authority. Tests mutate actual adapter inputs and use real local source paths in a bounded pilot; tests never write production graph data.

Alternatives rejected: a second routing engine; replaying entire transcripts as current authority; assuming changed configuration is loaded; treating the presence of a slot directory as a lease.
