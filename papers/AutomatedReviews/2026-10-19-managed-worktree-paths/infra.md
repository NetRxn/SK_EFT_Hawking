# Managed-worktree path portability — measured infra findings

Review date: 2026-10-19. Author: publication infrastructure repair assessment.
Status: OPEN/BUILD; specification independently accepted and implementation authored.
Whole independent source/control review is accepted in [SCOPED_REVIEW.md](SCOPED_REVIEW.md).
The full cache Verify retains a separate citation failure; recorded closure and integration remain owed.

These are execution-context defects reproduced in named managed checkouts of main
`ce194cdc4bf939b108c17edc9530a7f0a14565f9`. The carrying function bodies also match the
inspected current primary checkout. This is not evidence that execution in the canonical
primary checkout fails: its physical directory layout satisfies the old assumptions.

The actual baseline tail run, 2026-10-19 17:05:28–17:05:53 UTC, contains both original
failures. Its log SHA256 is
`f608e89d2377be8912f3286c603691abbba2eb9860f1f3b2c391e9c3b53193ec`.
The complete source-linked 39-identity diagnosis and original receipts are retained by the
publication lead; current exact receipt locations and hashes are in the ignored task evidence.
No previous failure is waived, and these findings do not close other inherited failures.

## Findings

### 1.1 — Logical repository-prefixed targets disappear in a differently named checkout

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/orchestrate.py::target_files`, `tests/test_orchestrate.py`
- **Observed:** the existing production case
  `tests/test_orchestrate.py::test_target_resolves_to_every_file_it_names_and_only_real_ones[SK_EFT_Hawking/src/core/formulas.py-expected4]`
  returns `[]` instead of `['src/core/formulas.py']` in the managed baseline checkout.
  `PROJECT_ROOT.parent / 'SK_EFT_Hawking/…'` assumes the active checkout has the canonical
  physical basename. The real active file exists, but neither attempted path reaches it.
- **Impact:** the planner can classify a valid declared target as untargeted and withhold
  its dispatch. This measured result does not establish that a concurrent collision occurred.
- **Existing owner and history:** ADR-012 P10 makes the file the unit of parallelism.
  Commit `f6e9d08faec603fa2749808aad9ed85ae68874a8` genuinely repaired canonical spelling,
  existence and multi-target handling. Its parent-directory prefix accommodation retained
  a physical-layout assumption. The already-recorded shared-registry finding in
  `2026-08-13-i1-wave-residue/infra.md` concerns a different write-scope defect.
- **Required repair:** within the existing `target_files`, interpret one exact leading
  logical `SK_EFT_Hawking/` prefix against the ACTIVE checkout. Keep the same parser,
  canonical resolution, containment, file existence, stable all-target enumeration and
  deduplication. Do not route the prefix to a canonical sibling checkout or add a resolver.
- **Conservation:** unprefixed and canonical-primary spellings, line ranges, multiple paths,
  strongest-lane selection and concurrent-file disjointness remain supported. Missing files,
  directories, foreign checkout paths, traversal and symlink escapes remain refused.
- **Verify:** `python -B -m pytest -q -p no:cacheprovider tests/test_orchestrate.py`
- **Review boundary:** source repair plus meaningful controls require independent review;
  specification acceptance is not a fixed finding or a publication gate result.

### 1.2 — The cache-file invariant bypasses the canonical workspace resolver

- **Severity:** major
- **Lane:** infra
- **Gate:** `citation_primary_sources_present`
- **Location:** `tests/test_phase6i_wave1.py::test_external_cache_paths_resolve_when_set`
- **Observed:** the existing production test fails on five nonempty files held in the real
  shared workspace: Volovik2026SecondSound (540 bytes), Volovik2024VacuumDecay (1893),
  AlphaProof2025 (4127), compcert (1532), sel4 (2067). Its fixed parent walk instead probes
  the managed-worktree container's nonexistent `Lit-Search` sibling. It additionally reports
  431 successful-state entries as tolerated sync drift in that particular baseline run.
- **Evidence limit:** presence and size of these files do not establish full-text fidelity,
  scientific source acceptance, acquisition success, or citation completeness.
- **Existing owner and history:** `src/core/workspace.py::find_workspace` owns workspace
  discovery. Commit `e305bf05ce71c7a7c5b0f5258feaf43fd9044399` migrated production consumers
  and the neighboring phase-directory test; the cache-FILE test retained its old walk.
  Commit `437546236f1d18d871a8cdc2526bb6581f163a9d` separately isolates the slow orphan
  extractor's output in `tmp_path`. That improvement is unrelated and must survive integration.
- **Required repair:** use the already imported `find_workspace()` for registry-relative
  shared cache paths; keep `SK_ROOT/docs/primary_sources_state.json` checkout-local. Remove
  the obsolete derived root only if it becomes unused. No resolver, cache copy or new gate.
- **Conservation:** keep the registry population, null-path handling, nonempty-file condition,
  and existing successful-state-only sync-drift distinction. Truly missing or zero-byte paths
  without a success record must still fail. Do not invent successful state or add exceptions.
- **Verify:** `python -B -m pytest -q -p no:cacheprovider tests/test_phase6i_wave1.py tests/test_workspace_resolver.py`
- **Review boundary:** the entire phase-file verify can remain red for the distinct known
  missing-citation obligation until its independently owned repair lands. That red is retained,
  not hidden by weakening this verify or attributing it to path portability.

## Repair ownership and disposition

The publication lead accepted this worker's assignment to prepare the specification. The
lead performs independent adversarial specification intake; a deliberate successor task must
assign implementation, followed by a genuinely nonauthor source/control reviewer. No future
implementer or reviewer is recorded as having accepted a task that has not been dispatched.

[Design](../../../docs/superpowers/specs/2026-10-19-managed-worktree-paths-design.md) and
[implementation plan](../../../docs/superpowers/plans/2026-10-19-managed-worktree-paths.md)
retain both defects as BUILD. These are global infrastructure findings; no unrelated paper
bundle is invented as their attribution. Filing open majors can increase the existing global
unattributed-blocker ratchet. Preserve that signal until supported closure through the existing
writer; do not raise a ceiling or fabricate per-bundle ownership to make the filing green.


## Author implementation checkpoint — closure withheld

The lead independently accepted the complete specification before issuing the separate
implementation assignment. Both existing consumers are repaired in the isolated candidate,
with the assertions and populations retained. The original two identities were actually
reproduced red on old source and passed with the repairs. Candidate import/source witnesses,
canonical/managed layout controls and production poison/restore receipts are retained in the
implementation handback. The whole Phase6i-file run still reports its distinct missing-citation
failure. This checkpoint does not close either finding or waive another failed requirement;
a genuinely nonauthor whole source/control review and supported closure are still required.
