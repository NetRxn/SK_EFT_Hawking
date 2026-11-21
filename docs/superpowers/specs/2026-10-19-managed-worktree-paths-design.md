# Managed-worktree path portability

Status: specification independently accepted by the publication lead on 2026-10-19.
Implementation and whole nonauthor source/control review are accepted at consumer-repair scope.
Complete verification, recorded closure and integration remain owed. See the scoped review in
`papers/AutomatedReviews/2026-10-19-managed-worktree-paths/SCOPED_REVIEW.md`. This is not a merge gate.
Base: main `ce194cdc4bf939b108c17edc9530a7f0a14565f9` in a separate named managed checkout.

## 1. Objective and measured pilot

Make the existing target-file contract and shared-source-cache invariant independent of the
active checkout's physical directory name. Preserve what they measure. Both original failures
were reproduced on the same main baseline in managed worktrees; their complete actual failure
bodies are carried in the baseline tail log SHA256
`f608e89d2377be8912f3286c603691abbba2eb9860f1f3b2c391e9c3b53193ec`.
The specification checkout originally had identical carrying function bodies. That measured
pilot was supplied by the publication lead. Implementation subsequently reproduced the original
two failures before changing source, then observed both passing with candidate import witnesses.

The target case loses a real active `src/core/formulas.py` when written with the logical
repository prefix. The cache test probes the worktree container instead of the shared
workspace, falsely declaring five held nonempty files missing. Neither result establishes
that the canonical primary checkout fails under its current physical layout.

## 2. Existing coverage and ownership — both layers

The mechanical layer is already present: `target_files` canonicalizes every existing file,
`target_groups` and `plan` preserve lane/overlap rules, their real-repository tests cover the
prefix and concurrent-file disjointness, and `find_workspace` plus its tests cover sentinel,
structural, cwd-independent and nested-worktree lookup. The cache test owns its file-presence
and successful-state distinction. These consumers need repair; their owner does not need a
second path resolver, finding parser, registry, check or readiness gate.

The reviewer-agent layer already audits wrong assumptions and claim/source fidelity:
`adversarial-reviewer` and `claims-reviewer` are described in the skeft-qa roster. Independent
infra specification review and later nonauthor source/control review remain required here;
no paper-agent review, lexical source mention or filename-presence test can establish that
active-checkout routing or true missing-file refusal works.

ADR-012 P10's carrying sentence is **“The unit of parallelism is the FILE”**. The adjacent
new normative clarification requires logical repository prefixes to resolve to the active
checkout. `src/core/workspace.py` owns the distinct shared workspace namespace. The topology
and QA/QI map distinguish scoped verification, whole-tree gates and recorded closure; none
may be inferred from this specification.

## 3. Decision D1 — one logical prefix, one active checkout

Keep `scripts/orchestrate.py::target_files` as the owner. For each token produced by its
existing parser, normalize one exact leading `SK_EFT_Hawking/` logical prefix to a path
relative to `PROJECT_ROOT`, which denotes the active checkout. Keep the existing canonical
path, containment and `is_file` checks after normalization, stable target order and dedup by
resolved active relative filename. Return every valid file named, not merely the first.

Do not join the logical prefix to `find_workspace()` or redirect it to a canonical sibling.
Do not treat an arbitrary managed checkout basename as another repository alias. Absolute
paths already inside the active checkout remain valid subject to the same containment check;
absolute foreign paths, traversal and symlink escape remain outside. Removing one prefix is
not recursive prefix removal and does not waive existence. Preserve compatible existing
parent-relative spellings only where their resolved file remains contained in the ACTIVE
checkout; the containment guard remains the authority, not string-prefix resemblance.

## 4. Decision D2 — shared cache through the existing workspace owner

In `tests/test_phase6i_wave1.py::test_external_cache_paths_resolve_when_set`, obtain the shared
workspace through its existing `find_workspace` import and resolve each existing registry
`primary_source_path` against that result. Keep the state record relative to `SK_ROOT/docs`.
Delete the obsolete `PROJECT_ROOT` definition/comment only if no remaining use requires it.
The neighbor phase-directory invariant and production cache consumers already use this owner.
Do not modify workspace discovery or copy/fetch literature to satisfy a test.

Retain the full registry iteration and existing branches: null path is not an external-file
obligation; a present file must be nonempty; missing/empty without recorded success is bad;
missing/empty with successful state remains the existing tolerated sync-drift category.
This repair changes location, not the fidelity policy. The five witnessed files include
abstracts/stubs; their presence does not close any full-text or scientific obligation.

## 5. Decision D3 — controls decide the actual contract

| Control | Real property to observe | What must turn red |
|---|---|---|
| Original target case | Prefixed real active file resolves to its unprefixed relative name | Restore old parent-based implementation in a named managed checkout |
| Canonical and managed layouts | Same logical spelling always denotes the active copy, with a separate canonical sibling present | A resolver that returns the sibling or drops the managed target |
| Target equivalence/composition | Prefix/unprefixed/absolute-in-root/line-range spellings dedup; all distinct named files survive | First-match-only, raw-spelling keys, or dropped second target |
| Target refusal | Missing file, directory, foreign absolute path, parent traversal and outward symlink stay rejected | Removing containment or file-existence checks |
| Planner composition | One active file cannot be concurrently dispatched to two groups; strongest required lane survives | A target alias that splits one file or drops its Lean member |
| Original cache case | Held nonempty paths resolve in the actual shared workspace | Restore parent-walking cache root in the managed checkout |
| Cache failure contract | Invoke the existing invariant against controlled registry/state/file inputs | Missing or zero-byte without success incorrectly accepted |
| Cache scope/state | Repository state stays active-checkout-local; success drift and null path retain existing semantics | Reading sibling state or converting all missing files to tolerated drift |
| Workspace owner | Existing sentinel/structural/cwd/worktree tests remain true | Bypassing or duplicating `find_workspace` |
| Architecture pin | New ADR P10 sentence plus runtime target resolution agree | Rewording the contract or regressing the real call while a comment remains |

Fixtures exercise layout cases and refusal branches; actual original production identities
supply the environment-level pilot. Later controls must assert the active code/import paths
and actual returned files/raised assertion, not scan for helper names. A controlled cache
fixture calls the existing test function with monkeypatched inputs; it does not introduce a
second cache validator. Keep original assertions intact.

For any mutation of a real tracked artifact, use the existing `scripts/seed_journal.py`
restore mechanism and an allocated isolated checkout. Save original bytes/metadata and real
red/restore results. Do not mutate shared Lit-Search files, live findings or primary source
state. Temporary layout fixtures need no fake scientific source acquisition. A later reviewer
must show that old target/cache behavior makes the relevant controls fail, then exact restore
succeeds. Actual red/restore receipts are now in the implementation handback; independent review is owed.

## 6. Decision D4 — bounded implementation and integration

Later source scope: `scripts/orchestrate.py`, `tests/test_orchestrate.py`, the cache invariant
and its controls in `tests/test_phase6i_wave1.py`, and an existing architecture-claims test
pinning the ADR sentence. Extend `tests/test_workspace_resolver.py` only if a distinct managed
layout is not already covered. The resolver itself stays unchanged. The specification task changed
only the canonical finding, this design/plan and the narrow ADR P10 clarification. The separate
implementation assignment now carries the bounded consumer changes and controls.

Preserve separate current-primary slow extractor isolation from commit `43754623` on future
integration. Preserve all NJL/ADW/source/proof/registry work and the SOURCE137 acceptance
boundary. No wholesale source replacement or implicit permission to layer that proposal.
A source-level fix does not authorize a ledger edit, bundle-green stamp, Lean slot use or merge.

## 7. Verification, review and release

Implementation successor: capture exact candidate/import witnesses and run the original two
identities, target/cache contract controls, whole orchestrator file, workspace resolver tests
and architecture claim pins. Run the entire phase test file and report other failures honestly;
the known missing-citation repair is separate. Broaden through the repository's existing
scoped verifier and required whole merge-candidate gate at the root-owned integration point.
No new check means no new check registration or ratchet entry. Existing registration/coverage
obligations are not weakened.

The publication lead performs adversarial SPECIFICATION intake before implementation. Its
review must challenge canonical-sibling routing, containment, multi-target/lane behavior,
state-file anchoring and whether any missing artifact was turned into a pass. After author
repair, a genuinely nonauthor reviewer checks the complete implementation and negative
controls. Correct findings through the existing closure writer only with actual evidence and
review, and integrate through a reviewed ordinary Git checkpoint. The final human publication
review, all scientific BUILDs, all bundle gates and whole-tree acceptance remain separate.

## 8. Intent-drift check and stopping point

The user's intent is publication debt paid down through real repairs, independently reviewed
and regularly integrated. This change removes two qualification-context defects so that the
existing measurements can run correctly in isolated worktrees. It does not reduce a scientific
claim, hide another failed test, move publication work into Lit-Search, or infer primary failure
from a managed-checkout failure. The independent specification intake and deliberate implementation assignment have occurred.
The next boundary is genuinely nonauthor whole source/control review, not another user approval
request. No finding is closed by author-side verification.
