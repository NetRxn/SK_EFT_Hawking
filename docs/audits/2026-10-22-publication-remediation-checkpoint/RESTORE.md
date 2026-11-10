# Recover source from the remote checkpoint

This restores source DATA; it does not establish current runtime/proof/gate authority. Read README and the original repository guidance first. Never apply an archive over a live/dirty shared checkout, active Lean slot or another owner's branch.

## Committed heads and unfinished changes

`BRANCH_CHECKPOINTS.json` maps each original local branch/detached checkout to its exact `base_head`, remote backup ref, source archive and merge state. All27 backup refs were independently verified after the atomic push. They preserve the original committed history. Fourteen source archives preserve the uncommitted work separately, avoiding false integration or completion of the unfinished merge.

1. Fetch the exact `codex/pub-checkpoint-20261022/...` ref from this repository and verify its SHA against the inventory.
2. Create a **fresh dedicated worktree/branch** at that base SHA. For proof work, this is source inspection only; ADR-008 owns any later Lean slot admission. Do not create an extra Lean runner.
3. Verify the archive SHA256 against `source-checkpoints/manifest.json`, then unpack it into a separate inspection directory. The archive root is the worktree slug. It contains `manifest.json`, `staged.patch`, `unstaged.patch`, `working-tree.patch`, `index-stage.z`, any merge metadata, and all untracked source under `untracked/`.
4. Inspect the full patches and files. For a source-only recovery, `git apply --binary working-tree.patch` restores the combined tracked state. To recover the original stage split instead, apply `git apply --index --binary staged.patch` followed by `git apply --binary unstaged.patch`. Empty patches require no command. Do not apply both combined and split patches.
5. Copy the archived untracked source to the same relative paths without overwriting unexpected files. Restore full permission bits from `states[*].mode`: Git patches preserve executable bits, not all permissions. Verify every resulting file/symlink/missing path, full bytes/SHA and mode against the manifest. Original nanosecond mtimes are recorded for evidence; a fresh clone's mtimes do not preserve old runtime freshness. Do not claim a historical runtime receipt as current if restoring them.
6. For split-index recovery, compare `git ls-files --stage -z` with `index-stage.z`/its recorded SHA. Raw machine-specific Git index bytes are intentionally not installed on another host.
7. The integrated-science archive includes original MERGE_HEAD/MERGE_MSG/MERGE_MODE/AUTO_MERGE/ORIG_HEAD where present. These are evidence of an unfinished merge, **not instructions to auto-complete it**. Inspect the exact parents and stage split, reconcile current ancestry, then use the normal deliberate integration process. Never copy a raw `.git` directory or stale lease into another checkout.

All14 combined patches were actually restored in isolated source-preimage probes and every captured source byte/kind/full-mode checked. The original source/index remained exact. A first probe exposed mode0600 versus Git's0644; the final protocol explicitly restores the separate full-mode metadata. The failed first preparation is retained locally, not represented as success. Additional split-index replay verification is recorded separately if performed. These are recovery checks, not candidate scientific tests.

## Ignored author/review DATA and runtime evidence

`evidence/manifest.json` enumerates original package paths, every included file/hash, complete source-DATA archives and explicitly omitted large local runtime bodies. Unpack evidence outside production paths and inspect as DATA. Absolute paths and hashes preserve provenance but do not make old packets portable/current. Synthetic future FIRST/review/grant/environment examples inside author packages are not actual authority and must never be installed as such.

Remote source recovery does not restore an executing process, native descriptor, resource owner, backend, tool session, current hook load, valid lease or actual source-restoration journal. Do not poll/restart historical terminal handles. The four WT2 commits remain unabsorbed; use current `slotctl status --json` and `slotctl doctor --json` plus exact ownership/base/epoch/quiescence/capacity/lifecycle evidence before any controller action. A stale FREE/READY label is insufficient, and dirty/quarantined slots cannot be reset to make them look available.

After source recovery, create new exact continuity packets through the existing adapter. Validate the original full acceptance requirements against actual current source and independent evidence. Complete the pending reviews and repairs in FORWARD_PLAN before any runtime grant, canonical closure, main merge or publication acceptance.
