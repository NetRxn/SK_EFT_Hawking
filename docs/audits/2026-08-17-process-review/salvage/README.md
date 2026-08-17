# Salvage — untracked content recovered before the 2026-08-17 worktree vacuum

Twenty-five merged worktrees were removed on 2026-08-17 (217 GB → 71 GB). Two of them held
untracked, non-ignored files that existed nowhere else. Those files were copied here first.

**Why this directory exists as a lesson, not just a holding pen:** the removal predicate was
"branch merged into `main` and zero commits ahead". That certifies every *committed* file is
preserved and says nothing about untracked ones. A vacuum built on it would have destroyed the
contents below. Any automated worktree reaper must additionally assert that the worktree holds no
untracked, non-ignored file — see `../FINDINGS.md` item 2.

## Disposition

| content | verdict | reasoning |
|---|---|---|
| `redraft-D2/.../2026-08-15-bundle-stage13/D2.md` | **discarded** | Derived summary, strictly staler than `main`'s: 114/61/3/1 vs main's 121/68/10/5 (lifetime/open/blocking/critical). |
| `redraft-D3/.../2026-08-15-bundle-stage13/D3.md` | **discarded** | Same; 390/69/1/0 vs main's 406/85/14/5, and main's id list carries the `2026-08-15-d3-stage10-redraft` findings this copy predates. |
| `redraft-D3/papers/D3/_section_transcripts/` (10 files) | **kept, not promoted** | Raw subagent JSONL for the ten agents that drafted D3's merged manuscript. |
| `redraft-D2/papers/D2/_sections/signatures-section.md` | **kept, not promoted** | Same class despite the name — raw subagent JSONL for `a5ea667e8aa34be02`, "Draft D2 signatures section". Misnamed `.md` and misfiled under `_sections/`, which otherwise holds integrated LaTeX. |

## Why the eleven were kept but not promoted into `papers/`

They are drafting **provenance**, not manuscript content. The integrated deliverable for D2 is the
tracked `papers/D2/_sections/signatures.tex`; D3's is its merged `paper_draft.tex`.

Duplicates of all eleven exist on the harness side as
`~/.claude/projects/<project>/<session>/subagents/agent-<id>.jsonl`, each *larger* than the repo
copy (these were truncated captures). Those harness transcripts are session-scoped and outside git,
so they are not durable — which is the only reason these copies are worth retaining at all.

Promoting them into `papers/` was rejected on three grounds: `_section_transcripts/` is a tracked
convention **nowhere** in the repo, so promotion would establish one by accident rather than by
decision; the D2 file's name and location are both wrong, so promoting it would enshrine the error;
and 28 MB of raw JSONL is real repo weight for provenance nothing queries.

## The open question this surfaced

**Are drafting transcripts durable provenance, and if so where do they live?** Two bundles persisted
them, under two different names (`_section_transcripts/` vs `_sections/*-section.md`), in two
different directories, neither tracked, during the same wave. That is an undecided convention being
improvised per bundle.

It belongs to the Stage-10 dispatch-brief contract (`../FINDINGS.md` item 5): if the answer is yes,
the brief states the one path; if no, the brief says not to write them into the worktree at all.
Settle it there rather than here.
