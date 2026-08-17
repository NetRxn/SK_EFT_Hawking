# The Stage-10 dispatch brief — what the lead owes a drafting agent

Read this before writing a brief for `skeft-qa:paper-drafter` or for a full-bundle redraft lead.

`paper-drafter` states what a brief carries **from the receiving end**. This is the author's side.
The two are counterparts and neither is a roster for the other: change one and check the other.

---

## The rule

**Every factual claim a brief makes names the artifact it was derived from.**

That is the whole contract. Everything below is its application.

A brief is an instruction, not a deliverable — nothing gates it, no reviewer reads it, and its
errors surface only when the receiving agent has already spent a dispatch acting on them. Naming the
origin is the one control that operates while the brief is being written, when a wrong claim costs
nothing to fix.

**It is also self-checking.** A claim whose origin you cannot name is a claim you did not verify, and
writing the sentence is where you find that out.

### The shape this catches

A brief claim with a bare number and no origin:

> …contains fifteen `\texttt` spans in total, so the audit's 169 references cannot be prose.

The same claim written to contract names what produced it — *"a `grep -c '\texttt{'` over
`papers/<bundle>/paper_draft.tex` counts fifteen"* — and the flaw becomes visible while writing,
because a raw-token grep is exactly what the discipline below says not to trust.

*Why this example and what it cost:
[`docs/WAVE_PIPELINE_RATIONALE.md`](../../../../../../docs/WAVE_PIPELINE_RATIONALE.md)
§ "Stage 10 — why a dispatch brief must name each claim's origin".*

---

## Where each claim class must come from

| the brief claims… | derive it from | never |
|---|---|---|
| a theorem exists, or says X | its **statement**, read via the `lean4` skill and `lean-lsp` tools | a grep for the name; a docstring; a metadata `claims` string |
| a declaration is absent | `lean/lean_deps.json` — the build authority | a `lean_local_search` miss, which returns empty for built declarations, silently |
| a theorem is strong enough to back a claim | its **carrier types**, unfolded to Mathlib or a real construction | kernel-purity plus an unconditional statement, which a posit also satisfies |
| the substrate's state | the owning `docs/roadmaps/Phase*` and the module's `git log` | the manuscript, the charter, or `bundle_metadata.json`, all of which predate later waves |
| a source says X | the source text at page level, from `Lit-Search/Phase-*/primary-sources/` | an abstract, a DOI record, or a `.json` metadata cache |
| we hold a source | the citation registry's **held** state (ADR-014) | the presence of a file named for the bibkey |
| a count, ratio or population | the command that produced it, quoted | a number carried from another document, including one you wrote |
| a gate's state | a run of that gate, on `main` if the worktree cannot run it | its name, or a remembered result |

A claim you cannot source is not forbidden — **mark it.** `⚠️ UNVERIFIED:` in front of it tells the
agent to establish it before relying on it, which is a cheap and honest instruction. What is
forbidden is an unmarked claim with no origin, because it is indistinguishable from a verified one.

---

## Sections a brief carries

Vary the prose; do not drop a section. Each exists because its absence was paid for.

1. **Target and workspace** — bundle, section or full redraft, worktree path, branch. Absolute paths
   throughout: `paper-drafter` holds no `Bash`, and a worktree cannot see gitignored state.
2. **Why this dispatch exists** — what is being redone and what standing the prior state has. A
   bundle reading *zero open findings* is the most dangerous start, not the safest: it can mean a
   passed review rather than a clean one.
3. **Settled context** — what this campaign already decided, so the agent does not re-derive it, each
   with its origin. Say plainly where a question is **open**, and that reporting evidence is wanted
   while a verdict is not.
4. **The override rule** — assemble incrementally. Write each section into the draft as it is ready
   and commit as you go; never accumulate for a final integration. A lead that runs low commits what
   exists. Two leads that analysed to the end of their runway shipped no manuscript.
5. **Verification discipline** — the table above, scoped to what this bundle actually leans on.
6. **The contradictions requirement** — verbatim, and in the report-back:
   *"End with CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES."* The sources win, the agent declines
   the instruction, and it says so. This is the instrument that detects a defective brief; it is not
   optional and not per-bundle.
7. **Findings format** — where to file, and that every `Verify` must have been executed and confirmed
   failing at HEAD.
8. **Git discipline** — explicit paths only. Never `git add -A`, `git add .`, or `git commit -a`; the
   repository is shared with concurrent agents.
9. **Report back** — sections written, commits, compile result, every theorem cited with its actual
   statement, findings filed, the contradictions section, and anything left undone, stated plainly.

---

## Reading the report back

The contradictions section is the contract's own instrument, and it separates two outcomes:

- a contradiction against a claim **whose origin the brief named** — the origin was misread, or the
  artifact changed. The contract worked and the brief was wrong anyway; correct the claim.
- a contradiction against an **unsourced** claim — the contract was not followed. This is the failure
  mode, and it is the one to count.

⚠️ The section lives in the **returned report**, not in the bundle's filed findings. Scanning
`papers/AutomatedReviews/<date>-<slug>/<bundle>.md` for it measures the wrong artifact.

---

*Owning decision: [ADR-011](../../../../../../docs/adrs/ADR-011-manuscript-quality-layer.md) §C6,
§D5, Phase 9. The law naming this file as owner: `docs/WAVE_EXECUTION_PIPELINE.md` § Stage 10.*
