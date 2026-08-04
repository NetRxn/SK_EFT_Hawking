# QA / QI Infrastructure Map

**Status:** production artifact. First map of the complete quality layer — code, agents, hooks, artifacts,
gates, and human decision points.
**Date:** 2026-08-03.
**Basis:** `scripts/validate.py` read in full (7,778 lines at read time) by the author; four read-only
reconnaissance sweeps over the artifact-generation, readiness/bundle, agent/hook/register, and
test-coverage subsystems; **every load-bearing claim independently verified against source by the author.**
Where a reconnaissance claim did not survive verification it is marked and corrected in §8.

**Companion documents:** [ADR-009](../adrs/ADR-009-validation-suite-modularization.md) (the validation-suite
decision) · [ADR-004](../adrs/ADR-004-substrate-integrity-gates.md) (R1–R5) ·
[ADR-002](../adrs/ADR-002-native-decide-policy.md) · [ADR-005](../adrs/ADR-005-derived-proof-atlas.md) ·
[ADR-007](../adrs/ADR-007-kernel-nogo-ledger-and-negative-frontier.md) ·
`docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md`.

> **How to read this map.** The system is genuinely well-designed in its *architecture* and substantially
> broken in its *wiring*. Section 6 is the important one: it separates what **actually blocks** from what
> **reads as blocking**. If you take one thing from this document, take that table.

---

## 1. The five planes

```mermaid
flowchart TB
    subgraph S["① SOURCES"]
        LEAN["lean/SKEFTHawking/**.lean<br/>2,039 files"]
        PY["src/**.py<br/>formulas · constants · provenance · citations"]
        TEX["papers/*/paper_draft.tex<br/>64 drafts / 21 bundles"]
        NB["notebooks/*.ipynb"]
    end

    subgraph G["② GENERATION — derived artifacts"]
        ED["ExtractDeps.lean<br/>→ lean_deps.json (70MB)"]
        CNT["update_counts.py<br/>→ counts.json / counts.tex"]
        ATL["atlas_view.py<br/>→ atlas_view.json"]
        BG["build_graph.py<br/>→ graph {nodes, links}"]
        PG[("Postgres + AGE<br/>sk_eft")]
    end

    subgraph V["③ VALIDATION — mechanical"]
        VAL["validate.py — framework<br/>registry · order · CLI · re-exports"]
        VCK["validation/checks/*.py<br/>59 checks · 11 modules"]
        GI["graph_integrity.py"]
        RG["readiness_gates.py<br/>11 gates × N papers"]
        BR["bundle_readiness.py<br/>→ heatmap + metadata counts"]
    end

    subgraph R["④ REVIEW — LLM agents"]
        FR["figure-reviewer<br/>Stage 9"]
        CR["claims-reviewer<br/>Stage 10"]
        AR["adversarial-reviewer<br/>Stage 13"]
        RF["ReviewFinding nodes<br/>→ FLAGS edges"]
    end

    subgraph H["⑤ HUMAN"]
        DASH["provenance dashboard<br/>:8050"]
        HEAT["heatmaps · registers<br/>QI · System-2"]
        DEC(["10 decision points<br/>§5"])
    end

    LEAN --> ED --> CNT & ATL & BG
    PY --> BG & CNT
    TEX --> BG
    BG --> PG & GI & RG
    RG --> BR
    ED & CNT & ATL & BG --> VCK
    GI & RG & BR --> VCK
    VCK --> VAL
    TEX --> FR & CR & AR
    NB --> VCK
    AR & CR --> RF --> BG
    VAL --> HEAT
    BR --> HEAT
    BG --> DASH
    HEAT & DASH --> DEC
    DEC -.->|"ratify · promote · close"| PY & TEX

    classDef broken stroke:#c0392b,stroke-width:3px
    class VCK,RG broken
```

Red-outlined nodes carry the enforcement defects in §6.

> **Plane ③ was split by ADR-009 Phase 2 (complete 2026-08-03).** `scripts/validate.py` was a single
> 7,900-line file when this map was first written. It is now **720 lines of framework** — result-type and
> check re-exports, the `_CHECKS` registry, `_CANONICAL_ORDER`, `run_checks`, reporting, the CLI, and
> `BUNDLE_CODES` for the roster gate — with **all 59 check bodies** in eleven modules under
> `scripts/validation/checks/`, none over ~1,080 lines, each readable in one pass:
>
> | module | checks | | module | checks |
> |---|---|---|---|---|
> | `lean_substrate` | 9 — R1–R3 substance gates | | `papers_prose` | 6 — prose vs the numbers |
> | `lean_toolchain` | 7 — build + trust surface | | `prose_lean_refs` | 2 — do cited names resolve |
> | `citations` | 4 — provenance + primary sources | | `bundles_readiness` | 6 — metadata · gates · roster |
> | `freshness` | 6 — the artifact regenerators | | `reviews` | 4 — the supersession ledger |
> | `physics` | 9 | | `graph_atlas` | 3 |
> | `notebooks` | 3 | | | |
>
> Shared layers: `validation/_registry.py` (result types + registry), `_config.py` (the three runtime
> flags), `_tex.py` (LaTeX scanning), and `scripts/validate_helpers.py` (the single path anchor). Each has
> **one owner, reached by attribute at call time** — never imported by value, which is what makes a flag or
> a monkeypatched path actually reach the check that reads it.
>
> **Nothing here changes what any check measures.** Verified against a baseline taken before any Phase-2
> work: **48 of 49 characterized checks byte-identical**, the sole difference being `graph_integrity`'s
> node count, which moves by exactly the 13 guard tests the migration added. §6's enforcement reality is
> therefore unchanged by the split — the semantic fixes are **Phase 3** (ADR-009 §Deferred), still pending,
> and §7's pattern is still live.

---

## 2. Artifact generation — writers, triggers, staleness keys

Every derived artifact, its sole writer, and how staleness is detected. **Staleness key is the load-bearing
column:** content-hash and content-compare are sound; mtime is weaker; *none* means drift is undetectable.

| Artifact | Writer | Staleness key | Auto-synced? |
|---|---|---|---|
| `lean/lean_deps.json` (70 MB) | `extract_lean_deps.py` | **content hash** of `**/*.lean` → `.hash` | yes (E1) |
| `docs/counts.json` / `.tex` | `update_counts.py` | mtime vs sources | yes (E2) |
| `papers/*/tables/*.tex` | `render_paper_tables.py` | mtime | yes (E3) |
| Inventory-Index autogen blocks | `update_inventory_index.py` | **content compare** | yes (E4) |
| `lean/atlas_view.json` | `atlas_view.py` | **content compare** (rebuilds) | yes (E5) |
| `docs/ATLAS_HEATMAP.md` | `atlas_heatmap.py` | **content compare** | yes (E6) |
| `lean/SKEFTHawking/KernelNoGos.lean` | `gen_kernel_nogos_module.py` | **content compare** | yes (E7) |
| `papers/claim_clusters.json` | `cluster_detect.py` | mtime | via check only |
| `docs/PERMANENT_TRACKED_HYPOTHESES.md` | `render_tracked_hypotheses.py` | content compare, **hard-fail, never auto-written** | no |
| `papers/cluster_bundle_index.json` | `bundle_clusters.py` | **none** | **no** |
| `docs/BUNDLE_READINESS_HEATMAP.md` | `bundle_readiness.py` | **none** | **no** |
| `docs/QI_REGISTER.md` | `qi_register.py` | **none** — *re-parses its own Closed Items* | **no** |
| PG + AGE `sk_eft` | `build_graph.write_graph_to_pg` | **none** (full delete + rewrite) | opt-in only |
| `figures/provenance_graph.json` | `build_graph --out` | **none** | **no — ~4 months stale** |

**Concurrency.** `harness_lock.regen_lock` is **skip-and-use-cache, never block-and-wait**: 5 s bounded poll,
then yield `False`. On skip, `load_lean_deps()` silently returns the stale 70 MB file, and downstream
generators write `counts.json` / `counts.tex` / `atlas_view.json` from stale input **and report success**.
The lock also fails *open* on any internal error. Only two real call sites take it; the suite's three
auto-regenerating checks (`counts_fresh`, `tables_fresh`, `claim_clusters_fresh` — now in
`validation/checks/freshness.py`) shell out **with no lock at all**.

**Cost.** `build_graph_json()` runs **4×** per validate run, and each run internally re-executes 16 node
extractors plus a full edge pass inside `extract_readiness_gate_nodes` (verified, `build_graph.py:2544-2601`)
to break gate↔graph recursion. Net **≈8 extraction passes and ≈20 parses of a 70 MB file per run**, ~15 s
per build. There is no shared graph handle.

---

## 3. The review pipeline — how a finding becomes a gate

```mermaid
flowchart LR
    A["adversarial-reviewer<br/>(opus)"] -->|writes| MD["papers/AutomatedReviews/<br/>&lt;date&gt;/&lt;paper&gt;.md"]
    MD -->|"_REVIEW_SECTION_RE<br/>heading parse"| EX["extract_review_finding_nodes"]
    EX -->|"status='open' at birth<br/>(unconditional)"| RFN["ReviewFinding node"]
    RFN -->|extract_flags_edges| FE["FLAGS → paper:X"]
    FE -->|"only consumer"| G11["Gate 11 FixPropagation"]
    G11 -->|"open ∧ severity ∈<br/>{critical,blocker,major}"| BL["state=blocked<br/>self-promotes to P1"]
    BL --> AGG["paper_aggregate_state<br/>→ RED"]
    AGG --> HM["BUNDLE_READINESS_HEATMAP.md"]
    LED["review_finding_supersessions.json<br/>870 entries, append-only"] -->|"status override<br/>+ blocking-closure bar"| EX

    D1(["⚠ dropped: no inferred<br/>paper OR bundle"]):::drop
    D2(["⚠ dropped: FLAGS target<br/>not in node_ids — silent"]):::drop
    D3(["⚠ dropped: heading outside<br/>the regex → 0 findings"]):::drop
    EX -.-> D1 & D3
    FE -.-> D2

    classDef drop fill:#fdecea,stroke:#c0392b,color:#7b241c
```

**Silent-drop points**, ranked by observed damage. (A sixth, outside this pipeline, was found and fixed
2026-08-03: `extract_python_test_nodes` keyed its id on `module::function` with the class omitted and
deduped on it, dropping **66 of 4,416** test nodes — and those nodes are what feed the VERIFIES coverage
edges Gate 4 reads, so a dropped node took its formula-targeted edges with it.)

**The VERIFIES resolver was wrong in both directions at once**, and both are now fixed (ADR-009 §Deferred
item 7). Against the dropped nodes above, `extract_verifies_edges` *fabricated* Lean-targeted edges by
resolving the **tail** of a Python name against Lean short names — `np.all` → `FaultTolerance.Pauli.all`,
`v` (from `import validate as v`) → `EWMassMatrixInputs.v`. **144 of 536** Lean-targeted edges were
phantom; all 17 declarations that lost an edge lost every edge they had. Two rules now gate the branch: a
ref rooted at a **module alias** is a Python module, never a Lean declaration; and a **dotted** ref may
resolve only as a full Lean name, never by its tail. ⚠️ **Gate 4 was named as the victim and is not one** —
it reads `formula:` targets only, so it never saw these edges. The consumer that did is
`last_modified.py`'s VERIFIES propagation, which stamped an unrelated test file's mtime onto Lean nodes.
A worked example of the standing lesson in §9: *the named blast radius is a claim, not a measurement.*

1. A finding with neither `inferred_paper` nor `inferred_bundle` is dropped from bundle aggregation.
2. `_emit` is a **no-op when the FLAGS target is absent** from `node_ids` — no log. This produced the D11 false-green.
3. Ambiguous paper-key prefix → all edges skipped (info-level log only).
4. `papers/AutomatedReviews/*/*.md` is a **one-level glob**; a review filed deeper is invisible.
5. A finding heading outside `_REVIEW_SECTION_RE` mints **zero** nodes — a whole round of blockers reads exactly like a clean round. (Partially guarded, post-hoc, by `review_docs_mint_findings`.)

**Gate 11 is the only evaluator that reads FLAGS.** Every other gate is blind to review findings.

---

## 4. The 11 readiness gates

| # | Gate | P | Can block? | What it actually computes |
|---|---|---|---|---|
| 1 | CitationIntegrity | 1 | ✅ | `\bibitem{}` keys ⊆ `PrimarySource` nodes. **Registry coverage only** — no DOI/title/author match, contra its doc |
| 2 | CrossPaperConsistency | 1 | ✅ | `CONTRADICTS` edges; cross-paper `REPORTS` value disagreement → `needs-recheck` |
| 3 | ParameterProvenance | 1 | ✅ | every `DEPENDS_ON → param:*` has `human_verified_date` |
| 4 | ComputationCorrectness | 1 | ✅ | grounded formulas have a non-`{bounds,unknown}` `VERIFIES` edge |
| 5 | LeanProofSubstance | 1 | ✅ | cited theorems ∌ `PlaceholderMarker` |
| 6 | AssumptionDisclosure | 1 | ✅ | each consumed hypothesis appears as a lowercased substring of the tex (heuristic by design) |
| 7 | NarrativeGrounding | 1 | ✅ | every `interesting` ProseClaim has ≥1 `SUPPORTS` |
| 8 | ProductionRunHealth | 1 | ✅ | linked runs not failed; MC-evidence prose needs a successful run |
| 9 | NumericalFreshness | 2 | ❌ | stale `REPORTS`, inline literals, table mtimes → **only ever `needs-recheck`** |
| 10 | FirstClaimVerification | 2 | ❌ | counts `first-claim` tags; the ledger node type **does not exist** |
| 11 | FixPropagation | 2→**1** | ✅ | open blocking findings; **self-promotes to P1 when blocking** |

**`evaluate_all_gates` converts any evaluator exception into `state='open'` — never `blocked`.** A crashing
gate is indistinguishable from a clean one. `READINESS_GATES.md` documents gates 9 and 10 as blocking; they
cannot.

---

## 5. Human decision points

Ten places a human actually decides. Six are structurally enforced as human-only
(`disable-model-invocation: true`, or a tier clamp an agent cannot lift).

| Decision | Surface | Human-only enforcement |
|---|---|---|
| Arm a `/goal` loop | `/skeft-qa:goal-prompt` | **structural** |
| Promote System-2 finding → `human-reviewed` | `/skeft-qa:debrief` | **structural** (`_clamp_tier` caps every other writer at `agent-reviewed`) |
| Close / misfile a System-2 finding | `/debrief` | **structural** — `## Misfiled` reachable only here |
| Integrate a process win into the harness | `/debrief` | per-win sign-off; *"self-improving, never self-mutating"* |
| Graduate a finding → standing pre-decision | `/debrief` → `PRE_DECISIONS.md` | **structural** |
| Sign off a structural-prevention proposal | `/debrief` | never auto-applied |
| Close a QI item (System-1) | `QI_REGISTER.md` block move | Invariant #13 preserves Closed Items verbatim |
| Approve a new project-local `axiom` | Invariant #15 + `AXIOM_METADATA` | policy + `axiom_closure_allowlist` |
| Toggle the AskUserQuestion guard | `/skeft-qa:goal-guard` | **structural** |
| Verify a parameter for submission | provenance dashboard | Invariant #8 |

**Inside a `/goal` loop the human is deliberately absent**: the AskUserQuestion guard denies, logs to
`blocked_questions.jsonl`, and redirects to the `coach` agent. The question reaches a human only
asynchronously via harvest → System-2 register → `/debrief`.

---

## 6. Enforcement reality — what actually blocks

**This is the section that matters.** The architecture implies far more enforcement than exists.

```mermaid
flowchart TB
    subgraph BLOCKS["✅ ACTUALLY BLOCKS"]
        PC["pre-commit, on main only:<br/>leak guard · notebook exec ·<br/>formula_grounding ·<br/>placeholder_not_cited ·<br/>native_decide_regression"]
        HARD["validate.py hard-failing checks<br/>(~49 of 59)"]
        EG["web-egress guard<br/>FAIL-CLOSED, 2 layers"]
    end
    subgraph SOFT["⚠ REPORTS, NEVER BLOCKS"]
        AP["8 always-pass checks incl.<br/>readiness_submission_gate<br/>paper_latex_compiles<br/>paper_toolchain_pin_drift"]
        ST["2 --strict-only gates —<br/>nothing passes --strict"]
        S14["Stage 14 QI — advisory by design"]
    end
    subgraph NONE["❌ CLAIMS ENFORCEMENT, HAS NONE"]
        T1["AI-DEFENSE Tier 1:<br/>both named scripts ABSENT"]
        T2["8 of 9 named Tier-2 checks<br/>never written"]
        S9["Stage 9 verdict —<br/>no machine reader"]
        SS["stage9/stage10_status —<br/>read by nothing"]
    end
    classDef ok fill:#eafaf1,stroke:#1e8449
    classDef warn fill:#fef9e7,stroke:#b7950b
    classDef bad fill:#fdecea,stroke:#c0392b
    class PC,HARD,EG ok
    class AP,ST,S14 warn
    class T1,T2,S9,SS bad
```

### The three tiers, concretely

**Blocks.** The commit gate runs exactly **three** validate checks and only hard-blocks on `main`; it exits
0 in a worktree, on missing `uv`, and on any check crash. `.git/hooks/pre-commit` is local-only and
uncommitted, so **a fresh clone has no mechanical gate at all.** The web-egress guard is the one
unambiguously fail-closed control in the system.

**Reports but never blocks.** Eight checks were structurally incapable of returning `passed=False`.
**Four remain, all four deliberately advisory with a stated reason** (`elaboration_knob_watchlist`,
`paper_toolchain_pin_drift`, `viz_consistency`, `inventory_index_autogen_fresh` — dispositioned
individually in ADR-009 §Deferred item 3). Of the four that were defects: `paper_latex_compiles` computed
its verdict and discarded it (**measured: D3 fails with 2 fatal LaTeX errors**), and `count_literals` /
`numerical_literals` were WARN-only pending a retrofit whose target — "all 15 papers" — receded as the
corpus grew to 64; both are now ratchets. And — `readiness_submission_gate` was repaired 2026-08-03 (ADR-009 Phase 3 item 1) and now
hard-fails when any paper has a blocked gate. It had been **inverted**: failing only when *zero*
`ReadinessGate` nodes existed and passing when it measured RED, marked only by an inline
`# WARN not FAIL during rollout`, with a `--strict` path its docstring promised and the body never
referenced. Measured at repair: **61 of 64 papers RED, verdict `True`** — which is why 14 bundles sat at
`stage13_status: green` with open blockers. It now reports RED as RED, and `validate.py` fails on it by
design.

**Claims enforcement, has none.** `docs/AI-DEFECT-DEFENSE-LAYER.md` names
`scripts/pre_commit_hook.sh` and `scripts/install_pre_commit.sh` as its Tier-1 implementation. **Verified:
both absent.** Of its nine named Tier-2 checks, one is registered. Pipeline Invariant #16 cites the document
as canonical — under a filename that is also wrong.

### Test protection over the gates themselves

| | at first mapping | now |
|---|---|---|
| Checks with a test that would **fail on a seeded defect** | **5** of 59 | **5** of 59 — unchanged |
| Checks tested only by `assert result.passed` on the live tree | 11 | 11 |
| Checks with **no test at all** | 37 | 37 |
| Tests asserting the check **count or registration order** | **0** | **25** (three suites) |

A check rewritten to `return CheckResult(passed=True, details=[])` still passes all eleven green-only tests.

**What ADR-009 Phase 0–2 did and did not change here.** The per-check number is *deliberately* unchanged: the
25 new tests protect the **framework and the migration contract**, not the check bodies. They freeze the check
count and registration order, assert that `_CANONICAL_ORDER` covers every registered check and that the sort
runs after the last registration, prove each runtime flag reaches the checks that read it, forbid a check
module from deriving a path from `__file__` or aliasing one by value, hold `validate.py` to one module
identity, and freeze the 54-name external surface. Every one is mutation-verified in both directions.

That is the migration's safety net, and it is not test coverage of the checks themselves. **Raising the
per-check number is D5's standing obligation** — every new or modified check ships a mutation test — and it
is the work that closes the §7 pattern. The split makes it tractable (a domain module fits in one read); it
does not perform it.

---

## 7. The systemic pattern

Six independent mechanisms, one shape: **absence of measurement rendered as success.**

| Mechanism | Reports | Actually |
|---|---|---|
| ~~`readiness_submission_gate`~~ | ~~pass~~ | **FIXED 2026-08-03** — hard-fails on any blocked gate; 11 tests, 5 mutations |
| ~~`paper_latex_compiles`~~ | ~~pass~~ | **FIXED 2026-08-03** — hard-fails on a real compile failure; D3 was failing silently |
| `check_bundle_source_freshness` | "fresh: all N source paper(s)…" | returns `None` for sourceless keys, compares zero files, **writes `freshness_stale: false`** |
| `evaluate_all_gates` | `open` | any evaluator exception |
| `harness_lock` on contention | "regenerate: succeeded" | wrote derived artifacts from stale input |
| AI-Defense Tier 1 | documented as implemented | files do not exist |

**One of the six is now closed, and the shape of the fix is the template for the rest:** the verdict must
be *derived* from what the check measured, never asserted alongside it. In every remaining row the check
computes the right answer and then discards it.

The type system permits it: `CheckResult.passed` is a bare `bool` with no `UNEVALUATED` state. The concept
exists in three hand-patched sites whose comments state the principle exactly — *"a readiness guard that
cannot load its own dependency reports 'no disagreement found' — indistinguishable from agreement"* — but
it does not exist in the types.

---

## 8. Claim lineage — the Class-1 detector

A fifth subsystem sits alongside the four above: **chain-of-backing**, which resolves every claims-reviewer
sentence link against the live graph. `scripts/chain_canonicalize.py --report` is its instrument.

Whole corpus, 2026-08-03: **3,442 links — 87% resolved, 121 `theorem-absent`, 112 `invalid-target`,
84 `formula-absent`.**

`theorem-absent` means **a manuscript sentence names a Lean theorem that does not exist**. Root-caused:
**~71 genuine, ~50 artifact.** The artifact half falls in four individually-fixable classes — kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) that have no graph node though the claims-reviewer spec
instructs agents to emit them; `module:` prefix double-mangling; by-design inductive-constructor filtering;
and mis-tagged link kinds.

Two of the genuine cases are severe:

- **A discharged axiom is still cited 15×.** `gapped_interface_axiom` was retired 2026-05-19; the project's
  axiom count is 0.
- **A theorem commented out as FALSE is still cited 5×.** `gap_solution_bounded` sits at
  `TetradGapEquation.lean:308-325` under the note *"This theorem is FALSE as originally stated."*
  (One of the five is a documented waiver: I1 cites it deliberately as history.)

Per-bundle, the instrument also **ranks** severity. D7 is the only bundle with more absent than resolved
links (15 vs 12). F and I3 have **zero links at all** — the flagship has no chain-of-backing whatsoever.
D6 and D9 have no `claims_review.json`, so Stage 10 never ran for them.

**Nothing gates on any of this.** The instrument exists, produces the right answer, and is connected to
nothing that can stop a submission — the §7 pattern, in the subsystem built to detect exactly that pattern
in the papers.

---

## 9. Provenance and scope

**Basis.** `scripts/validate.py` read in full by the author — 7,778 lines on 2026-08-03, and again at 7,900
after the `stage13_status` guard landed; four read-only reconnaissance sweeps over the artifact-generation,
readiness/bundle, agent/hook/register and test-coverage subsystems; every load-bearing claim re-verified
against source before entering this map. Line citations are anchored to that read — see the offset note in
ADR-009.

⚠️ **Those line citations are being invalidated by ADR-009 Phase 2**, which is moving the check bodies into
`scripts/validation/checks/*.py` (see the note under §1). A citation of the form `validate.py:NNNN` for a
CHECK BODY should now be read as "the check named X", and located by name in its module; citations for the
framework (registry, `run_checks`, reporting, CLI, `main`) still resolve in `validate.py`. The behaviour
those citations describe is unchanged — every phase boundary is verified `CHARACTERIZATION HELD`.

**Audit trail.** How each claim was established, which reconnaissance findings were rejected, and the
author's own corrected measurements: `.working-docs/qa-qi-map-verification-log.md`.

⚠️ **Standing lesson — a filed finding's blast radius is a claim, not a measurement.** ADR-009 §Deferred
item 7 was filed with a count (10), a consumer (`ComputationCorrectness`), a function name
(`extract_test_verifies_edges`) and an effort estimate ("one line"). Re-measured at the fix, **all four
were wrong**: 144, `last_modified.py`, `extract_verifies_edges`, and two independent rules neither of
which catches the other's cases. Nothing had drifted — the entry was written from a sample and never
summed. Every finding in this map and in ADR-009 §Deferred carries the same risk, so **re-measure the
scope before fixing, even when you wrote the finding yourself.** The fix is only as good as the partition
it rests on, and a partition inherited from prose is not a partition.

**Out of scope, verified non-overlapping.** The Codex control plane (`scripts/lean_slots/*`, `.codex/*`,
ADR-008) has **zero references** to `validate.py`, `register_check`, `gate_precheck`, `bundle_readiness`, or
`build_graph`. Parked in `.working-docs/tangential-items.md`.
