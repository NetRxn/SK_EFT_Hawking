# Holistic architectural assessment — QA / validation infrastructure

**Date:** 2026-08-06 · **Branch:** `infra/adr-009-validation-modularization`
**Mode:** READ-ONLY. No tracked file was modified. The only file written is this one.
**Ground truth measured at audit time:** 62 registered checks · 12 check modules · 21 bundles ·
64 paper drafts · 7 `PRODUCTION_SEEDED` checks · 47k graph nodes.

> ⚠️ **The tree moved under this audit — re-verify apex/closure numbers before acting.**
> Started at `92ac6b28` clean; ended at `f2bbe53d` with `papers/L2/bundle_metadata.json` and
> `scripts/validation/checks/bundles_readiness.py` dirty. Two ADR-010 apex retrofits landed
> mid-pass (`2c300780` D6, `f2bbe53d` D9) and `UNDECLARED_APEX_CEILING` moved 21 → 20 → (L2 in
> flight). Values are tagged **(HEAD@92ac6b28)** or **(live)** where it matters.

---

## 1. Verdict

**The measurement layer of this infrastructure is genuinely excellent and the defect that
remains is concentrated in one place: the graph edges the readiness gates stand on.** The
`measured` field, the cannot-measure baseline, the production-seeding ratchet, the memo's four
structural guards, the `--scope`-never-narrows-the-population discipline, and the
`readiness_verdicts_agree` cross-instrument — these are the work of someone who understood
"absence of measurement rendered as success" and closed it properly at the check layer.
**But two P1 readiness gates query edge types that no extractor emits**, and the consequences
are the signature defect in its purest live form: `ProductionRunHealth` reports PASS across a
graph holding **17 failed production runs**, because `PRODUCES` is emitted by nothing and
`relevant_runs` is therefore always `[]`. That is not a latent hazard — it is happening on
every run today, inside the gate set that decides submission readiness. Everything else is
second-order: a well-executed measurement discipline whose *guards* are hand-enumerated
populations (`RATCHETED_CHECKS`, `sync_manifest.EDGES`, `extract_all_edges_without_gates`, the
H1 `__file__` scan scope) that a new instrument silently escapes, plus one substantive
un-gated invariant (zero `sorry`). On the operator's specific worry — "many ways to do the same
thing" — the answer is **three real duplications and a lot of correctly-argued splits**; the
codebase is unusually good at documenting *why* a split exists, and most of what looks like
duplication is deliberate cross-instrumentation.

**Counts:** 2 CRITICAL · 6 HIGH · 8 MEDIUM · 7 LOW confirmed defects · 5 design tensions ·
3 HIGH + 3 lower plugin drifts · 16 documentation defects.

---

## 2. Duplication map

### 2a. Real duplication — recommend consolidation

| # | Job | Mechanisms | Recommendation |
|---|---|---|---|
| **DUP-1** | "is this derived artifact stale?" | **Seven mechanisms, three different physics.** (i) `sync_manifest.EDGES` (7 artifacts) — **content-compare** (`_atlas_view_stale:75`, `_atlas_heatmap_stale:93`, `_kernel_nogos_module_stale:109`) or source-hash (`_lean_deps_stale:32`); (ii) `counts_fresh` / `tables_fresh` / `claim_clusters_fresh` / `inventory_index_autogen_fresh` — **mtime**; (iii) `_H.ensure_lean_deps_fresh` — SHA-256 of `.lean`; (iv) `_memo` fingerprints — content hash; (v) `notebook_exec` skip-cache; (vi) `paper_latex_compiles` per-draft hash; (vii) `check_bundle_source_freshness.py` — source-dir **mtime**. | **The project already knows which idiom is sound and is not using it where it matters.** `_config.CI_SKIP` states in writing that the three mtime regenerators read STALE on every fresh clone — i.e. 3 of the validate-side freshness checks are *documented as unsound in one environment* while `sync_manifest` holds a correct content-compare for the same artifact class. Converge (ii) onto (i). Keep (iii)–(vi): different keys, different bypasses, a real split. |
| **DUP-2** | per-paper GREEN/YELLOW/RED verdict | **Four rules, three live.** `readiness_gates.paper_aggregate_state:862` (**dead** — zero production callers, yet its module docstring `:27` presents it as canonical, and the docstring does not describe what the function does); `bundles_readiness.classify_readiness:552` + `partition_readiness:584` (the live one, used by `readiness_submission_gate:652`); `provenance_dashboard._classify_paper:5194` + `_paper_gate_list:5202` (an independent third implementation that **synthesizes a missing gate as `open`**, which the other two never do). | **Consolidate onto `partition_readiness`; delete `paper_aggregate_state`.** Divergence proven: for a paper with 10 `passed` gates and one `'in-review'` (a legal `GateState`, `readiness_gates.py:54`), the three rules return `green` / `YELLOW` / `YELLOW`. The dashboard's synthesize-missing-gate behaviour additionally makes it disagree on any partial extraction. |
| **DUP-3** | "which extractors build the graph?" | Four hand-maintained parallel lists: `extract_all_edges:3957` (21) vs `extract_all_edges_without_gates:2790` (17); `extract_all_nodes:2894` (20) vs the inline `pre_nodes` in `extract_readiness_gate_nodes:2748` (15). | **Consolidate** — `without_gates` should be `extract_all_edges` minus an explicit exclusion set. See DEF-5. |
| **DUP-4** | kernel purity / `sorry` detection | `atlas_view.py:43,59,73` (`KERNEL_AXIOMS`, `_has_sorry`, `_is_kernel_pure`) vs `src/core/aristotle_submit.py:84,171,183` (independent duplicates; `_SORRY_TOKENS = ("sorryAx", "sorry")` — a **different predicate**). | Consolidate onto one owner. Divergence is latent: measured 0 records today whose core axioms contain `"sorry"` but not `"sorryAx"`. |
| **DUP-5** | the gate roster | `readiness_gates.GATES:814` (11) vs `provenance_dashboard.GATE_DEFS:5140` (a hand-copy). The dashboard's own comment `:5136` says it was centralized to stop *two JS copies* — it is now a fourth copy, and it sits **outside** `_ROSTER_CONSUMERS` (`bundles_readiness.py:813`), the mechanism that exists precisely to stop roster refragmentation. | Add it to `_ROSTER_CONSUMERS` or derive it. |
| **DUP-6** | parameter readiness | Gate 3 `ParameterProvenance` (`readiness_gates.py:232`, from graph `DEPENDS_ON` edges) vs `provenance_dashboard.py:584-634` (prefix-matching `PARAMETER_PROVENANCE` keys against `meta['platforms']`). Same notion, **entirely different inputs**, no cross-check. | Cross-check or consolidate. |

### 2b. Apparent duplication that is a real, justified split — keep both

- **`validate.py` re-exports vs `validation/_registry`, `_config`, `_tex`.** Binds the *same*
  objects (`_CHECKS` identity asserted in `test_validate_public_surface.py`); breaks a genuine
  import cycle. Documented, tested, correct.
- **`all_paper_drafts()` vs `bundle_drafts()`** (`validate_helpers.py:183, 191`). Two functions
  rather than one with a flag, deliberately — conflating them is how D10 shipped for a month
  outside the Lean-name-drift gate. Reasoning is written at `:176-181`. Keep.
- **`--strict` / `--ci` / `--scope`.** Three genuinely different consumers. `--scope` is
  exit-code-only and never narrows what runs (`validate.py:815-824`, pinned by
  `test_ci_mode.py::TestScopeSubstrate`). Keep.
- **`aggregate_by_bundle` (finding-derived) vs `partition_readiness` (gate-derived).** This is
  *deliberate* cross-instrumentation — two subsystems computing a verdict from different
  inputs so a third instrument can compare them (`bundles_readiness.py:27-31`). The correct
  answer to duplication you cannot remove. The bug is not the split; it is the uncovered
  YELLOW band (DEF-4).
- **Two `evaluate_all_gates` invocations** (pre-gate graph in `build_graph.py:2774`, full graph
  in `bundle_readiness.py:307`) — a documented recursion break, not duplicated logic.
- **`lean/atlas_view.json` tracked snapshot vs live `build_atlas`** — reconciled by exact
  content compare (`sync_manifest.py:75-89`); measured **not stale** today.
- **`QI_REGISTER` (System-1) vs `SYSTEM2_REGISTER` (System-2)** — see §2e.
- **`HYPOTHESIS_REGISTRY → PERMANENT_TRACKED_HYPOTHESES.md`** and
  **`KERNEL_NOGO_REGISTRY → KernelNoGos.lean`** — the same fact in two places, done *right*:
  the second is a pure render and drift **hard-fails** (`tracked_hypotheses_fresh`,
  `sync_manifest.py:141`) rather than being silently rewritten. This is the pattern the three
  ungated prose registers (§2e) do not have.

### 2c. The ratchet idiom is **five idioms wearing one docstring**

A dedicated inventory of every `*_CEILING` / `*_BASELINE` / `*_ALLOWLIST` / `*_EXCEPTIONS`
constant (I spot-verified `RATCHETED_CHECKS`, `UNDECLARED_APEX_CEILING`,
`CANNOT_MEASURE_PASS_BASELINE` myself):

1. **Zero-headroom ratchet WITH a live down-force test** (10) — the genuine house idiom. The
   *code* is one-sided (`population <= ceiling`); the *test*
   (`tests/test_ratchets_have_zero_headroom.py:88`) supplies the second side by re-running the
   production check against the live tree and asserting `population == ceiling`.
2. **Zero-headroom ratchet with NO down-force test** (4): `PROVENANCE_UNRESOLVABLE_CEILING`
   (`src/core/constants.py:1442`), `LEGACY_DRAFT_LATEX_BROKEN_CEILING` (`:1453`),
   `_LEDGER_DANGLING_BASELINE` (`checks/graph_atlas.py:182`, defined *inside* a function body
   so it cannot even be imported or monkeypatched), `UNDECLARED_APEX_CEILING`
   (`checks/bundles_readiness.py:1019`). **Indistinguishable from category 1 by reading the
   source.** Correct today by hand; free to gain slack tomorrow. **The largest inconsistency
   in the inventory.**
3. **True two-sided ratchet in the code** (3): `AWAITING_CEILING`, `FIXTURE_ONLY_CEILING`,
   `CI_MIN_CHECKS_RUN` — asserted `== population`. All three live in `tests/`.
4. **Suppression sets** (6): `VACUOUS_STATEMENT_BASELINE`, `UNREACHABLE_MODULE_EXCEPTIONS`,
   `_ROSTER_LITERAL_ALLOWLIST`, `_PROSE_REF_ALLOWLIST`, `_PROSE_REF_WAIVERS`,
   `MODELING_ASSUMPTION_THEOREMS`. Only `CANNOT_MEASURE_PASS_BASELINE` has a stale-entry test;
   the rest accumulate dead names that pre-suppress future defects.
5. **Frozen literal population, exact equality** (4): `EXPECTED_CHECKS` (order-sensitive),
   `EXPECTED_SURFACE`, `PRODUCTION_SEEDED`, `RATCHETED_CHECKS`.

Plus one mode-gated ceiling (`BIBITEM_TITLE_DRIFT_CEILING`, inert outside `--strict`) and one
detection threshold that is not a ratchet (`_ROSTER_LITERAL_THRESHOLD`).

**Recommendation:** promote category 2 into category 1 by adding those names to
`RATCHETED_CHECKS`. For `bundle_apex_resolves` this is a **one-line change that works
verbatim today** — see DEF-8.

### 2d. Test-side meta-guards — do they overlap?

| Guard | Asserts | Overlap |
|---|---|---|
| `test_validate_registry_contract.py` | `EXPECTED_CHECKS` (62, ordered) == live registry; `_apply_canonical_order()` call position | None — its frozen copy deliberately does **not** import `_CANONICAL_ORDER` |
| `test_validate_public_surface.py` | `EXPECTED_SURFACE` (54); `_CHECKS` identity; no `__file__`-derived paths **in the package** | None with the above; scope gap = DEF-6 |
| `test_d5_mutation_obligation.py` | every check declares a D5 status; `AWAITING_CEILING`; `FIXTURE_ONLY_CEILING`; verified entries name a real test | None. `MUTATION_VERIFIED` is disjoint in purpose from `measured` |
| `test_cannot_measure_baseline.py` | the syntactic cannot-measure-PASS population; every self-declared skip carries `measured=False` | **Complementary and load-bearing** — the only thing keeping `measured` honest, which is what `--ci`'s floor and `_memo` both stand on |
| `test_ci_mode.py` | `CI_MIN_CHECKS_RUN` zero-headroom; skips visible + real; `--scope` partition total; commit-gate names registered | None |
| `test_ratchets_have_zero_headroom.py` | `population == ceiling` for 6 rostered checks | Overlaps the other two zero-headroom assertions **in concept only** — three files implement one idea three times because the constants live in three places |

**Is D5 coherent with `measured` and the CI coverage floor? Yes — and non-overlapping.**
D5 asks *"has anyone proved this check can fail?"*; `measured` asks *"did it look at anything
this run?"*; the floor asks *"did enough checks look at something?"*. The chain is sound and
`test_every_self_declared_skip_declares_measured_False` is the joint that holds it together.
Two seams have re-opened: DEF-9 (floor slack) and DEF-10 (a skip vocabulary escape).

### 2e. Registries — coherent separation, but three prose stores are ungated and have drifted

| Store | Writer | validate gate | Enumerated/derived |
|---|---|---|---|
| `KERNEL_NOGO_REGISTRY` (`constants.py:4052`, 45) | hand | **GATED hard** — `nogo_substrate_integrity`, `lean_statements.py:591-624` | enumerated |
| `HYPOTHESIS_REGISTRY` (48) | hand | **GATED hard** — `tracked_hypothesis_ledger:487`, `tracked_hypotheses_fresh:551` | population **derived** from Lean binder scan |
| `AXIOM_METADATA` (10) | hand | **GATED hard** — `atlas_integrity:378`, `axiom_closure_allowlist:488` | population **derived** from axiom closures |
| proxy/vacuity whitelists (26+21+48) | hand | **GATED hard** — `proxy_body_audit:456`, `placeholder_not_cited`, `vacuous_statement_audit` | population **derived** from Lean bodies |
| `bundle_registry.BUNDLES` (21) | hand, one file | **BEST-GATED IN THE REPO** — 3-leg `bundle_registry_consistency:835` incl. an AST walk for re-hardcoded rosters | enumerated once, **consumers derived** |
| review corpus + supersession ledger (1561 / 870) | agents | **GATED** — 4 checks in `reviews.py` | derived |
| `CITATION_REGISTRY` (652) | hand | GATED **from usage only** | entries nothing cites are unchecked |
| `PARAMETER_PROVENANCE` (206) | hand | **PARTIAL** — coverage loop (`citations.py:64-103`) enumerates `EXPERIMENTS`/`ATOMS`/`POLARITON_PLATFORMS`; **`GRAPHENE_PLATFORMS` (86 keys, 6 covered) is outside it** | enumerated loop |
| `FIGURE_REGISTRY` (137) | hand | **WEAK** — `bundle_figure_integrity:131` filters `if not fs.name.startswith(("d11_","d12_")): continue`; **36 `fig_*` functions have no registry entry at all** | enumerated |
| `ARISTOTLE_THEOREMS` (322) | hand | GATED entry→declaration only, ratcheted at 14 stale keys. **Nothing checks declaration→entry** | enumerated |
| **`docs/QI_REGISTER.md`** | script + hand | **UNGATED** — zero references in `validate.py`, `validation/**`, `sync.py`, `sync_manifest.py`, `gate_precheck.py`, `pre-commit-sync.sh` | mixed |
| **`docs/dev-loops/SYSTEM2_REGISTER.md`** | agents | **UNGATED and un-gateable** — gitignored (`.gitignore:115-116`) | enumerated |
| **`docs/dev-loops/SETTLED_FORKS.md`** (59 blocks) | human + agents | **UNGATED** — read at `lean_statements.py:631-644` in a Detail constructed `passed=True`, so it can never fail | enumerated |

**System-1 / System-2 separation is real in intent and in code** — disjoint record types,
disjoint stores, disjoint writers, a deterministic tier clamp capping agent writes at
`agent-reviewed` (`system2_register.py:53-62`), and **no code path where an S-1 record can
become an S-2 record or vice versa**. What has degraded is the prose half of each:

- `QI_REGISTER.md` is **dead**. Its header claims *"411 ReviewFinding nodes currently in the
  graph"*; the live count is **1561**. Header stamped 2026-04-28, last commit 2026-07-03.
  Nothing regenerates it, so it can rot indefinitely.
- **A third, undeclared "QI" namespace exists.** `scripts/validation/**` is annotated
  throughout with `QI-09`…`QI-34` (21 ids) that live in
  `docs/audits/2026-08-04-qa-qi-infrastructure/FINDINGS_REGISTER.md` and are **disjoint from
  `QI_REGISTER.md`'s 23 `qi-<slug>` ids**. Same label, same semantics, three stores, zero
  cross-references. `qi-parameterprovenance` / `qi-leanproofsubstance` / `qi-countfreshness` /
  `qi-citationintegrity` name the same failure classes the 2026-08-04 audit re-filed as
  `QI-09`/`QI-11`/`QI-15`/`QI-17`.
- **`SETTLED_FORKS.md` ↔ `KERNEL_NOGO_REGISTRY` overlap, unreconciled:** 11 fork_ids in both,
  34 registry entries with no prose block, and the advisory audit's predicate is
  `authored_by:\s*kernel-no-go` while **36 of 59 blocks carry no `authored_by:` line at all**.
  Two of the invisible ones announce a kernel no-go in their own heading
  (`## 2026-07-21 — K7 seam-cover interior hypothesis (KERNEL no-go)…`) and are not in the
  registry.

---

## 3. Confirmed defects

### CRITICAL

---

#### **CRIT-1 — `ProductionRunHealth`, a P1 submission gate, is vacuous: it queries a `PRODUCES` edge that no extractor emits, and reports PASS over 17 failed production runs.**

**Where:** `scripts/readiness_gates.py:590` — `produces = idx.outgoing(run['id'], 'PRODUCES')`.

**What I ran** (built the real graph and counted):
```
grep -c "PRODUCES" scripts/build_graph.py                     → 0
grep -rn "'PRODUCES'" --include=*.py scripts/ src/            → 1 hit, readiness_gates.py:590 (a READ)

uv run --no-sync python -c "... bg.build_graph_json() ..."
  ProductionRun nodes: 18
  PRODUCES edges: 0
  edges out of ProductionRun nodes (ANY type): 0
  failed-status runs: 17
```

**Mechanism.** `readiness_gates.py:585-591` builds `relevant_runs` by filtering
`ProductionRun` nodes on whether any `PRODUCES` edge targets one of the paper's claim nodes.
With zero such edges, `relevant_runs` is **always `[]`**. Therefore `failed` (`:593`) is always
`[]` and `success_runs` (`:598`) is always `[]`. The gate reduces to a single live branch — a
regex for the literal phrase `Monte Carlo evidence|MC evidence` in the draft (`:604`) — and
otherwise falls to `:616-618`: `r.state = 'passed'`, note `'no MC claim and no failed runs'`.

**Failure scenario — this is not hypothetical, it is the current state.** 17 of the 18
`ProductionRun` nodes in the live graph carry a non-`success` status. A P1 gate named
`ProductionRunHealth` reports PASS for every paper. This is *exactly* the finding the whole
branch exists to close — **absence of measurement rendered as success** — sitting inside the
gate set that `readiness_submission_gate` consumes to decide whether a paper may be submitted.

**Refutation attempted.** I checked whether `PRODUCES` is emitted under another name (searched
every edge-type string literal in `build_graph.py`: `DEPENDS_ON, BACKED_BY, ASSUMES, VERIFIES,
VERIFIED_BY, USES, USED_BY, SOURCED_FROM, REPORTS, PROVED_BY, MEMBER_OF, LOGGED_BY, IMPORTS,
HAS_FIGURE, GROUNDED_IN, FLAGS, DEPENDS_ON_AXIOM, CLAIMS_APEX, CLAIMS, CITES_THEOREM,
CITES_SOURCE, CITES` — no `PRODUCES`). I checked whether `ProductionRun` nodes carry the link
in `meta` instead — they carry **zero outgoing edges of any type**. I checked whether
`extract_all_edges_without_gates` merely omits it — no, neither list has an emitter.
`docs/KNOWLEDGE_GRAPH.md:155` and `docs/READINESS_GATES.md:145,147` both document `PRODUCES` as
if it exists, so the gap is infrastructure debt, not a typo.

**Severity: CRITICAL.** Live, in a P1 gate, in the exact defect class this system exists to
remove. Note the second-order damage in PLUG-2: the adversarial-reviewer agent is instructed
to query this same non-existent edge and to mint a **BLOCKER** when it finds nothing.

---

#### **CRIT-2 — `NarrativeGrounding`, a P1 gate, is structurally always-blocked for the same reason, and its evidence string is misleading.**

**Where:** `scripts/readiness_gates.py:533` — `supports = idx.outgoing(pc['id'], 'SUPPORTS')`.

**What I ran:**
```
grep -c "SUPPORTS" scripts/build_graph.py                     → 0
grep -rn "'SUPPORTS'" --include=*.py scripts/ src/            → 1 hit, readiness_gates.py:533 (a READ)
live graph: ProseClaim nodes: 465 ·  SUPPORTS edges: 0
            edges out of ProseClaim nodes (ANY type): Counter()   ← literally none
```

**Mechanism.** `supports` is always `[]`, so **every** `ProseClaim` tagged `interesting`
lands in `unsupported` (`:534-538`), and `:540-543` sets `state = 'blocked'`. The gate is not
measuring narrative grounding; it is measuring *"does this paper have ≥1 interesting
ProseClaim node"*. Its emitted evidence (`:539`) always reads `… 0 have SUPPORTS edges`.

**Failure scenario.** This one **fails closed** — false RED, the safe direction — which is why
it is CRITICAL-but-second. The damage is different: `NarrativeGrounding` is currently a
blocking P1 gate on **D5, D6, D8, D10** for a reason that is not the reason, and any operator
or reviewer who chases it will look for missing formal support that is not the actual defect.
A gate that is always red is a gate people learn to route around — and `s13-lean` exists
partly because gates in this state made plain `s13` unpassable for any wave.

**Note the honest sibling.** The `elif not interesting:` branch (`:544-563`) is a
*correctly-built* corroboration path added in PR-review pass 2 — it distinguishes "no
interesting claims" from "prose was never extracted" and returns `open` for the latter. The
defect is that the branch above it can never be reached with a clean verdict.

**Severity: CRITICAL** (same root cause as CRIT-1; fix them together).

---

### HIGH

---

#### **DEF-3 — Invariant #4 (zero `sorry`) has no `validate.py` gate.**

**Where:** absence. **What I ran:**
```
grep -rn "sorry" scripts/validation/checks/*.py
  → freshness.py:230        (a DISPLAY string inside a staleness-reason message)
  → lean_statements.py:577  (a sorryAx conjunct scoped to KERNEL_NOGO entries only)
  → papers_prose.py:87      (a PROSE-literal pattern)
  → nothing else.
grep -rn "sorry_declarations" scripts/ src/ tests/    → producers + renderers only
docs/counts.json → sorry_declarations: 0
ls .github                                            → No such file or directory
grep -rn "sorry" tests/*.py | grep "assert.*== 0"     → only tests/test_a1_ext.py:205 (a1-scoped)
```
`sorry_declarations` is computed at `update_counts.py:227` and rendered in five places
(`counts.tex` `\sorrycount` `:359`, `update_inventory_index.py:159`, `export_web_atlas.py:247`,
`provenance_dashboard.py:996`, `paper_tables/sources.py:385`). Nothing asserts it.

**Refutation attempted.** `check_lean_build` (`lean_toolchain.py:395-397`) asserts
`returncode == 0` — but in Lean 4 `declaration uses 'sorry'` is a **warning**, so `lake build`
exits 0 with sorries present. `atlas_view._has_sorry:59` classifies a declaration
non-kernel-pure, but `atlas_integrity`'s five legs assert *internal consistency of the view*,
not that the sorry population is empty. `axiom_closure_allowlist` gates the axiom allowlist;
`sorryAx` is not in it. I could not find a gate.

**Failure scenario.** A `sorry` lands. `lake build` exits 0. All 62 checks pass.
`counts.json` records it, `\sorrycount` renders it, the dashboard shows it — and every gate
stays green, including `gate_precheck s13`, the guard in front of an adversarial-reviewer
dispatch. The only mechanical objection is `scripts/pre-commit-sync.sh:80-88`, which greps the
`lake build` log — and that path is (a) skipped entirely if `lake` is not on PATH (`:76`),
(b) entered only when the staged diff touches `.lean` (`:73`), and (c) **warn-only unless
`BRANCH = main`** (`:86`). This branch is 140+ commits off `main`, so for its entire life the
sorry guard has printed `(off-main: warn only)`.

**Severity: HIGH.** *(Scope note: `counts.json` says 0 today. This is a claim about the gate,
not a claim that a `sorry` exists — see §7.1.)*

---

#### **DEF-4 — `readiness_verdicts_agree` covers the RED and GREEN rows and skips YELLOW; four bundles are simultaneously heatmap-YELLOW and gate-RED, and the check passes.**

**Where:** `scripts/validation/checks/bundles_readiness.py:479-481` (`if … != 'GREEN': continue`)
and `:505-507` (`if … != 'RED': continue`). No loop looks at YELLOW.
Producer asymmetry: `scripts/bundle_readiness.py:390` applies the blocked-P1 demotion **only
when `readiness == "GREEN"`** — so a bundle already YELLOW for finding-count reasons (`:374`,
`>5 open findings`) keeps a bare `"YELLOW"` display while `blocked_p1_gates` is non-empty.

**Measured live** (`bundle_readiness.py --json`, read-only, vs
`validate.py --check readiness_submission_gate`):

| bundle | `aggregate_by_bundle` | `partition_readiness` |
|---|---|---|
| **D8** | `YELLOW` — 0 blockers, 14 open advisories; `blocked_p1_gates = [LeanProofSubstance, NarrativeGrounding]` | **RED** |
| **E2** | `YELLOW` — 0 blockers, 21 open advisories; `blocked_p1_gates = [LeanProofSubstance]` | **RED** |

and `validate.py --check readiness_verdicts_agree` → **✓ PASS**, `0 disagreement(s)`.

**Failure scenario.** The publication heatmap — the human-facing artifact — renders D8 and E2
as YELLOW with no mention of a blocked P1 gate, while the submission gate calls them RED. The
check written to detect exactly that class of disagreement is structurally unable to see the
middle band. Synthetic recipe: ≥6 open minor findings, 0 critical/major, a recorded review,
≥1 blocked P1 gate.

**Refutation attempted.** The information is not *lost* — `blocked_p1_gates` is in the payload,
so `bundle_metadata_matches_graph` still compares it. And part of D8's signal is spurious
(`NarrativeGrounding`, CRIT-2). But `LeanProofSubstance` is a real gate on both bundles, and
the check's own comment at `:446-478` reasons at length about the *reverse* leg's unreachable
branch without ever noticing the middle band is uncovered.

**Severity: HIGH.**

---

#### **DEF-5 — Four hand-maintained parallel enumerations of graph extractors, already divergent by 8, under a docstring that names one exclusion.**

**Where:** `build_graph.py:3957` vs `:2790`; `:2894` vs `:2748`.
**What I ran** (AST diff of `.extend(extract_*)` calls):
```
extract_all_edges 21 · extract_all_edges_without_gates 17
  missing: extract_claims_apex_edges (:3980)   ← added by 92ac6b28, today
           extract_backed_by_edges   (:3983)
           extract_logged_by_edges   (:3984)
           extract_member_of_edges   (:3985)
extract_all_nodes 20 · gate pre_nodes 15
  missing: extract_module_nodes (:2900) · extract_sentence_nodes (:2923)
           extract_audit_event_nodes (:2924) · extract_claim_cluster_nodes (:2925)
           (extract_readiness_gate_nodes — this one IS the deliberate recursion break)
```
**The docstring is wrong about its own function.** `build_graph.py:2790-2793`: *"Extract all
edges **except** gate-derived IMPACTED_BY."* It omits four more.

**Refutation attempted.** I checked whether any evaluator reads the missing types.
`readiness_gates.py` reads only `CLAIMS, GROUNDED_IN, VERIFIED_BY, VERIFIES, FLAGS, REPORTS,
DEPENDS_ON, ASSUMES, SUPPORTS, PRODUCES, CONTRADICTS` and node types `Paper, PrimarySource,
ProseClaim, ProductionRun, PlaceholderMarker`. **So the divergence is latent today.** It is
HIGH because of *what* is missing: `BACKED_BY` is the sentence-level prose-audit edge and
`Sentence`/`ClaimCluster` are its nodes. The next readiness gate anyone writes about prose
backing will evaluate over an empty population and pass vacuously. It is also the exact
structural hazard that would silently desynchronize the two `evaluate_all_gates` invocations
that `readiness_verdicts_agree` cross-checks against each other — the defect shape moved into
the check's own inputs.

**Severity: HIGH (latent).**

---

#### **DEF-6 — The H1 `__file__`-anchor guard stops at the package boundary; 17 of 62 checks do their measuring outside it.**

**Where:** `tests/test_validate_public_surface.py:203-204` scans exactly `scripts/validate.py`
+ `scripts/validation/**/*.py`. Its docstring (`:196-200`) argues *"SCOPE GROWS WITH THE
PACKAGE"* — correct, and one step short.

**What I ran** (AST: registered checks importing a sibling `scripts/*.py` inside the body):
```
17 checks delegate into 11 siblings, every one re-deriving its own root:
  atlas_view.py:33 · build_graph.py:39 · bundle_closure.py:30 · bundle_readiness.py:76
  bundle_registry.py:62 · check_bundle_source_freshness.py:38 · graph_integrity.py:26
  render_tracked_hypotheses.py:19 · update_counts.py:38 (no .resolve() — unlike every
  other anchor in the repo) · update_inventory_index.py:65
```
The 17: `bundle_metadata_matches_graph`, `readiness_verdicts_agree`,
`readiness_submission_gate`, `bundle_registry_consistency`, `bundle_apex_resolves`,
`bundle_source_freshness`, `inventory_index_autogen_fresh`, `graph_integrity`,
`atlas_integrity`, `atlas_hypothesis_discipline`, `proxy_body_audit`,
`tracked_hypotheses_fresh`, `native_decide_regression`, `axiom_closure_allowlist`,
`recurrence_reopens_closures`, `review_severity_declared`, `review_docs_mint_findings`.

**Failure scenario.** The natural next refactor (`scripts/graph/build_graph.py` — ADR-009's own
direction of travel) shifts one of these by a directory. `PROJECT_ROOT` becomes `scripts/`;
every artifact lookup misses; the delegating checks take their absent branch. Several of those
branches are on the sanctioned PASS list — `axiom_closure_allowlist` has **two** entries in
`CANNOT_MEASURE_PASS_BASELINE`. Green suite, nothing measured, and the guard written to prevent
exactly this cannot see it.

**Severity: HIGH (latent, one refactor away).**

---

#### **DEF-7 — `--ci`'s coverage floor — the instrument built to stop this defect class at the CI layer — has no caller. There is no CI.**

**Where:** `_config.py:108-124` (`CI_MIN_CHECKS_RUN = 58`), `validate.py:782-813`,
`tests/test_ci_mode.py` (338 lines of guard).
**What I ran:** `ls -a` → no `.github`, no CI config at any depth ≤ 2; every `--ci` occurrence
outside `docs/adrs/` is inside `tests/test_ci_mode.py` or a comment.
**Failure scenario:** identical in shape to the `--strict`-had-no-caller defect this branch
already found and fixed (`gate_precheck.py:66-82` records that history). A mode with no caller
has never been exercised against the real tree except by its own tests.
**Mitigation:** `VALIDATION_ARCHITECTURE.md` §6 already states this — disclosed, not hidden.
**Severity: HIGH.**

---

### MEDIUM

---

#### **DEF-8 — `RATCHETED_CHECKS` is an enumerated roster inside the guard whose purpose is to stop ratchets developing slack; `bundle_apex_resolves` is already missing and would pass today.**

`tests/test_ratchets_have_zero_headroom.py:46-53` (6 names); seam guard at `:100` is
`len(RATCHETED_CHECKS) >= 6` — a floor over a hand-list, not a derivation. The file's own
extraction predicate (*"checks whose summary Detail states `(ceiling N)`"*) **is derivable**:
an AST scan of the check package returns `bundle_apex_resolves`, `elaboration_knob_watchlist`,
`numerical_literals`, `count_literals`, `bundle_tables_use_pipeline`.
```python
_population_and_ceiling('bundle_apex_resolves')   # → (20, 20)
'bundle_apex_resolves' in RATCHETED_CHECKS        # → False
```
**Failure scenario:** `UNDECLARED_APEX_CEILING` is at zero headroom *only because a human
lowered it by hand* in the same change that declared D6's apexes (and again for D9, and again
for L2 in flight). The first time someone declares a bundle's apexes without lowering it, the
ratchet gains a silent slot and nothing fails. **Fix is one line and works verbatim today.**
**Severity: MEDIUM.**

---

#### **DEF-9 — `test_cannot_measure_baseline`'s seam floor has re-opened 1 unit of headroom against a comment that says it must be zero.**

`tests/test_cannot_measure_baseline.py:183` — `assert len(sites) >= 54`, under a comment at
`:177-182` stating *"**Zero headroom**: if the population legitimately shrinks, LOWER this in
the same commit and say why."*
**What I ran** (scan the current tree, and the tree at the commit that set the floor):
```
prev (9140ffeb, floor-setting commit): 54   cur: 55
ADDED since: [('lean_modules_in_build_graph', 'missing-input')]   REMOVED: []
```
**Refutation attempted:** I checked whether the new site is a PASS site (which would be worse —
a silent PASS escaping the baseline). It is not: `_pass_sites()` is 21, exactly equal to the
baseline's 21. No measurement escaped; only the seam guard lost a slot.
**Severity: MEDIUM.**

---

#### **DEF-10 — `bundle_apex_resolves` returns `measured=True` on a path whose own Detail says `UNMEASURABLE`, and neither AST scanner can see it.**

`scripts/validation/checks/bundles_readiness.py:1091-1100`:
```python
if not declared:
    details.append(Detail("apexes_resolve", True, f"UNMEASURABLE — no bundle declares …",
                          warning=True))
    return CheckResult(passed=all_pass, details=details)   # measured defaults True
```
`scan_cannot_measure_sites` matches only an `except` handler or an `if` whose test calls one of
`_PRESENCE_CALLS = {exists, is_file, is_dir, lean_deps_present, counts_present, which}`
(`:82-84`) — `if not declared:` is neither. And `_SKIP_WORDS` (`:228-229`) is
`SKIPPED|not found|absent|not installed|missing|unreadable|could not` — it does not contain
`UNMEASURABLE`. So a check that tells the reader in capitals that it could not measure counts
as evidence toward `CI_MIN_CHECKS_RUN`.
**Refutation attempted:** the branch is defensible — the *ratchet* leg did measure. I still
call it a defect because the scanner's vocabulary is itself an enumerated population and this
is the first instrument to escape it. Fix: add `UNMEASURABLE|nothing to measure` to `_SKIP_WORDS`.
**Severity: MEDIUM.**

---

#### **DEF-11 — The archived validation report, the project's only durable trust record, does not carry `measured`.**

`validate.py:407-412` (archive) and `:743-757` (`--json`) both emit `{passed, error, details}`.
```
docs/validation/reports/validation_20260805T021526Z.json
per-check keys: ['details', 'error', 'passed']    summary: {total: 59, passed: 57, failed: 2}
```
The `measured` field exists precisely because *"nothing could distinguish 'measured and
passed' from 'could not measure, so said PASS'"* (`_registry.py:76-99`). That distinction is
surfaced **only** on stderr, **only** under `--ci` (`:803-806`). Every archived report is
therefore un-auditable in exactly the dimension the field was added for.
One-line additive fix; no consumer breaks. **Severity: MEDIUM.**

---

#### **DEF-12 — `_print_failure_provenance` classifies a failing check by the wrapper's module; `--scope substrate` classifies it by the body's.**

`validate.py:376` uses `getattr(spec.func, "__module__", "")`; `validate.py:819` uses
`_leaf_module_of` → `_defining_module` (`:338-346`), which unwraps `__memo_body__`.
```
MEMOIZED: axiom_closure_allowlist      raw __module__=_memo  real=lean_toolchain
          lean_docstring_refs_resolve  raw __module__=_memo  real=lean_toolchain
```
`_memo` is in neither `_PAPER_SIDE_MODULES` nor `_SUBSTRATE_SIDE_MODULES`, so the printer falls
to its `else` and prints these as SUBSTRATE — accidentally correct today, since both really are.
**Failure scenario:** memoize any paper-side check (the module's own docstring nominates
`paper_latex_compiles`, already carrying a content-hash cache and living in `papers_prose`).
Its failure prints under "✗ SUBSTRATE" — telling a Lean-wave operator their wave broke
something — while `--scope substrate` correctly exits 0. `tests/test_ci_mode.py:334` pins
`_leaf_module_of` and does not reach the printer. **Severity: MEDIUM (latent).**

---

#### **DEF-13 — `sync_manifest.EDGES` claims to be *the* declarative table of mechanical edges and covers 7; its test asserts a hand-picked subset.**

`sync_manifest.py:1-9` — *"the single declarative table … so nothing hard-codes a dependency
edge twice."* `EDGES` (`:126-143`) holds 7. **Not covered, though each has a regenerator and a
`*_fresh`-style consumer:** `papers/claim_clusters.json` (`cluster_detect.py`), the generated
tracked-hypotheses doc (`render_tracked_hypotheses.py`), `docs/BUNDLE_READINESS_HEATMAP.md`
(`bundle_readiness.py`), `figures/structural_checks.json` (`review_figures.py`), the citation
cache. `tests/test_sync_manifest.py:24-32` asserts five substring matches are *present*; no
completeness assertion and no derivation to check against.
**Failure scenario:** `pre-commit-sync.sh:47` runs `sync.py --fast`, regenerating the cheap
`EDGES` and restaging them. An artifact outside the table is never auto-regenerated and never
restaged, so it drifts under the commit gate silently — the same shape as the hand-maintained
`BUNDLE_CODES` literal that hid D10 from `prose_theorem_reference_coverage` for a month
(`validate.py:471-476`). **Severity: MEDIUM.**

---

#### **DEF-14 — `check_bundle_source_freshness.py` scopes itself by `sentence_state._VALID_BUNDLE_TARGETS`, not by the gated roster.**

`scripts/check_bundle_source_freshness.py:107, 120`. `bundle_registry_consistency` gates
`BUNDLE_CODES` as the single source of truth including a `_ROSTER_CONSUMERS` leg; this is a
second consumer reading a second name.
**Measured:** all three populations are 21 and identical today (`BUNDLE_CODES`,
`_VALID_BUNDLE_TARGETS`, and the `papers/*/bundle_metadata.json` glob — empty symmetric
differences both ways). *(One sub-audit reports `_VALID_BUNDLE_TARGETS` is a pure alias at
`sentence_state.py:73`; if so this is a naming issue only — confirm before acting.)*
**Failure scenario:** a 22nd bundle registered and not aliased leaves it un-scanned; the check
reports a clean pass over the 21 it knows about. **Severity: MEDIUM (latent).**

---

#### **DEF-15 — `PARAMETER_PROVENANCE` coverage and `FIGURE_REGISTRY` integrity each scan an enumerated subset of their own population.**

- `citations.py:64-103` enumerates `EXPERIMENTS` / `ATOMS` / `POLARITON_PLATFORMS`.
  **`GRAPHENE_PLATFORMS` is not in the loop — 86 parameter keys, 6 covered.** A new platform
  dict ships unprovenanced and `parameter_provenance` passes.
- `bundles_readiness.py:131` derives the figure roster from `FIGURE_REGISTRY` (good) then
  filters `if not fs.name.startswith(("d11_","d12_")): continue`. Everything else in the
  137-entry registry is unguarded, and **36 `fig_*` functions in `src/core/visualizations.py`
  have no registry entry at all**.

**Severity: MEDIUM.** *(Relayed from a sub-audit; I did not independently re-run the counts —
verify before acting.)*

---

### LOW

- **DEF-16 — `_overlay_closure` does not emit three keys its design doc specifies.**
  `PUBLICATION_INTAKE_SHAPE.md:81` `meta.closure_depth_min`, `:83`
  `meta.homed_declaration_count` (module nodes), `:90` `meta.closure_exclusive`.
  `build_graph.py:4248-4279` emits none, and uses `home_count` (= number of *bundles*) on
  module nodes where the doc reserves a differently-named key for a declaration count.
  Mitigated: the doc is stamped `Status: DESIGN` and a repo-wide grep finds **zero** consumers
  of any overlay key outside `tests/test_bundle_closure.py`. LOW today, MEDIUM once a
  dashboard is written against the doc.
- **DEF-17 — `homed_by` is sorted on module nodes and unsorted on Lean nodes**
  (`build_graph.py:4262` vs `:4255`) — non-deterministic serialization, noisy diffs.
- **DEF-18 — `readiness_verdicts_agree`'s summary miscounts.** `checked` is incremented in both
  loops (`:493`, `:522`) and reported as *"{checked} heatmap-RED bundles cross-checked"*
  (`:542`). Live output says **17** against 16 RED bundles; the 17th is D9, the GREEN
  reverse-direction one. The comment at `:471-478` says the fix was to report the directions
  separately; the shared counter was left in.
- **DEF-19 — `bundle_closure.project_declarations` matches by prefix, not namespace boundary**
  (`bundle_closure.py:187`) — would also match a hypothetical `SKEFTHawkingExtra`.
- **DEF-20 — `_ROSTER_LITERAL_ALLOWLIST` docstring describes two entries; the frozenset has
  one** (`bundles_readiness.py:824-826`).
- **DEF-21 — `UNREACHABLE_MODULE_EXCEPTIONS`'s four tests monkeypatch it to `{}`, its
  production value**, so they cannot detect an entry being added
  (`lean_toolchain.py:902`; `tests/test_d5_lean_toolchain.py:547,554,561,569`).
- **DEF-22 — `_PROSE_REF_ALLOWLIST` (33 tokens, `prose_lean_refs.py:167`) suppresses *before*
  the ratchet counts** (`:715`), so allowlisted tokens are invisible to
  `LEGACY_DRAFT_UNRESOLVED_REF_CEILING`, and it has zero test references anywhere.

---

## 4. Design tensions (tradeoff stated; no recommendation forced)

**T-1 — `FIXTURE_ONLY_CEILING` is documented "may only be lowered" but its zero-headroom test
forces it up on every new check.** `tests/test_d5_mutation_obligation.py:608-615` vs `:723-732`
(`FIXTURE_ONLY_CEILING == len(registered) - len(PRODUCTION_SEEDED)`). **For:** the equality is
what gives the ratchet teeth; `<=` alone would silently absorb new untested checks.
**Against:** the constant's docstring states an invariant the test contradicts, so a reader must
choose which to believe. Resolvable by wording, or by re-expressing as a ratio — reasonable
people differ on which.

**T-2 — a memo HIT counts as `measured=True`, and `--ci` does not imply `--no-memo`.**
`_memo.py:315-322` returns a replayed PASS with `measured` defaulting True; `validate.py:691-695`
sets `NO_MEMO` from `--no-memo` only. **For:** the cache is content-addressed, machine-local and
gitignored (`_memo.py:91-94`), so a fresh runner has an empty cache and the floor is honest; and
`--strict` (the irreversible gate) already bypasses. **Against:** a self-hosted runner with a
persistent workspace — the common cheap configuration — would satisfy the floor by replay. The
eviction path (`:355-360`) runs only on a cache *miss*, so a green entry cached while `lake` was
present is replayed indefinitely on a machine where `lake` has since gone.

**T-3 — `bundle_apex_resolves` sits at the ratchet's maximum by design.**
`bundles_readiness.py:1016-1019` states plainly that the ceiling = every bundle, because
declaration is gated on an operator per-bundle review (ADR-010 §D5a). **For:** honest, and the
alternative puts unreviewed hand-data at the root of the derived substrate. **Against:** while
it holds, the check's three substantive legs are unreachable and `measured=True` is carried
entirely by the ratchet (DEF-10). The D6/D9/L2 retrofits are the walk out of this state.

**T-4 — `apex_theorems` lives in `bundle_metadata.json`, deliberately against Invariant #2.**
Rationale at `PUBLICATION_INTAKE_SHAPE.md:38-45` and `bundle_closure.py:34-37`: merging bundles
should concatenate apex lists and splitting should partition them, which co-location gives
free. **Against:** that file is *also* machine-written (`bundle_readiness.write_metadata_counts`
owns `open_findings`, `blocked_p1_gates`, `readiness`, `readiness_last_computed`), so one file
now mixes hand-authored editorial data with generated state — precisely the mixture that
`check_bundle_source_freshness`'s `write_metadata=False` purity fix (`:84-90`) had to protect
against. The split is defensible; the file is doing two jobs.

**T-5 — `--scope substrate` scopes the exit code only.** This is the *right* call, argued at
`validate.py:363-368`. The tension: `gate_precheck s13-lean` therefore dispatches an expensive
reviewer over a tree with **14 of 21 bundles in `stage13_status` drift** (verified red). The
gate says "safe to dispatch"; the corpus is not clean. Reasonable people differ on whether a
corpus-wide red should ever be non-blocking.

---

## 5. Plugin alignment

`.claude/plugins/skeft-qa/` — 8 agents, 6 commands, 6 skills, 5 hooks, 12 scripts.

**The ADR-009 modularization broke nothing.** A grep of the entire plugin for `validate.py:<line>`,
`in validate.py`, `def check_`, `validation/checks`, `_registry`, `CheckResult`,
`register_check` returns **zero hits** — the plugin only ever addresses checks by
`--check <name>`, which is the stable surface. All 6 `--check` names resolve against
`validate.py --list`. All pipeline stage numbers (4, 9, 12, 13, 14, "1–12") match
`docs/WAVE_EXECUTION_PIPELINE.md` headings. All ~40 repo paths exist. All CLI flags exist
(verified against each target's argparse). All registry symbols resolve. The ReviewFinding
schema matches `extract_review_finding_nodes` field-for-field — including the birth-status
invariant, where **the plugin is more current than `build_graph.py`'s own docstring**
(`:1729-1730` still says "Status defaults to 'open' unless the finding text contains ✅/✓
markers"; the code is unconditional `'open'`).

### HIGH

**PLUG-1 — the `PC` finding class is rejected by the validator the same document mandates.**
`agents/claims-reviewer.md:343` defines `## C.6 Class PC — Placeholder cited as verified` and
`:356` instructs emitting `"finding_classes": ["PC"]`.
`scripts/sentence_state.py:173` — `_VALID_FINDING_CLASSES = {'IA','TP','SD','TN','HD'}`; `:314`
raises a **hard error** (not a warning) for any other value.
`claims-reviewer.md:525-529` instructs the agent to run that validator and states *"If validate
fails, fix the JSON before reporting completion."* **So the first time a reviewer detects the
Invariant-#9 overclaim C.6 exists to catch, it has no legal way to record it.**
Latent-but-live: `papers/D11/claims_review.json` already carries `"by_finding_class": {…,
"PC": 0}` and validates clean **only because `by_finding_class` and
`blocking_issues[].finding_class` are not validated at all**. Same file also self-contradicts
at `:210` ("Five finding classes" — there are six), `:212` (enum omits PC), `:494` (example
omits PC).

**PLUG-2 — the adversarial-reviewer is instructed to query the non-existent `PRODUCES` edge and
to mint a BLOCKER when it finds nothing.** `agents/adversarial-reviewer.md:164` — *"Is there a
successful `ProductionRun` graph node with a `PRODUCES` edge to this claim? Query the graph."*
`:193` — *"No ProductionRun linked but paper prose claims numerical evidence → **BLOCKER**"*;
`:284` makes a BLOCKER submission-blocking. Since nothing is ever linked (CRIT-1, measured: 0
outgoing edges from any of 18 `ProductionRun` nodes), **every simulation-evidence claim in
every paper mints a spurious BLOCKER.** The plugin is faithfully mirroring the repo's own stale
docs (`docs/KNOWLEDGE_GRAPH.md:155`, `docs/READINESS_GATES.md:145,147`) — the debt is
infrastructural, the plugin is where it turns into false findings. **Fix CRIT-1 and this
resolves with it.**

**PLUG-3 — `wave-close` hard-stops on `s13` and does not know `s13-lean` exists.**
`skills/wave-close/SKILL.md:34` runs `gate_precheck.py s13`; `:36` — *"If `gate_precheck s13` is
FAIL, STOP."* `gate_precheck.py`'s own source (`:49-64`) states that *"two corpus-wide reds
mean plain `s13` cannot pass for ANY wave, Lean or paper"*, which is why `s13-lean` was added
on 2026-08-06. **So a `/goal` loop invoking `/skeft-qa:wave-close` on a Lean wave hits an
unconditional STOP at step 1 and can never satisfy its own acceptance criteria.** The
`submission` gate is also entirely absent from the plugin.

### LOWER

**PLUG-4 (LOW–MEDIUM) — `README.md` component inventory is stale in six ways.**
`:25` says `adversarial-reviewer` and `claims-reviewer` accept `bundle_target` — wrong in both
directions (it is `claims-reviewer` and `figure-reviewer`; `adversarial-reviewer` has no
bundle-aware mode). `:22` "five finding classes" (six). `:45` says the harvest routes noise to
"misfile" — **directly contradicting** `harvest-consolidator.md:29-32` and
`system2_register.py:14-16`, which say in bold that the harvest **drops** noise and never
writes misfiled. `:57` says "four hooks (all default-inert + fail-open)" — `hooks.json`
registers **five**, and the missing one (`PreToolUse(WebSearch|WebFetch)` →
`harness_web_egress_guard.py`) is described in the manifest itself as *"unconditional,
fail-closed"*, the opposite of the blanket claim. `:50-56` lists 4 commands of 6 (missing
`/frontier`, `/notebook`). The agents section documents 3 of 8.

**PLUG-5 (INFO)** — `claims-reviewer.md:323` hedges `src/core/hypothesis_registry.py`, which
does not exist. Primary path is correct; harmless.

---

## 6. Documentation defects

*(from a dedicated sub-audit; I independently spot-verified DOC-1, DOC-3, DOC-5, DOC-6 and the
`apex_theorems` correctness claim — all confirmed exactly as reported.)*

### HIGH — a reader is misled into a wrong action

| # | Doc says | Code does |
|---|---|---|
| **DOC-1** | `scripts/validate.py:18, 51` — `python scripts/validate.py --archive` | `:644` defines only `--no-archive`. **Verified:** `--archive` → `error: unrecognized arguments`, exit 2. This is the first usage block in the file; the correct epilog is 600 lines below. |
| **DOC-2** | `scripts/validate.py:40` — *"Checks are run in registration order"* | `:154-215` — `_CANONICAL_ORDER` + `_apply_canonical_order()` **decouple** them (ADR-009 H3), and the same file at `:148-167` explains why. `freshness.py`'s three regenerators must precede their consumers; a check author placing by file position gets the wrong ordering. |
| **DOC-3** | `docs/WAVE_EXECUTION_PIPELINE.md:244` — bump `322` *"in both places: `constants.py` … and `scripts/validate.py` (CHECK 5)"* | **Verified:** `grep -c 322 scripts/validate.py` → **0**. The site is `checks/lean_toolchain.py:184-185`. An operator following the stage law ships a half-bump that breaks `constants.py`'s import-time assert. |
| **DOC-4** | Four check-module headers list the wrong check set for their own module | `lean_substrate.py:4-6` names **9**, registers **6** (three moved to `lean_statements.py`); `lean_toolchain.py:3-6` 7 vs 8; `papers_prose.py:3-8` 6 vs 7; `bundles_readiness.py:3-5` 6 vs 7. |
| **DOC-5** | `scripts/build_graph.py:44` — *"22 node types"* | **Verified:** `len(SHAPE_MAP) == 26`. |

### MEDIUM — stale counts a reader would quote or budget against

- **DOC-6 "61 checks"** — actual **62**. Stale at `CLAUDE.md:109`,
  `VALIDATION_ARCHITECTURE.md:18,31`, `QA_QI_INFRASTRUCTURE_MAP.md:93,138`,
  `SK_EFT_Hawking_Inventory_Index.md:609`. *(The workspace-level `CLAUDE.md` says **21** — far
  more stale.)*
- **DOC-7** `README.md:410` — *"~28 cross-layer validation checks"* vs 62. This is the
  designated architecture entry point.
- **DOC-8** `QA_QI_INFRASTRUCTURE_MAP.md:141-152` per-module table: three rows wrong
  (`lean_toolchain` 7→8, `bundles_readiness` 6→7, `papers_prose` 6→7); the rows sum to **59**
  while the prose two lines above says 61 and reality is 62 — three inconsistent numbers in one
  paragraph. `:139` names the largest module as `citations` at 965; actual largest is
  `bundles_readiness.py` at 1,133. `:136` says `validate.py` is "~740 lines"; it is 830.
- **DOC-9** `CHECK_AUTHORING_GUIDE.md:71` — *"6 of 61 production-seeded"*; actual 7 of 62.
  `QA_QI_INFRASTRUCTURE_MAP.md:425` states a **third** figure ("4 of 59"). Three docs, three
  numbers, none current — and the stale 6/61 implies one seat of headroom where
  `FIXTURE_ONLY_CEILING` is exactly at the population.
- **DOC-10** `WAVE_EXECUTION_PIPELINE.md:689` — Invariant #14 enumerates *"18 targets"*,
  omitting **D10, D11, D12**. It reads as a closed enum. *(ADR-010:473 flags this site; unlanded.)*
- **DOC-11** `docs/BUNDLE_DIRECTORY_SCHEMA.md:45-91` omits four fields present in **21/21**
  live `bundle_metadata.json` (`open_findings`, `blocked_p1_gates`, `readiness`,
  `readiness_last_computed`), which `write_metadata_counts` owns. `:222` still says
  `_VALID_BUNDLE_TARGETS` has **14** entries; it has 21.
- **DOC-12** `ADR-004:66` cites `validate.py:706-733` for `axiom_closure_allowlist`; that code
  is now `checks/lean_toolchain.py:440`, and `validate.py:706-733` is argument handling.
- **DOC-13** `readiness_gates.py:27` — the module docstring describes `paper_aggregate_state` as
  *"red if any P1 blocked, yellow if any P2 open"*. The function (`:862-872`) reds on **any**
  blocked gate regardless of priority. Compounded by the function being dead (DUP-2).

### LOW

- **DOC-14** `_config.py:5` — *"Three flags"*; the module defines five and `validate.py:691-695`
  sets all five (`NO_MEMO` is read in a check body at `papers_prose.py:592`). Echoed at
  `QA_QI_INFRASTRUCTURE_MAP.md:158`.
- **DOC-15** `VALIDATION_GATE_TOPOLOGY.md:55` — *"0 green / 3 yellow / 61 red"*; re-measured:
  0 / 2 / 62. Date-stamped, so a careful reader is warned.
- **DOC-16** `check_bundle_source_freshness.py:30-32` — *"`validate.py` consumes it via
  `@register_check(...)`"*; `validate.py` has **zero** `@register_check` since ADR-009 Phase 2.
- **DOC-17** `SK_EFT_Hawking_Inventory_Index.md:606` — *"~65 scripts"* vs 98 `.py`;
  `WAVE_EXECUTION_PIPELINE.md:730` — *"All 16 checks"* (mitigated by `:335`).
- **DOC-18** `build_graph.py:1729-1730` and `:1900` describe ✅/✓-marker status inference that
  the code no longer performs (status is unconditionally `'open'`).

### Verified CORRECT (so absent findings read as coverage, not as gaps)

`VALIDATION_GATE_TOPOLOGY.md`'s **entire enforcement model** re-checked against code and holds:
Tier-0's three commit-gate checks and their fail-open / `main`-only semantics; s9's two checks;
s10's four; `s13 = __full__ --force-latex`; `s13-lean = --scope substrate`; `--scope`
deliberately absent from `submission`; `CI_SKIP` being exactly the three mtime regenerators +
`notebook_exec`; `--strict` implying `--no-memo` (`_memo.py:293`); the six `--strict`-only legs;
the §4 field-ownership table; and *"plain `s13` cannot pass for any wave"* (both named reds
still fail, and `bundle_metadata_matches_graph`'s "14 of 21 with drift" reproduces exactly —
and all 14 have the **same single cause**, `stage13_status='green'` with open blockers, with
**zero** count-drift, i.e. `write_metadata_counts` is current and the failure is entirely the
hand-maintained field). `VALIDATION_ARCHITECTURE.md`'s module inventory, `CheckResult` shape,
`_CHECKS`-identity hazard and H1/H3/H4/H5 descriptions with their named enforcing tests: all
correct, including §6's honest *"does not run in CI"*. `CHECK_AUTHORING_GUIDE.md`: correct
except `:71`. **`docs/BUNDLE_DIRECTORY_SCHEMA.md:91-114` documents `apex_theorems` fully and
correctly** — `APEX_KEY`, `declared`/`closure_measurable` semantics, "absent is UNKNOWN not
empty", the co-located-vs-central rationale — it landed *with* the code, not after it.
Module docstrings verified clean: `citations`, `freshness`, `graph_atlas`, `lean_statements`,
`notebooks`, `physics`, `prose_lean_refs`, `reviews`, `checks/__init__`, `_registry`, `_memo`.
`bundles_readiness.py`'s header is a *positive* example — it narrates and corrects its own
prior contradiction (QI-12).

---

## 7. What I could NOT assess, and why

1. **Lean-side truth beyond `lean_deps.json`.** I did not run `lake build` or the lean-lsp MCP.
   Every Lean claim here (`sorry_declarations == 0`, module reachability, axiom closures) is
   read from `docs/counts.json` / `lean/lean_deps.json` — from the extraction, not the kernel.
   **DEF-3 is a claim about the *gate*, not a claim that a `sorry` exists**; `counts.json` says
   0. Verifying the substrate needs `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`,
   out of scope for a read-only pass.
2. **The three slow / expensive checks were not executed by me.** `axiom_closure_allowlist`
   (145 s), `lean_docstring_refs_resolve` (53 s), `paper_latex_compiles` (16.6 s × 21), and the
   full ~332 s suite. Their *code* was read. `pytest -m slow` was not run — including
   `test_ci_mode.py::test_the_LIVE_floor_matches_what_a_REAL_run_MEASURES`, which is the only
   guard that would catch a check silently ceasing to measure.
3. **`provenance_dashboard.py` (5,543 lines) was sampled, not read.** Its trust-relevant call
   sites were audited; its HTTP layer, callback graph, and the Postgres/AGE sync path
   (`sync_graph_to_pg.py`) were not.
4. **Nothing outside this repository was examined** — correctly, per the workspace's one-way
   dependency rule. If a downstream consumer reads these registries or overlay keys, it is
   outside this report.
5. **Historical `MUTATION_VERIFIED` claims were not re-run.** The file itself says a mutation
   is an act against the tree, not an artifact in it. I verified the *seam guard* (each entry
   names a test whose code exercises the check) passes; I re-seeded none of the 62 mutations.
   **Every `MUTATION_VERIFIED` note is a claim I am relaying, not verifying.**
6. **The tree was dirty and moving.** Two apex retrofits landed mid-audit and a third (L2) was
   in flight at close. All apex/closure numbers are timestamped; re-measure before acting.
7. **No runtime probe of the plugin agents.** §5 is static analysis of prompt text against
   code; I did not dispatch a reviewer to observe an actual break.
8. **`bundle_readiness.py` was never run bare.** With no args it **writes** (`bundle_metadata.json`,
   per-bundle review docs, `BUNDLE_READINESS_HEATMAP.md`) and backfills metadata
   (`resolve_stage13_reviews(backfill=not args.json)`, `:761`). Only `--json` was used. Anyone
   re-verifying §3/DEF-4 must do the same.
9. **Findings marked *(relayed)*** — DEF-15, parts of §2c and §2e, and the DOC table — come from
   sub-audits with file:line evidence that I spot-checked but did not re-derive end to end.
   They are flagged so you can prioritize re-verification.

---

## 8. If you only do three things

1. **Emit `PRODUCES` and `SUPPORTS`, or delete the two gates.** CRIT-1 + CRIT-2 + PLUG-2 are one
   root cause. Today a P1 gate named `ProductionRunHealth` passes over 17 failed runs while
   `NarrativeGrounding` fails everything for a reason it does not measure. Until this is fixed,
   the readiness verdict for every paper is partly noise. Add an `extract_produces_edges` /
   `extract_supports_edges`, **and** add a structural guard that every edge type read by
   `readiness_gates.py` is emitted by some extractor — that guard is derivable and would have
   caught both on day one.
2. **Gate zero-`sorry` in `validate.py`.** A one-leg check comparing
   `counts['lean']['sorry_declarations']` to 0 (fail-closed on a missing `counts.json`) closes
   the project's headline invariant. Today its only enforcement is fail-open, `.lean`-scoped,
   and `main`-only — and this branch has been off `main` for 140+ commits.
3. **Derive `RATCHETED_CHECKS` instead of enumerating it**, and add the four category-2 ceilings
   (`UNDECLARED_APEX_CEILING`, `PROVENANCE_UNRESOLVABLE_CEILING`,
   `LEGACY_DRAFT_LATEX_BROKEN_CEILING`, `_LEDGER_DANGLING_BASELINE`). `bundle_apex_resolves`
   already returns `(20, 20)` through the existing helper — it is a one-line add that works
   today, and it converts the largest inconsistency in §2c into the house idiom.
