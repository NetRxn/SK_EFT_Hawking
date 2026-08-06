# H2 — The plugin, and the seams between the QA/QI parts

**Reviewer:** H2 (holistic architecture review, seams edition)
**Date:** 2026-08-05
**Tree reviewed:** worktree `rv2` @ `db430c65`
**Question:** not "is any piece defective" but "do the pieces fit each other".

---

## 0. Verdict up front

**The parts are individually good and the seams between them are weak — the system is
well-engineered inside each boundary and under-engineered across them.**

The pattern repeats at every seam I looked at. Each part has a real, defensible internal
design: `validate.py`'s 60 checks are modularized by domain with a registry that resists
re-fragmentation; the plugin's harness hooks are fail-closed where they must be and
fail-open where they must be; the atlas is derived and therefore cannot drift. But the
*edges* — where the deterministic suite hands off to an LLM reviewer, where a gate is
supposed to be called, where a plugin prompt names a check — are held together by prose,
and prose is not enforced anywhere.

Three concrete manifestations, in severity order:

1. **Three of four gates have no caller.** `gate_precheck` defines `s9`, `s10`, `s13`,
   `submission`. Exactly one (`s13`) is invoked by anything (`wave-close/SKILL.md:34`).
   `wave-close` step 2 then dispatches `claims-reviewer` directly — bypassing `s10`, the
   gate built specifically to guard that dispatch.
2. **The plugin's prompts drift against the code at ~20%, unguarded.** 26 of 132
   code-identifier references in the plugin markdown fail to resolve. There is no
   mechanism — no check, no test, no hook — that verifies any of them. The repo enforces
   exactly this discipline for Python↔Lean docstrings (`lean_docstring_refs_resolve`,
   `prose_theorem_reference_coverage`) and for the bundle roster
   (`bundle_registry_consistency`); the plugin sits outside every one of those perimeters.
3. **The LLM reviewers re-derive what the suite already computed.** `claims-reviewer`
   Class TN loads `lean_deps.json` and checks that `\texttt{...}` theorem references
   resolve — which is `prose_theorem_reference_coverage`, byte for byte in intent. Class
   TP re-reads `lean-toolchain` — which is `paper_toolchain_pin_drift`, a check whose own
   docstring says it is the *"structural mirror of claims-reviewer Class TP"*. The
   awareness is **one-way**: the checks know about the agents, the agents do not know
   about the checks.

What fits well is worth stating plainly, and I do so in §7.

---

## 1. Is the deterministic/LLM boundary principled? (Q1)

### 1a. It is principled in the *large* and accidental in the *small*

The stated split is coherent and I endorse it: deterministic checks own **structural
predicates over machine-readable artifacts** (does this name resolve, is this number
fresh, is this axiom closure allowed); LLM reviewers own **judgments requiring reading
prose in context** (is this sentence an overclaim, does this figure communicate what the
caption says, is this citation on-target). That is the right cut, and
`WAVE_EXECUTION_PIPELINE.md` Stage 13's rationale ("catch every failure class that Stages
1–12 cannot detect **by construction**") states it well.

Where it breaks down is that the boundary has **moved** — deterministic checks have been
built for things the agents were originally invented to catch — and **nothing re-cut the
agent prompts** when it moved. So the boundary today reflects the union of "what was hard
to automate in April 2026" and "what has been automated since", with no reconciliation.

### 1b. Checked TWICE (agent + check, same predicate)

| predicate | deterministic check | agent class | evidence of duplication |
|---|---|---|---|
| paper `\texttt{Theorem}` refs resolve in `lean_deps.json` | `prose_theorem_reference_coverage` | claims-reviewer **Class TN** (`claims-reviewer.md:273–315`) | Both load `lean/lean_deps.json` and do a `(module, name)` membership test. The agent prompt (`:284`, `:290`) spells the lookup in Python. Agent does not name the check. |
| paper toolchain/Mathlib pin matches `lean-toolchain` | `paper_toolchain_pin_drift` | claims-reviewer **Class TP** (`:234–250`) | `papers_prose.py:1010` literally says *"Structural mirror of claims-reviewer Class TP"*. |
| placeholder theorem cited as verified | `placeholder_not_cited` | claims-reviewer **Class PC** (`:341–371`) | **This one is handled correctly** — `:358` names the check and states the residual the agent adds (conceptual/notation forms the `tex_signature` match approximates). This is the model the other two should follow. |
| tracked-hypothesis disclosure | `tracked_hypothesis_ledger` + `disclosure_consistency` | claims-reviewer **Class HD** (`:316–340`) | Agent cites a check name that does not exist (`paper_hypothesis_disclosure`, §3). |
| count literals in prose vs `counts.json` | `count_literals`, `counts_fresh`, `axiom_count_prose_consistency` | adversarial-reviewer §7 + claims-reviewer **Class IA** | adversarial-reviewer *does* shell to `counts_fresh` / `count_literals` (`:181–182`) — the one place an agent consumes suite output. Class IA still re-derives. |

Class PC is the existence proof that this is solvable within the current design: name the
check, state the residual, let the agent spend its budget only on the residual. Four of the
five classes do not do it.

### 1c. Checked by NEITHER — the gap between them

- **The Python test suite is in no gate at all.** 5,554 tests, ~285 s
  (`VALIDATION_GATE_TOPOLOGY.md` §5). Tier 0 does not run pytest; `gate_precheck` s9/s10/
  s13/submission do not; `wave-close/SKILL.md` does not. `CLAUDE.md` says run everything
  "before PR / submission / wave close" — as prose, addressed to a human. **A wave can
  close with a red test suite and every gate green.** Given that the whole ADR-009
  modularization is guarded by a characterization harness *in pytest*, this is the largest
  uncovered surface in the system.
- **Stage 6 has no machine gate** for the same reason (see §4 table).
- **Nothing verifies the plugin's own prompts** (§3) — neither a check nor an agent.
- **Nothing verifies the governance prose against the registries it governs.**
  `bundle_registry_consistency` enforces the roster across `scripts/*.py` (including an AST
  leg that catches a *newly written* hardcoded roster — genuinely excellent design), and
  Leg A compares it to `PAPER_STRATEGY.md` §6. But the roster also lives, with three
  different values, in three governance docs that the check does not read:

  | source | roster size | as of |
  |---|---|---|
  | `scripts/bundle_registry.BUNDLE_CODES` (canonical) | **21** | D12, 2026-07-27 |
  | `docs/PAPER_STRATEGY.md` §intro | **21** | ✅ agrees |
  | workspace `CLAUDE.md:80` | **20** | D10+D11, 2026-06-29 |
  | `docs/WAVE_EXECUTION_PIPELINE.md` Invariant #14 | **18** | D9, 2026-06-10 |
  | `.../agents/claims-reviewer.md:72`, `figure-reviewer.md:71` | **14** | pre-D6 |
  | `scripts/review_runner.py:186` (argparse help) | **19** | pre-D10 |

  Six sources, four answers. The invariant that says "every paper-shaped output lifts into
  a bundle" enumerates a roster that has been wrong for two months, and the two bundle-aware
  reviewer agents cannot see D6–D12 or I3 at all.

**Assessment:** the split is *conceptually* principled but *operationally* it is "whatever
was automated, plus whatever the agents were told in April". The missing artifact is a
per-finding-class ownership table — one place that says, for each predicate, whether the
check owns it, the agent owns it, or the agent owns the residual after the check.

---

## 2. Do the agents consume the suite, or re-derive it? (Q2)

**They re-derive it, almost entirely. Nothing reads `validate.py --json`.**

Traced data flow (verified by grep over `.claude/plugins/skeft-qa/` and `scripts/`):

| direction | mechanism | status |
|---|---|---|
| suite → agent | `adversarial-reviewer.md:181–182` shells `validate.py --check counts_fresh` / `count_literals` | ✅ the **only** consumption of suite output by any agent |
| suite → agent | `figure-reviewer.md:116` reads `figures/structural_checks.json` if present | ✅ partial — reads a sibling artifact, not the suite |
| suite → agent | `--json` payload | ❌ **zero consumers anywhere in the repo.** The only live hits are `scripts/validate.py` itself and audit/ADR prose describing it as a frozen contract. It is a contract with no counterparty. |
| agent → suite | `claims_review.json` → `sentence_state.py` / `build_graph.py` / `cluster_detect.py` → `claim_clusters_fresh`, `bundle_consistency` | ✅ **this direction is well-built** |
| agent → suite | `papers/AutomatedReviews/**/*.md` → `build_graph.extract_review_finding_nodes` → `ReviewFinding` → Gate 11 → heatmap | ✅ well-built, with documented silent-drop points |

So the system is **half a loop**: agent output flows into the deterministic layer through
a real, typed pipeline; deterministic output does not flow back to the agents at all. Each
reviewer dispatch re-establishes facts the suite computed minutes earlier — and, worse,
re-establishes them with a *second implementation of the same predicate*, which is a drift
surface even when both implementations are correct today.

The cheapest correct fix is not to make agents parse `--json`. It is to make
`gate_precheck` **emit** what it just proved. If `gate_precheck s10` wrote a small
`gate_report.json` (`{stage, checks:[{name,passed,detail_count}], sha, ts}`) and the agent
prompts said *"read `gate_report.json`; Classes TN/TP/PC/HD are DISCHARGED for any file
whose check passed — spend your budget on the residual"*, the duplication and the drift
surface both close in one move. Cost: ~30 LoC in `gate_precheck.py`, one paragraph in each
of three agent prompts.

---

## 3. Drift between plugin prompts and the code they describe (Q3)

**Measured drift rate: 26 / 132 references fail to resolve = 19.7%.** Restricted to
machine-checkable load-bearing references (excluding CLI flags and Lean names, both clean):
**26 / 102 = 25.5%.**

**Nothing catches it.** Verified three ways:
- `grep -n "plugins\|skeft-qa\|SKILL\|agents/" scripts/validate.py` → zero hits. No check in
  the 60-check registry reads `.claude/plugins/`.
- `hooks/hooks.json` registers 5 handlers across 4 events; none validates documentation.
- The repo `pre-commit` hook contains no `plugins` reference.

The **one** test that reads plugin markdown is
`.claude/plugins/skeft-qa/tests/test_skill_safety.py`. It is a good test and it is the
right *shape* — a deterministic content-scan over `agents/*.md`, `commands/*.md`,
`skills/**.md`, no model judgment, runs in the fast suite. But its four predicates are all
**shell-invocation** defects (`!\`cmd\`` injection, bare `git rev-parse`, `python3` vs
`uv run python`, `cd`-before-`uv run`). It never asks whether a referenced check name,
path, constant, or count exists.

### The seven hard breaks (an agent following the prompt executes a failing command)

| # | file:line | reference | reality |
|---|---|---|---|
| 1 | `agents/claims-reviewer.md:312` | `validate.py --check paper_lean_refs` | no such check; live analogue is `prose_theorem_reference_coverage` |
| 2 | `agents/claims-reviewer.md:339` | `validate.py --check paper_hypothesis_disclosure` | no such check; live analogues `tracked_hypothesis_ledger` / `disclosure_consistency` |
| 3 | `agents/adversarial-reviewer.md:195` | `data/**/*.log` | **no `data/` directory exists**; run logs are in `logs/` |
| 4 | `agents/claims-reviewer.md:262` | `n_graviton_polarizations()` | real name `graviton_polarization_count(spacetime_dim)`, `src/core/formulas.py:708` |
| 5 | `agents/claims-reviewer.md:253/261` | `formulas.py::structural_obstacles` | defined in `src/adw/fluctuations.py:341`, wrong module |
| 6 | `agents/claims-reviewer.md:321` | `src/core/hypothesis_registry.py` | does not exist (hedged "if split") |
| 7 | `agents/claims-reviewer.md:253` | `STEALTH_DRIFT_REGISTRY` | defined nowhere in `src/` or `scripts/` |

### The roster/scope drifts (silently narrow what a reviewer looks at)

- `claims-reviewer.md:72` and `figure-reviewer.md:71`: `bundle_target` roster =
  `F, D1–D5, L1–L3, I1, I2, E1, E2` (**14**) vs canonical **21**. D6–D12 and I3 are
  invisible to both bundle-aware reviewers.
- `claims-reviewer.md:84`: "Tier 1 (D1–D5)" — Tier 1 is D1–D12.
- `claims-reviewer.md:86`: "Tier 3 (I1, I2)" — Tier 3 is I1, I2, **I3**.
- `agents/coach.md:17`: *"(Core PD-0..PD-4 + Full)"*. The Core section of `PRE_DECISIONS.md`
  contains, in file order, PD-0, PD-1, PD-2, PD-3, **PD-5**, PD-4. **PD-5 is
  operator-set (2026-07-29) — "review findings: BLOCKER/MAJOR/IMPORTANT are never
  deferred" — and it falls outside the range the coach is told to apply.** The human-proxy
  agent is instructed to ignore an operator's standing decision. This is the single most
  consequential drift in the plugin, because the coach exists precisely to resolve
  questions the way the operator would.

### Version / count literals

- `skills/goal-dev/references/lean-dev.md:39–40`: *"we run 4.29.x"* — actual toolchain
  `leanprover/lean4:v4.32.0`. The plugin contradicts the root `CLAUDE.md` it mirrors.
- `agents/claims-reviewer.md:229`: worked example asserts `lean-toolchain` says `v4.29.0`.
- `agents/adversarial-reviewer.md` output template: `model: claude-opus-4-6`;
  `readiness_gates_version: 1` (nothing defines or consumes that field).
- `agents/adversarial-reviewer.md:177`: "Gate 9 **CountFreshness**" —
  `docs/READINESS_GATES.md:161` names it **NumericalFreshness**. `claims-reviewer.md:232`
  gets it right, so the two reviewers disagree about a gate name.
- `skills/goal-dev/references/lean-friction-catalog.md:151`: "23-file in-tree precedent"
  for `maxRecDepth` — currently 24.
- `README.md:41`: "8-field marker" — `skills/goal-prompt/SKILL.md:121` says **11-field**
  and lists 11 keys.

### The one finding with a safety implication

`README.md:57` — *"### Hooks (`hooks/hooks.json` → `scripts/`) — **four** (all default-inert
+ **fail-open**)"*, followed by a 4-row table. `hooks.json` registers **five** handlers.
The omitted one is `PreToolUse(WebSearch|WebFetch)` → `harness_web_egress_guard.py`, which
is deliberately **fail-CLOSED** (its inline fallback emits
`"[web-egress] guard failed to launch; failing closed."`; root `CLAUDE.md` says so
explicitly). So the README states both a wrong count *and* the wrong safety property over a
set that excludes the security hook. A reader reasoning about blast radius from the README
draws the wrong conclusion in the one place it matters.

### Also drifting: the *code* side of the same seam

Drift is bidirectional. `scripts/validation/checks/papers_prose.py:897` and
`scripts/sentence_state.py:42` cite **`docs/agents/claims_reviewer.md`** as the definition
of Class TP. That file exists, is 24 KB, was last committed **2026-04-25**, and its own
header says the agent lives at `.claude/plugins/**physics-qa**/agents/claims-reviewer.md`
— the wrong plugin name. It documents **five** finding classes; the live agent implements
**six** (C.1–C.6, adding Class PC). And the live agent's own frontmatter still says
*"five finding classes"* while its body defines six. So: a shipped validation check cites a
three-month-stale duplicate spec, which names a nonexistent plugin, and the live spec
mis-describes itself.

**Recommendation (cheap, high value).** Add a fifth test to
`tests/test_skill_safety.py` — the harness already globs every plugin markdown file:

```
test_referenced_code_identifiers_resolve():
  for each `validate.py --check <name>`  -> assert name in validate._CHECKS
  for each `scripts/<x>.py` / `src/**.py` -> assert path exists
  for each ALL_CAPS registry identifier   -> assert grep-able in src/ or scripts/
  for each bundle-roster enumeration      -> assert set == bundle_registry.BUNDLE_CODES
```

**Cost: ~60 LoC, one file, no new infrastructure, runs in the fast suite.** It would have
caught 21 of the 26 findings above. The remaining 5 (version literals, model ids, prose
counts) want a second predicate comparing against `counts.json` / `lean-toolchain`, ~20 more
LoC.

---

## 4. Do the gates line up with the pipeline stages? (Q4)

| Stage | machine gate | LLM reviewer | verdict |
|---|---|---|---|
| 1 Constants | `--check numerical`, `parameter_provenance` | — | ✅ covered |
| 2 Formulas | `formula_grounding`, `formulas` | — | ✅ covered, strong (content-grounding, not name-presence) |
| 3 Lean theorems | `vacuous_statement_audit`, `proxy_body_audit`, `tracked_hypothesis_ledger`, `nogo_substrate_integrity` | — | ✅ covered; the ADR-004/007 gates are the best part of the suite |
| 4 Aristotle | `theorems` (registry resolves) | — | ⚠️ partial — registry integrity only, no submission-side gate |
| 5 Lean build | `lean_build`, `native_decide_regression`, `axiom_closure_allowlist` + tier-0 commit hook | — | ✅ covered at two tiers |
| 6 Python tests | **NONE** | — | ❌ **5,554 tests in no gate.** Prose instruction only. |
| 7 Cross-layer | `cross_path_consistency`, `physical_bounds`, `identities` | — | ✅ covered |
| 8 Visualizations | `viz_consistency` (advisory), `bundle_figure_integrity` | — | ✅ since 2026-08-05 |
| 9 Figure review | `gate_precheck s9` — **defined, zero callers** | figure-reviewer | ⚠️ gate exists, unwired |
| 10 Paper draft | `gate_precheck s10` — **defined, zero callers**; `paper_provenance` | claims-reviewer | ⚠️ gate exists, unwired |
| 11 Notebooks | `notebook_exec`, `notebooks`, `notebook_stored_outputs_current` | — | ✅ covered |
| 12 Doc sync | `counts_fresh`, `tables_fresh`, `inventory_index_autogen_fresh`, `claim_clusters_fresh`, + `sync.py --full` | — | ✅ covered, auto-regenerating |
| 13 Adversarial | `gate_precheck s13` ← `wave-close/SKILL.md:34` | adversarial-reviewer | ✅ **the one fully-wired gate** |
| 14 QI / process | **NONE** | — | ❌ see below |
| — Submission | `gate_precheck submission` — **defined, zero callers** | — | ⚠️ gate exists, unwired |

### The s9/s10 finding in detail

`gate_precheck.py`'s docstring is explicit: `s9` runs *"before the figure-reviewer"*, `s10`
*"before the claims-reviewer"*. Both were built (and s9 was repaired on 2026-08-05 with
`bundle_figure_integrity`, after review R5-MAJ2 found it could not fail). Yet:

- `grep -rn "gate_precheck"` over the whole plugin returns exactly one hit:
  `wave-close/SKILL.md:34`, and it is `s13`.
- `docs/BUNDLE_LIFT_PROCEDURE.md` — the frozen 14-step procedure that owns §8 (Stage 9) and
  §9 (Stage 10) — contains **zero** occurrences of "precheck" or "gate_precheck".
- `wave-close/SKILL.md` step 2 dispatches `claims-reviewer` **directly**, having run only
  `s13`. The s10 gate that exists specifically to protect that dispatch is skipped by the
  only workflow that performs it.

So the reviewer-precheck tier described in `VALIDATION_GATE_TOPOLOGY.md` §1 as *"before
dispatching an LLM reviewer"* is, today, a tier that nothing enters. The fix is two lines
of prose in `BUNDLE_LIFT_PROCEDURE.md` §§8–9 and one line in `wave-close/SKILL.md`.
**Cost: near zero. This is the highest value-per-effort item in this report.**

### Stage 14 is wired to nothing

- `scripts/qi_register.py` last committed **2026-04-29**; `docs/QI_REGISTER.md` last
  committed **2026-07-03** with a header timestamp of **2026-04-28** — i.e. hand-edited for
  two months past its last regeneration, so re-running the generator now would fight the
  curation.
- No automated caller of `qi_register.py` anywhere.
- No `validate.py` check reads `QI_REGISTER.md`.
- The repo's own `QA_QI_INFRASTRUCTURE_MAP.md:188` already records the reader column as
  **"none — *re-parses its own Closed Items*"**.

Stage 14 is declared advisory, which is defensible. But "advisory" and "unwired" are
different things: the System-2 register — the *same shape of store*, for dev-loop process
instead of paper process — **is** wired, into the SessionStart re-injection via
`harness_common.py`. System-1 got the doc and not the wiring. That asymmetry is the actual
defect, not the advisory status.

---

## 5. The known sharp edge: s13 runs the whole suite (Q5)

**Does the design hold? No — and the doc's own hedge ("deliberate but under-scoped") is the
correct diagnosis, understated.**

### The measurement

`VALIDATION_GATE_TOPOLOGY.md` §2 already records the live state honestly: with
`readiness_submission_gate` at 0 green / 3 yellow / 61 red across 64 papers, and
`bundle_metadata_matches_graph` red on 14 of 21 bundles, **`gate_precheck s13` cannot pass
today**. Since `wave-close/SKILL.md` step 1 says *"If `gate_precheck s13` is FAIL, STOP"*,
the sanctioned wave-close path for a pure-Lean wave is currently blocked by paper-corpus
state — permanently, until ADR-010 repairs the corpus. That is not a latent risk; it is the
present state.

This is the failure mode `VALIDATION_GATE_TOPOLOGY.md:61` itself names for `--strict`:
*"a gate that fires on correct work gets switched off."* The reasoning was applied to
`--strict` and not to s13, and s13 is the gate that actually fires on correct work.

### Why the rationale doesn't survive contact

The rationale is sound in form — don't spend an Opus dispatch on a known-bad tree. But it
proves too much. "Known-bad" is being read as *any* check red, when the relevant predicate
is *any check red **that the reviewer's findings could depend on***. A Lean wave's
adversarial review reads Lean modules, the atlas, and the wave roadmap. D3's LaTeX and
paper41's readiness gates cannot change a single finding in that review. Blocking on them
buys nothing and costs the gate its credibility.

### The right scoping rule

**Scope the gate by the wave's domain, with a mandatory always-on core.**

```
gate_precheck s13 --scope lean    # Lean/substrate wave
gate_precheck s13 --scope paper   # bundle lift / paper wave
gate_precheck s13                 # (no flag) = full suite, unchanged default
```

- `--scope lean` → the substrate partition **+ the always-on core**.
- `--scope paper` → the paper partition + the same core.
- Core (always, regardless of scope): `formula_grounding`, `placeholder_not_cited`,
  `native_decide_regression`, `lean_build`, `axiom_closure_allowlist`, `counts_fresh`.
  These are soundness, not corpus hygiene; a red here is disqualifying for any wave.

### What it costs to implement — genuinely small

**The partition already exists.** ADR-009 modularized the suite into
`scripts/validation/checks/*.py` along almost exactly domain lines. Measured live:

| domain | modules | n |
|---|---|---|
| **substrate** | `lean_statements` (3), `lean_substrate` (6), `lean_toolchain` (5), `graph_atlas` (3), `_memo` (2) | **19** |
| **physics** | `physics` (9), `notebooks` (3) | **12** |
| **paper** | `bundles_readiness` (6), `citations` (4), `papers_prose` (7), `prose_lean_refs` (2), `reviews` (4) | **23** |
| **mixed** | `freshness` (6) — `counts_fresh` is Lean-derived; `bundle_source_freshness`/`tables_fresh`/`claim_clusters_fresh` are paper | **6** |
| | | **60** |

So the work is:
1. Add `domain: str = "core"` to `CheckSpec` (`scripts/validation/_registry.py:105`), or —
   cheaper and equally sound — a literal `MODULE_DOMAIN: dict[str, str]` map keyed on
   `func.__module__`, with a per-check override dict for the 6 `freshness` splits.
   **~25 LoC.**
2. `gate_precheck.py`: accept `--scope`, translate to a `--check` list.
   **~15 LoC.**
3. A test asserting every registered check has a domain (so a new check cannot be silently
   unscoped — the same "AST anti-rehardcoding" instinct `bundle_registry_consistency`
   Leg C already demonstrates). **~20 LoC.**

**Total ≈ 60 LoC and one test.** Wall-time benefit is real but secondary (a `--scope lean`
run skips `paper_latex_compiles`' 16.6 s and the bundle/citation/review legs); the actual
benefit is that **the gate becomes passable on correct work**, which is what determines
whether it survives.

⚠️ **One caution.** Do not let `--scope` become a way to close a paper wave without the
paper checks. The scope should be derived from the wave's touched paths (or asserted by the
wave-close invocation and recorded in the close record `docs/dev-loops/<roadmap>/<wave>_close.md`),
not chosen freely at the prompt. A scope flag with no accountability is just a `--force`.

---

## 6. Register proliferation — coherent architecture, or accretion? (Q6)

**Both, and the seam between them is legible: everything that is DERIVED is coherent;
almost everything that is HAND-MAINTAINED is accretion.**

Counted: **~40 persistent stores.** **9 are derived and gated** (cannot drift). The rest are
hand-maintained, and of those the majority have **zero machine readers**.

### The table

W = writer · R = reader · D = the decision it drives · type = Derived (cannot drift) /
Hand (will drift) · verdict.

| store | writer | reader | decision it drives | type | verdict |
|---|---|---|---|---|---|
| `lean/lean_deps.json` (67 MB) | `extract_lean_deps.py` | 205 files; 6 checks | everything downstream | **Derived** (content-hash) | ✅ **keystone** |
| `lean/atlas_view.json` (7.7 MB) | `atlas_view.py` | harness hooks, `/frontier`, 4 checks | where to aim fan-out; what not to re-derive | **Derived** | ✅ **best-instrumented store in the repo** |
| `docs/counts.json` / `.tex` | `update_counts.py` | **135 files**, 5 checks | every count claim in every paper | **Derived** | ✅ exemplary |
| `docs/ATLAS_HEATMAP.md` | `atlas_heatmap.py` | `sync_manifest`, pre-commit | — | **Derived** | ✅ |
| `docs/PERMANENT_TRACKED_HYPOTHESES.md` | `render_tracked_hypotheses.py` | `tracked_hypotheses_fresh` | assumption-surface disclosure | **Derived** | ✅ (replaced two hand ledgers that held disjoint contents) |
| `lean/SKEFTHawking/KernelNoGos.lean` | `gen_kernel_nogos_module.py` | Lean build | dead-fork enforcement | **Derived** | ✅ |
| `docs/BUNDLE_READINESS_HEATMAP.md` | `bundle_readiness.py` | 3 checks | per-bundle Stage-13 readiness | **Derived** | ✅ |
| `papers/claim_clusters.json` | `cluster_detect.py` | 5 readers, `claim_clusters_fresh` | cross-paper claim consistency | **Derived** | ⚠️ only 3 clusters; last content change 2026-05-04 |
| `SK_EFT_Hawking_Inventory_Index.md` autogen blocks | `update_inventory_index.py` | `inventory_index_autogen_fresh` | orientation | **Derived** (partial) | ✅ |
| `KERNEL_NOGO_REGISTRY` (45) | hand | atlas, `gen_kernel_nogos`, harness, `nogo_substrate_integrity` | steer away from provably-dead forks | Hand | ✅ **best hand-maintained store** — gate proves each backing theorem exists, is kernel-pure, non-vacuous |
| `HYPOTHESIS_REGISTRY` (48) | hand | 99 files; 4 checks | what is assumed vs proved | Hand | ✅ gated |
| `CITATION_REGISTRY` (652) | hand | **246 files**; 3 checks | citation integrity | Hand | ✅ gated |
| `PARAMETER_PROVENANCE` (206) | hand | 91 files; 2 checks | parameter trust tier | Hand | ✅ gated |
| `ARISTOTLE_THEOREMS` (322) / `AXIOM_METADATA` (10) / `PLACEHOLDER_THEOREMS` (26) / `MODELING_ASSUMPTION_THEOREMS` (21) / `VACUOUS_STATEMENT_BASELINE` (48) | hand | checks | substrate honesty | Hand | ✅ all gated |
| `SORRY_GAPS` (329, `aristotle_interface.py`) | hand | — | historical | Hand | ⚠️ **no gate** — only ungated in-code registry |
| `papers/*/bundle_metadata.json` (21) | `bundle_readiness.py` + review cycle | 102 files; 4 checks | bundle stage status | Mixed | ✅ but two-writer split needs §4 of the topology doc to read it |
| `papers/*/append_log.json` (**20 of 21** — `D7` missing) | `bundle_append.py` | 3 readers | lift audit trail | Hand/script | ⚠️ one bundle silently lacks it |
| `papers/*/claims_review*.json` (**58** files, 9 with ad-hoc suffixes `_r1/_r2/_wave4a_4/.v2_smoke`) | claims-reviewer | 7 readers | sentence-level grounding | Agent output | ⚠️ no schema governs the suffix set |
| `papers/AutomatedReviews/` (99 dated dirs) | reviewer agents | `extract_review_finding_nodes` → gates | readiness gates | Append-only | ✅ pipeline works; documented silent-drop points |
| `docs/review_finding_supersessions.json` (646 KB) | hand/agent | prose refs only | finding closure | Hand | ⚠️ 646 KB append-only ledger, **no gate** |
| `docs/dev-loops/PRE_DECISIONS.md` | human via `/debrief` | **5 code readers** + mandatory-read directive | what the loop decides without asking | Hand | ✅ **well-wired**; ⚠️ coach reads a stale PD range (§3) |
| `docs/dev-loops/SETTLED_FORKS.md` (129 KB, 59 forks) | hand | `lean_statements.py:631` (advisory), harness, `repo_state_probe` | route bans | Hand | ✅ acceptable — the kernel-encodable subset is machine-enforced, prose is only the residual |
| `docs/dev-loops/SYSTEM2_REGISTER.md` | harvest (Haiku→Opus) | `/debrief`, harness `active_issues` | dev-loop process fixes | Agent, **gitignored** | ⚠️ **840 KB.** CLAUDE.md calls this the *sharded, active* shard (Index + Open + Wins) with the archive holding Closed. The archive is 240 KB. **The active shard is 3.5× its own archive** — the sharding has inverted. Unreadable as a register. |
| `docs/QI_REGISTER.md` (System-1) | `qi_register.py`, then hand | **none** (its own generator + a docstring) | nothing | Nominally derived, hand-overwritten | ❌ **orphaned** |
| `docs/adrs/` (10 ADRs, 324 KB) | human+LLM | **zero machine readers**; 85 md mentions | architecture decisions | Hand | ✅ correct as-is — ADRs *should* be human-read; flagging only that nothing checks their claims against code (ADR-009's own "59 checks" is now 60) |
| `docs/audits/` (4 corpora + loose, ~2 MB) | reviewer agents + human | `bundle_readiness.py` reads `stage13_*.md` | Stage-13 GREEN verdicts | Hand/append | ⚠️ growing fast; only one file class has a reader |
| `papers/*/READINESS_GATES.md` | human | **zero** — no code, no doc | nothing | Hand | ❌ **abandoned convention: 3 files for 21 bundles**, newest 2026-06-10 |
| `docs/READINESS_GATES.md` (the 11-gate spec) | human | — (impl is `scripts/readiness_gates.py`) | gate semantics | Hand | ⚠️ **spec↔implementation has no freshness gate**; already caused the CountFreshness/NumericalFreshness name split between the two reviewers |
| `docs/roadmaps/` (**134 files, 4.1 MB**) | human+LLM | **zero programmatic reads** (9 docstring citations) | wave planning | Hand | ⚠️ **clearest accretion signal**; 4+ naming conventions (`PhaseN_`, `Phase5x_`, `Phase6AA_`, `Phase6o_prime_`, `Wave_6v.N_`) |
| `LAB_NOTEBOOK*.md` | `/goal` loop via `notebook_lib.py` | `notebook_lib`, pre-commit (advisory) | in-loop resume | Agent, **gitignored** | ✅ correct — ephemeral by design |
| `docs/RESEARCH_STATUS_OVERVIEW.md` (132 KB) · `PAPER_DRAFT_MAPPING.md` (84 KB) · `KNOWLEDGE_GRAPH.md` · `DASHBOARD.md` · `SIXTEEN_CONVERGENCE_STATUS.md` · `PAPER_TABLES_STATUS.md` · `SK_EFT_Hawking_Inventory.md` (327 KB) · `QA_QI_INFRASTRUCTURE_MAP.md` | hand | **zero machine readers** | — | Hand | ⚠️ **unread status docs.** `DASHBOARD.md`/`KNOWLEDGE_GRAPH.md` last touched 2026-06-13; `PAPER_TABLES_STATUS.md` 2026-04-15 |
| `docs/WAVE_EXECUTION_PIPELINE.md` (17 invariants) | hand | none | **the law** | Hand | ⚠️ the governing doc has no freshness gate; Invariant #14's roster is 2 authorizations stale and its Quick Reference still says *"All 16 checks"* |

### Reading of the table

- **The derived layer is a genuinely coherent architecture.** `lean_deps.json` →
  `atlas_view.json` → frontier/anti-frontier → SessionStart injection is a real closed
  loop: machine truth flows to the agent automatically and cannot drift. Same for
  `counts.json` → `counts.tex` → `\input` → `count_literals`. These are the parts to
  hold up as the pattern.
- **The hand-maintained layer is accretion, with two honourable exceptions**
  (`KERNEL_NOGO_REGISTRY` and `HYPOTHESIS_REGISTRY`) — and the exceptions are exactly the
  ones that acquired a *gate*. That is the whole lesson: a hand-maintained store with a
  validate check is fine; without one it rots at the rate of the project.
- **Redundant / orphaned / unread, named explicitly:**
  - **Orphaned:** `docs/QI_REGISTER.md` (System-1) — no reader, generator 3 months stale,
    file hand-edited past it. `papers/*/READINESS_GATES.md` — 3 files, zero readers.
  - **Redundant:** `docs/agents/claims_reviewer.md` duplicates the live plugin agent spec
    and is 3 months behind it, while two shipped code sites cite the stale copy as
    authoritative. This should be deleted and the citations repointed —
    or, if the change-log content is worth keeping, retitled explicitly as history.
  - **Unread:** the 4.1 MB roadmap corpus, the ~700 KB of status docs, the 646 KB
    supersession ledger.
  - **Inverted:** `SYSTEM2_REGISTER.md` at 840 KB vs its 240 KB archive.

**Recommended consolidations, with costs.** (a) Retire `papers/*/READINESS_GATES.md` in
favour of `bundle_metadata.json` + the heatmap — **cost: delete 3 files, one grep.**
(b) Delete or explicitly historicize `docs/agents/claims_reviewer.md` and repoint
`papers_prose.py:897` + `sentence_state.py:42` at the plugin agent — **cost: 1 file, 2 line
edits.** (c) Give System-1's QI register the same wiring System-2 already has (a reader, or
retire it) — **cost: a decision, then ~20 LoC either way.** (d) Fix the System-2 shard
inversion by running the existing roll/shard machinery — **cost: one `/skeft-qa:harvest`
maintenance pass; the tooling exists.** I would not consolidate the roadmaps or ADRs: they
are human-read by design and consolidation would destroy provenance. The roadmap corpus
needs a naming convention and an archive cut-off, not a merge.

---

## 7. Onboarding cost (Q7)

### The repo `CLAUDE.md` is genuinely good

`SK_EFT_Hawking/CLAUDE.md` (17 KB) does exactly the right thing: it states
*"Bootstrap = this file + WAVE_EXECUTION_PIPELINE"* and then presents everything else as an
explicit **when-to-read** table ("Read before…"). That is progressive disclosure done
properly, and it names the right prevention docs: the Lean hard rules (no `maxHeartbeats`,
axiom sign-off, kernel purity, `noncomm_ring`, `erw` for `RingQuot`) are precisely the
rules whose violation costs the most, and they are in the bootstrap file rather than behind
a link. **Bootstrap cost ≈ 82 KB ≈ 21k tokens. Proportionate.**

### The workspace `CLAUDE.md` undoes it

`Fluid-Based-Physics-Research/CLAUDE.md` (27 KB) loads **first**, opens with *"IMPORTANT:
These instructions OVERRIDE any default behavior and you MUST follow them exactly"*, and
then declares a **§Mandatory References** block of 10 documents introduced with *"Before
doing any work, read these in order (THIS ALSO APPLIES TO ALL SUBAGENTS & ANY TIME CONTEXT
IS COMPRESSED NO EXCEPTIONS)"*.

Measured, that mandatory set is:

| doc | size |
|---|---|
| WAVE_EXECUTION_PIPELINE.md | 66 KB |
| README.md | 63 KB |
| SK_EFT_Hawking_Inventory_Index.md | 102 KB |
| PAPER_STRATEGY.md | 67 KB |
| PAPER_DRAFT_MAPPING.md | 84 KB |
| BUNDLE_LIFT_PROCEDURE.md | 25 KB |
| claims-reviewer-bundle-prompts.md | 60 KB |
| LATE_PHASE6_ABSORPTION_PROTOCOL.md | ~20 KB |
| + 2 more | |
| **total** | **≈ 490 KB ≈ 120k tokens** |

Two problems, in order of severity:

1. **The two files disagree about the mandatory set**, and the one that says "OVERRIDE …
   NO EXCEPTIONS" is the one demanding ~6× more reading. A fresh session — or worse, every
   subagent, which the workspace file explicitly binds — either burns 120k tokens on
   bootstrap or silently disobeys an instruction that calls itself mandatory. In practice
   agents disobey it, which trains disregard for the strongest-worded instruction in the
   workspace. That is the real cost.

2. **The workspace file is not in git**, so nothing can gate its freshness, and it has
   drifted hard:
   - *"Full validation suite (**21 checks**)"* — actual: **60**.
   - *"Mathlib pinned `5e932f97`, v4.29.1; toolchain `leanprover/lean4:v4.29.1`"* — actual
     **`81a5d257` / v4.32.0** (bumped 2026-07-29, per the repo `CLAUDE.md` and
     `lean/lean-toolchain`).
   - *"We use 4.29.1 … much of our code relies on 4.29.x features"* — same.
   - *"the 20 publication targets"* — actual **21**.

   Three of these are load-bearing: an agent that believes the toolchain is 4.29.1 will
   reason wrongly about Mathlib API availability and Aristotle skew.

**Recommendation.** Reduce workspace `CLAUDE.md` §Mandatory References to the same two-item
bootstrap the repo file already declares, convert the other eight to a when-to-read table
(the repo file's table can be referenced verbatim), and delete every count/pin literal from
it in favour of a pointer (*"pins: see `SK_EFT_Hawking/CLAUDE.md`; check count: `validate.py
--list` is authoritative"*). **Cost: one editing pass over one file.** The alternative —
gating it — is not available while it lives outside git.

**Does the mandatory set point at what prevents mistakes?** The repo file's does. The
workspace file's does not: it mandates the two largest reference docs (`Inventory_Index`
102 KB, `PAPER_DRAFT_MAPPING` 84 KB) which are *lookup* artifacts — valuable on demand,
near-worthless read front-to-back — while the highest-value prevention documents in the
repo, `docs/dev-loops/PRE_DECISIONS.md` and `SETTLED_FORKS.md`, are **not in its mandatory
list at all**. They are instead injected by the harness at SessionStart, which is the better
mechanism — but that means the mandatory list is both too long and missing the two items
that most reliably prevent wasted cycles.

---

## 8. What fits well (stated deliberately, not as consolation)

1. **The derived-artifact spine.** `lean_deps.json` → `atlas_view.json` → frontier +
   anti-frontier → SessionStart injection → `/skeft-qa:frontier`. Machine truth reaches the
   agent automatically, with no hand-maintained intermediary. The **negative** frontier in
   particular — kernel-checked dead forks pushed at the agent as data rather than prose —
   is the correct structural answer to a documented recurring failure, and I found no
   equivalent anywhere else in the system.
2. **`bundle_registry_consistency`'s Leg C.** An AST walk that flags any *newly written*
   hardcoded roster. Most consistency checks only see the maps that already exist; this one
   sees the next one before it drifts. That instinct — gate the generator, not just the
   instances — is the same one ADR-004 applies to QI closure pathways, and it is the single
   best idea in the codebase. It should be the template for §3's plugin-reference test.
3. **The tier-0 commit gate's disposition discipline.** Fail-open on a missing toolchain,
   hard-block only on `main`, hard-block only on genuine soundness (three named checks +
   a build-log-derived `sorry` signal rather than a naive grep), and warn-not-block on
   staleness with the *reason* printed because the common cause is a benign merge. Every
   one of those choices is the right one, and each is justified in-line with the incident
   that produced it.
4. **`gate_precheck`'s side-effect discipline.** Refusing to call `review_figures.py --check`
   because it rewrites a tracked file, and passing `--no-archive` because a precheck runs
   repeatedly — that is someone thinking correctly about what a *repeatable* gate must be.
5. **The agent→suite direction is a real typed pipeline.** Reviewer markdown → heading
   regex → `ReviewFinding` node → `FLAGS` edge → Gate 11 → aggregate → heatmap, with the
   silent-drop points enumerated in `QA_QI_INFRASTRUCTURE_MAP.md` §3 rather than hidden.
6. **`test_skill_safety.py` exists at all.** A deterministic content-scan over plugin
   markdown, no model judgment, in the fast suite, written from four real incidents. The
   mechanism this report asks for in §3 is not new infrastructure — it is four more
   predicates in a file that already does the hard part.
7. **`VALIDATION_GATE_TOPOLOGY.md` itself.** It was written yesterday, it names its own
   sharp edge as "deliberate but under-scoped", and it publishes the current red state
   rather than hiding it. A system that documents its own worst seam is a system that can
   be fixed. Most of §5 is agreement with a doc that had already diagnosed itself.

---

## 9. Recommendations, ordered by value ÷ cost

| # | change | cost |
|---|---|---|
| 1 | Wire `gate_precheck s9` / `s10` into `BUNDLE_LIFT_PROCEDURE.md` §§8–9 and `wave-close/SKILL.md` step 2 | 3 lines of prose |
| 2 | Fix `agents/coach.md:17` `PD-0..PD-4` → the full Core list (PD-5 is operator-set and currently excluded) | 1 line |
| 3 | Fix `README.md:57` hook count (4→5) and the fail-open claim (the egress guard is fail-**closed**) | 2 lines |
| 4 | Add `test_referenced_code_identifiers_resolve` to `tests/test_skill_safety.py` | ~60 LoC |
| 5 | Repoint the two bundle-aware agent rosters at the 21-code canonical set; ideally have them read `bundle_registry` rather than restate it | ~10 lines |
| 6 | `gate_precheck s13 --scope {lean,paper}` over the existing module partition, with an always-on soundness core | ~60 LoC + 1 test |
| 7 | Delete the two dead check names in `claims-reviewer.md` (`paper_lean_refs`, `paper_hypothesis_disclosure`); replace with the live names + a "DISCHARGED by the check, audit only the residual" clause, mirroring Class PC | ~6 lines |
| 8 | Delete or historicize `docs/agents/claims_reviewer.md`; repoint `papers_prose.py:897` + `sentence_state.py:42` | 1 file, 2 edits |
| 9 | Have `gate_precheck` emit `gate_report.json`; teach the three reviewers to read it and skip discharged classes | ~30 LoC + 3 prompt paragraphs |
| 10 | Put pytest in a gate (at minimum `--scope`-aware in `wave-close`) | ~10 LoC, +285 s per close |
| 11 | Trim workspace `CLAUDE.md` §Mandatory References to the repo file's 2-item bootstrap; strip its stale count/pin literals | 1 editing pass |
| 12 | Decide System-1 QI register's fate: wire it like System-2, or retire it | a decision |
| 13 | Fix the System-2 shard inversion (840 KB "active" vs 240 KB archive) using the existing roll/shard tooling | 1 maintenance pass |
| 14 | Retire `papers/*/READINESS_GATES.md` (3 files, 21 bundles, zero readers) | delete 3 files |

Items 1–3 are one-line fixes to live correctness defects and should not wait for anything.

---

## Appendix — method

- All measurements taken in worktree `rv2` @ `db430c65` unless noted; `SYSTEM2_*` and
  `docs/dev-loops/` sizes read from the main checkout (gitignored, absent in worktrees).
- Check inventory from `uv run --no-sync python scripts/validate.py --list` (**60**, not the
  59 stated in `CLAUDE.md:109`, `_registry.py:63`, and ADR-009) and from
  `validate._CHECKS` grouped by `func.__module__`.
- Roster from `scripts/bundle_registry.BUNDLE_CODES` at runtime (21).
- Two breadth scans were delegated (plugin-reference resolution; store inventory). Every
  finding cited in §3 as a hard break, and every claim in §6 marked ❌ or ⚠️, was
  independently re-verified by me at file:line before inclusion — specifically the bundle
  rosters, the README hook count and fail-open claim, the coach PD range against
  `PRE_DECISIONS.md`'s actual Core headings, the absence of `data/`, the two dead check
  names (executed: `ERROR: unknown check`), and the `gate_precheck` caller grep.
- A full `validate.py --no-archive --json` run was started on this worktree and had not
  completed at 10 minutes, against the 134.2 s steady-state figure in
  `VALIDATION_GATE_TOPOLOGY.md` §5. This is consistent with a cold memo cache in a fresh
  worktree (`axiom_closure_allowlist` alone is 171.6 s cold) and is **not** offered as a
  contradiction of that figure — but it is worth noting that the cited cost is a warm-cache
  cost, and a wave-close in a fresh worktree pays the cold one.
