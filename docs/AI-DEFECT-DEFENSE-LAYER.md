# AI-Defect Defense Layer — Design Proposal (partially superseded)

This document defines the three-tier defense layer that backstops the SK-EFT Hawking pipeline against the AI-generated-content failure classes documented by Mathlib's April 2026 contribution-guidelines update and arXiv's three-stage 2025–2026 moderation actions (CS moratorium Oct 2025, Math endorsement tightening Dec 2025 / Jan 2026, Dietterich one-year ban May 2026). The layer is structured as pre-commit hook → `validate.py` check → reviewer-agent residue, with explicit promotion of LLM-caught defects to deterministic prevention wherever feasible.

> ⚠️ **STATUS: this is a PROPOSAL, not a description of the running system.** It was
> written as a design and never built as specified. Read §Coverage below **first** — it
> maps every proposed control to what actually guards that ground today, and most of the
> substance has since shipped by other names and through other mechanisms. Nothing here
> should be cited as evidence that a control exists.

**Proposed implementation (unbuilt as written).** Tier 1 as a committed
`scripts/pre_commit_hook.sh` plus an idempotent `scripts/install_pre_commit.sh`; Tier 2 as
named `validate.py` checks; Tier 3 as a prep-brief consumed by the reviewer agents (which
ship in the `skeft-qa` plugin). Neither Tier-1 script was written. The commit gate that
does exist is `scripts/pre-commit-sync.sh` plus a local, uncommitted `.git/hooks/pre-commit`
— a different design, documented in
[`docs/architecture/VALIDATION_GATE_TOPOLOGY.md`](architecture/VALIDATION_GATE_TOPOLOGY.md).

## Status model

This is a defense layer, not a new readiness gate. The three tiers map onto the existing 11-gate taxonomy in `READINESS_GATES.md`:

- **Tier 1** (pre-commit hooks) fires before Stage 1 — entry-condition checks that prevent obvious LLM artifacts from entering the codebase.
- **Tier 2** (`validate.py` checks) fires at Stages 5, 7, and 12 — joining the existing 22+ checks, mapping to gates 1, 5, 6, 9.
- **Tier 3** (reviewer agents) fires at Stages 9, 10, 13 — applied to the irreducible semantic residue, with a pre-review briefing of which deterministic checks have already cleared.

Tiers 1 and 2 are deterministic; Tier 3 is LLM-judgment-only. Tier 1+2 must be green before Tier 3 may run — see Pipeline Invariant #16.

---

## Coverage — what actually guards this ground

Measured against the live check registry, not inherited from this document's own claims.
Read this before treating any Tier below as a description of the system.

### Tier 2 — proposed check → what exists

| proposed check | today |
|---|---|
| `axiom_closure_allowlist` | ✅ **shipped under this exact name.** Every declaration's transitive axiom closure is held to an allowlist |
| `bundle_lean_refs_resolve` | ✅ covered by `prose_theorem_reference_coverage` — bundle-draft Lean references in any verbatim form — and `lean_docstring_refs_resolve` for the docstring direction |
| `bundle_latex_compile_clean_citations` | ✅ covered by `paper_latex_compiles`, which compiles every bundle draft (its slow-gate default SKIP is gone) |
| `bibitem_registry_character_match` | ◐ **partial.** `bibitem_title_primary_source` compares the registry title to page-1 text of the cached PDF. Authors, journal, volume and page are not compared by any check |
| `threshold_arithmetic` | ◐ **partial, by artifact not by rule.** `paper_table`, `d1_hierarchy_table` and `f_hierarchy_claims` hold their targets to the canonical evaluator at displayed precision. There is no general mechanism that recomputes an arbitrary number quoted in arbitrary prose |
| `citation_bibkey_form_matches_metadata` | ❌ not built. `theorem_name_embedded_citations` checks a different thing — declaration names embedding author+year |
| `theorem_quoted_bound_matches_lean_literal` | ❌ not built, and named as a genuine absence in [`VALIDATION_ARCHITECTURE.md` §6](architecture/VALIDATION_ARCHITECTURE.md#6-what-this-subsystem-does-not-do): a cited theorem's *statement* is unverified |
| `mathlib_linter_clean` | ❌ not built; no `lintDriver` is configured |
| `viz_log_axis_hrect_safety` | ❌ not built (`viz_consistency` covers imported-physics and style, not this) |

### Tier 1 — proposed token check → what exists

| proposed | today |
|---|---|
| `set_option maxHeartbeats` in a proof body | ✅ **enforced** — Invariant #10, via a zero-headroom ratchet in `lean_toolchain.py`, alongside the advisory `elaboration_knob_watchlist` for the kernel-irrelevant knobs |
| `native_decide` justification | ✅ covered by `native_decide_regression` (decl-closure ratchet), which the commit gate runs |
| `^axiom` needs `AXIOM_METADATA` | ✅ Invariant #15 (axiom sign-off) plus `axiom_closure_allowlist`; the allowlist is the mechanical half |
| `decreasing_by sorry` | ✅ subsumed by `lean_zero_sorry` — Invariant #4 fails on `sorry` anywhere in a closure |
| forbidden placeholder strings in TeX | ◐ `paper_provenance` catches a placeholder bibliography; the general LLM-artifact string list is not scanned |
| **`@[csimp]` without a justification comment** | ❌ **not guarded anywhere** — zero occurrences of `csimp` across `scripts/` and `tests/`. This is the one genuinely uncovered soundness item in the whole proposal: `@[csimp]` can smuggle an axiom past the kernel's usual guarantees (`leanprover/lean4` issue #7463). If any part of this document is built, build this |
| `unsafe` / `partial def` scope limits | ❌ not gated by a check (`lean_verify` surfaces them interactively) |

**The residue worth building is small and specific**: the `@[csimp]` guard, and the two
citation-metadata checks. The rest is either shipped, partial-by-design, or superseded.

---

## Tier 1 — Pre-commit hooks

Fires on every `git commit` to `SK_EFT_Hawking/`. Failures abort the commit; `git commit --no-verify` is the documented emergency override with mandatory follow-up before the next push.

### Token-class checks (staged Lean diff)

For every new `+`-line in `*.lean` files:

- `^axiom ` (declaration-level) — must have a matching entry in `src/core/constants.py::AXIOM_METADATA`. Backstops Pipeline Invariant #15.
- `@[csimp]` — disallowed without inline `-- csimp-justification: <text>` comment (per `leanprover/lean4` issue #7463, axiom-smuggling exploit).
- `unsafe` — disallowed outside files declared as `lean_exe` in `lakefile.toml`. ExtractDeps.lean is the only currently-exempt file.
- `partial def` — same scope as `unsafe`.
- `decreasing_by sorry` — disallowed unconditionally (zero-sorry discipline).
- `set_option maxHeartbeats` or `set_option synthInstance.maxHeartbeats` — disallowed in any line whose enclosing context is `theorem`/`lemma`/`example`/`def`/`noncomputable def` (Pipeline Invariant #10, ExtractDeps.lean exempted).
- `native_decide` — must be on a line preceded within 3 lines by `-- native_decide: <justification>` comment.

### Token-class checks (staged TeX diff)

For every new `+`-line in `papers/**/*.tex`:

- Forbidden LLM-artifact strings (case-insensitive grep): `as an AI`, `language model`, `ChatGPT`, `Claude `, `GPT-`, `Certainly!`, `Here is a `, `would you like`, `let me know`, `I cannot`, `I'm sorry`, `Note that I`, `In summary,`, `the data in this table is illustrative`, `fill in the real`. These are Dietterich's documented arXiv one-strike triggers.
- Forbidden placeholder strings: `[REFERENCE]`, `[CITATION]`, `XXX`, `TODO`, `(citation needed)`.

### Structural checks (staged TeX diff)

- Every `\texttt{Module.symbol}` pattern in newly-added lines resolves against `lean/lean_deps.json` (Class TN check at commit time; backstops `qi-leantheoremdrift`).
- Every `\bibitem{key}` reference in newly-added lines has a matching `key` in `src/core/citations.py::CITATION_REGISTRY` (commit-time prefiguring of Stage 13's CitationIntegrity gate).


### Installation

`scripts/pre_commit_hook.sh` is the source-of-truth script (committed to the repo). `scripts/install_pre_commit.sh` copies it into `.git/hooks/pre-commit` and chmod-+x's it. The installer is idempotent; running it twice on the same checkout produces the same hook.

---

## Tier 2 — `validate.py` extensions

Each new check follows the existing `validate.py --check <name>` discipline. Registration goes in `scripts/validate.py`'s check registry; the help output (`validate.py --list`) gains a one-line entry per check. Failure semantics mirror existing checks: WARN by default, FAIL at submission gate. Per-paper aggregation flows through `validate.py --check readiness_submission_gate`.

| Check | Closes QI item | Maps to gate | Cost (Regime B) |
|---|---|---|---|
| `bundle_lean_refs_resolve` | qi-leantheoremdrift | 5 LeanProofSubstance + 9 NumericalFreshness | 2–4 hr |
| `axiom_closure_allowlist` | (new — backstops Invariant #15) | 5 LeanProofSubstance | 4–6 hr |
| `bibitem_registry_character_match` | qi-bibitem_registry_drift | 1 CitationIntegrity | 2–3 hr |
| `bundle_latex_compile_clean_citations` | qi-bundle_skeleton_inline_bibliography | 1 CitationIntegrity | 2 hr |
| `citation_bibkey_form_matches_metadata` | qi-citation_authoryear_metadata_match | 1 CitationIntegrity | 1–2 hr |
| `threshold_arithmetic` | qi-numericalverification | 9 NumericalFreshness + 4 ComputationCorrectness | 4–6 hr |
| `theorem_quoted_bound_matches_lean_literal` | qi-leantheoremname + qi-prose_lean_numerical_bound_gap | 5 LeanProofSubstance | 3–5 hr |
| `mathlib_linter_clean` | (wraps `lake lint`) | 5 LeanProofSubstance | 15 min config + 1 wave to scrub |
| `viz_log_axis_hrect_safety` | qi-vizdiscipline | (advisory) | 1–2 hr |

### Check specifications

**`bundle_lean_refs_resolve`.** Walks every `papers/<key>/paper_draft.tex`, extracts `\texttt{([A-Za-z]+\.[a-zA-Z_]+)}` matches, looks up each `(module, symbol)` pair in `lean/lean_deps.json`. Fails on any unresolved reference. Promotes `scripts/audit_paper_lean_refs.py` (Phase 6i Wave 4) from advisory to gating.

**`axiom_closure_allowlist`.** New `lean_exe AxiomAudit` that walks every theorem in `SKEFTHawking.*`, runs `Lean.collectAxioms` on each, emits `{theorem_name: [axiom_names...]}` as JSON to stdout. Python wrapper compares each closure against `[propext, Classical.choice, Quot.sound] ∪ AXIOM_METADATA.keys()`. Fails on any axiom outside the union. Reuses ExtractDeps.lean's existing closure machinery; the new Lean code is the JSON-emission entry point. Mirrors the lean4 plugin's `/check-axioms` slash command exactly so a developer who uses `/lean4:checkpoint` interactively satisfies this check at commit time.

**`bibitem_registry_character_match`.** For each `\bibitem{key}` in every paper, parses the bibitem text (authors, title, journal, volume, page, year) and compares against `CITATION_REGISTRY[key]` to within character tolerance (case-insensitive, whitespace-normalized, common journal abbreviations). Fails on substantive mismatch. Catches the D1-style "bibitem and registry describe different real papers" failure mode (4 instances in one bundle Stage 13).

**`bundle_latex_compile_clean_citations`.** Greps every `papers/<bundle>/paper_draft.log` for `Citation '.+' undefined` and `No file .+\.bbl` patterns. Augments the bundle-lift procedure's LaTeX-compile gate. Companion change: update `scripts/bundle_append.py` template to emit inline `\begin{thebibliography}{99}` instead of `\bibliography{<name>}` so the empty-bib failure mode cannot recur structurally (per the QI-register's structural-prevention pattern).

**`citation_bibkey_form_matches_metadata`.** For each `CITATION_REGISTRY[key]`, parses the bibkey using `<LastName>(<LastName>)*<Year>` regex. Verifies the parsed last-name appears in the entry's `authors` field and the parsed year matches `entry['year']` within ±1 (arXiv-vs-journal year drift allowed). Catches `KaulMajumdar1998` (canonical paper is 2000 PRL) and `SextyWetterich2009` (canonical paper is Berges-Sexty 2008, no Wetterich).

**`threshold_arithmetic`.** Scans paper TeX for `≈|=`-quoted relations between named formula terms and numerical values via regex (`\$([A-Za-z_]+)\([0-9.]+(\\kappa|c)?\) \\approx [0-9.]+\$` pattern family). Evaluates the named formula via `src.core.formulas` at the quoted argument; fails on >0.5% disagreement. Catches the E1-style propagating G-threshold drift (`G > 0.01` quoted but correct value is `G > 0.5`).

**`theorem_quoted_bound_matches_lean_literal`.** When a `\texttt{Module.symbol}` reference appears in a sentence quoting a numerical bound (`X ≤ Y` / `X = Y` / `X ≈ Y`), checks that the named Lean theorem's *statement* (not docstring) contains `Y` as a literal, OR that the prose-quoted value is bounded by the theorem's stated bound. Extends claims-reviewer Class TN with statement-vs-docstring discrimination. Once this ships, the claims-reviewer's Class TN scope shrinks accordingly.

**`mathlib_linter_clean`.** Wraps `lake lint`. Setup: add `lintDriver = "batteries/runLinter"` to the first block of `lean/lakefile.toml`. Initially WARN-only during the first wave that scrubs accumulated violations; escalates to FAIL at the close of that wave. Enables Mathlib's default linter suite (`dup_namespace`, `dangerous_instance`, `fails_quickly`, `has_nonempty_instance`, `check_univs`, `unreachable_tactic`, `unused_tactic`, `unused_arguments`, `ge_or_gt`, `doc_blame`, `illegal_constants`).

**`viz_log_axis_hrect_safety`.** Scans `src/core/visualizations.py` for `add_hrect` + `annotation_position` + log-scale-yaxis combinations and emits WARN. Advisory only — figure-reviewer remains the final arbiter. Closes `qi-vizdiscipline` at the structural-prevention level.

---

## Tier 3 — Reviewer-agent residue

The three existing agents shift to consuming a deterministic-status prep brief and concentrate their context budget on the irreducible semantic residue.

### Pre-review briefing protocol

New `scripts/review_runner.py --prep-brief` command emits per-paper or per-bundle JSON to `papers/AutomatedReviews/<date>/<paper>.prep-brief.json`:

```json
{
  "paper": "D3",
  "bundle_target": "D3",
  "review_date": "2026-05-27T14:32:00Z",
  "tier_1_status": "clean | no_recent_commits",
  "tier_2_status": {
    "bundle_lean_refs_resolve": "passed | failed | skipped",
    "axiom_closure_allowlist": "passed | failed | skipped",
    "bibitem_registry_character_match": "passed | failed | skipped",
    "bundle_latex_compile_clean_citations": "passed | failed | skipped",
    "citation_bibkey_form_matches_metadata": "passed | failed | skipped",
    "threshold_arithmetic": "passed | failed | skipped",
    "theorem_quoted_bound_matches_lean_literal": "passed | failed | skipped",
    "mathlib_linter_clean": "passed | failed | skipped"
  },
  "agent_focus_residue": [
    "structural_tautology_in_lean_proof_bodies",
    "semantic_citation_target_match",
    "definitional_intent_match",
    "narrative_overclaim_judgment",
    "cross_bundle_cluster_semantic_drift",
    "first_claim_prior_art_search"
  ]
}
```

### Agent prompt updates

Adversarial-reviewer and claims-reviewer add step zero: "Read the prep brief. If any Tier 2 check is `failed`, halt and instruct the user to fix Tier 2 before invoking Tier 3. Tier 3 agents are residue-only and must not be used as a fix-Tier-2 cycle."

Adversarial-reviewer finding-class instructions narrow:

- Class 1 (CitationIntegrity): cache + Tier 2 verify metadata; agent verifies whether the cited paper actually supports the sentence's claim (semantic).
- Class 2 (ParameterProvenance): Tier 2 verifies entry-vs-paper agreement; agent verifies whether the cited source's table/figure actually contains the value in context.
- Class 3 (LeanProofSubstance): PlaceholderMarker syntactic check is Tier 2; agent checks for structural tautology where a hypothesis appears in the conclusion via `⟨_,_⟩` / `And.intro` (the `qi-gate-5-self-audit-blind-spot` pattern).
- Class 4 (CrossPaperConsistency): bibkey-arXiv consistency is Tier 2; agent checks semantic-meaning consistency across papers.
- Class 5 (NarrativeGrounding): largely LLM. First-claim search is the only sub-class with potential determinism (Gate 10 ledger, currently `needs-recheck`).
- Class 6 (AssumptionDisclosure): Tier 2's claims-reviewer Class HD catches missing-in-prose; agent verifies disclosure is load-bearing for reader interpretation.
- Class 7 (NumericalFreshness): Tier 2's `threshold_arithmetic` catches drift; agent checks whether the prose-quoted value matches the *intended* claim, not just the *current* canonical value.
- Class 8 (ProductionRunHealth): graph query is Tier 2; agent checks whether the prose claim of evidence is appropriately calibrated to the run's actual scope.

Claims-reviewer Class TN's `\texttt{Module.symbol}` arm sunsets once `bundle_lean_refs_resolve` ships. Class TN survives in the agent until `theorem_quoted_bound_matches_lean_literal` also ships, after which it sunsets entirely.

Figure-reviewer is unchanged.

---

## Integration with the lean4 plugin

Interactive and CI flows are complementary:

**Interactive flow (Claude Code developer session).** `prove`/`autoprove` → `review` → `golf` → `checkpoint` (build + axiom check + commit) → push. The `/lean4:checkpoint` workflow's axiom check uses the same `Lean.collectAxioms` logic as Tier 2's `axiom_closure_allowlist`. A developer who uses `/lean4:checkpoint` is satisfying Tier 2's axiom gate at save time.

**CI flow.** `git commit` → Tier 1 hooks fire (independent of whether the developer used the plugin) → push → CI runs `validate.py` full suite → Tier 2 fires → if green, Stage 9/10/13 run reviewer agents → if green, paper advances per existing readiness-gate workflow.

The `/lean4:check-axioms` slash command and `validate.py --check axiom_closure_allowlist` share an underlying Lean executable (`lean_exe AxiomAudit` in `lean/SKEFTHawking/AxiomAudit.lean`). Discipline defined once; invoked interactively from the plugin and non-interactively from CI.

`lean4-contribute` is unrelated to Mathlib upstream — it's a helper for filing GitHub issues on the lean4-skills repo itself. Re-enable on its actual merits, separately from any Mathlib-PR-upstream consideration. Mathlib-PR-upstream tooling belongs in the future spin-out repo (see deferred items below).

---

## Proposed pipeline invariant — UNNUMBERED

⚠️ **This carries no invariant number, deliberately.** The numbered invariants are
allocated in `WAVE_EXECUTION_PIPELINE.md`, which is their only registry: **#15** is axiom
sign-off, **#16** is the tracked-hypothesis registry, **#17** is the kernel no-go registry.
A proposal does not hold a number — it would be allocated the next free one at the point
it is built and appended there, and until then any number written here is a collision
waiting to be quoted.

Proposed language, were this built:

> **16. Every commit passes the three-tier AI-defect-defense layer.** Tier 1 pre-commit hooks fire automatically on `git commit`; Tier 2 `validate.py` checks fire at Stage 7 and at the submission gate; Tier 3 reviewer agents fire at Stages 9 / 10 / 13 only on artifacts that have already cleared Tier 1 + Tier 2. Tier 3 agents MUST NOT be invoked on artifacts with open Tier 1 / Tier 2 failures — the agents are residue-only and may not be used as a fix-Tier-2 cycle. Tier 2 checks grow (never shrink) as new defect classes surface, following the QI-register promotion pattern: every LLM-caught defect class that appears twice becomes a candidate for promotion to a Tier 2 check on the next wave. The lean4 plugin's interactive workflows (`/lean4:check-axioms`, `/lean4:checkpoint`, `/lean4:review`) are the developer-facing equivalent of Tiers 1 + 2 and may be invoked at any time during a session; CI does not depend on developer use of the plugin. See this document for the design.

### Pipeline-stage edits

- Stage 5 gate text: append "AND `lake lint` passes (post-retrofit; WARN-only during retrofit wave)" AND "AND `validate.py --check axiom_closure_allowlist` passes."
- Stage 7 check count: 22 → 29 (new Tier 2 checks).
- Stage 13 prerequisites: add "Tier 1 and Tier 2 are green. Tier 3 agents will refuse to run if either is failing — see Pipeline Invariant #16."

---

## QI register closure map

Seven open QI items close as structural prevention when their corresponding Tier 2 check ships (matches Wave 1 CitationIntegrity / Wave 6 CountFreshness closure pattern):

| QI item | Closes when this ships |
|---|---|
| qi-leantheoremdrift | `bundle_lean_refs_resolve` |
| qi-bundle_skeleton_inline_bibliography | `bundle_latex_compile_clean_citations` + bundle_append.py template fix |
| qi-bibitem_registry_drift | `bibitem_registry_character_match` |
| qi-citation_authoryear_metadata_match | `citation_bibkey_form_matches_metadata` |
| qi-numericalverification | `threshold_arithmetic` |
| qi-leantheoremname | `theorem_quoted_bound_matches_lean_literal` |
| qi-prose_lean_numerical_bound_gap | `theorem_quoted_bound_matches_lean_literal` (same check, both cases) |
| qi-vizdiscipline | `viz_log_axis_hrect_safety` (advisory closure) |

Closures recorded in `docs/QI_REGISTER.md` `## Closed Items` with `evidence_on_close: <wave-id>`. `qi-gate-5-self-audit-blind-spot-on-sibling-tautologies` stays open — Tier 3 residue, no Tier 2 promotion available.

---

## Pareto-ordered rollout checklist

Items ordered by leverage (highest first); each is independently shippable. Cost estimates are Regime B (internal velocity).

### Top quartile (highest leverage)

**P1. Add `lintDriver = "batteries/runLinter"` to `lean/lakefile.toml`.** One-line config change. Run `lake lint` once locally, file the accumulated violations as a tracked retrofit wave (probably 1 day total). Mathlib's default linter suite becomes available across all future commits. **Cost: 15 min config + 1 wave of scrubbing.**

**P2. Ship `bundle_lean_refs_resolve`.** Promotes `qi-leantheoremdrift`. Single biggest empirically-validated promotion — closes the QI item that surfaced ~32 BLOCKER instances across D1+D2+D3+D4. Augments existing `scripts/audit_paper_lean_refs.py`. **Cost: 2–4 hr.**

**P3. Install `scripts/pre_commit_hook.sh` with token + structural checks.** Lean-token grep, LLM-artifact TeX grep, `\texttt{Module.symbol}` resolution, bibitem-key existence. Installer is `scripts/install_pre_commit.sh`. **Cost: 4–6 hr.**

**P4. Ship `axiom_closure_allowlist`.** ✅ **SHIPPED 2026-05-28 (commit `1798633`).** Lifts lean4 plugin's `/check-axioms` logic into a non-interactive gate. Backstops Pipeline Invariant #15. Lean exe `lean/SKEFTHawking/AxiomAudit.lean` (reuses the memoized `AxiomClosure`) + `validate.py --check axiom_closure_allowlist` (registered in the default suite, ~49s; WARN-first, hard-fail under `--strict`). **Audit finding:** 0 declared axioms + 0 genuinely-unexpected axioms (Invariant #15 clean), but **811 declarations transitively use `native_decide`** (per-decl compiler-trust axiom `*._native.native_decide.ax_*`) — recognised as a distinct accepted-but-visible category; the real trust surface that `counts.json 'Axioms: 0'` does not capture. `AXIOM_METADATA` (10 historical-eliminability keys) reconciled: none currently live.

### Second quartile (high leverage, paper-side QI promotions)

**P5. Ship `bibitem_registry_character_match`.** Closes `qi-bibitem_registry_drift`. **Cost: 2–3 hr.**

**P6. Ship `bundle_latex_compile_clean_citations` + fix `bundle_append.py` template** to emit inline `\begin{thebibliography}{99}` instead of `\bibliography{<name>}`. Closes `qi-bundle_skeleton_inline_bibliography` at the structural-prevention level. **Cost: 2 hr.**

**P7. Ship `theorem_quoted_bound_matches_lean_literal`.** Closes both `qi-leantheoremname` and `qi-prose_lean_numerical_bound_gap`. Once shipped, claims-reviewer Class TN can fully sunset. **Cost: 3–5 hr.**

**P8. Ship `threshold_arithmetic`.** Closes `qi-numericalverification`. Most cost is the regex extraction + formula-evaluation linkage. **Cost: 4–6 hr.**

**P9. Ship `citation_bibkey_form_matches_metadata`.** Closes `qi-citation_authoryear_metadata_match`. Cheapest individual promotion. **Cost: 1–2 hr.**

### Third quartile (agent shaping)

**P10. Ship `scripts/review_runner.py --prep-brief`.** Emits the Tier 2 status JSON the agents consume. **Cost: 2–3 hr.**

**P11. Update `adversarial-reviewer.md` and `claims-reviewer.md` to read the prep brief and refuse to run on Tier-1/2 failures.** Narrows finding-class instructions per the residue list. **Cost: 2–3 hr.**

**P12. Sunset claims-reviewer Class TN's `\texttt{Module.symbol}` arm.** Document the status change in the agent file. **Cost: 30 min.**

### Fourth quartile (documentation + advisory)

**P13. Append Pipeline Invariant #16 to `WAVE_EXECUTION_PIPELINE.md`.** Paste the language from the section above. **Cost: 15 min.**

**P14. Update `docs/QI_REGISTER.md` `## Closed Items` for the eight promoted QI items.** Use existing closure-pathway convention (#2 structural prevention) per QI item. **Cost: 30 min per item batch.**

**P15. Update `docs/READINESS_GATES.md` gates 1, 5, 6, 9 to reference the new Tier 2 checks in their evaluator-input lists.** **Cost: 30 min.**

**P16. Ship `viz_log_axis_hrect_safety`.** Closes `qi-vizdiscipline`. Advisory only. **Cost: 1–2 hr.**

### Deferred (post-spin-out)

**D1. Mathlib-PR-upstream layer.** Lives in the future Mathlib-targeted spin-out repo. Adds AI-disclosure label automation, `LLM-generated` PR label rule, American-spelling regex, naming-convention enforcement (`Is`-prefix discipline), `lake lint` wired into Mathlib's CI workflow format. **Cost: 3–5 days in a dedicated wave when the spin-out repo exists.**

**D2. Gate 10 (FirstClaimVerification) ledger.** Per `READINESS_GATES.md`: currently `needs-recheck` for every paper with a first-claim. Adds `FirstClaimLedger` node type to the graph. **Cost: 2 days.**

---

## Acceptance criteria

The defense layer is shipped when:

1. P1–P13 are complete; `validate.py --list` shows the new Tier 2 checks; `lake lint` is wired and either WARN-clean or FAIL-clean.
2. `validate.py` full suite passes with all new checks enabled.
3. Tier 1 pre-commit hook is installed; `scripts/install_pre_commit.sh` is idempotent.
4. Eight promoted QI items have `evidence_on_close` populated in `docs/QI_REGISTER.md`.
5. Pipeline Invariant #16 is in `WAVE_EXECUTION_PIPELINE.md`.
6. One full wave executes start-to-finish with the layer active, and the QI register does not surface any defect class that should have been caught at a tier earlier than where it was caught.

P14–P16 are documentation polish; D1–D2 are deferred.

---

## Why this and not more / fewer

The defense layer is shaped by the project's existing QI-promotion pattern. Wave 1 promoted citation integrity to the primary-source cache; Wave 6 promoted count freshness to the counts.tex macros. This layer extends that pattern: every Tier 2 check promotes an already-observed LLM-caught defect class. No speculative checks. The eight Tier 2 promotions correspond to all eight open process-level QI items eligible for structural prevention; the ninth check (`axiom_closure_allowlist`) backstops the highest-stakes Pipeline Invariant (#15).

Tier 1 catches the universally-cheap LLM tells documented as Dietterich's arXiv one-strike triggers. Tier 3 shrinks rather than grows — the agents shed work that became deterministic, gaining context budget for residue at no infrastructure cost.

**Not included and why:**

- **`#lint` (Lean 3 user command):** subsumed by `lake lint` via Batteries' `runLinter`.
- **CRLF / file-encoding / whitespace checks:** standard Mathlib-CI fare; folded into `lake lint`'s `style` linters.
- **`bundle_bib_filename`:** superseded by `bundle_latex_compile_clean_citations` per the QI register's own analysis.
- **Notebook-side LLM-artifact grep:** notebooks enforce no-evaluative-print discipline already (CHECK 6); LLM artifacts in markdown cells are caught by the claims-reviewer; a separate tier isn't worth the infrastructure cost.

The layer is additive going forward: new Tier 2 checks continue to be added as new defect classes surface, following the same promotion path. The success metric is whether the QI register's open-items count trends down over time without trading for an increase in agent context cost. If a defect class appears twice and there's no Tier 2 check planned, that becomes a QI item itself.