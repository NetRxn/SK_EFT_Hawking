# ADR-004 — Substrate Integrity Gates: shift-left structural prevention of the proof-substance & assumption-disclosure failure classes

- **Status:** **ACCEPTED + IMPLEMENTED (2026-06-13).** Five standing automated gates (R1–R5) installed and green, moving detection of the *proof-substance* and *assumption-disclosure* failure classes left from the Stage-13 fresh-context review into Stages 2/5/7; the two QI items that name these classes (`qi-leanproofsubstance`, `qi-assumptiondisclosure`) re-closed via **structural prevention** (Stage-14 pathway #2); Pipeline Invariants #4 and #9 given automated teeth and **new Invariant #16** added. Delivered as commits `6dc125ea` (W1+W2) / `1555759c`+`616cc35d` (W3) / `1df05fc9` (W4) / `047d73cf` (W5) / W6 integration; gates: `placeholder_not_cited`, `proxy_body_audit`, `tracked_hypothesis_ledger`, `tracked_hypotheses_fresh`, `formula_grounding`, `native_decide_regression`. Two follow-up backlogs surfaced (NOT effort-deferred, gated + visible): **FormulaRefSweep** (81 dangling formula→Lean refs) and the 6 `vacuous_proxy` theorem strengthenings. Execution tracked by [SubstrateIntegrityGates roadmap](../roadmaps/SubstrateIntegrityGates_Roadmap.md).
- **Deciders:** John Roehm (project owner); investigation + draft by Claude (Opus 4.8).
- **Context source:** the 2026-06-13 whole-substrate weakness audit ([SUBSTRATE_WEAKNESS_AUDIT_2026-06-13](../audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md) — 408 findings → 60 ranked, with a primary-author hand-verification pass against source for the 7 highest-severity items); direct reads of `WAVE_EXECUTION_PIPELINE.md` (Stages 2/3a/5/7/10/13/14 + Invariants #4/#9/#15), `docs/QI_REGISTER.md` (`qi-leanproofsubstance`, `qi-assumptiondisclosure`, `qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`, `qi-prose_lean_numerical_bound_gap`), `src/core/constants.py` (`PLACEHOLDER_THEOREMS`, `HYPOTHESIS_REGISTRY`), `scripts/validate.py` (`check_formulas_to_theorems`), and the Lean source behind findings #1/#3/#9/#13/#25.
- **Related:** [ADR-002](ADR-002-native-decide-policy.md) (kernel-trust / `native_decide` posture — its **P4 gate** `axiom_closure_allowlist` owns the compiler-trust surface; R4 surfaces that gate's decl-closure count into `counts.json`, R2 defers the `native_decide` class to it, R5 enforces its Decision #2 prose-precision); [ADR-003](ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md) (the `topo` `2 ∣ σ/8` tracked-hypothesis posture — confirms audit finding #1 is principled framing, not deception; `topo` is already in `HYPOTHESIS_REGISTRY['rokhlin_sigma_mod_16']` and is the template compliant-disclosed-assumption for R2/R3); [ADR-001](ADR-001-commring-qcyc5ext-roadmap.md) (upstream of ADR-002; supplies the `powerTable` machinery that *eliminates* native_decides in the qgroup cluster R4 counts); [Phase 5q.T roadmap](../roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md) (its **T5 proxy-detector** is the seed R2 generalizes); `HYPOTHESIS_REGISTRY` + `PLACEHOLDER_THEOREMS` (`constants.py`); Pipeline Invariants #4, #9, #15.

---

## Context

### The audit finding that motivates this ADR

The 2026-06-13 audit established that the library is genuinely kernel-clean (**0 axioms, 0 sorry**, `counts.json`) and that the real weakness surface is four *structural* classes that every existing automated counter is blind to by construction:

1. **Defining-the-conclusion / proof-substance.** Substantive content is discharged into a *definition* — a struct field (`SmoothSpinManifold4.topo : 2 ∣ σ/8`), a definitional identity (`verlindeEntropy_SU2k := kaulMajumdarS A G_N 0`), a Bool registry (`rDIndependentNoGo | _ => true`), or a `: True` stub (`gauge_emergence_statement`, `h2_discharged`) — so the headline theorem's *proof* is a trivial `rfl` / `decide` / `cases <;> rfl` / field projection. The **statement is not literally `True`** (evades the placeholder counter), there is **no `sorry`/`axiom`** (evades those counters), and there may be **no `native_decide`** (evades the lint). All three guards pass simultaneously.

2. **Tracked-hypothesis ledger drift.** Load-bearing assumptions are packaged honestly as `def … : Prop` hypotheses (the project's principled alternative to axioms) but are not swept into either ledger. On disk: **81** `def H_*` Props, **42** consumed as `(h : H_*)` hypotheses, **only 7** in `HYPOTHESIS_REGISTRY` and **7** in `PERMANENT_TRACKED_HYPOTHESES.md`. Struct-field assumptions like `topo` are not `H_*`-named and are invisible to even a naive sweep.

3. **Name-presence formula grounding.** Pipeline Invariant #4 ("every formula has a Lean theorem") is enforced by `check_formulas_to_theorems`, which only verifies the cited theorem **name string** exists in the Lean tree and appears in the docstring — never that the theorem's *statement* encodes the formula's relation. The mapping is **7 hardcoded pairs**; most of `formulas.py` is unchecked. This is how a 7–9-order δ_diss dimensional error hid for the project's history.

4. **Placeholder-cited-as-verified in prose.** Invariant #9 already states placeholder `True := trivial` theorems "MUST NOT be referenced by any … paper claim," but nothing enforces it. `paper7_chirality_formal/paper_draft.tex` (L306–310) presents the general-`G` equivalence `Z(Vec_G) ≅ Rep(D(G))` — a `True := trivial` stub — as part of "4049 theorems … provide end-to-end formal verification." The Stage-10 claims-reviewer FAILs only on "theorem not in Lean OR has `sorry`"; a sorry-free placeholder **passes**.

### Why this is a recurrence, not a discovery

The two QI items that *name* classes (1)+(4) and (2) were both closed **2026-04-29** via Stage-14 closure **pathway #1** (per-finding supersession — flip the specific `ReviewFinding` nodes):

- `qi-leanproofsubstance` — closed Phase 6i Wave 4 ("all 26 LeanProofSubstance nodes" superseded).
- `qi-assumptiondisclosure` — closed Phase 6i Wave 5 ("all 30 nodes: 18 STALE + 11 ACCEPTED + 1 CLOSED" + a few content fixes).

The pipeline's own Stage-14 doc distinguishes pathway #1 (fix instances) from **pathway #2 (structural prevention — install durable infrastructure that prevents the class from recurring)**. Both substance/disclosure QI items were closed by #1, which leaves the *generator* intact. The audit confirms the predicted consequence: both classes recur in modules shipped **after** 2026-04-29 (the 6n/6e/5q.B/5x/5z arc), and two related items remain **open and unaddressed** (`qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`, opened 2026-05-26, explicitly about Stage-3a checklist item 5 — the defining-the-conclusion check — having a blind spot; `qi-prose_lean_numerical_bound_gap`, a fresh instance of which is audit finding #54).

### What is NOT wrong

The Lean source is **scrupulously honest in its docstrings** — `topo` is documented as "the only remaining tracked hypothesis … irreducibly topological" (and is the subject of [ADR-003](ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md)); `rDIndependentNoGo`'s legs are labelled "encoded as a Boolean flag"; `verlindeEntropy_SU2k` is documented "interprets at the Laplace-saddle limit … tracked by `H_VerlindeKMLiteralSumDerivation`." The failure is **not dishonesty**; it is that this honesty lives only in human-readable docstrings and never propagates to (a) the tracked-hypothesis ledger, (b) the placeholder registry, (c) the axiom-count optics, or (d) paper prose. The remediation is therefore *mechanization of existing manual discipline*, not new policy invented from scratch — and the genuinely Mathlib-walled mathematics (`topo`, prime-density, Caves/CCR) is **not** to be re-proved.

---

## Decision

Adopt the **Substrate Integrity Gates**: five standing automated gates, each a mechanization of an existing manual checklist item / invariant, landing at the earliest pipeline stage that can catch its class. Detection shifts left from the Stage-13 fresh-context review (which catches these only when invoked, and only per-paper) into Stages 2/5/7 (which run every wave).

| Gate | Mechanizes | New artifact | Stage | Closes / enforces |
|---|---|---|---|---|
| **R1 — formula content-grounding** | Invariant #4 (name-presence → statement-content) | `lean_grounding_audit` + `validate.py --check formula_grounding`; expand the 7-pair map to all of `formulas.py` | 2 gate / 7 | the δ_diss class; new `qi-formula-content-grounding` |
| **R2 — proxy-body audit** | Stage-3a checklist items 4 & 5 (trivial-discharge + defining-the-conclusion); generalizes the Phase-5q.T **T5** detector | extend `build_graph.py` `_PLACEHOLDER_BODY_PATTERNS` to name-claims-structural-quantity ∧ body-is-`rfl`/`cases<;>rfl`/field-projection/identity-return/`trivial`; `validate.py --check proxy_body_audit`; `MODELING_ASSUMPTION_THEOREMS` whitelist requiring docstring disclosure. **Defers the `native_decide` / finite-combinatorial-`decide` class entirely to ADR-002's P4 gate (`axiom_closure_allowlist`) — those are policy-tolerated, not proxy defects.** | 5 / 7 | structural-prevention close of `qi-leanproofsubstance` + `qi-gate-5-self-audit-blind-spot` |
| **R3 — single tracked-hypothesis source of truth** | the spirit of Invariant #9, extended to tracked Props + struct-field assumptions | **Collapse the two disjoint ledgers to ONE.** `HYPOTHESIS_REGISTRY` (machine-readable, rich) becomes the sole source (add a `prose`/`publication_note` field); `PERMANENT_TRACKED_HYPOTHESES.md` becomes AUTO-GENERATED from it (`scripts/render_tracked_hypotheses.py` + `tracked_hypotheses_fresh` check, à la counts.json→counts.tex). `validate.py --check tracked_hypothesis_ledger` asserts every consumed `(h : Prop)` AND Prop-valued struct field maps to a registry entry. `topo`/`16∣σ` is ALREADY covered by `rokhlin_sigma_mod_16` — do NOT double-register. **new Invariant #16** | 7 / 12 | structural-prevention close of `qi-assumptiondisclosure` |
| **R4 — native_decide accounting** | ADR-002's P4 gate (`axiom_closure_allowlist`) already computes the decl-closure; `lint_native_decide_comments.py` enforces comments | **surface the EXISTING `axiom_closure_allowlist` decl-closure count into `counts.json`** (the authoritative trust-surface metric — `546` as of 2026-06-10; NOT the call-site grep, which is a different, larger number) via `update_counts.py`, with a no-silent-increase regression threshold. **Elimination policy stays owned by ADR-002**; R4 only makes the number a tracked metric. | 5 / 12 | makes the kernel-trust surface a regression-gated number (the "199" was a files-with-string misread) |
| **R5 — placeholder-not-cited** | Invariant #9's unenforced paper-claim clause; **ADR-002 Decision #2** (precise "kernel-checked modulo `native_decide`" wording); generalizes `qi-prose_lean_numerical_bound_gap` | complete `PLACEHOLDER_THEOREMS` (11 → 26 on-disk); `validate.py --check placeholder_not_cited`; add Stage-10 claims-reviewer FAIL conditions for (a) placeholder cited as verified AND (b) a Category-A `native_decide` theorem cited as "kernel-verified" without the ADR-002 modulo-wording | 7 / 10 | direct fix of finding #3 (paper7) |

**Plus three pipeline edits:**

1. **Invariant #4** is restated as *content*-grounding (the cited theorem's statement must encode the formula), enforced by R1.
2. **Invariant #9** gains automated enforcement of its paper-claim clause (R5) and its registry is required complete (R2 produces the full list).
3. **New Invariant #16 — every consumed assumption is in a ledger.** Every Prop taken as a load-bearing hypothesis (by parameter OR by assumed struct field) appears in `HYPOTHESIS_REGISTRY` or `PERMANENT_TRACKED_HYPOTHESES.md`, with disclosure metadata. Enforced by R3.
4. **Stage-14 policy:** substance/disclosure-class QI items (`qi-leanproofsubstance`, `qi-assumptiondisclosure`, and successors) may close **only** via pathway #2 (structural prevention). Pathway #1 (per-finding supersession) is insufficient for a class with a live generator.

**Scope guard.** The gates flag and require *disclosure or fix*; they do **not** require re-deriving genuinely Mathlib-walled mathematics. A struct-field/definitional assumption with a complete docstring + a ledger entry + a `MODELING_ASSUMPTION_THEOREMS` registration is **compliant**, not a defect — exactly the ADR-003 posture for `topo`.

---

## Overlap reconciliation with prior ADRs (so the ADR set stays one system, not four)

This ADR was cross-checked against ADR-001/002/003 to ensure it *extends* their machinery rather than re-litigating settled policy. The boundaries:

- **ADR-002 (`native_decide` policy) owns the compiler-trust surface — R2 and R4 defer to it.** ADR-002 already (a) adopts `native_decide` for finite combinatorial facts (anyon/TQFT/quantum-group) as accepted policy, (b) makes the surface visible via the **P4 gate** `validate.py --check axiom_closure_allowlist`, which *already computes the decl-closure count* (validate.py:706–733), and (c) Decision #2 mandates precise "kernel-checked modulo `native_decide`" prose. Therefore: **R2's proxy-body detector explicitly excludes the `native_decide`/finite-combinatorial-`decide` class** (it is policy-tolerated, not a defining-the-conclusion defect); **R4 does not build new accounting** — it surfaces ADR-002's existing decl-closure number (**546** as of 2026-06-10, down from the 587 at ADR-002's 2026-05-30 cleanup) into `counts.json` with a regression threshold, leaving all *elimination* policy (Route-1/Route-1′, Category-A/B) to ADR-002; **R5's prose check incorporates ADR-002 Decision #2** as a second FAIL condition alongside placeholder-citation. The audit's "~460–620 / 551" figures are **call-site** counts (≈ ADR-002's secondary 712 metric), not the authoritative decl-closure — R4 standardizes on decl-closure to avoid a third competing number.

- **ADR-003 (Rokhlin `16∣σ` / `topo` posture) is the canonical precedent for R2/R3's "compliant disclosed assumption" — `topo` is already in the registry.** ADR-003 establishes that `2∣σ/8` (`SmoothSpinManifold4.topo`) is an *irreducible, principled tracked hypothesis*, and `HYPOTHESIS_REGISTRY['rokhlin_sigma_mod_16']` already records it (`status: discharged`, `dependent_theorems`, `circularity_note`). So `SmoothSpinManifold4.rokhlin`/`topo` is the **template `MODELING_ASSUMPTION_THEOREMS` whitelist entry** for R2 and is **already ledger-covered** for R3 — neither re-opens it. R2/R3 generalize the ADR-003 discipline (one carefully-disclosed struct-field assumption) to the rest of the substrate that lacks it.

- **ADR-001 (`QCyc*`/`PolyQuot*` `CommRing` roadmap) is upstream of ADR-002, not ADR-004.** It supplies the kernel-pure `powerTable` machinery ADR-002 uses to *eliminate* native_decides in the number-field/qgroup cluster (154 of the 546 decl-closure). R4 only *counts* that cluster; any elimination work remains ADR-001/002 territory. No new overlap to integrate.

**Net:** R1 and the Stage-14 policy are genuinely new; R2/R3/R4/R5 are enforcement layers that bind to existing gates (`axiom_closure_allowlist`), registries (`HYPOTHESIS_REGISTRY`, `PLACEHOLDER_THEOREMS`), and policies (ADR-002/003). ADR-002 and ADR-003 carry a forward `See also: ADR-004` pointer so the linkage is bidirectional.

---

## Consequences

**Positive.** The four structural failure classes become build-time failures rather than fresh-context-review-only findings; the two prematurely-closed QI items close durably; `0 axioms / 0 sorry` is joined by *measured* numbers for placeholder coverage, consumed-assumption coverage, formula grounding, and native_decide surface; the one ship-gating overclaim (#3) is fixed and prevented from recurring; the honest-in-docstring discipline is promoted to honest-in-machine-state.

**Costs / risks.** R1 (statement parsing) and R2 (body-pattern classification) carry false-positive risk — both ship with an explicit disclosure-registry whitelist (`MODELING_ASSUMPTION_THEOREMS`) so legitimate documented modeling choices pass; the triage of the initial flagged set is a one-time cost (estimated small — the audit already enumerated the candidates). R3's bidirectional sweep will surface a backlog of ~tens of consumed Props to triage into "register vs downgrade-to-non-load-bearing"; this is the genuine assumption-disclosure debt the per-finding closures left, and clearing it is the point. The gates add Stage-7 runtime (bounded; they are static scans, not builds).

**Explicitly out of scope.** Re-proving `topo` (Atiyah–Singer/Â-genus, Mathlib-absent), the Ross–Selinger prime-density wall, the Caves/CCR floor, or any of the named literature walls. Those are tracked-hypothesis posture (ADR-003 style), and the gates' job is to ensure they are *disclosed*, not discharged.

---

## Alternatives considered

1. **Per-finding fix only (status quo / pathway #1 again).** Rejected — this is precisely what closed the QI items in April 2026 and produced the recurrence; it leaves the generator alive.
2. **Rely on Stage-13 adversarial review.** Rejected as sole mechanism — Stage 13 is per-paper, fresh-context, and only runs when invoked; `qi-gate-5-self-audit-blind-spot` documents that self-audit substitutes miss the class, and bundle-GREEN states predate later re-flagging. Stage 13 remains the backstop; R1–R5 shift detection left so Stage 13 is not the only catcher.
3. **A single monolithic "substance auditor" agent run each wave.** Rejected as the primary mechanism — an LLM pass is non-deterministic and unversioned; the failure classes are mechanically detectable (name-pattern ∧ body-pattern; consumed-Prop ∧ ledger-membership; formula-relation ∧ statement-AST), so deterministic `validate.py` checks are the durable form. (The claims-reviewer LLM pass is retained and strengthened at Stage 10 for the prose side.)
