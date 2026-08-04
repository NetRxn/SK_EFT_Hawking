# ADR-010 — Publication portfolio: purpose, distribution, and late-phase absorption

- **Status:** **PROPOSED — CHARTER ACCEPTED, ANALYSIS PENDING (2026-08-04).**
  This document was authored *before* the analysis it commissions, deliberately: the operator's framing
  and constraints were given in a live session and would otherwise be lost at the next compaction.
  §Context and §Constraints are **verified against source** and are durable. §Decision states the
  *criteria and method* the re-assessment must satisfy. §Open records what is **not** decided — most
  importantly the roster number, which is **not** to be assumed.
  **No roster change, no `PAPER_STRATEGY.md` edit and no manuscript edit is authorized by this ADR.**
- **Decider:** John Roehm (project owner). Direction given 2026-08-04:
  > *"My intent is to publish the strongest form of any paper we deliver. I've noticed that the naming
  > convention & late stage work keeps pulling into D (depth) but then we regularly don't have anywhere
  > near enough content (e.g., 60pg turns into 11pgs). I'm not going to dictate the spread — I'd like a
  > strategic re-assessment of the purpose of all of the papers, in context of the absorbed & unabsorbed
  > roadmap work, and a recommendation on an optimal distribution, as well as a more solidified plan for
  > late phase absorption into the plan. Remember, the original strategy was written before many
  > different avenues we started to deliver on. The big picture wasn't re-evaluated."*
- **Sequencing (operator ruling, same session):** **the QA/QI infrastructure must be re-solidified and in
  place first.** [ADR-009](ADR-009-validation-suite-modularization.md) closes and merges before the
  portfolio analysis begins. The dials this ADR's recommendations will be measured by are the ones
  ADR-009 is currently repairing; recommending against broken instrumentation repeats the failure that
  produced the audit.
- **Scope:** the purpose, boundaries, count and sequencing of the publication bundles; the mechanism by
  which late-phase work reaches a bundle; and the process rules that govern bundle authorization.
  **Out of scope:** the content of any individual manuscript (that is the remediation goal that follows),
  the validation suite (ADR-009), and Claude-Code onboarding (ADR-008, deferred).
- **Related:** [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) (the document under re-assessment) ·
  [`docs/PAPER_DRAFT_MAPPING.md`](../PAPER_DRAFT_MAPPING.md) ·
  [`docs/BUNDLE_LIFT_PROCEDURE.md`](../BUNDLE_LIFT_PROCEDURE.md) ·
  [`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`](../LATE_PHASE6_ABSORPTION_PROTOCOL.md) ·
  [`docs/audits/2026-08-01-publication-readiness/`](../audits/2026-08-01-publication-readiness/)
  (SYNTHESIS · REMEDIATION_PLAN · CROSS-portfolio-coherence · CROSS-absorbability-and-strategy-drift ·
  CROSS-build-integrity · 10 per-bundle reports) · `scripts/bundle_registry.py` (the machine roster) ·
  Pipeline Invariant #14 (`WAVE_EXECUTION_PIPELINE.md:689`).

---

## Context

### The pathology the operator named

**Late work keeps being authorized into Tier-1 "deep" containers that then never reach their charter.**
The roster grew 13 → 14 → 15 → 16 → 17 → 18 → 20 → 21 by successive authorizations
(`PAPER_STRATEGY.md:27` records the full chain), each adding a *depth* paper. Measured at the audit:
**Tier-1 aggregate is ~181 pp against a ~475 pp charter** (`SYNTHESIS.md` §1). A 40 pp target ships as
11. Only **D3** meets its page target — and D3 is the one bundle that does not compile.

This is a *structural* outcome, not a series of individual authoring failures, and the re-assessment must
name the mechanism rather than the symptom. Three candidate generators are already documented and each
must be evaluated:

1. **Authorization has no content floor.** Invariant #14 requires user authorization to add a bundle
   target, but nothing at authorization time asserts that substrate exists to fill it. A bundle is
   created, then hopefully filled.
2. **`BUNDLE_LIFT_PROCEDURE` §3a inserts one section stub per source.** `SYNTHESIS.md` §3 Class 4
   identifies this as what "manufactures the stitched lift" — D3 is 30 sections at a median of 262 words,
   with `source_manifest.md` mapping sources 1:1 onto 22 of them. The procedure produces *shape* without
   producing *content*.
3. **Nothing measures the gap continuously.** Page-count vs charter is computed nowhere; it surfaced only
   when a human read the drafts.

### The strategy document predates most of what was delivered

`PAPER_STRATEGY.md` describes "twenty-one publication targets" (`:27`) but its architecture section still
frames Tier 1 as twelve themed deep papers whose boundaries were drawn before Phases 6AA–6EE existed. The
audit found the drafts are in several places **more honest than the strategy document describing them**
(`SYNTHESIS.md` §4): D5's measured 0.83σ/1.04σ against the charter's advertised 3.5–5.7σ; I3's §8.9
withdrawal against §2.4's priority claims. *"Where they conflict, the strategy doc is usually the thing
that needs fixing."*

### Work that has no home

- **~340 kernel-verified Lean modules across 10 arcs appear in no bundle draft**, plus **8 fully-closed
  phases** (6h, 6j, 6k, 6l, 6q, 6r, 6r′, 6s) with no bundle home (`SYNTHESIS.md` §3 Class 6).
- Includes the **entire Pin⁺ ℤ/16 arc** (162 `PinPlus*` + ~88 Smith/Wu declarations, zero `papers/` hits)
  and the **whole `GenericSUd*` SU(d) substrate that D8 advertises as its headline**.
- **16 manifest-claimed sections across 7 bundles are commented-out stubs sitting after the
  bibliography** while `append_log.json` still counts them (`SYNTHESIS.md` §3 Class 4). D1 has four, so
  part of its 73 % shortfall is self-inflicted commenting rather than missing work.

### Late-phase absorption is structurally dead for the newer half of the roster

`LATE_PHASE6_ABSORPTION_PROTOCOL`'s Stage-C trigger **does not fire for D6–D12**: every bundle authorized
since D6 is *sourceless* (no entries in `PAPER_DRAFT_MAPPING.md`), and nothing tracks Lean-module mtimes.
The instrument that was supposed to notice is `check_bundle_source_freshness.py`, which returns `None`
for sourceless keys and skips — reporting *"fresh: all 1 source paper(s) older than last_lift"* for a
comparison it never performed (`SYNTHESIS.md` §2). So the newest, fastest-growing arcs are precisely the
ones with no absorption path.

### Two documents disagree with the live roster

- **Pipeline Invariant #14** (`WAVE_EXECUTION_PIPELINE.md:689`) enumerates
  `F, D1–D9, L1–L3, I1–I3, E1, E2` — *"18 targets as of the 2026-06-10 D9 authorization"* — an enum that
  **cannot legally hold D10, D11 or D12**. Verified directly 2026-08-04.
- **`PAPER_STRATEGY.md:341`** still carries *"All 14 bundles have shipped Stage 9 + Stage 10 + Stage 13
  reviewer triples GREEN"* from 2026-05-07.

Both are instances of the audit's own finding **X-14**: roster count/membership stale across 36 doc and
script sites, *including three rule texts*.

---

## Constraints — verified, and load-bearing for any recommendation

### C1. The roster is machine-gated in three legs. A number is not a change-set.

`validate.py --check bundle_registry_consistency` (`scripts/validation/checks/bundles_readiness.py:745`,
read in full 2026-08-04) enforces the single source of truth in three independent legs. **Any roster
change must move all of them together or the suite goes red:**

- **Leg A — documentary agreement.** `bundle_registry.parse_strategy_roster()` parses
  **`PAPER_STRATEGY.md` §6 "Summary table"** into `{code: tier}` and requires exact equality with the
  registry, on **codes *and* tiers**. A bundle authorized in the strategy doc but never registered — or
  registered but absent from §6 — fails here. This is the leg with teeth for the actual failure mode.
- **Leg B — consumer agreement.** Every module in `_ROSTER_CONSUMERS` must expose bundle-keyed attributes
  whose key sets equal the registry's **exactly**. Seven modules today:
  `sentence_state` (`_VALID_BUNDLE_TARGETS`) · `validate` (`BUNDLE_CODES`) ·
  `bundle_readiness` (`_BUNDLE_ORDER`, `_TIER_OF`) · `review_runner` (`TIER_OF`) ·
  `bundle_source_manifest` (`_TIER_OF`, `_BUNDLE_TITLES`, `_BUNDLE_TARGET_JOURNAL`, `_BUNDLE_SUBPHASE`) ·
  `datastar_bundles` (`_TIER_OF`, `_BUNDLE_TITLES`) · `aristotle_usage_by_bundle` (`ALL_BUNDLES`).
- **Leg C — no re-hardcoding.** An AST walk over `scripts/*.py` fails any literal dict/list/tuple/set
  holding **≥ 6** distinct bundle codes outside `bundle_registry.py`. This is the leg that stops the
  *next* authorization from regressing the seven-places problem.

The gate exists because the roster **was** hardcoded in seven places, and every omission failed *silently
and differently* — `validate.py` skipped D10 in the one check that catches Lean theorem-name drift in
prose; `bundle_readiness.py` rendered 19 of 21 bundles while looking complete. **ADR-010's recommendation
must therefore ship as a complete change-set — §6 table, registry, seven consumers, Invariant #14's enum,
and the 36 prose sites — not as a target number.**

### C2. The live roster is 21. Nothing on disk supports 14.

`scripts/bundle_registry.py → BUNDLE_CODES` = **21**, verified 2026-08-04:
`D1–D12, E1, E2, F, I1–I3, L1–L3`.

A prior session recorded a *"roster decision: 21 → 14 (author's call, operator delegated)"*. **That figure
is unsupported by any document in the repository and must not be carried forward.** It is additionally one
of the stale counts the audit itself files as **P0 defect X-11** (*"Manuscripts state the roster as 14, 15
and 17"*). Correction recorded 2026-08-04.

### C3. The audit's own recommendation is 21 → 16 — as INPUT, not a conclusion.

Stated twice, in detail:
- `SYNTHESIS.md` §5 **D-1** — *"Roster consolidation, 21 → 16."*
- `CROSS-portfolio-coherence.md` §6.4 — *"Recommended roster — 16 targets"*, with a full per-target table
  and estimated page deltas.

The proposed merges: **D6+D9+D12 → D6★** (device/network certification stack) · **D10+D11 → D10★**
(condensed-matter/molecular substrate) · **E1+E2 → E★** · **D7 folded into D1** · **D4 §9 → D8**.
21 − 5 = 16. Rationale: the two largest duplication findings (D6/D9 sharing 78 identical Lean theorems;
D4 §9 = 62 % of the entire D8 manuscript, with both papers asserting priority over it) **are boundary
failures between bundles that should not be separate**.

The audit also records what it would *not* do: *"shrink the targets to match the current drafts… would be
the walk-back this project's own remediation posture forbids."*

**This is a starting hypothesis to evaluate against the substrate, not a decision to ratify.**

### C4. The analysis must be done from the substrate, by the author, with the content actually read.

Operator constraint, given explicitly (2026-08-04):

> *"I'm really worried about you making decisions on the most appropriate way to combine the papers since
> the content is clearly not in your context."*

Accordingly: **no merge, split or retirement may be recommended on the strength of a summary, a bundle
name, an audit table, or a subagent report.** Each recommendation must rest on the manuscripts and the
Lean modules themselves, read directly. Where a recommendation rests on something not read, it must say
so. This mirrors the standing lesson already recorded in `QA_QI_INFRASTRUCTURE_MAP.md` §9 — *a filed
finding's blast radius is a claim, not a measurement* — which this workstream has now violated twice and
caught twice.

### C5. Claim strength is not the flexible variable.

Governing posture, unchanged (`REMEDIATION_PLAN.md` §0, memory `feedback-remediation-build-dont-walkback`):
**the publication schedule moves; the claims do not.** A container may be resized because the substrate
is genuinely a different shape than the charter assumed — never because resizing is the cheap way to make
a shortfall disappear. The distinction is the whole subject of `REMEDIATION_PLAN.md` §0 and must be
explicit in every recommendation this ADR makes.

---

## Decision

### D1 — ADR-010 is a document, and its execution is a separate goal

The deliverable is **this ADR, completed**: a researched, densely-linked analysis a later goal can execute
from. This ADR's own completion **does not** edit `PAPER_STRATEGY.md`, `PAPER_DRAFT_MAPPING.md`,
`bundle_registry.py`, Invariant #14, or any manuscript. Separating analysis from execution is deliberate:
the roster change is a coordinated multi-file change-set (C1) that should be reviewed as a plan before it
is made as a diff.

### D2 — Every target gets a re-derived purpose statement

For each of the 21 current bundles, the analysis states: **audience, venue, the claim only this container
can make, the substrate that backs it (named Lean modules / phases), and its honest current size against
its charter.** Re-derived from what exists now — *not* inherited from `PAPER_STRATEGY.md`, which predates
most delivered avenues and was never re-evaluated as a whole (§Context).

A target whose purpose cannot be stated without reference to another target's substrate is a boundary
failure and must be named as one.

### D3 — The D-tier gravity pathology is diagnosed at the mechanism, and a control is specified

The analysis must (a) identify which of the three candidate generators in §Context actually produces the
shortfall — with evidence — and (b) specify the control that stops recurrence. A control is acceptable
only if it is *checkable*: a rule that depends on an author remembering it is the state we are already in.

Explicitly in scope for the control: **a content floor at authorization time** (does substrate exist to
fill this container before it is created?), and **continuous measurement of size against charter** rather
than discovery at review.

### D4 — Distribution is recommended per-target, with the merge/split/retire decision justified individually

Not a headline number. For each proposed change: what moves, why the substrate says so, what the
resulting container's charter becomes, and what breaks (C1's change-set). The audit's 21 → 16 is the
starting hypothesis (C3); departures from it are expected and must be argued.

### D5 — Unabsorbed work is homed or its absence is justified

The ~340 modules, the 8 closed phases, the Pin⁺ ℤ/16 arc and the `GenericSUd*` substrate each get a
destination or a written reason they have none. "No home" is an acceptable outcome — *"defensive
publication of the substrate, not a paper"* is a legitimate disposition — but it must be a decision, not
an omission.

### D6 — Late-phase absorption is repaired, not merely described

The analysis specifies: how a sourceless bundle (D6–D12 today) acquires a working freshness trigger; what
`check_bundle_source_freshness.py` must track instead of source-paper mtimes (Lean-module mtimes are the
audit's proposal, and must be evaluated rather than assumed); and how the content floor from D3 is
measured continuously. Any instrument proposed here follows `REMEDIATION_PLAN.md` §6a's standing rule —
**identify the defect class → establish what existing machinery covers it, by reading the code → describe
the residue → request approval → only then build.** Never build before the third step.

### D7 — Process-document drift is corrected as part of the change-set

Invariant #14's 18-target enum, `PAPER_STRATEGY.md:341`'s "All 14 bundles", and the 36-site roster drift
(X-14) are listed with their fixes. The mechanism that let a *rule text* go stale is itself a finding: a
rule enumerating a roster is a hardcoded roster, and Leg C exists because that pattern is known-bad in
code. Whether the same discipline should apply to prose is an open question for D3's control.

---

## Open — NOT decided by this ADR

1. **The roster number.** `SYNTHESIS.md` §5 lists D-1 among *"decisions required from the operator"*.
   The operator has explicitly **declined to dictate the spread** and asked for a recommendation instead.
   So the analysis proposes; the operator disposes. **Do not assume a number, and do not carry "14".**
2. **Whether D10 ships the Coulomb result or waits for the DFT layer** (`SYNTHESIS.md` D-4), including
   whether PhysLib's now-reachable spectral theory makes D10's in-tree Kato–Rellich redundant.
3. **L1's disposition** (`SYNTHESIS.md` D-3) — re-found the falsification, restate it as a
   project-constructed identification, or retire it. A scientific-integrity call, not a portfolio one,
   but it changes what L1 *is*.
4. **`native_decide` disclosure posture** (`SYNTHESIS.md` D-5) — affects what D4 and I2 may claim, hence
   their charters.
5. **The graphene `Γ_H` dimensional question** (`SYNTHESIS.md` D-6) — a physics adjudication that inverts
   E2's headline and therefore bears on whether E1+E2 should merge.

Items 2–5 are recorded here because each **changes a container's charter**, so the distribution
recommendation must state its dependence on them rather than silently assuming a resolution.

---

## Consequences

**Accepted.** Publication is deferred further. Per C5 that is the intended trade: the schedule is the
flexible variable. The audit already states the consequence plainly — *"no Tier-1 bundle ships on the
previous timeline"* — and the roster analysis is upstream of even that.

**A sequencing trap to avoid.** `CROSS-portfolio-coherence.md` §6.4 warns that merges should land
*before* further Stage-13 or lift work on D6/D7/D9/D10/D11/D12/E1/E2, *"or that work is spent on
containers that are about to be dissolved."* Conversely `SYNTHESIS.md` §6 Phase 2 notes that removing
D9's content from D6 **drops D6 to ~7 pp** — the length gap widens before it closes. Both are true; the
analysis must sequence around them explicitly.

**Risk if not done.** The generator keeps running: the next authorized bundle is another under-filled
depth container, and the ~340 un-homed modules keep growing. The audit's verdict — *no bundle in the
portfolio is submittable today; best grade C−* — is the current state of a portfolio whose strategy was
last evaluated whole before Phases 6AA–6EE existed.

**Risk if done badly.** A roster change that moves the number without moving C1's change-set turns the
suite red in seven consumers at once and, worse, can be "fixed" by editing the registry to match a stale
consumer — re-fragmenting the single source of truth the gate exists to protect.

---

## Alternatives considered

1. **Execute the roster change directly, skipping the ADR.** Rejected by the operator: the content is not
   in context, the change-set is coordinated across a dozen files and three enforcement legs, and the
   decision is theirs. The ADR is the review surface.
2. **Ratify the audit's 21 → 16 as-is.** Rejected as insufficient diligence. The audit's own §7 lists what
   it could not check — including the 78 D6/D9 theorem statements against the Lean, which is exactly the
   evidence that decides whether D6+D9 is a merge or a contradiction.
3. **Shrink the charters to match the current drafts.** Rejected — the audit names this as the walk-back
   the remediation posture forbids (C5), and several bundles demonstrably have the substrate for a real
   article.
4. **Do this before ADR-009.** Rejected by the operator: the dials that measure a bundle's readiness are
   the ones under repair, and recommending against broken instrumentation is what produced the audit.

---

## References

- `docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md` — verdict, 80 P0 findings, the systemic
  finding (§2), the six defect classes (§3), what is genuinely sound (§4), the five operator decisions
  (§5), the remediation sequence (§6).
- `.../REMEDIATION_PLAN.md` — the BUILD (B1–B8) / CORRECT-TO-SUBSTRATE / FACTUAL triage that supersedes
  SYNTHESIS §6 Phase 1, and §6a's build-authorization rule.
- `.../CROSS-portfolio-coherence.md` §5 (every inconsistent roster statement), §6.4 (the 16-target
  recommendation and table), §7 (what the auditor could not check).
- `.../CROSS-absorbability-and-strategy-drift.md` — the 60-item drift ledger and the absorption analysis.
- `scripts/bundle_registry.py` — the machine roster; `parse_strategy_roster()` is Leg A's parser.
- `scripts/validation/checks/bundles_readiness.py:745` — `bundle_registry_consistency`, the three-leg gate.
- `docs/WAVE_EXECUTION_PIPELINE.md:689` — Invariant #14, carrying the stale 18-target enum.
- `docs/architecture/.working-docs/RESUME_STATE.md` — the live tracker for both workstreams.
- [ADR-009](ADR-009-validation-suite-modularization.md) — must close and merge first.
