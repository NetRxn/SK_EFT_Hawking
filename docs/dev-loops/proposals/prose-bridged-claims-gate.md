# Proposal: prose-bridged claims — a gate for the defect class no current check sees

**Status:** DRAFT — **NOT APPROVED.** Awaiting operator go/no-go on Check A.
**Opened:** 2026-07-30. **Filed by:** operator, hand-injected from another channel (not
`--propose-gate`; no ≥3-compact-event GAP-A trigger — see *Provenance* below).
**Source of the finding:** Phase 6EE, three independent fresh-context adversarial reviews.
**Domain:** **System-1** (correctness of what we claim) — these docstrings are what paper claims
cite. The *process* half — that three review rounds were needed to surface it — is System-2.

---

## Provenance note (why this file is here)

`proposals/README.md` describes this directory as the landing zone for System-2 GAP-A drafts
written by `scripts/system2_register.py --propose-gate` on a ≥3-distinct-compact-event recurrence.
This proposal is **neither**: it is a System-1 finding, injected by hand from a separate channel.
It is filed here because this is the project's only human-sign-off proposal pipeline, and the
sign-off posture is identical (spec §1 principle 6 — *self-improving, never self-mutating*).

**Open operator decision:** whether an approved version also earns a `docs/QI_REGISTER.md` open
item (it is a process-level, multi-module failure class, which is what that register tracks) or
lives solely as a `validate.py` check. Not decided here.

---

## Summary

A theorem can be true, kernel-pure, non-vacuous, build-clean, and pass every check we run, while
the sentence next to it describing what it means is false. Every gate we own inspects the
*statement*; none inspects the *bridge* between the statement and the physical object it is named
for. Phase 6EE produced eleven instances of this in one phase, including both of its BLOCKERs.

## Evidence

Three fresh-context adversarial reviews of the same four modules:

| Round | Findings | Notable |
|---|---|---|
| 1 | 1 BLOCKER, 7 MAJOR, 6 IMPORTANT | composite theorem assumed its own conclusion |
| 2 | 1 BLOCKER, 7 MAJOR, 6 IMPORTANT | headline bound's hypotheses **provably excluded** the physical system it was named for |
| 3 | 0 BLOCKER, 3 MAJOR, 5 IMPORTANT | round 2's *own fixes* were bridged to their referents by prose |

> ⚠ **Tallies are provisional — see V5 below.** `docs/dev-loops/Phase6EE/LAB_NOTEBOOK_INDEX.md:38–39`
> records review 2 as `BLOCKER 1/1, MAJOR 3/3`, which does not match the row above. Re-derive from
> `LAB_NOTEBOOK.md` before the numbers are quoted anywhere load-bearing. The *shape* of the evidence
> (three rounds, round 3 finding defects in round 2's own fixes) is not in question.

Throughout, `validate.py` reported 50/50, `lake build` was clean, kernel purity held at 100%, and
`vacuous_statement_audit` passed — correctly. The defect is invisible to all of them.

Representative instances (Phase 6EE):

- A calibration theorem's docstring cited `rwaGenerator_sq` as supplying its content. That theorem
  was called by **nothing in the phase**; the proof was `unfold; field_simp`.
- A witness docstring claimed a ceiling "bites at 3/4 where the photon-budget ceiling alone would
  permit 999/1000". Neither number appeared in the statement.
- The inventory described a witness as bounding a remainder by `10⁻²`; the shipped theorem said
  `1/500`. Source and documentation disagreed about an already-remediated result.
- The justification for the phase's entire mathematical route appeared in three documents with
  **three different formulas** and no backing declaration.
- A docstring claimed priority ("first theorem in the series to…") that a pre-existing theorem
  falsified.

## Defect class (proposed definition)

> **Prose-bridged claim.** A declaration whose name, docstring, or roadmap entry asserts a
> relationship to another object — a referent, a quantity, a priority, a counterfactual — that no
> shipped declaration establishes.

Sub-class, machine-detectable and the more severe: *a theorem whose hypothesis set provably
excludes the instantiation its docstring names.*

---

## Proposed Check A — "cited means called"

**Rule.** If a docstring names another declaration as justification, that declaration must appear
in the proof's dependency set.

**Catches:** uncalled citations, citations of non-existent declarations, "composes X" where X is a
hypothesis rather than a call, "derived from Y" where Y is assumed.

**Known false-positive risk:** docstrings legitimately mention related-but-unused declarations for
orientation ("contrast with…", "see also…"). Mitigation: exempt sentences under a marked prefix, or
accept and tier (below).

## Proposed Check B — "numerals and superlatives must be in the statement"

**Rule.** Flag any docstring or roadmap sentence containing a numeral or a priority word (*first,
only, ×, yields, would give*) whose numerals do not appear in the adjacent declaration's statement.

**Catches:** quantitative drift between docs and source, unbacked priority claims, counterfactuals
with no referent, witnesses advertising strength they don't assert.

## Tiering (load-bearing — do not skip)

Advisory repo-wide; **blocking** for modules in the phase under active development. `validate.py`
currently emits many hundreds of warnings; a new check firing hundreds of times repo-wide changes no
behavior. Blocking-on-new-work is what makes it bite.

**Operator guidance recorded at injection:** *"I'd resist the temptation to make it repo-wide-blocking.
The instinct will be to clean up all existing violations. That's a large project against
mostly-harmless legacy prose, and it would burn the goodwill needed to keep the check enabled on new
work — which is where it actually earns its keep."* — Treat repo-wide-blocking as **out of scope for
any approved version**, not as a phase 2.

## What this explicitly does NOT solve

The deeper half of every review round was semantic and stays with the adversarial reviewer:

- hypothesis sets no physical system can satisfy (vacuous-by-unsatisfiability)
- composites that assume their own conclusion
- "gap" theorems that reduce to a triviality (`max(a,b) < a+b`)
- witnesses that are technically valid but sit at a degenerate operating point

Estimated split: **the gate catches about half of what the reviews found, including both BLOCKERs.**
It is a noise filter that lets review attention reach the hard half — not a replacement for review.

---

# Verification pass — 2026-07-30

The proposal as injected carried nine items asserted from session memory in a read-only context.
All nine were checked against the repo. **Two findings change the proposal's shape; both make it
cheaper.**

### 🔑 V-HEADLINE — the ExtractDeps extension is not needed. For either check.

The implementation sketch's step 1 ("extend `ExtractDeps.lean` to emit docstring + statement —
*the bulk of the work and the only risky part*") is **unnecessary**, because both halves of the
needed data already exist on separate, cheaper paths:

- **Statements** are already emitted. `lean_deps.json` carries a `type` field — the pretty-printed
  elaborated statement — for every declaration. 17.8 MB of it across the corpus. The `ppExpr` cost
  is already paid and already cached (`.lean_typestr_cache.json`).
- **Docstrings** do not need to come from `ExtractDeps` at all. `check_lean_docstring_refs_resolve`
  (`scripts/validate.py:5669`) already reads docstring blocks straight from `.lean` source with
  `_DOCSTRING_BLOCK_RE` / `_DOCSTRING_TOKEN_RE` and resolves the backticked tokens against
  `lean_deps.json`.

**Consequence:** the risky O(project-size) metaprogram change drops out, the build-time-delta
measurement (item 3) becomes moot, and both checks become pure Python over data we already
regenerate. Revised cost: Check A is **a delta on an existing check**, not a new subsystem.

There is also a **correctness reason** to prefer the source-regex path over emitting docstrings from
`ExtractDeps`: the per-decl JSON cache key is
`mixHash(declHash, kind, module, hash(axiom closure))` (`ExtractDeps.lean`, `jsonCacheKey`).
**A docstring-only edit does not change `declHash`** — so an emitted docstring would be served
stale from cache until something else about the declaration changed. Fixing that means widening the
cache key, i.e. more churn in the most performance-sensitive file we own, to obtain data that is
already free from the source.

### 🔑 V-PRIOR-ART — Check A is a strict superset of a check we already ship.

`check_lean_docstring_refs_resolve` already asks *"does the cited name **exist**?"*
Check A asks *"does the cited name exist **and get called**?"* Same inputs, same loop, one added
set-membership test. It also already ships:

- **the tiering this proposal calls load-bearing**, in exactly the proposed shape —
  `_DOCSTRING_STRICT_FAMILIES = ("SKEFTHawking.Detection.", "SKEFTHawking.Electrothermal.")`
  (`validate.py:5664`): FAIL inside the strict (active-work) families, advisory everywhere else.
  Check A extends the tuple; it does not build a tiering mechanism.
- **a proven false-positive mitigation of the right shape** — the `disclaim` regex, which exempts a
  token whose surrounding ±400 chars disclaim it ("deliberately", "not shipped", "rejected",
  "superseded"). The "contrast with… / see also…" exemption Check A needs is the same construct
  with a different word list, and the existing check's own docstring records *why* the honest-exemption
  approach beat the `difflib` near-match filter it replaced. Reuse that judgement; do not re-litigate it.

**The one genuinely new piece of parsing:** the existing check walks docstring blocks with
`findall`, so it never associates a block with the declaration it documents. Check A needs that
association (which decl's dep set to test). `finditer` + capture the following
`theorem|lemma|def|instance <name>`. Modest, and self-contained.

### Item-by-item

| # | Item | Verdict |
|---|---|---|
| 1 | `lean_deps.json` schema | **CONFIRMED + corrected.** No docstring field. Fields: `name, kind, module, type, axiom_deps_project, axiom_deps_core, name_deps_project, type_deps_project, value_deps_project, name_deps_extracted, name_deps_timed_out, structure_fields`. Edges are **immediate/direct, not transitive** — `name_deps_project` is the project-filtered union of the decl's `type ∪ value` immediate refs; `type_deps_project`/`value_deps_project` are the honest statement-vs-proof split (ADR-005 D-G, R-06). Only `axiom_deps_*` is a closure. **Check A must walk if it wants transitive** — but direct is arguably the right semantics for "cited means called", and is free. |
| — | corpus size | **CORRECTED.** 40,202 declarations, not ~26k (26,046 of them theorems; 39,959 `SKEFTHawking.*`-named). `lean_deps.json` is 70.5 MB. |
| 2 | `Lean.findDocString?` at v4.32.0 | **CONFIRMED available** — `Lean/DocString.lean:33`, `(env : Environment) (declName : Name) (includeBuiltin := true) : IO (Option String)`. **Moot** given V-HEADLINE. |
| 3 | Extraction build-time cost | **MOOT** — no `ExtractDeps` change proposed any more. This was the operator-flagged soft spot; it dissolves rather than resolving. |
| 4 | Overlap with `vacuous_statement_audit` | **CONFIRMED none.** That check (`validate.py:1008`) classifies the *elaborated type* as reflexive / `True` / ground-arithmetic. It is name-, tactic-, **and docstring-agnostic**. It cannot see a prose bridge. Check B does not duplicate it. |
| 5 | Hit-rate table | **NOT re-derived — and it does not reproduce.** `Phase6EE/LAB_NOTEBOOK_INDEX.md:38–39` disagrees with the round-2 row. Treat ~50% and the per-round tallies as provisional pending a read of `LAB_NOTEBOOK.md`. Flagged inline above. |
| 6 | Cited examples still read as described | **Spot-checked one; it has been remediated — informatively.** `Control/DriveCalibration.lean:89` now documents `rwaGenerator_sq` as "consumed", and `:95` proves it: `rw [rwaGenerator_sq, rwaRate_sq]`. So this instance would **pass** Check A today and would have **failed** it before remediation — a live positive control for the rule. The other four were not re-checked. |
| 7 | `validate.py` check registration | **CONFIRMED, and richer than assumed.** `@register_check("name", "description")` decorator (documented at `validate.py:34`). Severity is per-`Detail` (`warning=True` = advisory ⚠) plus the check-level `CheckResult(passed=…)`, with a `--strict` CLI flag that tightens advisories. Per-module tiered severity **already exists** and needs no building — see V-PRIOR-ART. |
| 8 | Registration precedent (`KERNEL_NOGO_REGISTRY` / Invariant #17) | **CONFIRMED not applicable.** Invariant #17 (`WAVE_EXECUTION_PIPELINE.md:697`) is registry-backed because each no-go needs a *backing artifact* (an FQN list, a `nogo_kind`, kernel-purity). A prose-bridge check has no per-instance artifact to register — its input is the corpus. **Register as a plain `validate.py` check.** |
| 9 | Prior art | **FOUND — substantial.** See V-PRIOR-ART. Also adjacent: `prose_theorem_reference_coverage` (`:5211`), `theorem_name_embedded_citations` (`:5432`), `proxy_body_audit` (`:432`). The proposal must be re-framed as *extending* `lean_docstring_refs_resolve`, not as a greenfield check. |

### Revised implementation sketch

1. ~~Extend `ExtractDeps.lean`~~ — **dropped.**
2. Extend `check_lean_docstring_refs_resolve` with declaration association (`finditer` + following
   decl name) and, for each token that *does* resolve, a membership test against that decl's
   `name_deps_project`. Add an orientation-exemption word list alongside the existing `disclaim` regex.
3. Check B: a second check over the same association, comparing docstring numerals against the
   decl's `type` string (already in `lean_deps.json`).
4. Dry-run over the full corpus; tune the false-positive rate; extend `_DOCSTRING_STRICT_FAMILIES`
   to the phase under active development and **nothing else**.

**Revised cost:** Check A ≈ hours, not a day, and no risk to the extraction path. Check B similar,
gated on A's false-positive rate coming in acceptable.

---

## Decision needed

**Go/no-go on building Check A**, in its revised form (an extension of
`check_lean_docstring_refs_resolve`, active-work-tiered, never repo-wide-blocking).

Out of Phase 6EE scope — 6EE closes without it.
