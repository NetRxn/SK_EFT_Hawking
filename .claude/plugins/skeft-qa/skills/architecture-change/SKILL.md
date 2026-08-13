---
name: architecture-change
description: >
  This skill should be used when the user asks to "write an ADR", "write an architecture decision
  record", "spec this out", "review this spec", "review this ADR", "plan an infra build", "add a
  validation check", "add a gate", "add a ratchet", "wire in a new check", "add an agent, command,
  hook or skill to the plugin", or "change the architecture" — and, unprompted, whenever a change
  would add or alter any part of SK_EFT_Hawking's own machinery (a check, a gate, an extractor, a
  node or edge type, a hook, a writer, a dashboard surface, a plugin component), or would create or
  edit anything under docs/adrs/, docs/architecture/, docs/superpowers/specs/,
  docs/superpowers/plans/, scripts/validation/checks/, or .claude/plugins/skeft-qa/. Invoke it
  BEFORE designing, and again before an ADR, spec or plan is treated as settled. For Lean proof
  work inside a /goal loop — the MCP proof loop, worktree fan-out, tactic friction — use goal-dev
  instead.
---

# Changing the machine — the repeatable sequence

This is the `infra`-lane process: work on the machine that runs the physics, as opposed to work on
the physics itself. It is codified rather than remembered because the failures below are cheap to
repeat and expensive to discover.

**It owns the sequence and nothing else.** The rules it enforces are owned elsewhere and are not
restated here — read them, do not re-derive them:

- `CLAUDE.md` § *Architecture documents* — the architecture rules. Rule 0 routes here; rules 1–3
  (read before designing · update in the same commit · never write a count into a narrative) are
  what this sequence enforces.
- `docs/architecture/README.md` — the two rules, the ownership table, and which document answers
  which question.
- `docs/architecture/CHECK_AUTHORING_GUIDE.md` — what a new check owes semantically, especially
  §2.4 (production-seeded mutation) and §2.5 (guard the seam).

**The worked example is ADR-012** (`docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md`),
corrected three times by three different instruments — and **still carrying residual drift**, which
the reference records and which is part of using the example well. Every rule below cites what it
caught there. Read `references/adr-012-worked-example.md` before running this sequence for the
first time; it is the evidence, and it is what makes the rules arguable rather than arbitrary.

⚠️ **Every ADR-012 figure quoted below is a measurement dated 2026-08-12, illustrative and not
current.** Re-derive anything you intend to act on — that is step 2, and quoting these numbers
forward is the failure step 2 exists to prevent.

## Scope, and what scales with it

**Unconditional at any size:** step 1 (orient), step 2 (measure), step 3 (the document lands
first), step 7's three shipping obligations, and step 8 (terminate at a merged wave). These are
the cost of the rule, and it is one step plus the reading.

**Scales with the change:** step 4 runs at minimum one adversarial pass, and all three instruments
when the scope is contested or the change spans subsystems. Step 5's pilot is **required whenever
the design asserts anything about a population's shape** — how many, what kind, how much is already
repaired — and skippable when it asserts nothing.

⚠️ A sequence that reads as all-or-nothing gets dropped whole on small changes. Adding one
dashboard pane does not need a pilot; it still needs orient, measure, doc-first and the shipping
obligations.

---

## The sequence

### 1. Orient — read what already covers the defect

Read the `docs/architecture/` document that owns the surface, then **read the code it points at**.
Establish what existing machinery already covers the defect, and describe the residue that is
genuinely uncovered (ADR-010 §6a).

*Failure it prevents:* building a second mechanism beside one that already works — in ADR-012 a
proposed check already existed, ratcheted and mutation-verified, and the replacement was *weaker*
than what it would have displaced (§C9). Orientation deleted a whole task.

⚠️ Prefer **promote** or **extend** over **add beside**. Two copies of a mechanism is the defect,
not the cure — so a promotion deletes the original in the same commit (§D13).

### 2. Measure at HEAD — and re-measure every number that is quoted

Every figure that steers a decision is derived from the live artifact and dated. A number read out
of a prior document — including a document authored in this same session — is a **claim**, not a
measurement.

*Failure it prevents:* a design justified by a premise that is false — three ADR-012 drafts rested
on a gating claim the code contradicted, never traced.

### 3. Specify before building — the document lands first

The ADR (the decision and its constraints) and the spec (the design) are written **before** the
code. A document written afterwards is a changelog; only one written first is a specification.

Artifacts, in the house locations:

| artifact | home | holds |
|---|---|---|
| ADR | `docs/adrs/ADR-NNN-<slug>.md` | context · measured constraints · numbered decisions · overlap reconciliation with prior ADRs · plan phases · consequences · alternatives |
| spec | `docs/superpowers/specs/<date>-<slug>-design.md` | the design the ADR's decisions imply |
| plan | `docs/superpowers/plans/<date>-<slug>.md` | tasks, global constraints, file-to-task map |

Number the decisions and **keep the numbers stable** — they are cited from the spec, the plan, the
memory index and later ADRs. A renumber silently invalidates every citation.

State each constraint as **measured and load-bearing**, with the code location that establishes it.
A constraint with no measurement behind it is a preference.

### 4. Review the SPECIFICATION adversarially, not only the implementation

This is the step most often skipped and the one that returns the most. Run it with **different
instruments**, because each finds a different class:

| instrument | question it asks | what it found in ADR-012 |
|---|---|---|
| a **pilot** on real data (§5) | does the problem look like the document says? | most of the proposed build already existed; scope *shrank* |
| an **adversarial review** of the ADR + spec + plan together | is any of this already built, unbuildable, or unregistered? | a check that already existed; a guard that could never fire in production; every registration obligation omitted from the plan |
| an **intent-drift assessment** against the operator's original words | is this still the thing that was asked for? | the first draft solved half the problem and dropped the other half — including the problem that started the thread |

*Failure it prevents:* shipping a specification's first draft. **A process that produces a
specification nobody adversarially reviews produces this document's first draft** (§D18).

⚠️ The instruments are not interchangeable. The adversarial review read the document against the
code and could not see the missing half; the drift assessment read it against the ask and could not
see `ledger_ids_resolve`. Running one and calling it reviewed leaves the other class open.

⚠️ **Self-review does not substitute.** A reviewer reading their own work is reading their own
assumptions — in ADR-012 that cost two real errors, one introduced while fixing a finding about
the same class.

### 5. Pilot — because a pilot changes scope

Run the design against a real slice of the real corpus before committing to build it. Record every
row's disposition and evidence in a manifest.

*Failure it prevents:* building for an imagined population. *In ADR-012:* a 117-finding triage
found ~84% already repaired — the backlog was a **recording** gap, not a defect backlog — which
rewrote two decisions and added two constraints. It also behaved as a review pass in its own right,
surfacing defects no finding had recorded, because **disposition requires reading the artifact,
which is the same act as reviewing it.**

### 6. Plan, then fan out

Order phases by what unblocks the most, and say in the plan what is **deliberately out of scope**
and which plan will own it. Carry the global constraints at the top of the plan so a fresh worker
inherits them; hand each worker a coherent block, not an atomized brick.

⚠️ **Do not split a build whose halves are inert apart.** ADR-012's closure-side guard could not
fire until the routing-side parser produced its input, so shipping closure alone would have
produced a guard green in tests and dead in production — item 1 on
`docs/architecture/CHECK_AUTHORING_GUIDE.md` §6's checklist. Routing and closure became one build
for that reason (§D18).

### 7. Ship — non-vacuity, then every registration site, then the docs

Three obligations, all in the same commit. The detail, and how to re-derive the registration sites
rather than trusting any list: **`references/shipping-checklist.md`**.

1. **Non-vacuity is a shipping requirement, not a review note.** A check ships with a test that
   seeds the defect **into the production artifact the check reads** and observes red, or it does
   not ship (§D8; guide §2.4). A fixture-only mutation proves the test works, not that the check
   can fail in production. *In ADR-012:* §C4 records the same mechanism already failing vacuously —
   a gate reported "all P1 passed" while blockers sat unclosed, because the findings produced zero
   edges. **An unrecordable finding is indistinguishable from no finding.**
2. **Every registration obligation, or the suite breaks.** *In ADR-012:* the plan that first
   enumerated them missed one site and three tests went red. Re-derive the list; do not quote it.
3. **Every document the change made wrong is corrected in the same commit** — architecture rule 2.
   *In ADR-012:* §D16 records that this project's documented failures concentrate here.

### 8. Terminate at a merged wave, not at a green test

The work is done when the verification command passes, the closure record is written through its
single writer, the documents are corrected, the wave close-out artifact is updated, the relevant
gates are green, and the change is merged (§D16). Anything short of that leaves a finding that
reads closed and a system that is not.

⚠️ **Defects mutate rather than close.** ADR-012's pilot found this independently across slices: a
corrected count that re-drifted, a trivial predicate replaced by a differently-trivial one, a repair
that landed in a comment while the code kept its defect. **A fix verified once at a point in time,
with no mechanism attached, is a fix that will re-break** — which is why step 7's obligation is a
mechanism and not a demonstration.

---

## The four rules that fail silently

Everything else in this sequence announces itself when skipped. These do not:

- **Read before designing** — the duplicate mechanism builds cleanly and passes its own tests.
- **Doc before code** — a changelog reads exactly like a specification afterwards.
- **Non-vacuity** — a check that cannot fire is indistinguishable from a check finding nothing.
- **Re-measure before acting on a filed number** — including a number filed earlier in this
  session, by this agent.

## References

- `references/adr-012-worked-example.md` — ADR-012 end to end: the first draft, its three
  correction rounds, what each instrument caught, and the residual drift a third correction still
  left behind.
- `references/shipping-checklist.md` — the registration sites a new check owes, how to re-derive
  them from the code rather than trusting a list, and the non-vacuity bar.
