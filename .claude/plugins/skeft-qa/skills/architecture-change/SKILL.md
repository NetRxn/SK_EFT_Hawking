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

The `infra`-lane process: work on the machine that runs the physics, as opposed to the physics.

**This skill owns the sequence and nothing else.** The rules it enforces are owned elsewhere —
read them, do not re-derive them:

- `CLAUDE.md` § *Architecture documents* — the architecture rules. Rule 0 routes here; rules 1–3
  (read before designing · update in the same commit · never write a count into a narrative) are
  what this sequence enforces.
- `docs/architecture/README.md` — the ownership table: which document answers which question.
- `docs/architecture/CHECK_AUTHORING_GUIDE.md` — what a new check owes, especially §2.4
  (production-seeded mutation) and §2.5 (guard the seam).

**Read `references/adr-012-worked-example.md` before running this sequence for the first time.**
It carries the worked example, the failure each step prevents, and the residual drift a third
correction round still left behind.

## Scope — what scales with the change

**Unconditional at any size:** orient · measure · document-first · step 7's shipping obligations ·
terminate.

**Scales:** step 4 runs at minimum one adversarial pass, all three instruments when scope is
contested or the change spans subsystems. Step 5's pilot is required whenever the design asserts
anything about a **population's shape** — how many, what kind, how much is already repaired — and
skippable when it asserts nothing.

## The sequence

### 1. Orient

Read the `docs/architecture/` document that owns the surface, then read the code it points at.
State what existing machinery already covers the defect, and the residue genuinely uncovered.

Prefer **promote** or **extend** over **add beside**. A promotion deletes the original in the same
commit.

### 2. Measure at HEAD

Derive every figure that steers a decision from the live artifact, and date it. A number read out
of a prior document — including one authored this session — is a claim, not a measurement.
Re-derive it.

**Ask of every predicate you write or measure with: what does this actually assert, and is that
the thing I mean?** A predicate keyed on a *proxy* for its purpose is correct for the population
it was written against and wrong for the rest — and it fails silently, because a wrong predicate
and an empty population return the same answer. The recurring shapes:

| the predicate asserts | it is standing in for | it is wrong for |
|---|---|---|
| a flag spelling, an extension, a constant's name | what the command *does*, what the file *holds*, what the capability *is* | every spelling the author did not enumerate |
| a directory exists | the artifact inside it exists | a directory materialised without its contents |
| a delimiter follows the token | the token ends there | a token ending its line |
| one level of children | a tree that nests | every deeper level |
| one file is uncommitted | any relevant file is uncommitted | every file outside the chosen one |
| a config record | what is actually running | the whole window between a config change and a restart |

Two checks cost nothing and catch all of it: **name a known-present instance and confirm the
predicate finds it**, and **state the predicate in words** — if the sentence is not the thing you
meant, the code is not either.

### 3. Specify before building

Write the ADR and the spec **before** the code.

| artifact | home | holds |
|---|---|---|
| ADR | `docs/adrs/ADR-NNN-<slug>.md` | context · measured constraints · numbered decisions · overlap reconciliation with prior ADRs · plan · consequences · alternatives |
| spec | `docs/superpowers/specs/<date>-<slug>-design.md` | the design the decisions imply |
| plan | `docs/superpowers/plans/<date>-<slug>.md` | tasks, global constraints, file-to-task map |

Number the decisions and keep the numbers stable — they are cited from the spec, the plan, the
memory index and later ADRs. State each constraint as measured, with the code location that
establishes it.

### 4. Review the SPECIFICATION adversarially

Run different instruments; each finds a different class:

| instrument | question |
|---|---|
| a **pilot** on real data (step 5) | does the problem look like the document says? |
| an **adversarial review** of ADR + spec + plan | is any of this already built, unbuildable, or unregistered? |
| an **intent-drift assessment** against the operator's own words | is this still the thing that was asked for? |

The instruments are not interchangeable — running one and calling it reviewed leaves the other
classes open. Self-review does not substitute.

### 5. Pilot

Run the design against a real slice of the real corpus before committing to build it. Record every
row's disposition and evidence in a manifest.

### 6. Plan, then fan out

Order phases by what unblocks the most. State what is deliberately out of scope and which plan
owns it. Carry the global constraints at the top so a fresh worker inherits them; hand each worker
a coherent block, not an atomized brick.

Do not split a build whose halves are inert apart.

### 7. Ship

Three obligations, same commit:

1. **Non-vacuity.** A check ships with a test that seeds the defect **into the production artifact
   the check reads** and observes red, or it does not ship. A fixture-only mutation proves the test
   works, not that the check can fail in production.
2. **Every registration site.** Run `${CLAUDE_PLUGIN_ROOT}/skills/architecture-change/scripts/registration_sites.py <check_name>` — it probes the
   live tree and reports what is still owed. Do not quote a list; the last hand-derived one named
   four of eleven.
3. **Every document the change made wrong**, corrected here — architecture rule 2.

### 8. Terminate at a merged wave, not a green test

Done means: the verification command passes, the closure record is written through its single
writer, the documents are corrected, the wave close-out artifact is updated, the gates are green,
and the change is merged.

## The four rules that fail silently

Everything else announces itself when skipped. These do not:

- **Read before designing** — the duplicate mechanism builds cleanly and passes its own tests.
- **Doc before code** — a changelog reads exactly like a specification afterwards.
- **Non-vacuity** — a check that cannot fire is indistinguishable from a check finding nothing.
- **Re-measure before acting on a filed number** — including one filed earlier this session.

## Resources

- `${CLAUDE_PLUGIN_ROOT}/skills/architecture-change/scripts/registration_sites.py` — probe the live tree for the registration sites a check owes.
- `references/adr-012-worked-example.md` — the worked example, the failure behind each step, and
  the drift a third correction still left.
- `references/shipping-checklist.md` — the non-vacuity bar and how to re-derive registration sites
  by hand if the script is unavailable.
