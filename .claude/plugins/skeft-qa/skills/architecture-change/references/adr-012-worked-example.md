# Worked example — ADR-012, and its three correction rounds

Source: `docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md`. Read it for the full text;
this file distills what the *process* did to it, which is the part `SKILL.md` codifies.

⚠️ **Every figure below is quoted as of 2026-08-12 and is illustrative, not current.** ADR-012's own
standing instruction is to re-derive before acting on any of them — and §Pilot records what happened
when that was skipped. Quoting them here to steer a decision would reproduce the defect the example
teaches.

---

## What it was for

An I1 review pass closed with a list of REQUIRED and RECOMMENDED findings and one live substrate
defect. The operator's question was whether a DAG directs the work a review creates. The honest
answer: a *dependency* graph existed and a *work-routing* graph did not. A finding recorded what was
wrong and nothing about who repaired it — no lane, no target, no verification command, no edges — so
nothing could be scheduled or parallelized, and every remediation re-derived its orientation from
cold context.

That is the whole problem statement. Everything below is what happened to the document that tried to
solve it.

---

## The first draft

It proposed: four new fields on the finding template, requiring a reviewer change and a corpus
backfill; a new ledger-integrity check with an aggregate ceiling; a closure-bar extension; and a
build sequenced as *closure first, routing later*.

**Three of those four were wrong**, and no amount of internal care would have found it. Each was
caught by a different instrument pointed at the specification itself.

---

## Round 1 — the pilot (117 findings, dispositioned)

**Instrument:** run the design against a real slice of the real corpus before building it. Every row
carried a disposition, evidence, lane and target, into a manifest under
`docs/audits/2026-08-12-critical-triage/`.

**What it found.**

- **The backlog was a recording gap, not a defect backlog.** Roughly 84% were already repaired.
  Several review documents had been formally closed by later re-reviews that were never written into
  the closure ledger — three such re-reviews accounted for fourteen "fixed" verdicts in one slice.
  The system's problem was the record, not the work.
- **Two of the four proposed fields already existed in the corpus.** The reviewer template had
  carried `Gate:` and `Location:` lines for weeks, on the large majority of findings — and the
  extractor parsed only severity and status, discarding them. `Gate:` and `Location:` were exactly
  the `blocks` and `target` the ADR set out to invent. The "unaffordable retrofit" turned out to be a
  parser change with no backfill and no re-review.
- **Triage behaved as a review pass in its own right.** It surfaced defects no finding had recorded:
  a live closure bypass, a false closure in the ledger, a document contradicting itself by a factor
  of seven, two Lean predicates with byte-identical bodies presented as distinct results, a
  contraction field that reduces to a tautology at the instantiation used, and a wrong-target
  citation that had survived three months and a fix pass. **This is a result about process, not
  luck: disposition requires reading the artifact, which is the same act as reviewing it.**
- **Defects mutate rather than close.** Independently across slices: a count literal corrected to the
  review-era value and then re-drifted past it; a trivially-true predicate replaced by a differently
  trivially-true one; a figure whose repair landed in a *comment* while the code kept its invented
  labels; a closure bypass that moved from the heading to the ledger once the heading route was
  closed. **A fix verified once at a point in time, with no mechanism attached, is a fix that will
  re-break.** This is the strongest argument for attaching a verification command to a finding, and
  the first draft did not anticipate it.
- **A defect survived a lift and was strengthened by it.** A source paper was corrected to say a
  module "does not itself supply a machine-checked proof"; the bundle that absorbed it says the same
  theorem "substantively discharges" the hypothesis. Lift is a place where a closed finding reopens
  silently, and nothing checks it.
- **Self-review is not a substitute for independent review.** The lead's own remediation, checked by
  an agent instructed to be adversarial about it, contained two real errors — including a false
  attribution imported from an unverified docstring *while fixing a finding about unverified
  attribution*.

**Effect on the document:** two decisions rewritten, two constraints added, and scope materially
**reduced**. A pilot is not a confidence exercise; it is a scoping instrument.

---

## Round 2 — an adversarial review of the ADR, the spec and the plan together

**Instrument:** a fresh reader given all three documents and the code, asked what is already built,
what cannot fire, and what is unwired.

**What it found.**

1. **The spec proposed to build a check that already existed.** `ledger_ids_resolve` was live,
   pinned at zero headroom, mutation-verified against the correct host, and deliberately scoped to
   one id scheme with the reason stated in the code. The spec's headline number — an unmeasured
   orphan count "nothing measured" — was the aggregate over three schemes; the live scheme's count
   matched the existing baseline **exactly**.

   The proposed replacement would also have been **weaker**: an aggregate ceiling mixes permanently
   inert legacy records with live ones, so deleting one inert record silently buys a free slot for a
   real dangling closure. This is the "second mechanism beside one that already exists" failure that
   `CLAUDE.md` rule 1 names — landing *inside the change written to prevent it*.

   The resulting rule (§D13): **promote or widen, never duplicate**, and a promotion deletes the
   original leg in the same commit.

2. **One proposed guard could never fire in production.** The closure bar was to require a
   `verified_by` record for any finding carrying a `verify` command — but no finding could carry a
   `verify` command until the extractor parsed one. A parameter with no producer is a leg that cannot
   fire on any input: item 1 on `docs/architecture/CHECK_AUTHORING_GUIDE.md` §6's checklist. This is
   why routing and closure became one build rather than two.

3. **The plan omitted every registration obligation a new check carries.** See
   `shipping-checklist.md`. When the obligations were written into the plan's global constraints,
   the enumeration itself missed one site — `EXPECTED_CHECKS` — and three tests went red. **Even the
   corrected list was wrong**, which is why that file teaches derivation rather than a roster.

---

## Round 3 — an intent-drift assessment against the operator's original words

**Instrument:** re-read the operator's original specification, then read the draft, and ask whether
the draft still solves what was asked.

**What it found:** the first draft had solved the *closure* half of the loop and **silently dropped
the routing half — including the problem that started the thread.** Ten further decisions exist only
because of that assessment: the routing DAG, the decision-package definition, the operator queue,
the operator control surface, the termination condition, parked work, and the queueing of prior
ADRs' open items.

Two things this instrument caught that neither other instrument could:

- **A design can be internally coherent and still be a different design.** Round 2 read the document
  against the code and found nothing wrong with the closure half, because nothing *was* wrong with
  it. The missing half is invisible to any review that takes the document's own scope as given.
- **Paraphrase erodes requirements.** The ADR ends up quoting the operator verbatim in §D11 —
  a finding must arrive *"way beyond 'we have a problem'"* — with the note that the paraphrase kept
  losing it. Where a requirement has survived three restatements, quote it.

**Cost, stated in the ADR rather than hidden:** scope roughly tripled. The operator's ruling was
explicit — get it right now rather than discover and bolt on later. *"The first draft's narrower
scope was not a smaller version of this design; it was a different design."*

---

## What the rounds returned

| round | instrument | net effect on scope | class it catches |
|---|---|---|---|
| 1 | pilot on real data | **reduced** | the problem is not shaped like the document says |
| 2 | adversarial review of ADR + spec + plan | reduced, and unblocked a dead guard | already built · cannot fire · unregistered |
| 3 | intent-drift vs. the original ask | **tripled** | the document answers a different question |

They are not interchangeable, and none subsumes another. Running one and calling the specification
reviewed leaves the other two classes open.

---

## Why each step exists — the failure it prevents

The skill states what to do. These are the failures behind each instruction, kept here so
the sequence reads as a procedure rather than an argument.

| step | failure it prevents | what it cost in ADR-012 |
|---|---|---|
| 1 orient | a second mechanism beside one that already works | a proposed check already existed, ratcheted and mutation-verified, and the replacement was *weaker* (§C9). Orientation deleted a whole task |
| 2 measure | a design justified by a false premise | three drafts rested on a gating claim the code contradicted, never traced |
| 3 specify | a changelog that reads like a specification afterwards | — |
| 4 review | shipping a specification's first draft | §D18: a process that produces a spec nobody adversarially reviews produces this document's first draft |
| 5 pilot | building for an imagined population | a 117-finding triage found ~84% already repaired — a *recording* gap, not a defect backlog — rewriting two decisions and adding two constraints |
| 6 plan | splitting a build whose halves are inert apart | see "Three details" above |
| 7 ship | a check that cannot fire, an unregistered surface, a stale doc | §C4: a gate reported "all P1 passed" while blockers sat unclosed, because the findings produced zero edges. An unrecordable finding is indistinguishable from no finding |
| 8 terminate | a finding that reads closed over a system that is not | §D16 |

⚠️ **Defects mutate rather than close.** The pilot found this across slices: a corrected count
that re-drifted, a trivial predicate replaced by a differently-trivial one, a repair that landed
in a comment while the code kept its defect. **A fix verified once, with no mechanism attached,
is a fix that will re-break** — which is why step 7's obligation is a mechanism, not a
demonstration.

## Three details the skill cites but does not retell

Kept here so the skill can name the failure in a clause and a reader who wants the case has it.

**Step 2 — the premise that was never traced to code.** Three consecutive drafts asserted that
open REQUIRED findings *"blocked nothing"*. The code showed `major` had been a blocking severity
for weeks: the gating half of the diagnosis was simply wrong, and nobody had opened the file.
Separately the pilot's finding count had already moved by the time the closure writer existed,
and P7 re-derived it rather than reusing the number.

**Step 4 — self-review does not substitute.** In the pilot, an adversarial check of the lead's
own remediation found two real errors, and one of them was a **false attribution introduced while
fixing a finding about false attribution**. The lead was not careless; a reviewer reading their
own work is reading their own assumptions.

**Step 6 — halves that are inert apart.** The closure-side guard could not fire until the
routing-side parser produced its input. Shipping closure alone would have produced a guard green
in tests and dead in production — item 1 on `CHECK_AUTHORING_GUIDE` §6's checklist. Routing and
closure became one build for that reason (§D18).


## Reading this example critically

A third correction round is not a proof of correctness. ADR-012 still carries drift, and noticing it
is part of using it well:

- Its **Status block** says *"Nothing else in this document is implemented"* while its §Plan marks
  most phases complete and one decision `✅ IMPLEMENTED`. The status header was written first and
  never re-derived — the same failure class the document is about.
- Its §Consequences carries *"Live agent activity has no writer"* as a named risk, while §D20 (added
  later) establishes that `/goal`-level activity **does** have a writer and specifies a pane over it.
  A late correction landed in one section and not the other.
- Its §D9 non-vacuity paragraph carries two incompatible unattributed populations in adjacent
  sentences, because an inserted correction did not replace the figures around it.

**The lesson, and it is the same one:** an amendment corrects the paragraph it lands in, and every
other statement of the same fact stays wrong. When a correction lands, grep the document for the
claim it invalidates.

---

## Index — which lesson belongs to which step

| `SKILL.md` step | lesson from ADR-012 |
|---|---|
| 1 · orient | `ledger_ids_resolve` already existed, ratcheted and mutation-verified (§C9) |
| 2 · measure | "REQUIRED blocks nothing" was written three times and was false at HEAD (§Context) |
| 3 · specify first | the ADR states plainly that it is written before the code, deliberately |
| 4 · adversarial review | three instruments, three disjoint classes, one of them the missing half |
| 5 · pilot | ~84% already repaired; two of four proposed fields already in the corpus |
| 6 · plan | closure-without-routing produced a guard that no production path could enable (§D18) |
| 7 · ship | non-vacuity as a shipping requirement (§D8, §C4); the missed registration site |
| 8 · terminate | done means merged, with the docs corrected in the same commit (§D16) |
