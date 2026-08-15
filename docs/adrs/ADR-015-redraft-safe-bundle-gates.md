# ADR-015 — Gates that survive a redraft: deregistration, abstract size, apex-claim grounding

**Status:** Accepted · **Date:** 2026-08-15 · **Lane:** `infra`

**Supersedes nothing. Extends** ADR-011 (manuscript quality layer, which introduced
`bundle_manuscript_length` and `bundle_lean_module_coverage`) and ADR-010 §Open (which
introduced `bundle_apex_resolves`).

---

## Context

The Stage-10 full redraft of L3 landed on 2026-08-15 and is the **pilot** for redrafting
all twenty-one publication bundles. Its finding document,
[`papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md`](../../papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md),
surfaced three defects in the gate layer that will recur on the other twenty. One of them
did not merely fail to catch a defect — **it caused one**.

⚠️ **Ordering disclosure, because the architecture-change sequence says specify before
building and this ADR was written after the code.** For decisions 1–3 the pilot's
finding document *was* the specification: §5.2, §5.1 and §3 each state the defect, the
measured consequence, the expected behaviour and a proposed fix, and each was reviewed
by the operator before this work started. This ADR records the decisions, the
measurements re-derived at HEAD, and the places where the implementation departs from
what the finding proposed. It is not a substitute for having written it first, and the
one place that cost something is noted under Decision 2.

---

## Measured at HEAD, 2026-08-15

Every figure below was re-derived from the live artifacts for this ADR, not quoted from
the finding document — including the finding document's own numbers.

| what | measured |
|---|---|
| bundles in the roster | 21 (`bundle_registry.BUNDLE_CODES`) |
| bundles whose declared venue is a letter | 5 — L1, L2, L3, E1, E2 |
| `bundle_lean_module_coverage` live absence count | 149, exactly its ceiling — **zero headroom** |
| L3's registered-but-unreached modules, before and after its redraft | 4 and 4 |
| declared apex theorems corpus-wide | 639 across all 21 bundles |
| apex names that fail to resolve | 0 |
| apex `claims` strings read by any check, test or reviewer agent, before this ADR | **0** |
| apex claims whose numerals are absent from the statement (one-hop) | 31 across 12 bundles |
| abstracts sized by any gate, before this ADR | **0** |

**Abstract sizes, all 21 bundles, rendered-proxy characters.** The five letters are the
population with a declared ceiling; the rest are listed because the operator asked which
would be rejected today and a venue may yet declare a limit.

| bundle | venue | abstract (chars) | verdict |
|---|---|---|---|
| L1 | PRL | 1849 | **3.1× over 600** |
| L2 | PRL | 2454 | **4.1× over 600** |
| L3 | PRL | 581 | within (redrafted 2026-08-15) |
| E1 | PRL \| PRR | 1943 | **3.2× over 600** |
| E2 | PRL \| PRR | 2158 | **3.6× over 600** |
| D1 | PRD | 3678 | no ceiling declared |
| D2 | PRD \| JHEP | 3106 | no ceiling declared |
| D3 | PRD | 3105 | no ceiling declared |
| D4 | Comm. Math. Phys. \| PRX Quantum | 2944 | no ceiling declared |
| D5 | PRD | 4516 | no ceiling declared |
| D6 | PRD or JHEP | 2306 | no ceiling declared |
| D7 | PRX Quantum or Physical Review X | 2474 | no ceiling declared |
| D8 | PRX Quantum \| Quantum | 2949 | no ceiling declared |
| D9 | PRX Quantum \| Quantum | 3063 | no ceiling declared |
| D10 | PRD \| PRX Quantum \| J. Chem. Phys. | 2226 | no ceiling declared |
| D11 | PRD \| PRX Quantum \| PRB | 2024 | no ceiling declared |
| D12 | PRX Quantum \| Quantum \| Phys. Rev. Applied | 1886 | no ceiling declared |
| F | Living Rev. Relativity \| Phys. Rep. | 2581 | no ceiling declared |
| I1 | CPC \| Phys. Rep. | 2409 | no ceiling declared |
| I2 | JOSS | 2452 | no ceiling declared |
| I3 | JOSS \| CPC | 3302 | no ceiling declared |

---

## Decisions

### D1 — A bundle may DEREGISTER a Lean module, and the ratchet ceiling stays where it is

**The defect is a content defect.** `bundle_lean_module_coverage` sits at its ceiling with
zero headroom, so a redraft that legitimately stops depending on a module raises the
corpus count and turns the corpus red. The cheap path was therefore to keep naming the
module — and the pilot took it. Measured, from the finding: **the L3 drafting lead
retained two theorem citations in the Discussion purely to hold the ratchet green, and
the `prose-reviewer` independently flagged exactly those two as belonging to a different
paper's argument.** A gate that makes the manuscript worse is worse than no gate.

**Decision.** `scripts/bundle_append.py` gains `--deregister-lean-modules` +
`--deregistration-rationale`. The event is **appended**; the registering event is never
edited or removed. `check_bundle_lean_module_coverage` scores the **net** registration
set, walked in event order by the single implementation
`bundle_append.net_registered_modules`.

**Explicitly rejected: raising or removing the ceiling.** It buys identical relief and
destroys the measurement. Deregistration *lowers* the live count, which is a
down-ratchet — the direction this ratchet already permits.

**Four properties keep it from being an escape hatch**, and the fourth is the one that
matters:

1. a named CLI mode with a required rationale — there is no silent form;
2. append-only, so the history still says the bundle once depended on the module;
3. **every deregistration is reported on every run, including a green one**, naming the
   modules and not merely counting them;
4. **the claim is falsifiable against the manuscript.** Deregistering a module the draft
   still reaches — by name or by citing its theorems — is a hard, unratcheted FAILURE.
   "I no longer depend on this" is checked, not accepted on the word of the agent that
   wrote it.

The rationale floor is asserted **in the check as well as in the writer**, because
`append_log.json` is an ordinary tracked file and a hand edit reaches it. A gate that
trusts its own CLI to have been used is not a gate.

⚠️ **Consequence for the redraft campaign.** Each deregistration lowers the live absence
count. `LEAN_MODULE_ABSENT_CEILING` must be lowered to the new live value **in the same
commit** — `test_the_ratchet_has_zero_headroom` fails otherwise, which is the intended
cost and the reason the drop cannot be pocketed as headroom for a later bundle.

### D2 — The abstract ceiling is DECLARED per bundle, and its provenance travels with it

The superseded L3 abstract was ~1900 characters against PRL's ~600, and every gate passed
it: `bundle_manuscript_length` sizes the whole manuscript, and four pages is within a
3750 word-equivalent ceiling however the words are distributed. Five bundles are letters.

**Decision.** A new `bundle_abstract_length` check reads
`length_target.abstract_ceiling` — `{unit, ceiling, source, source_verified,
source_note}` — from each bundle's own `bundle_metadata.json`, exactly parallel to the
`length_target` it sits inside. **The check hardcodes no venue's limit and must not
start.** A venue table in the check would be the `CHECK_AUTHORING_GUIDE` §6 failure *"a
hand-maintained list parallel to a registry"*: the venue already lives in the bundle's
metadata.

⚠️ **This is where writing the ADR after the code cost something.** The design assumed the
venue limits could simply be looked up. A `research-scout` pass over fourteen journals on
2026-08-15 returned **one** primary-verified answer — JOSS, which states no separate
abstract limit at all. APS (`journals.aps.org/robots.txt` disallows automated agents),
Elsevier and AIP (403 to every request, including `robots.txt`) and Springer (login wall)
are all structurally unreachable. So the PRL ~600 now declared on the five letters is
**the pilot finding's number, not a primary-sourced one.**

That is recorded rather than smoothed over: `source_verified: false` is carried in the
metadata and **printed on every run, including a passing one**, so a green is never read
as *"confirmed venue-conformant"*. Confirming the fourteen venues against their actual
author guides is filed as a finding, not assumed. It does not block: every failing bundle
is 3–4× over, so no plausible correction to the figure changes a live verdict.

A bundle with no declared ceiling is reported **by name** as UNMEASURED with
`measured=False`, never as a quiet pass — the `bundle_manuscript_length` policy,
deliberately mirrored.

### D3 — The apex `claims` string is checked for three decidable properties, and the check says what it cannot do

`bundle_metadata.json.apex_theorems[*].claims` — 639 strings — was read by no check, no
test and no reviewer agent. The pilot found one of L3's thirteen describing a theorem
that does not exist in that form (§2.3).

**Scope decision, and it is the load-bearing one.** `bundle_apex_resolves` already
hard-fails on an apex that names no live declaration and on one that resolves to a
non-theorem. Re-asserting either would be the second-resolver duplication `CLAUDE.md`
rule 1 names. `apex_theorem_claims_grounded` therefore owns **the string and nothing
else**, and skips any apex the other check reports unresolved rather than
double-reporting it.

Three legs:

1. **present and non-placeholder** — hard fail, live population 0;
2. **not a restatement of the theorem's own name** — hard fail, live population 0;
3. **numerals appear in the statement, or in the statement of anything it references** —
   ratcheted at 31.

Legs 1 and 2 are hard *because* their population is zero: that is what a regression guard
looks like, and a ratchet at zero is the same thing with a worse name. Both are
production-seeded to prove they can fire.

⚠️ **What the check cannot verify is written into its docstring, at length, because its
silence must not be read as endorsement.** Claim-to-type equivalence is not decidable and
the check does not approximate it. It does not establish that the claim describes the
theorem, that it is true of it, that it is not its converse, that it is not strictly
stronger, or that its hypotheses match. **The exact §2.3 defect that motivated it would
not be caught by it** — that claim carries no numerals and is not a name-restatement.
Catching it needed a human reading the type beside the prose, and still does.

Two calibrations, both measured rather than guessed:

* single digits 0–9 are excluded from leg 3. An elaborated Lean type writes small
  literals through `OfNat`/`One`/`Zero`, and prose uses them as enumeration. Including
  them took the population from 31 to **159**, essentially all noise.
* the statement haystack is **one hop** — the type, plus the types of declarations the
  type references. A full closure moved 34 → 31, which pays for neither the cost nor the
  weaker meaning of a hit.

**An entry under leg 3 is a pointer to check, not a proven defect**, and the ratchet is
what makes that honest. `lean_deps.json` carries types, not definition bodies, so a
numeral living inside a `def`'s value — `G_N_sakharov = 12π/(N_f Λ²)` — is invisible to
any depth of type walk and lands here while being perfectly correct.

---

## Consequences

* Three of the twenty-one bundles' gates change behaviour; `bundle_abstract_length` is
  **RED on arrival** on L1, L2, E1 and E2. That is the instrument working — those four
  abstracts would be desk-returned — and it is the redraft campaign's first work item.
* `CI_MIN_CHECKS_RUN` 82 → 84. Both new checks measure in production.
* The redraft of each remaining bundle now has a sanctioned way to drop a dependency, so
  no other bundle should repeat L3's retained-citation defect.
* `LEAN_MODULE_ABSENT_CEILING` will move down repeatedly during the campaign. Each move
  is a commit that also states which bundle deregistered what and why.

## Alternatives rejected

| alternative | why not |
|---|---|
| raise or remove `LEAN_MODULE_ABSENT_CEILING` | identical relief, destroys the measurement; explicitly ruled out by the task and by `bundle_manuscript_length`'s own precedent |
| let `bundle_append.py` DELETE the registering event | a drop must stay visible; an edited log cannot say the dependency once existed |
| a venue → abstract-limit table inside the check | a hand-maintained list parallel to the bundle metadata that already carries the venue |
| block the abstract gate until venue limits are primary-verified | the four failures are 3–4× over; waiting on an unreachable author guide to report a 4× overrun is deferral |
| extend `bundle_apex_resolves` with the claims legs | it gates the apex NAME and is cited as doing exactly that; a second concern in it would make its verdict unreadable |
| a claim-to-type equivalence check | not decidable; an approximation that reported a verdict would manufacture the confidence this suite exists to prevent |
