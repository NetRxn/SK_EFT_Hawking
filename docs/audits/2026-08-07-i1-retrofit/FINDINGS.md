# I1 apex retrofit — the methodology paper describes a pipeline half its current size

**Date:** 2026-08-07 · Fifteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/I1/paper_draft.tex`
(1,875 lines, every line, including the nine `% TODO: substantive draft` comment blocks and the
three commented lift stubs after the bibliography), `bundle_metadata.json`, and — for the
infrastructure claims — `validate.py --list`, `docs/WAVE_EXECUTION_PIPELINE.md`, and
`lean/lean-toolchain`.

---

## 1. What was declared

**6 apexes → 73 declarations across 7 modules, depth 4, zero private truncations.**

I1 is a **methodology** paper: its subject is the pipeline, not the physics. It names only seven
Lean theorems in monospace across 1,875 lines, and six are declared — the seventh resolves to an
`IntCongr.rfl` token collision, not a citation.

| § | worked case | apexes |
|---|---|---|
| §3 | the FirstOrderKMS Aristotle counterexample | 1 |
| §4 | the gap-solution-bounded disproof | 1 |
| §5 | the chirality-wall decomposition (root + hidden dependency + its resolution) | 3 |
| §13 | structural-Prop scoping, worked on the 1D wave equation | 1 |

**The three worked cases are the apexes, and that is the right reading.** I1 does not claim
physics results; it claims that a *pipeline* catches a class of errors, and each worked case is a
theorem that exists in its corrected form *because* the pipeline forced the correction.

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Computational-physics groups and the formal-methods-for-science community — people deciding whether continuous verification is worth its cost. Explicitly domain-agnostic: the closing section names pharmaceutical software, financial modelling and climate modelling. |
| **Venue** | CPC \| Phys. Rep., per the metadata. CPC fits: a methods paper with a public repository. |
| **The claim only this container can make** | **That continuous verification is cheaper than retrofitted verification, evidenced from a running program rather than argued.** The load-bearing evidence is the three worked cases where a *failure* of the pipeline's automated layer was diagnostic — a prover refusing a wrong theorem, a folklore claim refuted by counterexample, a monolith that was large rather than hard. No sibling reports on the method; the siblings *are* the method's output. |
| **Substrate** | 7 modules, 73 declarations, depth 4: `SKDoubling`, `TetradGapEquation`, `EWBaryogenesisChiralityWall`, `WaveEquation1D` and their dependencies. **Deliberately small** — a methodology paper's substrate is its case studies. |
| **Honest size vs charter** | 1,875 lines — substantial prose, and the largest Tier-3 draft. But **nine sections still carry `% TODO: substantive draft` comment blocks that are stale**: every one of those sections now has real prose. The TODOs are scaffolding nobody removed. |
| **Boundary failure?** | **No.** I1 ∩ every other declared bundle is measured below; its purpose is statable entirely on its own case studies. |

---

## 2. ⚠️ The finding: I1's infrastructure figures describe a pipeline about half its current size

I1 is the paper *about* the pipeline, so its numbers are load-bearing in a way another bundle's
would not be. Each was re-derived from the artifact it names:

| I1 says | live | source |
|---|---|---|
| *"thirty-three registered checks at the time of writing (June 2026), enumerated live by `validate.py --list`"* | **66** | `validate.py --list` |
| *"fourteen stages and fifteen invariants"*; *"The invariant set has since grown to fifteen"* | invariants run to **#17** | `WAVE_EXECUTION_PIPELINE.md` |
| *"seventeen publication targets … eight themed deep papers (`D1`–`D8`)"* (§8, §14, and Invariant 14's text *"beyond the current seventeen"*) | **21** bundles, `D1`–`D12` | `validate.BUNDLE_CODES` |
| *"the project's local toolchain is currently `leanprover/lean4:v4.29.0`"*, and *"All worked-case theorems … verified to compile cleanly on the project's local 4.29.0 toolchain"* | **`v4.32.0`** | `lean/lean-toolchain` |

**The check count has exactly doubled.** The toolchain claim is the sharper one: it is not a count
but a *verification claim* — that specific theorems were checked on a specific toolchain — and the
toolchain named is two minor versions behind. The theorems presumably still compile; the sentence
as written asserts something that was checked against a configuration that no longer exists.

⚠️ **This is the same defect class as F's §9 (TODO-D15), and it lands harder here.** F is a survey
describing infrastructure in passing. **I1 *is* the infrastructure paper** — a methodology paper
whose central argument is that the pipeline keeps prose synchronised with reality, describing that
pipeline at roughly half its current size. Filed under **TODO-D15** as its second bundle.

---

## 3. Nine stale `% TODO: substantive draft` blocks

Every section from §3 onward opens with a comment block reading *"TODO: substantive draft.
Substrate to draw from: …"* followed by a bulleted plan and a "Section thesis" — and then, below
it, the fully drafted section. **All nine are stale.** They are invisible in the PDF and harmless
to a reader, but they are the authoring scaffolding for a paper that has since been written, and
they make the source unreadable as a status signal: a reader of the `.tex` cannot tell drafted
from undrafted.

Compare D7, where the bracketed placeholders are the *rendered* content and accurately signal an
unwritten section. **I1's TODOs say "unwritten" about written sections; D7's brackets say
"unwritten" about unwritten ones.** Only the second is honest by accident of being visible.

Recorded, not filed as its own TODO — it is a source-hygiene item with no reader-visible effect.

---

## 4. The closure, and the TODO-D3 coupling

| pair | shared | modules |
|---|---|---|
| **I1 ∩ D1** | **30** | `SKDoubling` 27, `Basic` 3 |
| **I1 ∩ F** | **26** | `SKDoubling` 26 |
| **I1 ∩ D2** | 1 | `Z16AnomalyComputation` |
| everything else declared | **0** | |

⚠️ **I wrote a guess for this table before measuring it and had to replace it.** The guess was
"D2 20 / D3 3 / F 3", reasoning from which bundles *own* the case studies. The measurement says
the overlap is overwhelmingly **`SKDoubling`** — Worked Case 1's module — which D1 and F both
claim, while the chirality-wall case (D2's territory) contributes **one** declaration and the gap
equation (D3's) contributes **none**.

**The reason is instructive:** an apex's closure is what it *rests on*, not what it is *about*.
`sm_no_nu_R_ewbg_doubly_forbidden` is a chirality-wall theorem but its dependency cone barely
touches what D2 declares; `firstOrder_uniqueness` sits on the whole `SKDoubling` stack. **A
methodology paper's overlap tracks its case studies' substrate, not their subject matter** — and
guessing from subject matter got the shape and the magnitudes wrong.

⚠️ **TODO-D3 remains open and is confirmed live by this pass.** I1 §4 cites the disproved stub at
*"lines 307–321"* and the live theorem at *"lines 329–345"*; the actual block is **311–325** and
`gap_solution_monotone` is at **333** — a systematic 4-line offset. I1 §10 names the coupled
waiver (`prose_theorem_reference_coverage`'s `waived:I1:gap_solution_bounded`) as *"the canonical
waiver"*, so **the two must be fixed together**, as TODO-D3 already says. Not re-filed.

**And I1 cites Lean by line number pervasively** — `Basic.lean` line 152, `SKDoubling.lean`
244–280 / 156–168 / 367–379 / 412–439, `EWBaryogenesisChiralityWall.lean` 106–114, plus registry
line numbers in `constants.py` (2282, 1391, 2127, 2329). TODO-D3's fix shape — *cite by
declaration name, not by line* — applies to all of them, and its own note that "any other
line-number citation into this file is likely off by the same amount" is now the general case.

---

## 5. What I1 gets right, and it is unusual

**It publishes a bad number about itself.** §10 and §14 report that a June-2026 remediation found
fabricated *attributions* — prose ascribing to a real, cached, correctly-identified source a claim
the source does not make — at *"roughly three per ten spot-checked load-bearing attributions"*,
and says so in the abstract. The paper then names this *"exactly the kind of number a verification
program must be willing to publish about itself."*

Also honest, each checked:

- **A speedup claim is declined for lack of a benchmark**: the interactive loop replaces a ~15 s
  round-trip with millisecond LSP inspection, but *"we have not measured this factor on a
  controlled benchmark set, and quantitative speedup claims would require such a benchmark to be
  load-bearing."* An easy 1000× headline, not taken.
- **The "no findings recorded is not evidence of review" argument** is stated in as many words,
  and is why the yellow-unreviewed verdict class exists.
- **A corrected count is reported with both drifted halves**: the manual `109/119` cross-platform
  reuse figure corrected to `106/114`, *"with both the numerator and the denominator of the manual
  count having drifted."*
- **The strengthening discipline's limits are stated**: the prospective checklist catches the
  obvious anti-patterns and *misses* identity-function wrappers, within-own-±2σ-band tautologies,
  pairwise-distinctness on inductive constructors, and definitional-unfolding-as-physics.

⚠️ **The irony is the finding, not a rhetorical flourish.** §2's four opening failure modes
include *"a parameter whose value was inherited from a prior draft and had drifted."* §2's own
infrastructure figures are that failure mode, in the paper that names it.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/I1/bundle_metadata.json` | `apex_theorems` added — 6 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 7 → 6 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D15 gains I1 as its second bundle; TODO-D3 confirmed live and generalised; TODO-D14 → six bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V33 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 548 apexes across 15 bundles.
