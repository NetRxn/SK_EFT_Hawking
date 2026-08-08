# D7 apex retrofit — a second declaration conflict, and a bundle that is five-sevenths placeholder

**Date:** 2026-08-07 · Fourteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D7/paper_draft.tex`
(339 lines, every line), `bundle_metadata.json`, and — because this bundle resolves a conflict —
`papers/D1/paper_draft.tex` §8.2 re-read against it, plus a run of the existing
`prose_theorem_reference_coverage` check.

---

## 1. What was declared

**14 apexes → 93 declarations across 8 modules, depth 3, zero private truncations.**

| § | thread | apexes |
|---|---|---|
| §3 | the loop-correction rate function (Cramér/Legendre) | 8 |
| §4 | the categorical-Chern ↔ real-space-Chern bridge | 1 |
| §5 | the demarcation biconditional + contrapositive | 3 |
| §6 | the Kibble–Zurek–Unruh foundation | 1 |
| §2 | belief-propagation substrate | **0** — see §4 |

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | The classical-simulability / quantum-advantage community — people who read Tindall–Sels and Antão–Lado and want the boundary stated as a criterion rather than as a pair of demonstrations. |
| **Venue** | PRX Quantum or PRX, per the metadata. Plausible for the claim; **not** for the current draft (§4). |
| **The claim only this container can make** | **A kernel-verified simulability *demarcation biconditional*** — that a system on a factor graph with categorical-Chern data is classically simulable in the combined BP / Chebyshev-TN regime **iff** the loop-correction rate vanishes with non-negative weights **and** `c₁ = 0`, with the contrapositive giving the quantum-advantage regime explicitly. Two published results bracket the territory; D7 is the only container that states where the line is. |
| **Substrate** | 8 modules, 93 declarations, depth 3: `BPLDPSimulability`, `AnalogHawkingDemarcation`, `ChernBridge`, `KibbleZurekUnruh`, and their dependencies. |
| **Honest size vs charter** | **339 lines against ~40pp — the largest shortfall in the portfolio, and structurally so:** five of its seven sections (§§2–6) are square-bracket placeholders describing what the section *will* contain. Only the abstract, introduction and discussion carry prose. `stage9_status: not_started`, 12 open blockers. |
| **Boundary failure?** | **No, once the §3 reassignment lands.** D7's purpose is statable on its own substrate; the conflict was that *another* bundle had declared it. |

---

## 2. ⚠️ Second declaration conflict: D1 §8.2 had declared D7's entire headline

**Six of D7's fourteen apexes were declared by D1** — including all three
`AnalogHawkingDemarcation` theorems, the `BPLDPSimulability` headline biconditional, the
`ChernBridge` theorem, and the `KibbleZurekUnruh` foundation.

This is the mirror image of the D4→D8 case, and it resolves the same way:

| | D1 | D7 |
|---|---|---|
| where the content appears | **§8.2**, a subsection of *Synthesis and outlook*, headed *"Independent cross-check: Kibble–Zurek–Unruh universality"* | **the title, the abstract, and §§2–6** — the whole paper |
| what it does with it | cites it as an independent corroboration of D1's universality claim | states, proves and delimits it |

**Action taken:** six apexes reassigned **D1 → D7**. D1's closure fell **249 → 171** declarations
and **18 → 12** modules; D7's is 93/8.

⚠️ **The rule this is the second instance of, stated so the remaining bundles inherit it:**
*the container that develops content owns it; the container that cites it in a cross-check
subsection does not.* Both instances were found the same way — by reading the second draft in
full and letting the two drafts' own framing decide — and in both, the closure corroborated the
reassignment independently.

⚠️ **Note the asymmetry with D4→D8.** There, D8's draft *explicitly* ceded Fibonacci to D4, so
the drafts settled it in words. Here neither draft mentions the other, and the decision rests on
**where the content sits in each document** — D7's title versus D1's §8.2. That is a weaker
signal, and I record it as such: if the operator reads D1 §8.2 as load-bearing for D1's
universality claim rather than as a cross-check, the assignment should be revisited.

---

## 3. ⚠️ A dangling theorem name in the sentence that names D7's own headline

D7's introduction (line 127) reads:

> *"The biconditional `analog\_hawking\_quantum\_advantage\_demarcation' (Lean module
> `AnalogHawkingDemarcation.lean`) ties these two axes together at the type level."*

**`analog_hawking_quantum_advantage_demarcation` does not exist.** The live names are
`analog_hawking_fourCycleFree_demarcation` and `analog_hawking_tree_simulable_demarcation`.
Verified underscore-aware and seeded: the same probe returns PRESENT for
`analog_hawking_fourCycleFree_demarcation`.

**Existing coverage, read rather than assumed:** `prose_theorem_reference_coverage` runs green and
**does not report D7 at all**. The reason is the quoting: D7 writes the name in
`` `name' `` backtick-apostrophe form, not `\texttt{}`, and the extractor keys on the latter. So
this is a **coverage gap in a working check**, not a missing check.

Per §6a I am **not building anything**. Filed as **TODO-D18** with the defect, the existing
coverage, and the residue; the fix (widen the extractor's quoting forms, or normalise the draft to
`\texttt{}`) needs approval.

---

## 4. §2 declares nothing, and that is the honest reading

D7's §2 describes 24 substantive `BeliefPropagation.lean` theorems — message-update positivity,
factorization, fixed-point stability, Bethe free energy — but **names none of them**. The section
is a placeholder: *"Section content to be expanded in subsequent Stage-10 revision passes."*

An apex is a statement the manuscript presents as a result. A section that describes a theorem
family in aggregate without naming a member presents no statement, so **§2 gets zero apexes,
correctly** — and the closure records the consequence: 93 declarations, none of them the BP
substrate's own theorems.

**This is the sharpest instance of the retrofit's recurring finding**, and it is cleaner than
D11's: there, proved content was missing from a *finished* manuscript; here the manuscript is
explicit that it has not been written yet. **D7 is not overclaiming — it is unwritten.** Its
abstract makes a first-claim (with a scoped, honestly hedged footnote) and its discussion is
careful about three named residual scope points; the body between them is brackets.

---

## 5. What D7 gets right

- **The first-claim is scoped and hedged in a footnote that names its search method** — GitHub
  topics, Mathlib indexes, Coq/Agda ecosystems, dated — and closes *"We make no broader
  first-claim and welcome notification of prior work."*
- **The D7-EV3 review finding is recorded as an upgrade, with what it replaced**: the rate is now
  a genuine Cramér/Legendre construction, *"upgrades the earlier {0,1}-valued tree indicator"*.
- **The honest residual is named twice**: the rate attaches to the *combinatorial* loop-presence
  observable, not to the *dynamical* loop-correction terms of the Chertkov–Chernyak series.
- **The KZU application section says what it does not contain**: *"the
  `AnalogHawkingDemarcation.lean` module does not import `KibbleZurekUnruh.lean` and there are no
  `analog_hawking_simulable_BEC_instance` or analogous platform-specific lemmas at this writing."*
  Checked — that module name is absent from the corpus, exactly as stated.
- **Deleted tautologies are recorded, with their classification**: §5's note that three P5
  tautologies caught by the Round-1 review were deleted, naming which.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D7/bundle_metadata.json` | `apex_theorems` added — 14 entries |
| `papers/D1/bundle_metadata.json` | **6 apexes reassigned to D7** — closure 249 → 171, modules 18 → 12 |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 8 → 7 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | **TODO-D18** (the `prose_theorem_reference_coverage` quoting gap) |
| `docs/audits/2026-08-07-d1-retrofit/FINDINGS.md` | reconciled to the new closure |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V32 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 542 apexes across 14 bundles.
