# F apex retrofit — the flagship surveys a program four bundles smaller than the one that exists

**Date:** 2026-08-07 · Eighth bundle retrofitted under ADR-010 §D5a, and the first Tier-0.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/F/paper_draft.tex`
(2,494 lines, every line), `papers/F/bundle_metadata.json`, and — for the claims that became
findings — `docs/counts.tex`, `validate.py --list`, `docs/WAVE_EXECUTION_PIPELINE.md`,
`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`, and the axiom profile of every declared apex.

---

## 1. What was declared

**29 apexes → 221 declarations across 27 modules, depth 5, one private truncation.**

F is a survey, so its apexes are the theorems **it** names as backing its own predictive-register
entries and its substrate-identity synthesis claim — not everything its siblings claim.

| § | thread | apexes |
|---|---|---|
| §3 | gauge erasure (Closure 1) | 2 |
| §4 | SK-EFT analog Hawking | 1 |
| §6 | emergent gravity: Sakharov coefficient, three closures, four gates, entropy, Λ, torsion, Lorentzian backbone | 17 |
| §7 | topological QC: one MTC, four faces | 6 |
| §8 | dark sector: the 8/8 entropic-gravity closure | 3 |

---

## 2. ⚠️ The flagship's architecture section is four bundles out of date

F states its scope repeatedly and consistently: *"the sixteen sibling-bundle threads"*,
*"$17$ publication targets"*, *"Tier 1 (8 deep papers): Bundle~D1 … Bundle~D8"*, *"this
flagship review (F) ships last, citing all 16 siblings"*, *"the 17-bundle architecture as a
coherent submission package"*.

**The live roster is 21 bundles.** D9, D10, D11 and D12 — four Tier-1 deep papers, three of them
now with declared apexes and measured closures — appear **nowhere** in the document that claims
to survey the program. ADR-010's D10+D11 authorization (2026-06-29) post-dates this draft, and
nothing brought the flagship forward.

This is not a stale count in a narrative; it is a **scope** claim. A survey that enumerates its
own contents and omits four of them is wrong about what it surveys, and the sentence
*"integrates the sixteen sibling threads into a single survey"* is the thesis of the paper.

**§11.1 compounds it:** *"the substrate program has shipped 17 bundles to reviewer-triple-closed
Stage-13 GREEN status."* Both halves fail — the roster is 21, and the live readiness data says no
bundle is submittable. F itself is `readiness: RED` with 23 open blockers. Filed as **TODO-D15**.

---

## 3. The closure: F's declared substrate is D1-shaped and touches none of the QC bundles

| pair | shared declarations |
|---|---|
| **F ∩ D1** | **27** |
| F ∩ D6, D9, D10, D11, D12, L2 | **0** each |

D2, D3, D4, D5, L1, L3, I1–I3, E1, E2 are still undeclared, so F cannot yet be measured against
them — and most of F's apexes are their content (`HeatKernelExpansion`, `GravitationalWaves`,
`QECHolographyBridge`, `EntropicGravityDarkEnergy`). The zeros that *are* measurable say
something specific: **the flagship's substrate touches none of the six quantum-computation,
detection and band-theory bundles.** Two of those (D6, D7, D8) it names; four (D9–D12) it does
not know exist.

**F §7's D6 absorption checklist is stale in the other direction.** Six boxes, all unchecked,
including *"Wave 6v.2 ship — pending"*, *"Wave 6v.5 ship — pending"*, *"Wave 6v.6 ship —
pending"*. D6's own declared apexes include `wave_6v_5_substantive_closure`,
`wave_6v_6_substantive_closure` and `shor_ecc256_tgate_count_le` (the 6v.2 headline), and D6 has
completed its Stage-13 pass. **At least four of the six boxes are done and the flagship still
shows them open.**

---

## 4. ⚠️ The `native_decide` disclosure defect is corpus-wide, not a D1 slip

Yesterday's D1 retrofit filed TODO-D13 against §3.1's claim that four counting theorems are
*"closed by `native_decide`"* when they are `by decide`. **F has the same defect
independently**: §7.2 annotates `FigureEightKnot.figure_eight_normalized` with
`(\texttt{native\_decide})`.

Measured: `figure_eight_normalized` carries the axiom profile
`{propext, Classical.choice, Quot.sound}` — and **`Lean.ofReduceBool`, the axiom a
`native_decide` proof necessarily carries, appears on ZERO declarations project-wide.**

Two independently drafted manuscripts each volunteer a trust weakness the library does not have.
That changes the item's shape:

- It is a **corpus-wide prose pattern**, not one author's slip, so the fix is a sweep, not a
  sentence.
- It **resolves** ADR-010's open *`native_decide` disclosure posture* item on the merits: there is
  nothing to disclose. The posture question was posed as *how much should we say about our
  `native_decide` use*; the measurement says the answer is *that we have none*, and the live
  defect is drafts claiming otherwise.

TODO-D13 is broadened accordingly rather than duplicated.

---

## 5. Stale infrastructure descriptions in §9

F's §9 describes the verification stack. Each item below was re-derived, not assumed:

| F says | live | source |
|---|---|---|
| *"`validate.py`; 29+ checks"* | **66** | `validate.py --list` |
| *"Pipeline Invariants 1--14"* | invariants run to **#17** | `WAVE_EXECUTION_PIPELINE.md` |
| *"`physics-qa:figure-reviewer`"* | plugin is **`skeft-qa`** | `.claude/plugins/` |
| *"frozen 7-stage protocol with branches D.1/D.2/D.3"* | 7 stages ✓, but branch **D.4** exists | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:9,56` |
| *"$\sim 322$ Aristotle-proved theorems"* | value ✓ today | `\aristotleproved{}` = 322 |

The last one is the interesting one: **the value is right and the mechanism is wrong.** F
`\input`s `counts.tex` and uses `\substantivetheorems{}`, `\leanmodules{}`, `\axiomcount{}` and
`\sorrycount{}` as macros throughout — then hardcodes `322` for the one figure that has a macro
(`\aristotleproved{}`) sitting in the same file. It is correct now and will silently drift, which
is exactly what the macro exists to prevent. Filed under **TODO-D15** with the roster staleness,
since both are the same failure: the flagship describes a snapshot of the program rather than the
program.

---

## 6. What F gets right, and it is worth saying

Recorded because a findings document that only lists defects mis-describes the object.

- **The Wen-ADW factor-6000 figure is honestly scoped.** F states the Lean-certified content is
  `coupling_deficit` at the four-fermion level (`G_4f < G_c^ADW/1000`) and says in both §6.2 and
  §10 that *"the factor-6000 figure on the emergent Newton constant ratio is an informal
  extrapolation … and is not separately Lean-verified at the Newton-constant level."*
- **The dark-energy thresholds are not flattened.** The abstract says *"two of four quantitative
  mechanisms exceed Jeffreys-decisive"* and the register separates the Bayes-decisive pair, the
  ≥5σ exclusion under *nominal profile assumptions*, and the merely-moderate ΔAIC = 4.7. The two
  aggregator theorems (`both_decisive_bayes_bounds_exceed_jeffreys_decisive` vs
  `all_quantitative_bounds_disfavoured`) are deliberately distinct, and the prose tracks them.
- **The cosmological constant is labelled reproduced, not solved**, with the rigorous Lean bound
  (10^100) distinguished from the heuristic (10^122) every time both appear.
- **The vestigial-graviton natural range is flagged as a project-adopted naturalness window**,
  *"a modeling choice of this project rather than a published derivation"* — in both §6.2 and §10.
- **`dai_freed_spin_z4` is disclaimed as an external hypothesis**, not Lean-verified content, so
  it was excluded from the apex list on the draft's own instruction (§7 below).

The defects in §2–§5 are *bookkeeping about the program*. The physics claims are hedged with more
care than the surrounding infrastructure prose.

---

## 7. Candidates rejected

| candidate | why rejected |
|---|---|
| `SKEFTHawking.dai_freed_spin_z4` | F §5.2 says the cobordism computation is *"described in both papers as an external hypothesis, not as Lean-verified content"*. Declaring it would make F claim what it explicitly disclaims. |

---

## 8. Ledger

| artifact | change |
|---|---|
| `papers/F/bundle_metadata.json` | `apex_theorems` added — 29 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 14 → 13 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D15 (roster + infra staleness); TODO-D13 broadened to corpus-wide |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V24 |

Gate: `validate.py --check bundle_apex_resolves` — PASS.
