# D1 apex retrofit — the honest denominator, a false disclosure, and four lifts that lifted nothing

**Date:** 2026-08-07 · Seventh bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D1/paper_draft.tex`
(1,234 lines, every line, including the bibliography and the commented material after it),
`papers/D1/bundle_metadata.json`, `papers/D1/append_log.json` (all 13 events), and — for the
claims that turned out to be the findings — `lean/SKEFTHawking/SecondOrderSK.lean` at the four
counting theorems, plus a full run of `scripts/count_theorem_reuse.py`.

---

## 1. What was declared

**41 apexes → 249 declarations across 18 modules, depth 3, zero private truncations.**

| § | layer | apexes |
|---|---|---|
| §2 | first-order SK-EFT, acoustic-metric backbone, universality | 6 |
| §3 | second-order: counting, positivity, KMS optimality, CGL FDR | 10 |
| §4 | exact-WKB connection and the three non-perturbative effects | 9 |
| §6 | polariton platform | 3 |
| §7 | graphene Dirac fluid: block-diagonalisation, noise spectrum, WF cross-check | 7 |
| §8 | Kibble–Zurek–Unruh cross-check and the simulability demarcation | 6 |

**D1 ∩ every other declared bundle = 0** (D6, D9, D10, D11, D12, L2). Notably that includes
`ChernBridge`, which **D11's own §8 carves out** as "a categorical Chebyshev marker that a
companion bundle describes in Chern language". D1 is that companion bundle, D1 claims the module,
D11 disclaims it — and the two closures agree.

---

## 2. The honest denominator for TODO-D9

D1's abstract says: *"End-to-end, `\substantivetheorems{}` Lean theorems are machine-verified."*
That macro is **project-scoped** (live value in `docs/counts.tex`) and auto-inflates as the
library grows — the defect TODO-D9 records.

**The measured closure of everything D1 claims is 249 declarations.** That is the number a
reader of *this* abstract is entitled to. The ratio is roughly two orders of magnitude, and it
grows every time an unrelated wave lands.

⚠️ **TODO-D9's own arithmetic used 114 as the denominator, and that number is not D1's
substrate** — it is the population of the *nine 1+1D BEC modules* over which §7.2's reuse
fraction is computed, which is a different set for a different purpose. Both numbers describe
real things; neither was the bundle's substrate, because nothing measured it until now. Update
TODO-D9's arithmetic to 249 rather than carrying the old ratio forward.

---

## 3. ⚠️ §3.1's `native_decide` disclosure is false — and false in the damaging direction

The draft states that the small-`N` counting cases *"are independently closed by `native_decide`
in `SecondOrderSK.firstOrder_count`, `secondOrder_count`, `secondOrder_count_with_parity`,
`thirdOrder_count`."*

**They are not.** Read directly in `lean/SKEFTHawking/SecondOrderSK.lean`:

| theorem | line | proof |
|---|---|---|
| `firstOrder_count` | 258–260 | `by decide` |
| `secondOrder_count` | 270–272 | `by decide` |
| `secondOrder_count_with_parity` | 282–285 | `by decide` |
| `thirdOrder_count` | 935–937 | `by decide` |

Their own docstrings say *"Use decide."* All four carry the axiom profile
`{propext, Classical.choice, Quot.sound}` and nothing else. And the decisive check:
**`Lean.ofReduceBool` — the axiom a `native_decide` proof necessarily carries — appears on ZERO
declarations project-wide.** There is no load-bearing `native_decide` anywhere in this library.

`decide` is checked by the kernel; `native_decide` is not. **D1 is disclosing a trust weakness it
does not have**, and volunteering it in exactly the place a referee looks for one. D11's own
draft states the distinction correctly (*"`decide` … is checked by the kernel and is a different
thing from `native_decide`"*), so the project knows it; D1's sentence predates or ignores it.

This also bears directly on ADR-010's open **`native_decide` disclosure posture** item: the
posture cannot be decided from the drafts, because at least one draft's disclosure does not
describe its own substrate. Filed as **TODO-D13**.

---

## 4. ⚠️ Four `Lift-section` events lifted nothing

`append_log.json` records four **`Lift-section`** events on 2026-05-06:

| source | target § | what is in the manuscript |
|---|---|---|
| `_phase6n_W1a_lean_only` | §3 | commented-out heading + `TODO: lift content` |
| `_phase6n_W2c_lean_only` | §5 | commented-out heading + `TODO: lift content` |
| `_phase6n_W2b_lean_only` | §6 | commented-out heading + `TODO: lift content` |
| `_phase6o_W1a_lean_only` | §6 | commented-out heading + `TODO: lift content` |

All four sit **after `\end{thebibliography}`**, all four are fully commented out, and each carries
three unresolved `TODO`s (lift the content; trace the numerical claims; cache the citations).
The named content is substantial — a kinematic-dispersive geometric envelope with a closed-form
`γ_n`, an LDP linear-response framework, a quantum-Crooks no-go landscape, and boostless /
Carrollian soft theorems with a Strominger-triangle closure.

**Commenting the stubs out was the right call and is documented as such** (2026-05-06 Session 2 —
they were empty post-bibliography artefacts of `bundle_append.py`'s default insertion). The
defect is that the *log still reads `Lift-section`*, so the absorption ledger records four
completed lifts that inserted zero words. Anything that counts absorptions from this log
over-counts D1 by four. Filed as **TODO-D14**.

This is the D11 pattern in a different key: there, proved content was missing from the
manuscript; here, the bookkeeping asserts it was added.

---

## 5. Re-measured and NOT filed

Recorded because the near-miss is the point.

**The `114` in §7.2 is correct.** The `lean_deps` extraction attributes **194** author-written
theorems to the nine named modules, which looks like an 80-theorem understatement — but running
`scripts/count_theorem_reuse.py` reproduces **114 / 106 / 8 → 92.98%** exactly, module by module.
The two numbers are the project's two counting conventions: source-level hand-written
declarations versus the extraction, which additionally counts Lean-generated equation lemmas.
Filing this as an error would have been wrong, and the extraction is the seductive number because
it is the one already in hand.

*Per `feedback-remeasure-filed-findings-before-fixing`: the script was run, not assumed.*

**Residual, minor:** D1 does not say which convention its `114` uses. D11's draft discloses the
two conventions explicitly and states which it uses throughout. D1 should borrow that sentence —
folded into TODO-D9's prose fix rather than filed separately, since both are `counts.tex`
disclosure defects in the same manuscript.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D1/bundle_metadata.json` | `apex_theorems` added — 41 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 15 → 14 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D13 (`native_decide`), TODO-D14 (the four empty lifts); TODO-D9's denominator corrected |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V23 |

Gate: `validate.py --check bundle_apex_resolves` — PASS.
