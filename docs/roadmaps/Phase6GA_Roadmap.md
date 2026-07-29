# Phase 6GA — `native_decide` → `decide +kernel` ratchet-down: the small clusters

**Status: PLANNED (namespace authorized 2026-07-29).** First phase of the `6G*` series
(*soundness-surface ratcheting*). Independent of every other active phase.

**Series framing (`6G*` = ratcheting).** A namespace for work that **removes** concessions rather
than adding results: `native_decide` → kernel, `maxHeartbeats` elimination, axiom discharge,
tracked-hypothesis retirement. Separate from `6F*` because the deliverable stays in-repo, and
separate from the research namespaces because success is measured as a *decrease* in a tracked
number under ADR-002's ratchet, not as new mathematics. Room to grow: `6GB` (the large
`anyon_mtc` cluster, if 6GA's economics hold), `6GC` (the four `maxHeartbeats` quantum-group
files), `6GD+`.

**Thesis.** `native_decide` proves by *compiled native execution*, adding a generated
`ofReduceBool`-class axiom to every consumer's closure — the project's largest standing soundness
concession. `decide +kernel` decides in the **kernel**, so a converted declaration carries no such
axiom. Current surface (`docs/counts.json`, ADR-002 ratchet): **546 decl-closure**, clustered
`anyon_mtc` 327 / `number_field_qgroup` 154 / `other` 53 / `lattice_signature` 12, over **494 real
tactic sites in 43 files**.

**This is not a bump dividend.** `decide +kernel` was verified available at v4.29.1 as well (probe
run under both installed toolchains, 2026-07-29). It is a pre-existing, unexploited option that the
v4.32 re-validation happened to surface.

**Evidence it works (spike, 2026-07-29 — whole-module swap, re-elaborated, default heartbeats).**

| module | cluster | sites | native | `decide +kernel` | errors |
|---|---|---|---|---|---|
| `KacWaltonFusion` | anyon_mtc | 58 | 5.2s | 5.5s | **0** |
| `FibonacciMTC` | anyon_mtc | 11 | 5.4s | 17.2s | **0** |
| `QCyc40` | number_field_qgroup | 21 | 7.3s | 50.8s | **0** |
| `E8Lattice` | lattice_signature | 2 probed | — | clean | **0** |

**90 of 494 sites converted with zero errors, no Invariant-#10 violation.** Cost ranges from
negligible to ~7×.

> **⚠️ GUARDRAIL — this is a spike, not a finished result.** 90 sites of 494, in 3 files of 43.
> QCyc40's 7× is the warning: cost appears superlinear in the cyclotomic arithmetic, so the
> heaviest modules may not convert within default heartbeats. **Whole-build wall-clock impact is
> unmeasured.** Wave 1 measures before Wave 2 commits.

> **⚠️ GUARDRAIL — never raise heartbeats to force a conversion.** A module that will not convert
> at default heartbeats **stays `native_decide`**. Invariant #10 is not negotiable for a
> cosmetic axiom-count win, and a `maxHeartbeats` proof body is a worse defect than the
> `ofReduceBool` it would remove.

> **⚠️ GUARDRAIL — the ratchet is a floor, not a target.** ADR-002 tracks
> `native_decide_decl_closure` so it cannot silently *grow*. Driving it down is good; driving it
> down by weakening a statement, or by moving a decision out of the checked surface, is not.
> Every conversion keeps the statement byte-identical.

> **KNOWN NEGATIVE — does not generalize to the private braid-word corpus.** `decide +kernel` was
> tested on `NetRxnRD.TopologicalQC.SU2_3FibBraidWordsTGate`'s chunk identities (5×5 matrix
> products over `QCyc5Ext`) and **fails** — the tactic errors out after 147s where `native_decide`
> succeeds in 73s. Do not open a private counterpart to this phase on the strength of these
> public numbers.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.**
> 1. **Bootstrap reads:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` →
>    `docs/WAVE_EXECUTION_PIPELINE.md` → ADR-002 (the ratchet) →
>    `docs/assessments/UpstreamDisposition_Revalidation_2026-07-29.md` §4 (the spike data).
> 2. **Measure before converting.** A conversion that triples the build for one axiom is a bad
>    trade; the phase's job is to find where the trade is good.
> 3. Kernel-purity, zero sorry, no new axioms (#15), no `maxHeartbeats` (#10).

**Standing invariants:** statements byte-identical; no `maxHeartbeats`; never push.

---

## Wave 1 — Economics: measure the whole-build cost

**Goal.** Convert the two small clusters (`lattice_signature` 12, `other` 53) and measure the
*full-build* delta, not per-module elapsed.

**Done (AC).**
- [ ] Baseline: `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`, wall clock recorded.
- [ ] Same after conversion. **If the full build regresses more than ~10%, stop and report** —
      the phase is not worth it at that price and should close with the finding.
- [ ] `docs/counts.json` `native_decide_decl_closure` drops by the converted count; ADR-002
      ratchet updated to the new floor.
- [ ] Spot-check `#print axioms` on three converted declarations: the generated
      `native_decide.ax_*` axioms are **gone**, closure is `{propext, Classical.choice, Quot.sound}`.

## Wave 2 — `number_field_qgroup` (154), gated on Wave 1

**Goal.** The cyclotomic cluster, where QCyc40's 7× says the cost may bite.

**Done (AC).** Per-module go/no-go on measured cost; modules that do not convert at default
heartbeats are **left alone and listed**, not forced.

## Wave 3 — decide whether `anyon_mtc` (327) is worth a `6GB`

**Goal.** A recommendation, not a conversion. The largest cluster; `KacWaltonFusion`'s 58 sites
converting at +0.3s is encouraging, `FibonacciMTC`'s 3.2× is not.

---

## Open UNKNOWNs

- **UNKNOWN-1:** does `decide +kernel` on a `Decidable` instance over `QCyc5Ext`/`QCyc40` produce a
  kernel-reduction blow-up that only shows at scale? QCyc40's 7× is one data point.
- **UNKNOWN-2:** whether the ADR-002 ratchet should track *converted* separately from *removed*,
  so a conversion is visibly different from deleting a theorem.
- **UNKNOWN-3:** the 53 `other`-cluster sites are uncharacterized — enumerate at Wave 1 before
  assuming they behave like the named clusters.
