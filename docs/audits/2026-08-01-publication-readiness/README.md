# Publication-Readiness Audit — 2026-08-01

**Status:** assessment COMPLETE — all 13 auditors reported. See [`SYNTHESIS.md`](SYNTHESIS.md).
**Scope:** all 21 publication bundles in `papers/` (F; D1–D12; L1–L3; I1–I3; E1, E2), plus the
strategy and process layer that produces them.

**Headline:** no bundle is submittable; best grade C−; **80 P0 findings**. The systemic cause is that
the project's quality instrumentation reports *absence of measurement* as success — five separate
mechanisms confirmed reporting clean while measuring nothing. Six operator decisions are pending in
`SYNTHESIS.md` §5.

---

## Why this audit exists

The project has strong machinery for **claim correctness** — Stage-13 adversarial review, the
claims-reviewer sentence walker, `bundle_readiness.py`, the gate × bundle heatmap. That
machinery asks *"is each sentence backed?"* and answers it well.

It does not ask *"is this a publishable manuscript?"* The operator's report is that the drafts
are far below production quality along exactly the axes the gates do not measure:

- **length** — deep papers running 2–8k words against 30–50 pp targets; the flagship at ~13.6k
  words against an 80–150 pp target
- **coherence** — disjointed structure and duplicated content across bundles
- **voice** — prose that in places has degraded from an article addressed to a reader into a
  discussion with an adversarial review agent

A corpus can pass every claim-level gate and still be unpublishable. That is the hypothesis this
audit tests, and the reason its findings are recorded separately from the existing review stream
rather than folded into it.

## Method

Thirteen independent auditors, dispatched in parallel from a single shared rubric
([`RUBRIC.md`](RUBRIC.md)), each in a fresh context:

- **Ten bundle auditors**, grouped by thematic family so that intra-family duplication and
  splash/deep discipline fall inside one auditor's view.
- **Three cross-cutting auditors** — portfolio coherence and duplication; mechanical build
  integrity; absorbability and strategy-vs-reality drift.

Standing instructions to every auditor: establish ground truth yourself (compile the LaTeX, read
the page count off the PDF, grep the Lean tree); treat prior review findings, `bundle_metadata.json`
statuses and the readiness heatmap as claims to be checked rather than conclusions to inherit;
quote evidence with file and line; assess only — change nothing.

That last constraint is deliberate. Remediation is planned from the complete picture, once, rather
than bundle by bundle as findings arrive.

## Layout

```
2026-08-01-publication-readiness/
├── README.md                                  ← this file
├── RUBRIC.md                                  ← shared rubric: axes, severity scale, output contract
├── SYNTHESIS.md                               ← portfolio verdict + remediation plan (written last)
├── CROSS-portfolio-coherence.md               ← duplication map, boundary integrity, roster recommendation
├── CROSS-build-integrity.md                   ← compile/page-count/citation/metadata master table
├── CROSS-absorbability-and-strategy-drift.md  ← drift ledger, phase→bundle routing, process fixes
└── bundles/
    ├── F.md              ← Tier 0 flagship
    ├── D1-E1-E2.md       ← analog-Hawking family (deep + two experimental letters)
    ├── D2-L2.md          ← anomaly / generations (deep + splash)
    ├── D3-L1-L3.md       ← emergent gravity (deep + two splashes; L1 ships first)
    ├── D4-D8.md          ← topological QC / gate compilation siblings
    ├── D5.md             ← dark sector
    ├── D6-D7.md          ← fault tolerance / simulability
    ├── D9-D12.md         ← device & detector certification stack
    ├── D10-D11.md        ← comp-chem & band-theory substrate breadth
    └── I1-I2-I3.md       ← infrastructure papers
```

## Severity scale

`P0` submission-blocking (desk-reject class) · `P1` referee-fatal · `P2` major-revision quality ·
`P3` polish. Every P0/P1 carries a required end state and a remediation size class
(`trivial` / `small` / `medium` / `large` / `new-work`).

The size class is the load-bearing field: it is what separates an editing task from work that has
not been done yet, and the remediation plan is built from it.

## What happens with the results

1. **Synthesis** — `SYNTHESIS.md`: portfolio verdict, the P0 register, and a sequenced
   remediation plan ordered by publication value rather than by bundle number.
2. **Strategy revision** — `docs/PAPER_STRATEGY.md` and `docs/PAPER_DRAFT_MAPPING.md` rewritten
   against the drift ledger, including the roster question (is 21 the right number?).
3. **Remediation** — executed against the P0/P1 register.
4. **Process repair** — new manuscript-level gates in `scripts/bundle_readiness.py` /
   `validate.py`, and the `BUNDLE_LIFT_PROCEDURE` / `LATE_PHASE6_ABSORPTION_PROTOCOL` changes
   needed so future waves absorb cleanly instead of accreting.

Steps 2–4 do not begin until step 1 is complete.
