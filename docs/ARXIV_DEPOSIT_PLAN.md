# arXiv Deposit Plan — Sequencing, Endorsements, Conversion

**Authority:** user decisions 2026-06-10. Records the deposit sequencing for
the 17 publication bundles (`docs/PAPER_STRATEGY.md` architecture). Companion
documents: `docs/DISCLOSURE_TEXT.md` (disclosure must be installed per bundle
**before** deposit), `docs/roadmaps/AttributionContentSweep_Roadmap.md` (the
sweep whose completion is this plan's trigger),
`scripts/convert_inprep_citations.py` (Step-3 tooling).

**User decisions encoded (2026-06-10, verbatim intent):**
- No arXiv endorsement is currently held — obtaining endorsement(s) leads the
  plan (Step 0).
- No bundles are held back from the coordinated batch (Step 2) — except F,
  which deposits last by design, and D6/D7 which join iff their lifts complete
  by the trigger date.
- The in-prep → arXiv conversion script is authorized, "as long as it's
  documented" (it is: `scripts/convert_inprep_citations.py` module docstring
  documents the design choice and modes; tests at
  `tests/test_convert_inprep_citations.py`).

---

## Trigger

**Completion of the attribution-content sweep** — every bundle GREEN under
the recorded-review semantics (post-2026-06-10 fresh-context Stage-13 review
recorded in `bundle_metadata.json`; heatmap GREEN per commit `3e0e8252`
semantics), per the sweep roadmap's exit criteria. The sweep also installs the
standard disclosure block per bundle (`docs/DISCLOSURE_TEXT.md` §3), so by
trigger time every bundle carries its correct disclosure variant.

---

## Step 0 — obtain arXiv endorsement(s) BEFORE anything

None currently held. arXiv endorsement is **per subject category** (an
endorsement for gr-qc does not cover quant-ph, etc.; repeat submissions to an
already-endorsed category need no new endorsement). The portfolio spans at
least gr-qc / hep-th / hep-ph / quant-ph / physics.comp-ph / cond-mat /
math.PR, so multiple endorsements are needed — gather them in parallel during
the sweep, gr-qc first (it gates Step 1).

### Per-bundle primary categories (planning assignments)

Derived from each bundle's journal target (`docs/PAPER_STRATEGY.md` §2 +
`papers/<bundle>/bundle_metadata.json` `target_journal`) and topic; the
per-paper `\pacs{04.x...}` declarations in the gravity-sector source drafts
corroborate the gr-qc assignments. Confirm each primary at submission time;
cross-lists are advisory and (per current arXiv policy — verify at
submission) do not require separate endorsement.

| Bundle | Tier | Journal target | Primary category | Suggested cross-lists |
|---|---:|---|---|---|
| L1 | 2 | PRL | gr-qc | astro-ph.HE |
| L2 | 2 | PRL | hep-th | hep-ph |
| L3 | 2 | PRL | gr-qc | cond-mat.quant-gas |
| D1 | 1 | PRD | gr-qc | cond-mat.quant-gas |
| D2 | 1 | PRD/JHEP | hep-th | hep-ph |
| D3 | 1 | PRD | gr-qc | hep-th |
| D4 | 1 | CMP / PRX Quantum | quant-ph | math.QA, cond-mat.str-el |
| D5 | 1 | PRD | hep-ph | astro-ph.CO, gr-qc |
| D6 | 1 | PRD/JHEP | quant-ph | cs.IT |
| D7 | 1 | PRX Quantum / PRX | quant-ph | cond-mat.str-el |
| D8 | 1 | PRX Quantum / Quantum | quant-ph | cs.ET |
| I1 | 3 | CPC / Phys. Rep. | physics.comp-ph | cs.LO |
| I2 | 3 | JOSS | physics.comp-ph | cs.SE, cs.LO |
| I3 | 3 | JOSS / CPC | math.PR (alt: cs.LO) | cs.LO, math.PR |
| E1 | 4 | PRL/PRR | cond-mat.quant-gas | gr-qc |
| E2 | 4 | PRL/PRR | cond-mat.mes-hall | gr-qc |
| F  | 0 | Living Rev. Rel. / Phys. Rep. | gr-qc | hep-th, quant-ph, cond-mat.quant-gas |

### Endorsements needed (distinct primary categories)

1. **gr-qc** — L1, L3, D1, D3, F (5 bundles; gates Step 1 — obtain FIRST).
2. **hep-th** — L2, D2.
3. **hep-ph** — D5.
4. **quant-ph** — D4, D6, D7, D8.
5. **physics.comp-ph** — I1, I2.
6. **cond-mat.quant-gas** — E1.
7. **cond-mat.mes-hall** — E2.
8. **math.PR** — I3 (decision point: if math.PR endorsement proves hard to
   obtain, I3's primary falls back to cs.LO — cs categories use a different
   endorsement regime; decide at Step-2 prep).

Practical notes: (i) an endorser must be an active arXiv author in the
target category — candidate endorsers are the experimental groups already
engaged by the program (analog-gravity / polariton / graphene contacts) and
the Lean/Mathlib community for the infrastructure bundles; (ii) endorsement
requests are generated from the arXiv submission start page per category and
carry an endorsement code; (iii) gmail-only affiliation means auto-endorsement
will not apply — every category above needs an explicit endorser unless an
institutional affiliation lands first.

---

## Step 1 — L1 deposits first, alone

L1 (GW170817 vs vestigial-graviton, PRL, 4pp) is the endorsement/voucher
vehicle per `docs/PAPER_STRATEGY.md` ("the critical path is L1 → voucher →
everything else"; strongest stand-alone candidate: clean falsification at
LIGO precision, no dependence on sibling bundles). Sequence:

1. gr-qc endorsement obtained (Step 0).
2. L1 sweep visit complete (it is priority 1 in the sweep roadmap) +
   disclosure block installed (Variant A per the 2026-06-10 register run —
   see `docs/DISCLOSURE_TEXT.md` §2).
3. Deposit L1 to gr-qc (cross astro-ph.HE). Record the arXiv id.
4. L1's announcement establishes the submitting account's standing for the
   remaining deposits and provides the first real self-cite target.

---

## Step 2 — single coordinated batch: all remaining ready bundles EXCEPT F

**No holds (user decision 2026-06-10).** After L1 announces and the sweep
trigger is met, deposit in one coordinated batch:

- **In the batch:** D1, D2, D3, D4, D5, D8, L2, L3, I1, I2, I3, E1, E2.
- **D6 and D7 join iff their bundle-paper lifts are complete by the trigger
  date** (as of 2026-06-10, D6 stage-9 not started / stage-10 skeleton; D7
  stage-9 not started — both have GREEN content but incomplete lift gates;
  see `papers/D6/bundle_metadata.json`, `papers/D7/bundle_metadata.json`).
  If not complete, they deposit in a trailing mini-batch before Step 4.
- **Not in the batch:** F (Step 4, by design — it cites everything).

Batch mechanics: same announcement window where possible (arXiv announces
nightly Sun–Thu ET; submit the batch within one cycle so the cross-references
resolve in the same announcement); each bundle goes to its Step-0 primary
category; per-bundle disclosure variant per `docs/DISCLOSURE_TEXT.md` §2
must already be installed (sweep exit criterion).

---

## Step 3 — announcement-window conversion pass

When the batch's arXiv ids are assigned (at announcement), run the
documented one-pass conversion:

```bash
# 1. Build the mapping file from the assigned ids
#    {bibkey: {"arxiv": "YYMM.NNNNN"}} for every announced bundle/companion
# 2. Dry-run, inspect the full diff summary
uv run python scripts/convert_inprep_citations.py --map deposit_ids.json
# 3. Apply (registry + all draft bibitems + invariant-#11 cache stubs)
uv run python scripts/convert_inprep_citations.py --map deposit_ids.json --apply
# 4. Per-paper gate (repeat per deposited bundle)
uv run python scripts/convert_inprep_citations.py --check D1
# 5. Registry + cache invariants
uv run python scripts/validate.py --check citation_primary_sources_present
# 6. Recompile + replace the deposited versions (arXiv v2 where needed)
```

Inventory at plan-writing (2026-06-10): **32 `inprep: True` registry
entries** (a raw `grep 'inprep.*True'` shows 37 lines; 5 are
docstring/notes mentions, not entries). Of the 32: 30 have `\bibitem`s in
drafts; `Roehm2026Wave10` and `WaveDeepResearchSMG2024` have none
(registry-only; `WaveDeepResearchSMG2024` is a project-internal
deep-research synthesis marker expected to REMAIN inprep — do not map it).
Bundle self-cite keys (`Roehm2026D1` … `Roehm2026I2`, `Roehm2026F`) map to
the batch's assigned ids; numbered-wave keys (`Roehm2026Wave*`,
`LinearizedEFE2026`, `HigherCurvature2026`, `DiffInvariance2026`,
`FractonNonAbelian2025`) map to whichever deposited bundle absorbed that
content per `docs/PAPER_DRAFT_MAPPING.md` — build the mapping file
accordingly at conversion time.

Prose-level "in preparation" phrases (e.g. `papers/I1/paper_draft.tex`
narrative text) are NOT auto-rewritten — the `--check` gate flags them for
manual edit during the same pass.

---

## Step 4 — F deposits last, fully citable

After Step 3, every F bibliography self-cite resolves to a real arXiv id.
Gate before depositing F:

```bash
uv run python scripts/convert_inprep_citations.py --check F   # must PASS
```

plus F's LaTeX recompile and its sweep visit being the roadmap's last
(priority 5 — F inherits all sibling corrections). F then deposits to gr-qc
with the full cross-list set, citing the entire announced portfolio.

---

## Sequencing summary

```
sweep (all bundles GREEN, disclosure installed)     ← trigger
   │
Step 0  endorsements per category (gr-qc first)     ← leads everything
   │
Step 1  L1 alone → announce (voucher + first id)
   │
Step 2  batch: D1–D5, D8, L2, L3, I1–I3, E1, E2     (+D6/D7 iff lifts done)
   │
Step 3  convert_inprep_citations.py --apply + --check per paper
   │
Step 4  F last, fully citable (--check F gate)
```
