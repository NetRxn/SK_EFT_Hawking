# ADR-014 — Source acquisition and citation fidelity: holding a cache is not holding the source

- **Status:** **ACCEPTED (2026-08-15); IMPLEMENTATION IN PROGRESS.** Decisions 1–3 shipped
  (register + overlay + egress whitelist); Decision 4 (fidelity dimension on
  `citation_primary_sources_present`) and Decision 5 (D12 prose repair, blocked on acquisition)
  outstanding.
- **Deciders:** John Roehm (project owner); investigation + draft by Claude (Opus 5).
- **Context source:** direct reads at HEAD of `src/core/citations.py`,
  `scripts/validation/checks/citations.py::check_citation_primary_sources_present`,
  `.claude/plugins/skeft-qa/scripts/harness_web_egress_guard.py`,
  `papers/D12/paper_draft.tex:395-500`, and
  `Lit-Search/Phase-6e/primary-sources/Mather1982.abstract.txt`.
- **Related:** [ADR-004](ADR-004-substrate-integrity-gates.md) (the shift-left structural-prevention
  pattern this ADR reuses); [ADR-011](ADR-011-manuscript-quality-layer.md) (F-05 scar-tissue
  prohibition — the *prose* half of the same defect, amended separately);
  [ADR-012](ADR-012-finding-lifecycle-routing-and-closure.md) (routing: this ADR's gate FLAGS,
  it does not block); `CLAUDE.md` § *Research ladder & web-egress security*.

---

## Context

### The measured defect

`check_citation_primary_sources_present` verifies that a cited bibkey has an artifact on disk
under `Lit-Search/Phase-*/primary-sources/`. Its accepted extensions are:

```python
EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]
```

**An `abstract.txt` satisfies it.** So a source we hold only as a publisher abstract is
indistinguishable, to every consumer of this check, from one we hold in full text. The check
asserts *a file exists*, which is a proxy for *we hold the source*, and the two come apart.

That is not hypothetical. `Mather1982` is held as a 5,975-byte abstract. Its cache file ends
with the line **"we hold this source in ABSTRACT ONLY -- the body has not been read"**, and
`PARAMETER_PROVENANCE['MATHER_1982_GRADIENT_REDUCTION']` records a convention ambiguity —
whether the source's "as much as 30 %" is a PSD or an amplitude reduction, a 21.5-point
difference at D12's worked point — as though the ambiguity were a property of the source.
It is not. It is a property of **not having read the source**. The body would settle it; the
abstract cannot. The check was green throughout.

### Why the prose route is not the repair

D12 resolved this in the manuscript, disclosing at four sites that it cites what it has not
read (`:405-406`, `:474-475`, `:498`). Measured corpus-wide 2026-08-15: **64 drafts scanned,
6 such lines, all in D12** — contained, not a habit.

That disclosure is a submission non-starter. But **deleting it while keeping the citation is
strictly worse**: it converts a visible gap into an invisible one, and is the narrow-and-
reclassify move rather than a repair. `:474-475` attributes D12's closed form to
`IrwinHilton2005`; removing the hedge leaves a bare unsupported attribution.

The repair is **acquisition**. Acquisition costs money, against a limited budget. So the gap
must be measured and ranked, not narrated — and the egress guard must actually permit the
domains where the sources live.

### Why ranking is the whole problem

Measured at HEAD 2026-08-15:

| population | count |
|---|---:|
| `CITATION_REGISTRY` entries | 664 |
| not held in full text | 294 |
| …of those, cited in the 21 submission bundles | 198 |
| …of those, load-bearing | 6 |
| …of those, not reachable by a free route | 1 |

An unranked list of 198 is indistinguishable from a demand to buy 198 papers. Ranked, the
spend is at most one or two, and three of the six load-bearing gaps (`PDG2024`, `Sen2013`,
`BB84`) are open access — they were fetch tasks sitting in a budget list.

---

## Decision

### 1. Fidelity is a first-class property of a held source, and `abstract` is not `full`

`full` (pdf/tex/json body) · `abstract` (publisher abstract only) · `none` · `missing`
(path recorded, file absent). No consumer may treat `abstract` as evidence of the source's
contents. A claim resting on an `abstract`-fidelity source is **unbacked**, and a provenance
record that describes a source's ambiguity from its abstract is recording its own ignorance.

### 2. The acquisition register is derived, never hand-maintained

`scripts/source_acquisition_register.py` → `docs/SOURCE_ACQUISITION_REGISTER.md`, measured at
HEAD every run, `--check` exiting 1 on drift so a stale register fails rather than misleads.
Scope is the **21 submission bundles**; legacy `paperNN` drafts are excluded because they are
not the submission surface and a gap there is not a budget item.

### 3. The load-bearing signal is a FLOOR, and the register says so in its own output

The automated signal fires when a source supplies a registered `PARAMETER_PROVENANCE` value or
is named in `formulas.py`. A source supplying a **closed form, theorem or convention** is
invisible to it. `IrwinHilton2005` is the measured proof: it is the attributed source of D12's
gradient-factor closed form and neither signal fires.

Curated verdicts therefore live in `docs/source_acquisition_overlay.json` and override in
**both** directions — promoting what the signal cannot see, demoting textbooks it would never
have flagged. A P1/P2 row reads *"not detected as load-bearing"*, never *"confirmed
decorative"*. **Two standing rules:**

- **A free route is never a budget item.** Lumping `PDG2024`/`Sen2013`/`BB84` into a spend
  total would have overstated the cost six-fold.
- **An unchecked paywall is a guess, not a cost.** `route: paywalled` is honest only once
  `route_note` records which free routes were actually tried. Unassessed routes are surfaced
  separately so a provisional label cannot masquerade as a priced one.

### 4. The gate FLAGS; it does not block

Per ADR-012 routing and the operator's 2026-08-15 direction: a paper relying on an unread
load-bearing source surfaces as a **dashboard flag**, not a blocked P1 gate. Blocking the
pipeline on a condition only acquisition can clear stalls every downstream stage — including
the adversarial review that would find the *next* such defect.

This is implemented by **extending `citation_primary_sources_present` with the fidelity
dimension**, not by adding a sibling check. Rule 1 of the architecture rules: the recurring
failure is a second mechanism beside one that already exists.

### 5. Human endorsement is terminal

Human sign-off is the **last** step, after the full pipeline including adversarial review —
never a mid-pipeline blocker. Routing an unfinished research question to the operator as a
sign-off decision is a defect in the routing, not a request for judgement. Recorded here
because `MATHER_1982_GRADIENT_REDUCTION` and `GW.CHI_VEST_NATURAL_LOWER/_UPPER` reached the
operator that way on 2026-08-15; the gate semantics themselves are amended in ADR-012.

### 6. Egress whitelist additions, scoped to the measured acquisition targets

The `PreToolUse(WebSearch|WebFetch)` guard's `_WHITELIST` is the **real** whitelist;
`research-scout.md` deliberately carries none, and `.claude/settings.local.json` names a
strict subset. Added for the P0 targets, each with its target named:

| domain | for |
|---|---|
| `adsabs.harvard.edu` | NASA ADS scanned full text — `Mather1982` |
| `ntrs.nasa.gov` | NASA Technical Reports Server — `Mather1982` |
| `nvlpubs.nist.gov` | NIST public-access publications — `IrwinHilton2005` (NIST authors) |
| `link.springer.com` | JHEP + Springer chapters — `Sen2013`, `IrwinHilton2005` |
| `opg.optica.org` | Optica — `Mather1982` landing/metadata |
| `sciencedirect.com` | TCS 560 open republication — `BB84` |

`nature.com` (`Zhao2023`) and `arxiv.org`/`pdg.lbl.gov` were already whitelisted.

---

## Consequences

- Acquiring a source is a **fetch task with a named free route first**, and the register makes
  the free/paid split structural rather than a judgement call at spend time.
- D12's four disclosure sites remain until acquisition lands. They are the honest state; the
  ADR-011 amendment covers the *prose* rule, and this ADR covers why deleting them early is a
  regression rather than a fix.
- The `abstract`-counts-as-present hole existed for the life of the check. Every prior green
  run of `citation_primary_sources_present` should be read as "a file was present", not "the
  source was held".

## Alternatives considered

**Add a new check beside the existing one.** Rejected — architecture rule 1. The existing
check already walks exactly the right population; it was measuring the wrong property of it.

**Block on unread load-bearing sources.** Rejected by operator decision 2026-08-15. A blocking
gate on a condition only money can clear stalls the pipeline behind a purchase queue.

**Drop the citations we cannot afford.** Rejected — a citation is dropped because the claim
does not need it, established by reading, never because the source was expensive. That is the
walk-back pattern, and the register's P1/P2 tiers exist to make the "does the claim need it"
question answerable rather than to license removal.
