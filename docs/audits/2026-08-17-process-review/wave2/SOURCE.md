# Wave 2 — Cluster SOURCE — verified findings

Window: t0 = 2026-08-15 09:46 CDT → HEAD `4c81c2ec`. Loaded plugin cache = `f33dc0a1`
(commit `f33dc0a1b2e5`); `fd6cac3d`, `e9e5e314`, `c4b1a1ca`, `f58a3fe4` were never loaded —
checked below and none touches this cluster's mechanism.

---

### SOURCE-1 — a CrossRef `.json` metadata stub is silently counted as full-text held, same defect class ADR-014 D1 already fixed for `.abstract.txt`

- **Wave-1 source IDs:** B-03, B-06, C-08, G-09
- **Verdict:** RE-DIAGNOSED
- **Evidence at HEAD:**
  `scripts/validation/checks/citations.py:565` — `EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]`.
  The existence loop (`:648-668`) breaks on the **first** matching extension and only
  down-grades fidelity when `ext == "abstract.txt"` (`:660-667`); a `.json` hit is appended
  straight to `cached` with no fidelity flag, indistinguishable from a `.pdf`/`.tex`.

  Sampled every `.json` cache file on disk:
  ```
  find Lit-Search -path "*/primary-sources/*.json" | wc -l   → 111
  ```
  Of the 111, 89 carry no `abstract` field at all (bare CrossRef bibliographic record —
  title/authors/DOI/reference list, no prose) and the remaining 22 carry only an `abstract`
  field (same fidelity as an `.abstract.txt`, just wrapped in JSON). **0 of 111 contain
  full-text body content.** Confirmed by hand for the two keys wave-1 named:
  `Lit-Search/Phase-1-and-Background/primary-sources/GellMannOakesRenner1968.json` and
  `Lit-Search/Phase-6d/primary-sources/GMOR1968.json` are both bare Crossref records
  (`"source": "Crossref"`, no `abstract` key).

  `docs/SOURCE_ACQUISITION_REGISTER.md` (the ADR-014-derived register) independently
  lists `GellMannOakesRenner1968` as "not held in full text" (P2, line 54) — but only
  because its registry `primary_source_path` field happens to be `None`; the register's
  `_holding()` (`scripts/source_acquisition_register.py:56-62`) never globs the disk the
  way the validate-gate check does, so the two mechanisms agree here by accident, not by
  a shared fix. A bibkey with a **declared** `primary_source_path` ending `.json` (e.g.
  `ChristensenDuff1979`, `Vergeles2025` are `.abstract.txt`/`.pdf` so unaffected, but
  `GMOR1968`'s declared path *is* `.json`) reads "full" through `_holding()` too.

  Live check output confirms the summary line hides the split:
  ```
  uv run python scripts/validate.py --check citation_primary_sources_present
  → 516 bibkeys cited across 64 papers — 357 cached (298 full text, 59 ABSTRACT ONLY) / …
  ```
  "298 full text" is not decomposed by extension; the run never reports how many of those
  298 are `.json`.

- **Population (measured this session):**
  ```
  Total CITATION_REGISTRY entries:                              664
  → cache resolves to pdf/tex (genuine full text):               349
  → cache resolves to .json (CrossRef stub, counted as "full"):   82   ← the defect population
  → cache resolves to .abstract.txt (correctly flagged):          68
  → no cache file at all:                                        165
  ```
  Of the 82 json-stub entries, **45 are cited in a submission bundle right now** (15 of the
  21 bundles: D1 D2 D3 D4 D5 D6 D8 D9 E1 E2 F I1 L1 L2 L3), e.g. `GellMannOakesRenner1968`
  (D3), `ChristensenDuff1978` (F), `Israel1986` (F, L3), `Hawking1971/1972/1975` (D3, F),
  `Weinberg1989` (D3, F), `Witten1989` (D4, F). The mechanical "load-bearing" floor signal
  (named in `formulas.py` or `PARAMETER_PROVENANCE`) fires on **0** of the 45 — matching
  ADR-014's own documented blind spot (a source supplying a closed form/theorem/convention,
  not a registered numeral, is invisible to that floor); `GellMannOakesRenner1968` supplies
  exactly such a convention (the GMOR relation) in `papers/D3/paper_draft.tex:2294`.
  Commands run: the Python census above (`src.core.citations.CITATION_REGISTRY` +
  `bibkey_phase` + disk glob, replicating the check's own extension-priority logic) and a
  `\cite{}`-regex scan of the 21 `papers/*/paper_draft.tex` with TeX comments stripped
  (same method as `scripts/source_acquisition_register.py::_bundle_usage`).

- **Already-addressed by:** partially. `0347d0db` (2026-08-15 09:53, in-window) added the
  `.abstract.txt` fidelity flag (ADR-014 D1) and `9cd6dd72` (12:36, in-window) added the
  `citation_class` exemption discipline (ADR-014 D7) — both real, both live at HEAD, neither
  touches `.json`. None of the four unloaded plugin commits (`fd6cac3d`, `e9e5e314`,
  `c4b1a1ca`, `f58a3fe4`) touch `citations.py`, `source_acquisition_register.py`, or any
  fidelity logic (checked their diffs directly). **The `.json` half of the defect is live
  and unaddressed at HEAD.**

  The *specific bibkeys* wave-1 named split three ways: `ChristensenDuff1978`,
  `HughesDrever1960`, `Israel1986` were removed from **D3** by the redraft commit
  `dc8ad349` (2026-08-15 15:11, in-window; D3 now cites only `Vassilevich2003` for its
  heat-kernel claims) — but `ChristensenDuff1978` and `Israel1986` are still live citations
  in **F**, unfixed. `GMOR1968` (exact key) is not cited by any submission bundle (only
  legacy `paper37`); its twin `GellMannOakesRenner1968` is still live in D3. `Witten2016`
  and `TachikawaYonekura2018` (B-06) were never committed as `\cite{}`/`\bibitem` anywhere
  in D2's history (`git log -p` on `papers/D2/paper_draft.tex` shows zero occurrences) —
  the drafter's stated workaround ("I wrote around both … so the text compiles as-is")
  held; this specific instance never reached the tree and is **KILLED as originally framed**.

- **Mechanism:** `check_citation_primary_sources_present`'s extension list treats "a file
  exists with this name" as a proxy for "we hold the source." ADR-014 D1 corrected that
  proxy for one extension (`.abstract.txt`) after `Mather1982` demonstrated the cost; the
  same proxy failure is still live for `.json`, which in this corpus is populated
  exclusively by CrossRef API dumps (bibliographic metadata, occasionally an abstract) —
  never a retrieved text. The check's own summary line ("cached … full text") actively
  misreports these 82 entries' fidelity to anyone who reads it.
- **Recurs on the next bundle?** YES — every new `\cite{}` of one of the other 37
  json-stub-only entries not yet cited in a bundle (or any newly-fetched CrossRef record
  saved as `.json`) reproduces the same silent miscount; the check gives no signal to catch
  it, and the derived acquisition register only avoids the bug by coincidence (reading the
  registry field rather than the disk) rather than by a shared fix.

---

### SOURCE-2 — none of the three automated review agents re-reads a primary source to check whether a Lean theorem's content matches it; only a primary-source re-read (done by the drafting lead, not by a review agent) catches that class of error

- **Wave-1 source IDs:** G-01, H-09, H-04, G-06
- **Verdict:** CONFIRMED (mechanism) — the two concrete instances named are ALREADY-ADDRESSED at HEAD; the review-agent gap that let them through is not.
- **Evidence at HEAD (what each agent actually checks):**
  - `adversarial-reviewer.md` Class 1 (`:179-202`) fetches arXiv/DOI **metadata** (title,
    authors, venue) and compares it to the `\bibitem` text — bibliographic correctness, not
    mathematical content. Class 2 (`:204-218`) re-reads a primary source only for a value
    already registered in `PARAMETER_PROVENANCE` with a named table/figure/equation — a
    Lean theorem's internal coefficients (e.g. a heat-kernel `a₂`/`a₄` rational) are not
    `PARAMETER_PROVENANCE` entries and fall outside this class. Class 3 (`:220-253`)
    inspects proof *structure* (tautology/placeholder patterns) and statement-vs-docstring
    overclaim, never a coefficient's numeric correctness against literature.
  - `claims-reviewer.md`'s six finding classes (IA/TP/SD/TN/HD/PC, `:219-365`) are all
    **internal**-consistency checks: prose number vs. `grep`/`lean_deps.json`/
    `formulas.py`/`constants.py`. None fetches or reads an external primary source. Its own
    "recomputation" (Part B, `:206`) explicitly means recomputing via the project's own
    Python, not comparing to the cited paper.
  - `prose-reviewer.md` (`:127-130`) explicitly declines: "Judge the prose, not the
    physics… Whether a claim is *true* belongs to `claims-reviewer` and
    `adversarial-reviewer`." It also holds no `Bash`/`WebFetch` tool at all (`tools:
    ["Read","Glob","Grep"]`, line 19).

- **Concrete instance 1 — Dirac heat-kernel `a₂`/`a₄` (D3, H-09).**
  `papers/paper39_heat_kernel_expansion/claims_review.json` (claims-reviewer run,
  2026-04-27) summary: *"All numerical anchors (GUT 1/G_N = 3.98e31, M_P^2 = 1.49e38,
  **a4 rationals**, GB combo -1/48) verified to <0.1% via **Python heat_kernel module**."*
  — the check compared the Lean/paper values against the project's own `formulas.py`
  implementation of the same (wrong) values, which is why it PASSED; it never touched
  Vassilevich. `papers/AutomatedReviews/2026-04-28-0158-…/paper39_heat_kernel_expansion.md`
  (adversarial-reviewer re-invocation) closes its only heat-kernel-adjacent BLOCKERs on
  citation-registry membership (`Gilkey1995`, `LinearizedEFE2026` present in
  `CITATION_REGISTRY`) — again never the coefficient values. The error (`a₂` missing the
  spinor trace ×4; `a₄` triple `(-5,+7,-12)` vs. published `(+30,-48,-42)`, two of three
  signs flipped) was found only in
  `papers/AutomatedReviews/2026-08-15-d3-stage10-redraft/D3.md` §0.1–0.2, by the drafting
  lead reading `Lit-Search/Phase-6e/primary-sources/Vassilevich2003.pdf` directly (stated
  "reviewer: lead", "kind: stage10-redraft" — not a run of any of the three named agents).
  **Already fixed at HEAD**: `be81b983` (2026-08-15 15:55, in-window, "Give the Dirac heat
  kernel its index trace: a_2, a_4 and everything downstream").
- **Concrete instance 2 — KZM exponent mislabel (D7, H-04/H-10).** No D7 Stage-13 review
  document (`2026-0[4-8]*-bundle-stage13/D7.md`, `papers/D7/claims_review.json`) mentions
  KZM/Kibble-Zurek/freeze-out/defect-density at all — the claim was never checked by the
  pipeline, only asserted. Found in
  `papers/AutomatedReviews/2026-08-17-d7-stage10-redraft/D7.md` D7-01, again by the lead
  reading `Lit-Search/Phase-6w/primary-sources/TindallMelloFishmanStoudenmireSels2026Science392.pdf`
  at page level, not by an agent invocation. **Already fixed at HEAD**: verified live —
  `lean/lean_deps.json` now carries all four distinct exponent declarations
  (`kzmFreezeOutTimeExponent`, `kzmFreezeOutLengthExponent`, `kzmDefectDensityExponent`,
  `kzmCorrelationCollapseExponent`) the finding's own `Verify` command demands, landed by
  `ea4c92ea` / `27e1c991` / `4e1935d8` (2026-08-17 03:03–03:19, in-window, minutes before
  HEAD `4c81c2ec` at 03:58).
- **Already-addressed by:** the two *named instances* — yes, `be81b983` and
  `ea4c92ea`/`27e1c991`/`4e1935d8`, both in-window. The *mechanism* (no review agent's
  instructions require re-deriving a cited theorem's content from its primary source
  unless the value happens to be a registered `PARAMETER_PROVENANCE` numeral) — no. None
  of the four unloaded plugin commits touch any of the three agent definition files
  (checked their diffs directly).
- **Mechanism:** the three review agents verify **internal** consistency (prose ↔ Lean ↔
  `formulas.py`/`constants.py` ↔ citation registry membership) and **citation metadata**
  correctness. None verifies that a Lean theorem's *mathematical content* reproduces what
  its cited primary source actually states, except for the narrow slice already captured
  as a `PARAMETER_PROVENANCE` numeral. A wrong coefficient that is wrong consistently across
  Lean, Python and prose is invisible to every check that only compares those three against
  each other — which is exactly the shape of both instances above.
- **Recurs on the next bundle?** YES — the agent definitions are unchanged; the fix each
  time was ad hoc (a lead reading a PDF during a redraft), not a standing instruction or
  gate. Any future Lean theorem encoding a literature coefficient outside
  `PARAMETER_PROVENANCE` carries the same blind spot.

---

### SOURCE-3 — `apex_theorems[*].claims` is free prose whose semantic content vs. the theorem's type is verified by no gate; a shallow gate now exists but only for three narrow, non-semantic properties, and it is currently RED

- **Wave-1 source IDs:** D-03, G-07, C-01
- **Verdict:** RE-DIAGNOSED (partially addressed, and the addressed part is failing)
- **Evidence at HEAD:** `scripts/validation/checks/bundles_readiness.py:3421`
  `check_apex_theorem_claims_grounded`, added in-window (`d8c3b858`, 2026-08-15 13:00,
  "Three gates the redraft campaign needs…"; extended by `5b844f53`, 16:08). Its own
  docstring (`:3437-3457`) states the scope precisely: it checks three DECIDABLE
  properties — claim present/non-placeholder, claim not a bare restatement of the
  theorem's name, and claim numerals appear somewhere in the theorem's (one-hop) type
  closure — and explicitly disclaims semantic verification: *"Claim-to-type equivalence is
  not decidable, and this check does not approximate it… The exact L3 §2.3 defect that
  motivated this check would NOT be caught by it."*

  Live run:
  ```
  uv run python scripts/validate.py --check apex_theorem_claims_grounded
  → 636 declared apex claim(s) scored (floor 634) — 0 placeholder, 0 name-restatement
    (both gating, both zero), 33 with a numeral absent from the statement (ceiling 31)
  → Overall: 0/1 checks passed  [RED at HEAD]
  ```
  Command run in this session: the check above, against `bundle_registry.BUNDLE_CODES`
  (21 codes: F, D1–D12, L1–L3, I1–I3, E1, E2) × each bundle's
  `bundle_metadata.json::apex_theorems`.

- **Population (re-derived, not quoted from wave 1):**
  ```
  apex_theorems[*].claims entries across the 21 submission bundles: 636
  ```
  Every one of the 636 is, by construction of the field (a human-authored sentence naming
  what a specific Lean theorem "establishes" — `bundle_metadata.json` schema, e.g.
  `papers/D3/bundle_metadata.json`), a prose assertion of a physics/math result. Of the
  636:
  - 0 fail the presence/non-placeholder leg (hard gate, zero by design)
  - 0 fail the name-restatement leg (hard gate, zero by design)
  - **33 fail the numeral-grounding leg** — currently over the frozen ceiling of 31,
    i.e. the gate itself is red right now
  - **all 636** have their claim-to-theorem-type semantic correctness verified by
    **no** check, no test, and — per the same docstring — would not have caught the one
    confirmed live instance (`papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md`
    §2.3: `falsifier_alpha_ADW_dependence`'s metadata claim describes a δ_ADW dependence;
    the theorem is `1 < α_ADW → 0 < (α_ADW - 1) * Λ_UV`, mentioning neither the bundle nor
    δ) even were it re-run today, because that claim carries no numeral and is not a bare
    name-restatement.

  Figure captions: no dedicated check exists either (`scripts/validation/checks/
  papers_prose.py:247` only *excludes* `\caption{}` blocks from the em-dash/prose-pattern
  scan; it never compares caption text to the referenced PNG/figure content) — consistent
  with G-07's E1/E2 evidence and un-gated exactly as wave-1 found it.

- **Already-addressed by:** `d8c3b858`/`5b844f53` (both in-window) shipped a real gate
  covering three narrow properties of the `claims` string — this is genuine, new
  infrastructure, not a no-op. It does **not** address the semantic-mismatch defect D-03/
  G-07/C-01 actually describe (a claim asserting content the theorem's type does not
  carry), which the check's own docstring says by name it cannot catch. None of the four
  unloaded plugin commits touch `bundles_readiness.py` or any bundle-metadata check.
- **Mechanism:** `apex_theorems[*].claims` is authored prose with no structural link to
  the theorem's elaborated type; the new gate mechanically screens for the cheapest three
  failure shapes (empty, name-echo, numeral-absent) but "claim describes what the theorem
  actually proves" has no decidable proxy and is asserted nowhere to be checked by anything
  else in the pipeline (`claims-reviewer`'s HD class checks *hypothesis disclosure*, not
  claim-to-type equivalence; `vacuous_statement_audit` checks the theorem's own
  substantiveness, not whether the *claims* field matches it).
- **Recurs on the next bundle?** YES — every apex theorem declared with a claim that
  contains no numeral (a large fraction: qualitative/existential physics statements, e.g.
  "gauge erasure holds," "the vestigial phase requires no condensate") passes the live gate
  by construction while remaining completely unverified against the theorem's actual
  content.

---

## Compact table

| ID | Verdict | Population | Recurs |
|---|---|---|---|
| SOURCE-1 | RE-DIAGNOSED | 82/664 registry entries cache to a bare CrossRef `.json` counted as full text (0/111 sampled `.json` caches hold body text); 45 of the 82 cited live across 15/21 bundles; specific B-06 keys (Witten2016, TachikawaYonekura2018) never reached the tree — KILLED for that instance | YES |
| SOURCE-2 | CONFIRMED (mechanism); named instances ALREADY-ADDRESSED | 3/3 review agents lack primary-source content verification outside registered `PARAMETER_PROVENANCE` numerals; both named defects (D3 a₂/a₄, D7 KZM exponent) fixed in-window (`be81b983`; `ea4c92ea`/`27e1c991`/`4e1935d8`) by a lead's direct PDF read, not by a review agent | YES |
| SOURCE-3 | RE-DIAGNOSED (partially addressed; new gate currently RED) | 636 apex `claims` entries across 21 bundles, all semantically unverified against theorem type by any gate; new 3-leg gate (`apex_theorem_claims_grounded`, shipped in-window) covers only presence/non-restatement/numeral-presence and is itself failing (33 > ceiling 31); figure captions remain wholly unguarded | YES |
