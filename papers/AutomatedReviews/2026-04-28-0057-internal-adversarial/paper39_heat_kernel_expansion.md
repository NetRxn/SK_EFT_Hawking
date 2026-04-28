---
paper: paper39_heat_kernel_expansion
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T00:57:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper39_heat_kernel_expansion

## Summary

Findings: **3 BLOCKER, 0 REQUIRED, 4 RECOMMENDED** (7 total). Gates affected:
**Gate 1 CitationIntegrity (2 BLOCKERs)**, **Gate 2 CrossPaperConsistency (1
BLOCKER, 1 RECOMMENDED)**, **Gate 6 AssumptionDisclosure (1 RECOMMENDED)**, Gate
1 (1 RECOMMENDED on `fetch_failed`), Gate 7 NarrativeGrounding (1 RECOMMENDED).
The paper is **NOT submission-ready**. The cited claim that the recent
hygiene-fix sweep added Vassilevich2003 + ChristensenDuff1979 to the registry is
correct, but the parallel hygiene-fix claim that all paper39 bibitems were
covered is **not** — `Gilkey1995` and `LinearizedEFE2026` remain registry
absences (the prior claims-reviewer flagged these as WARN; they are BLOCKERs
under the canonical Gate 1 criteria, "every bibkey in the .tex has a matching
CITATION_REGISTRY entry"). Stage-13 verdict: **blocked**. Lean module is clean
(0 sorry, 0 new axioms beyond kernel; 19/19 substantive theorems verified; load-
bearing `G_N_from_a2_eq_G_N_sakharov` does invoke
`LinearizedEFE.G_N_sakharov` by name as claimed; quantitative anchor 1/G_N =
3.98e31 GeV² verified < M_P² = 1.49e38 GeV² independently in Python; a4 GB
combination verified to 1e-15 against `-N_f/(48 (4π)²)`).

## Findings

### 1.1 — 🔴 BLOCKER — `Gilkey1995` bibkey absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:482-485`
  (bibitem); `src/core/citations.py` (registry — **absent**).
- **Observed:** `\bibitem{Gilkey1995}` is cited in §2 of the paper
  (line 140, `~\cite{Gilkey1995,Vassilevich2003}`) and listed in the
  bibliography. `grep -n "Gilkey" src/core/citations.py` returns no hits.
  The paper's own `claims_review.md:38` explicitly tracks this gap, marked WARN
  by the prior claims-reviewer (2026-04-28). The prompt asserts the recent
  hygiene-fix sweep added Vassilevich2003 + ChristensenDuff1979 + Stelle1977 +
  Lovelock1971 + CalmetCapozzielloPryer2019 + Berti2015 — this is verified in
  the registry — but Gilkey1995 was not included.
- **Evidence:**
  ```
  $ grep -nE "Gilkey" src/core/citations.py
  (no output)
  $ grep -nE "(Stelle1977|Lovelock1971|CalmetCapozzielloPryer2019|Berti2015)" src/core/citations.py
  2035:    'Stelle1977': {
  2051:    'Lovelock1971': {
  2067:    'CalmetCapozzielloPryer2019': {
  2084:    'Berti2015': {
  ```
- **Expected:** A `'Gilkey1995'` entry in `CITATION_REGISTRY` matching the
  bibitem (P. B. Gilkey, *Invariance Theory, the Heat Equation, and the
  Atiyah–Singer Index Theorem*, 2nd ed., CRC Press 1995). Gate 1 pass criterion:
  "Every bibkey in the .tex has a matching CITATION_REGISTRY entry" — this is
  unambiguous.
- **Fix:** Add Gilkey1995 to `CITATION_REGISTRY` with `authors`, `title`,
  `publisher = 'CRC Press'`, `edition = '2nd'`, `year`, `used_in =
  ['papers/paper39_heat_kernel_expansion/paper_draft.tex']`,
  `arxiv_verified = N/A` (book), `doi_verified = N/A`. Note: see 1.2 below
  for year-edition advisory. Re-run Stage 13 to clear.
- **Cache:** fresh-fetch (registry grep returns empty)

### 1.2 — 🔵 RECOMMENDED — `Gilkey1995` edition-year metadata could not be primary-source-verified

- **Gate:** CitationIntegrity
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:484`
- **Observed:** Bibitem says "2nd ed. (CRC Press, 1995)". The 2nd-edition
  date is widely cited as either 1994 (Wikipedia Atiyah–Singer page:
  "Gilkey, Peter B. (1994), … CRC Press, ISBN 978-0-8493-7874-4") or 1995
  (other sources). The 1st edition was Publish or Perish 1984; the 2nd
  edition (CRC Press) carries copyright dates that vary across catalog
  records.
- **Evidence:** Wikipedia `https://en.wikipedia.org/wiki/Atiyah-Singer_index_theorem`
  cites "1994" with ISBN 978-0-8493-7874-4. Direct CRC/Routledge fetch
  returned 403; Amazon returned 500; WorldCat returned 403. Could not pin
  the edition year to a primary source in this run. (`fetch_failed` per
  finding-class-1 protocol.)
- **Expected:** Authoritative confirmation of the 1995 vs 1994 vs 1995-with-
  1994-copyright issue. ISBN 978-0-8493-7874-4 should be added to the
  registry entry to disambiguate.
- **Fix:** Either (a) verify against a library-catalog primary source and
  pin the year, or (b) drop the year-disagreement risk by adding the ISBN
  to both the bibitem and the registry entry. Track in
  `citation_verifications.jsonl` with `verdict: fetch_failed` so this isn't
  silently dropped.
- **Cache:** fetch-failed (CRC, Amazon, Google Books all 4xx/5xx)

### 1.3 — 🔴 BLOCKER — `LinearizedEFE2026` bibkey absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:88,476-479`
  (in-prep self-cite to companion paper23); `src/core/citations.py` (registry
  — **absent**).
- **Observed:** `\cite{LinearizedEFE2026,Vergeles2025}` appears in the
  introduction; the bibitem is in the bibliography. `grep -n "LinearizedEFE2026"
  src/core/citations.py` returns nothing. The prior claims-reviewer documented
  this in `papers/paper39_heat_kernel_expansion/claims_review.md:38` as
  "Optional: add with note 'in preparation, this project'". Under the
  Gate 1 binary criterion ("every bibkey in the .tex has a matching
  CITATION_REGISTRY entry"), an in-prep self-cite is not exempt. The pipeline
  invariant is registry-completeness, not external-vs-self.
- **Evidence:**
  ```
  $ grep -rn "LinearizedEFE2026" src/
  (no output — i.e., not in CITATION_REGISTRY, not in PARAMETER_PROVENANCE,
   not in formulas.py)
  $ grep -n "LinearizedEFE2026" papers/paper39_heat_kernel_expansion/paper_draft.tex
  88:free-fermion limit~\cite{LinearizedEFE2026,Vergeles2025}.
  476:\bibitem{LinearizedEFE2026}
  ```
- **Expected:** A `'LinearizedEFE2026'` entry in `CITATION_REGISTRY` with
  authors `Roehm, J. G.`, title matching the bibitem, `used_in =
  ['papers/paper39_heat_kernel_expansion/paper_draft.tex']` (and any
  paper40 / future companion that cites it), `arxiv` and `doi` left null
  with `notes: 'In preparation, this project; companion of paper23'`.
- **Fix:** Add a self-cite registry entry. Once paper23 is released this
  becomes a cycle-resolving entry rather than a placeholder.
- **Cache:** fresh-fetch (registry grep returns empty)

### 2.1 — 🔴 BLOCKER — `Vergeles2025` title differs across papers (cross-paper bibitem inconsistency)

- **Gate:** CrossPaperConsistency
- **Location:**
  - `papers/paper39_heat_kernel_expansion/paper_draft.tex:471-474` —
    title: *"Unitarity of 4D Lattice Theory of Gravity"*
  - `papers/paper23_linearized_efe/paper_draft.tex` —
    title: *"Akama–Diakonov gravity is a unitary theory"*
  - `papers/paper25_gravitational_waves/paper_draft.tex:458` —
    title: *"Akama–Diakonov gravity is a unitary theory"*
  - `papers/paper26_bh_entropy/paper_draft.tex` —
    title: *"Unitarity of 4D Lattice Theory of Gravity"*
  - `src/core/citations.py` registry —
    title: *"Unitarity of 4D Lattice Theory of Gravity"* (matches paper39 +
    paper26)
- **Observed:** Same arXiv ID `2506.00036` and same volume/page reference
  (PRD 112, 054509, 2025), but the TITLE in the bibitem text disagrees
  between paper23+paper25 (one phrasing) and paper39+paper26+registry (the
  other). The arXiv abstract page returns *"Unitarity of 4D Lattice Theory
  of Gravity"* (verified via WebFetch on `arxiv.org/abs/2506.00036` —
  `verdict: match` with paper39's bibitem). Therefore paper23 and paper25
  carry the **wrong title** for this bibkey. The
  `2026-04-26T03:00:00+00:00` cache record explicitly notes that
  "the actual title 'Unitarity of 4D Lattice Theory of Gravity' is
  verified" and that paper5 + paper26 were corrected — paper23 and paper25
  were missed in that sweep.
- **Evidence:** WebFetch `https://arxiv.org/abs/2506.00036` →
  *"Unitarity of 4D Lattice Theory of Gravity"*; `citation_verifications.jsonl`
  entry from 2026-04-26 confirming this. paper23 line `\bibitem{Vergeles2025}
  S.~N.~Vergeles, ``Akama--Diakonov gravity is a unitary theory,''
  Phys.\ Rev.\ D \textbf{112}, 054509 (2025).`
- **Expected:** All five papers (paper23, paper25, paper26, paper39, +
  registry) carry identical bibitem text for `Vergeles2025` — namely the
  arXiv-verified title *"Unitarity of 4D Lattice Theory of Gravity"*.
- **Fix:** This is **not** a paper39-internal fix — paper39's bibitem is
  correct. The fix lands in paper23 and paper25 bibitem text. However, until
  paper23 and paper25 are corrected, this finding flips Gate 2 to `blocked`
  for paper39 because the same bibkey resolves differently across companions
  (Gate 2 wording: "Same bibkey used in two papers but pointing to different
  arXiv IDs / metadata → BLOCKER"). The arXiv ID is identical here, so this
  is the title-mismatch sub-case — equally a Gate 2 blocker per the pass
  criteria, since the registry-truth is paper39-aligned but two siblings
  disagree.
- **Cache:** cache-verified (2026-04-26T03:00:00 record) + fresh cross-paper
  diff this run

### 2.2 — 🔵 RECOMMENDED — Two distinct `α_ADW` "natural ranges" used across companion papers

- **Gate:** CrossPaperConsistency
- **Location:**
  - `papers/paper23_linearized_efe/paper_draft.tex:54,350,375` —
    "Vergeles natural range $[0.1, 10]$"
  - `papers/paper39_heat_kernel_expansion/paper_draft.tex:340-343` —
    "natural-parameter region $(0.5 \le \alphaADW \le 1.5)$" + figure scan
    over `[0.05, 5.0]` (line 282)
- **Observed:** paper23 reports α_ADW natural range as [0.1, 10] (citing
  Vergeles); paper39 reports a "natural-parameter region" of [0.5, 1.5]
  (matching `GRAV_PARAMS.G_N_MATCH_TOLERANCE = 0.5`, ±50%) and figure-scans
  [0.05, 5.0]. These are not the same band. The two ranges describe
  different concepts — paper23's [0.1, 10] is the Vergeles unitarity-derived
  natural band on α_ADW itself; paper39's [0.5, 1.5] is the *project-policy*
  ±50% relative-error band on G_N matching. The conflation risk is real:
  paper39 §5 discussion frames [0.5, 1.5] as "the mean-field validity
  boundary," and a reader who has just read paper23 will see "[0.5, 1.5]
  inside [0.1, 10]" without an explicit pointer.
- **Evidence:** see locations cited.
- **Expected:** paper39 should add a 1-sentence cross-link clarifying that
  its [0.5, 1.5] is a project-policy match-tolerance band on G_N, distinct
  from paper23's [0.1, 10] Vergeles-natural band on α_ADW. Or, equivalently,
  paper39's discussion §5 could explicitly note that [0.5, 1.5] ⊂ [0.1, 10]
  and that the two bands have orthogonal physical content.
- **Fix:** Add a clarifying sentence in §5 (line ~340) of the form:
  "This [0.5, 1.5] band is the project-policy ±50% G_N match-tolerance
  (`GRAV_PARAMS.G_N_MATCH_TOLERANCE`) and is strictly inside the broader
  Vergeles-natural α_ADW band [0.1, 10] reported in companion paper23,
  Phase 6a Wave 1; the two bands constrain different quantities."
- **Cache:** N/A (cross-paper prose diff, not a citation fetch)

### 5.1 — 🔵 RECOMMENDED — abstract phrasing "deep PDE-level result" without explicit "tracked-hypothesis" disclaimer in same sentence

- **Gate:** NarrativeGrounding
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:51-56`
- **Observed:** Abstract reads *"The asymptotic expansion itself --- a deep
  PDE-level result in spin-bundle differential geometry --- is encoded as a
  tracked hypothesis structure DiracHeatKernelAsymptotic..."*. This is the
  honest disclosure path and clearly tagged as `interpretive`/`tracked
  hypothesis`. However, the immediately preceding sentence asserts "**The
  Lean module HeatKernelExpansion.lean ships 19 substantive theorems, zero
  sorry statements, and zero new axioms beyond the Lean 4 kernel's standard
  three.**" — the casual reader may infer that *the asymptotic existence
  itself is proved in Lean*, when in fact the structure-as-hypothesis pattern
  defers it. The §4 disclosure (line 175-185) is clear; the abstract elision
  is the marginal risk.
- **Evidence:** abstract paragraph (lines 31-62); §4 disclosure (lines
  175-185); §8 disclosure (lines 396-407).
- **Expected:** Either (a) the abstract's "zero sorry, zero new axioms"
  sentence is followed by an explicit "(modulo a tracked-hypothesis structure
  for the manifold-level asymptotic existence)" parenthetical, or (b) the
  current §4/§8 prose is sufficient under Gate 7 if the interpretive tag in
  the abstract sentence about the structure is treated as load-bearing.
- **Fix:** Insert "(modulo the manifold-level asymptotic existence, which
  is encoded as a tracked-hypothesis structure)" after "zero new axioms
  beyond the Lean 4 kernel's standard three." in the abstract.
- **Cache:** N/A

### 6.1 — 🔵 RECOMMENDED — Decision Gate E.2 biconditional positivity hypotheses (Λ > 0, N_f > 0) not stated in §3 prose theorem statement

- **Gate:** AssumptionDisclosure
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:243-261`
  (paper §3 displayed theorem statement); Lean source
  `lean/SKEFTHawking/HeatKernelExpansion.lean:403-405`.
- **Observed:** The Lean theorem signature is
  `theorem a2_matches_GNemerg_iff_alpha_ADW_unity {Λ N_f α : ℝ} (hΛ : 0 < Λ)
  (hN : 0 < N_f) : G_N_from_a2 Λ N_f = SKEFTHawking.LinearizedEFE.G_N_emerg
  Λ N_f α ↔ α = 1`. Both `hΛ : 0 < Λ` and `hN : 0 < N_f` are load-bearing
  (the proof's forward direction explicitly invokes
  `G_N_sakharov_pos hΛ hN` to derive `G_N_sakharov ≠ 0` for the
  `mul_right_cancel₀`). The paper's §3 displayed theorem statement reads
  "Let Λ, N_f > 0 and α ∈ ℝ. Then..." — this **does** disclose Λ, N_f > 0.
  The §5 anchor theorem `G_N_from_a2_at_GUT_inverse` and the discussion
  in §3-§4 use Λ_UV = 10^16 GeV and N_f = 15 implicitly (both positive),
  but the pre-condition is implicit. This is borderline — the ±0 case for
  N_f is degenerate (formula has N_f in denominator) and a careful reader
  will recognize this, but undisclosed implicit hypotheses are how silent
  generalization errors ship.
- **Evidence:** Lean signature (lines 403-405); paper §3 (line 246, "Let
  Λ, N_f > 0").
- **Expected:** Confirmed disclosed in the §3 displayed theorem statement.
  This finding is RECOMMENDED rather than BLOCKER because the disclosure is
  present; the recommendation is to also surface Λ, N_f > 0 explicitly in the
  §6 quantitative-anchor framing (line 219-235) where the GUT parameters are
  introduced.
- **Fix:** Optional — add a parenthetical "(Λ_UV, N_f > 0 throughout)" to
  the §6 introduction. Not a true gate failure.
- **Cache:** N/A

### 7.1 — 🔵 RECOMMENDED — paper macros for theorem and test counts are static literals, not pulled from canonical pipeline

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `papers/paper39_heat_kernel_expansion/paper_draft.tex:18-19`
- **Observed:** Paper defines
  `\newcommand{\heatKernelThms}{19}` and
  `\newcommand{\heatKernelTests}{36}` as **paper-local static literals**, not
  via `\input{../../docs/counts.tex}` macros. The paper does
  `\input{../../docs/counts.tex}` on line 17 (so global counts are macro-fed),
  but the Wave-1-specific counts are inline static literals. `validate.py
  --check count_literals` does not flag them because the regex is calibrated
  to `\d+\s+(theorems|sorry|...)` style prose, not `\newcommand{\xxx}{19}`
  style macros. If the Lean module gains or loses a theorem (e.g. via
  strengthening pass), `\heatKernelThms{}` will silently drift from the
  canonical 19. Same for the 36 tests claim. (Pipeline counts via
  `validate.py --check counts_fresh` PASSED clean as of this run, so the
  values are *currently* correct.)
- **Evidence:** `count_literals` PASS with no warning for paper39 (per
  this-run `validate.py` output); paper draft lines 18-19 are static.
- **Expected:** Either (a) introduce paper-specific macros in
  `docs/counts.tex` (e.g. `\heatKernelThms` and `\heatKernelTests`)
  generated from the Lean count + pytest collection, or (b) leave the
  static-literal pattern but add a Wave-13 audit step to re-grep the
  counts against the canonical source on every wave-strengthening pass.
- **Fix:** Add per-paper count macros to `docs/counts.tex` (auto-generated
  by the counts pipeline). Once available, replace the two
  `\newcommand{...}` lines with `\input` references. Low priority given
  the tests-paper-pair currently agrees with the pipeline.
- **Cache:** N/A

## QI Candidate

**Systemic gap surfaced:** the `claims_review.json` for paper39 explicitly
records the four citation-registry gaps (Gilkey1995, Vassilevich2003,
ChristensenDuff1979, LinearizedEFE2026) as `WARN` (line 138 of that file).
The prompt asserts the recent hygiene-fix sweep added Vassilevich2003 +
ChristensenDuff1979, which I verified, but **Gilkey1995 and LinearizedEFE2026
were left out**. The systemic issue is that the claims-reviewer marks
registry-absences as WARN (no submission impact) while the canonical Gate 1
treats registry-absences as BLOCKER. This severity mismatch means the
upstream reviewer's "no FAIL" verdict was misread by the hygiene-fix author
as "no BLOCKER" — the two reviewer roles are using different severity scales
for the same finding class. **QI proposal:** unify the severity
ladder — claims-reviewer should emit BLOCKER (not WARN) for any registry
absence, OR the hygiene-fix workflow should treat *every* claims-reviewer WARN
as a candidate Gate-1 BLOCKER under canonical-gate criteria, regardless of
the upstream tag. Otherwise this class of failure (registry-absent bibkeys
ship to submission) will recur every time a new paper is added to the
project.
