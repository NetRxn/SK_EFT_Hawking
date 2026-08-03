# Cross-Bundle Build & Mechanical Integrity — Publication-Readiness Audit
**Auditor:** CROSS-build-integrity (mechanical sweep, all 21 bundles)   **Date:** 2026-08-01
**Artifacts examined:** `papers/{F,D1..D12,L1,L2,L3,I1,I2,I3,E1,E2}/` — `paper_draft.tex`, `paper_draft.pdf`, `bundle_metadata.json`, `append_log.json`, `source_manifest.md`, `change_log.md`, `figures/`, `bibliography.bib`; plus `docs/BUNDLE_READINESS_HEATMAP.md`, `docs/BUNDLE_DIRECTORY_SCHEMA.md`, `docs/BUNDLE_LIFT_PROCEDURE.md`, `docs/audits/stage13_attribution_sweep_2026-06-10.md`, `docs/review_finding_supersessions.json`.

**Scope note.** This report is purely mechanical: objectively true-or-false facts checked uniformly
across all 21 bundles. No prose critique — that is the sibling auditors' scope.

## Method — every command run

Builds were performed on **copies** of each bundle directory in a scratch tree, so no build artifact
was created, modified, or deleted inside the repository. Pre-existing PDFs were read but never
overwritten.

```bash
S=<scratch>/build
for b in F D1..D12 L1 L2 L3 I1 I2 I3 E1 E2; do
  cp -R $REPO/papers/$b $S/$b
  (cd $S/$b && rm -f paper_draft.{aux,log,out,toc,bbl,blg,fdb_latexmk,fls,synctex.gz,pdf})
  (cd $S/$b && latexmk -pdf -interaction=nonstopmode paper_draft.tex)
  pdfinfo $S/$b/paper_draft.pdf | grep Pages          # true fresh page count
  pdfinfo $REPO/papers/$b/paper_draft.pdf | grep Pages # pre-existing on-disk page count
done
# D3 additionally rebuilt with -f (latexmk aborts otherwise) to obtain a converged document
# staleness test: pdftotext both PDFs, diff the extracted text
texcount -0 -sum -merge papers/<b>/paper_draft.tex           # word counts
pdflatex -interaction=nonstopmode -halt-on-error ...         # the lift procedure's own gate
uv run python scripts/bundle_readiness.py --json             # read-only regeneration (verified: no file mutation)
uv run python scripts/validate.py --check <name> --no-archive
```

`latexmk`, `pdflatex`, `bibtex`, `texcount`, `detex` at `/Library/TeX/texbin/`; `pdfinfo`/`pdftotext`
at `/opt/homebrew/bin/`.

**Litter check.** `git status --porcelain` before/after is unchanged apart from artifacts that
already existed at session start (`docs/counts.{json,tex}` modified at 00:52:59, i.e. ~12 h before
this audit; `papers/AutomatedReviews/2026-08-01-bundle-stage13/` untracked at session start).
`validate.py --check bundle_source_freshness` rewrites nine `bundle_metadata.json` files with
**byte-identical content** (mtime touched only, confirmed by `git status` showing them unmodified);
that is the check's own designed behaviour, not an edit by this audit.

---

# MASTER TABLE

## A. Compile status, true page count, stale-PDF detection, warnings

| Bundle | Compile (`latexmk -pdf -interaction=nonstopmode`) | Fresh pp | On-disk pp | pp match | pdftotext diff lines vs on-disk PDF | On-disk PDF stale? | Undef refs | Undef cites | Overfull >20pt | Max overfull | `Missing $` |
|---|---|---:|---:|:---:|---:|:---:|---:|---:|---:|---:|---:|
| F | clean (rc=0) | 23 | 23 | ✓ | 888 | **YES** | 0 | 0 | 14 | 310.4pt | 0 |
| D1 | clean (rc=0) | 10 | 9 | **✗** | 510 | **YES** | 0 | 0 | 4 | 124.7pt | 0 |
| D2 | clean (rc=0) | 11 | 11 | ✓ | 0 | no | 0 | 0 | 7 | 133.0pt | 0 |
| **D3** | **FAILS (rc=12)** | 59 † | 57 | **✗** | 641 | **YES** | 3 | 0 | 56 | 454.6pt | 0 |
| D4 | clean (rc=0) | 31 | 31 | ✓ | 33 | **YES** | 0 | 0 | 35 | 489.8pt | 0 |
| D5 | clean (rc=0) | 14 | 14 | ✓ | 568 | **YES** | 0 | 0 | 24 | 165.2pt | 0 |
| D6 | clean (rc=0) | 12 | 12 | ✓ | 0 | no | 0 | 0 | 14 | 200.0pt | 0 |
| D7 | clean (rc=0) | 3 | 3 | ✓ | 0 | no | 0 | 0 | 0 | 14.7pt | 0 |
| D8 | clean (rc=0) | 9 | 9 | ✓ | 0 | no | 0 | 0 | 7 | 222.8pt | 0 |
| D9 | clean (rc=0) | 12 | 10 | **✗** | 409 | **YES** | 0 | 0 | 5 | 60.3pt | 0 |
| D10 | clean (rc=0) | 5 | 5 | ✓ | 0 | no | 0 | 0 | 0 | 2.9pt | 0 |
| D11 | clean (rc=0) | 9 | 9 | ✓ | 0 | no | 0 | 0 | 0 | — | 0 |
| D12 | clean (rc=0) | 11 | 11 | ✓ | 0 | no | 0 | 0 | 0 | — | 0 |
| L1 | clean (rc=0) | 3 | 3 | ✓ | 2 | date-line only | 0 | 0 | 3 | 192.6pt | 0 |
| L2 | clean (rc=0) | 4 | 4 | ✓ | 0 | no | 0 | 0 | 2 | 37.3pt | 0 |
| L3 | clean (rc=0) | 4 | 4 | ✓ | 2 | date-line only | 0 | 0 | 3 | 99.7pt | 0 |
| I1 | clean (rc=0) | 23 | 23 | ✓ | 10 | **YES (counts)** | 0 | 0 | 14 | 211.4pt | 0 |
| I2 | clean (rc=0) | 15 | 15 | ✓ | 0 | no | 0 | 0 | 12 | 149.0pt | 0 |
| I3 | clean (rc=0) | 18 | 18 | ✓ | 2 | **YES (counts)** | 0 | 0 | 24 | 236.6pt | 0 |
| E1 | clean (rc=0) | 5 | 5 | ✓ | 74 | **YES** | 0 | 0 | 0 | — | 0 |
| E2 | clean (rc=0) | 5 | 5 | ✓ | 4 | **YES (counts)** | 0 | 0 | 1 | 94.5pt | 0 |

† D3's 59 pp is from a **forced** run (`latexmk -f`); the unforced run aborts at 53 pp and never
converges (bibtex/second pass never run, leaving 208 undefined refs + 86 undefined citations as a
*consequence of the abort*, not as independent defects). Under `-halt-on-error` — the flag the
project's own `docs/BUNDLE_LIFT_PROCEDURE.md` §7 gate mandates — D3 produces **no PDF at all**.

**Tally: 20/21 compile, 1/21 (D3) fails. 10/21 on-disk PDFs are stale** (F, D1, D3, D4, D5, D9, I1,
I3, E1, E2), of which **3 differ in page count** (D1 9→10, D3 57→59, D9 10→12).

## B. Content metrics, figure integrity, citation integrity

| Bundle | Words | §sec | §§sub | figure envs | table envs | eq envs | `\includegraphics` | missing gfx file | fig labels never `\ref`'d | `\cite` calls | unique keys | bib entries | dangling cites | uncited bib entries |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| F | 12095 | 12 | 65 | 0 | 0 | 8 | 0 | 0 | 0 | 72 | 53 | 53 | 0 | 0 |
| D1 | 4655 | 9 | 32 | 0 | 1 | 12 | 0 | 0 | 0 | 41 | 42 | 42 | 0 | 0 |
| D2 | 6580 | 6 | 24 | 0 | 0 | 7 | 0 | 0 | 0 | 40 | 31 | 31 | 0 | 0 |
| D3 | 11298 | 31 | 114 | 0 | 0 | 19 | 0 | 0 | 0 | 78 | 69 | 69 | 0 | 0 |
| D4 | 7394 | 11 | 46 | 0 | 0 | 5 | 0 | 0 | 0 | 22 | 18 | 18 | 0 | 0 |
| D5 | 7541 | 13 | 27 | 7 | 0 | 2 | 7 | 0 | **7** | 9 | 9 | 27 | 0 | **18** |
| D6 | 6326 | 7 | 14 | 0 | 0 | 5 | 0 | 0 | 0 | 9 | 9 | 9 | 0 | 0 |
| D7 | 1655 | 7 | 1 | 0 | 0 | **0** | 0 | 0 | 0 | 3 | 3 | 6 | 0 | **3** |
| D8 | 4911 | 13 | 5 | 3 | 0 | **0** | 3 | 0 | 0 | 26 | 17 | 17 | 0 | 0 |
| D9 | 5671 | 9 | 16 | 4 | 0 | **0** | 4 | 0 | 0 | 77 | 42 | 42 | 0 | 0 |
| D10 | 2389 | 7 | 10 | 0 | 0 | 5 | 0 | 0 | 0 | 13 | 17 | 17 | 0 | 0 |
| D11 | 5372 | 9 | 7 | 4 | 0 | 2 | 4 | 0 | **2** | 16 | 14 | 14 | 0 | 0 |
| D12 | 6864 | 9 | 11 | 3 | 0 | 4 | 3 | 0 | 0 | 21 | 15 | 15 | 0 | 0 |
| L1 | 1480 | 3 | 0 | 1 | 0 | 2 | 1 | 0 | **1** | 11 | 10 | 10 | 0 | 0 |
| L2 | 1939 | 7 | 0 | 2 | 0 | 3 | 2 | 0 | **2** | 21 | 16 | 16 | 0 | 0 |
| L3 | 1638 | 3 | 0 | 1 | 0 | 5 | 1 | 0 | **1** | 21 | 14 | 14 | 0 | 0 |
| I1 | 9794 | 15 | 0 | 6 | 1 | **0** | 6 | 0 | **6** (+1 table) | 11 | 10 | 10 | 0 | 0 |
| I2 | 4600 | 9 | 23 | 5 | 0 | **0** | 5 | 0 | **5** | 11 | 7 | 7 | 0 | 0 |
| I3 | 6427 | 10 | 28 | 0 | 0 | **0** | 0 | 0 | 0 | 19 | 10 | 10 | 0 | 0 |
| E1 | 2162 | 9 | 0 | 2 | 0 | 8 | 2 | 0 | **2** | 23 | 19 | 19 | 0 | 0 |
| E2 | 2324 | 8 | 0 | 4 | 0 | 7 | 4 | 0 | **4** | 34 | 18 | 18 | 0 | 0 |

**Zero missing graphics files and zero orphan figure files on disk across all 21 bundles** — every
`\includegraphics` target resolves, and every `figures/*.png` on disk is included by some
`\includegraphics`. All bundle figure PNGs are git-tracked. **Dangling citations: 0 across all 21
bundles.** **Uncited bibliography entries: D5 (18 of 27) and D7 (3 of 6); 0 elsewhere.**

## C. Schema conformance, `bundle_metadata.json` consistency, journal front/back matter

| Bundle | mandatory files missing | stage9 | stage10 | stage13 | blockers | advisories | readiness | green-with-blockers? | `freshness_stale` | `redo_required` | `last_lift` < tex mtime | Stage-13 review doc resolves | author | affil | abstract | PACS/kw | ack | data-avail | code-avail |
|---|---|---|---|---|---:|---:|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| F | — | green | green | green | 23 | 89 | RED | **YES** | true | false | **YES** | ✓ (`#f` inside `{#d2 #l2 #f}`) | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D1 | — | green | green | green | 37 | 21 | RED | **YES** | true | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** |
| D2 | — | green | green | green | 19 | 41 | RED | **YES** | true | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** |
| D3 | — | green | green | green | 7 | 50 | RED | **YES** | true | false | **YES** | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D4 | — | green | green | green | 1 | 33 | RED | **YES** | true | false | **YES** | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D5 | — | green | green | green | 17 | 45 | RED | **YES** | true | false | **YES** | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D6 | — | not_started | skeleton | green | 0 | 0 | YELLOW | no | false | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | **✗** | **✗** | **✗** |
| **D7** | **`source_manifest.md`, `append_log.json`** | not_started | green | green | 12 | 5 | RED | **YES** | false | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | **✗** | **✗** | **✗** |
| D8 | — | pending | pending | green | 0 | 14 | YELLOW | no | false | false | **YES** | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D9 | — | green | pending | green | 0 | 0 | GREEN | no | false | false | **YES** | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D10 | — | green | green | green | 0 | 3 | YELLOW | no | false | false | **YES** | ✓ (JSON key present ×5) | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| D11 | — | green | green | pending | 23 | 63 | RED | **yes (s9+s10)** | false | **true** | **YES** | n/a (null) | ✓ | **✗** | ✓ | **✗** | ✓ | **✗** | **✗** |
| D12 | — | pending-redo | pending-redo | pending-redo | 46 | 102 | RED | no | false | **true** | **YES** | n/a (null) | ✓ | **✗** | ✓ | **✗** | ✓ | **✗** | **✗** |
| L1 | — | green | green | green | 2 | 3 | RED | **YES** | false | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | **✗** | **✗** | **✗** |
| L2 | — | green | green | green | 16 | 27 | RED | **YES** | true | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** |
| L3 | — | green | green | green | 6 | 18 | RED | **YES** | false | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | **✗** | **✗** | **✗** |
| **I1** | — | green | green | green | 16 | 25 | RED | **YES** | true | false | no | **✗ anchor `#i1` absent** | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | ✓ |
| **I2** | — | green | green | green | 19 | 42 | RED | **YES** | false | false | **YES** | **✗ anchor `#i2` absent** | ✓ | **✗** | ✓ | **✗** | **✗** | **✗** | **✗** |
| **I3** | — | pending | green | green | 16 | 20 | RED | **YES** | false | false | **YES** | **✗ anchor `#i3` absent** | ✓ | **✗** | ✓ | **✗** | ✓ | **✗** | **✗** |
| E1 | — | green | green | green | 5 | 7 | RED | **YES** | true | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** |
| E2 | — | green | green | green | 0 | 21 | YELLOW | no | false | false | **YES** | ✓ | ✓ | ✓ | ✓ | **✗** | ✓ | **✗** | **✗** |

**Tallies.** 1 bundle (D7) missing mandatory schema files. **15 bundles carry `stage13_status:
"green"` while `blockers_open > 0` and their own `readiness` field says `RED`** (F, D1–D5, D7, L1,
L2, L3, I1, I2, I3, E1 = 14 with the stage-13 form; D11 with the stage-9/10 form = 15 total).
**20/21 bundles have `last_lift` older than the draft's mtime** (only I1 does not). **0/21 have
PACS/keywords. 0/21 have a data-availability statement. 20/21 lack a code/artifact-availability
statement** (I1 alone has one). **12/21 lack an affiliation block.**

---

# PER-BUNDLE FAILURE DETAIL

## 1. Compile failure — D3 (the single worst mechanical defect)

**`papers/D3/paper_draft.tex:712`.** First fatal error, verbatim from
`paper_draft.log:995` of the forced build:

```
! Undefined control sequence.
<recently read> \Imm 
                     
l.712 ...induced-gravity route it is derived $\Imm
                                                  $-independently
```

Source line 712:

```latex
tuning; in the ADW Sakharov induced-gravity route it is derived $\Imm$-independently
```

`\Imm` (evidently intended as the Immirzi parameter γ) is never defined in the preamble.

Consequences, each verified:

1. **The project's own mandated gate fails outright.** `docs/BUNDLE_LIFT_PROCEDURE.md` §7 requires
   `pdflatex paper_draft.tex` to produce "a clean PDF with no `Missing $` / `Misplaced &` /
   `Undefined control sequence` errors" and states "**Stage 9 may not be invoked until LaTeX
   compiles cleanly.**" Running exactly that gate:
   ```
   $ pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/d3halt paper_draft.tex
   rc=1
   !  ==> Fatal error occurred, no output PDF file produced!
   ```
   D3's `bundle_metadata.json` nevertheless records `stage9_status: green`, `stage10_status: green`,
   `stage13_status: green`. The gate was bypassed.
2. **`latexmk` refuses to converge.** rc=12; bibtex is never run to completion and the second pass
   never happens, so the unforced build leaves 208 undefined references and 86 undefined citations.
   Forced (`-f`) it converges to 59 pp with 3 residual undefined references (below).
3. **Silent content corruption in the shipped PDF.** The existing 57-pp `papers/D3/paper_draft.pdf`
   was built by a non-halting run, so the undefined macro simply vanished. `pdftotext` of that PDF,
   line 1203:
   > "…in the ADW Sakharov induced-gravity route it is derived **-independently**"

   The physics claim "derived γ-independently" reads as "derived -independently". A referee sees a
   sentence with a missing symbol and a dangling hyphen.

**Required end state:** define `\Imm` in the preamble (or replace with `\gamma`), then recompile
under `-halt-on-error` and re-run Stages 9/10/13, whose green statuses were recorded against a
draft that does not build. **Size:** `trivial` for the macro; `small` for the gate re-run.

### D3 residual undefined references (forced build)

```
LaTeX Warning: Reference `sec:singularity-thms' on page 46 undefined
LaTeX Warning: Reference `sec:cfl-z3-matching' on page 51 undefined
LaTeX Warning: Reference `sec:singularity-thms' on page 51 undefined
```
Two distinct labels (`sec:singularity-thms`, `sec:cfl-z3-matching`) are referenced but never
defined. These render as `??` in the PDF. **Size:** `trivial`.

## 2. Stale on-disk PDFs (10 of 21)

`papers/**/*.pdf` is git-ignored (`.gitignore:88`), so "the committed PDF" is strictly "the PDF that
happens to be on disk". Anyone who reviewed a bundle by opening its PDF read a different document
from the source. Detection: `pdftotext` both PDFs and diff.

| Bundle | On-disk pp → fresh pp | diff lines | Nature of the drift |
|---|---|---:|---|
| F | 23 → 23 | 888 | broad prose drift; PDF built 2026-06-10, `.tex` last edited 2026-07-20 |
| D1 | **9 → 10** | 510 | broad prose drift + one extra page |
| D3 | **57 → 59** | 641 | broad prose drift + two extra pages |
| D4 | 31 → 31 | 33 | date line + a ~9-line block on `HorizonBoundaryCondition` placeholder fields |
| D5 | 14 → 14 | 568 | broad prose drift |
| D9 | **10 → 12** | 409 | broad prose drift + two extra pages |
| E1 | 5 → 5 | 74 | prose drift |
| **I1** | 23 → 23 | 10 | **headline verification counts wrong by >2×** |
| **I3** | 18 → 18 | 2 | **headline theorem count wrong by >4×** |
| E2 | 5 → 5 | 4 | date line + theorem count 26063 → 26077 |

The I1 and I3 cases are the most damaging because the stale numbers are the papers' central claim.
`diff` of the extracted text:

**I1 abstract (on-disk PDF vs fresh):**
```
< pipeline has produced 12463 machine-checked theorems across 936 Lean modules with 0 remaining
> pipeline has produced 26103 machine-checked theorems across 2012 Lean modules with 0 remaining
```
and at body line 445:
```
< Invariant 9 addresses a subtle inflation problem: 26 of our 12463 theorems are True := trivial
> Invariant 9 addresses a subtle inflation problem: 26 of our 26103 theorems are True := trivial
```

**I3 (body line 95):**
```
< bulk of the SK–EFT Hawking project's ∼5858 theorems were written
> bulk of the SK–EFT Hawking project's ∼26103 theorems were written
```

The `.tex` sources are correct (they `\input{counts.tex}`); it is the rendered PDFs that are wrong.
**Required end state:** rebuild every bundle PDF as part of the readiness pass, and treat the PDF as
a build product that is regenerated before any review, never reviewed as found. **Size:** `trivial`
(rebuild) — but any prior review conclusion drawn from those PDFs must be re-checked.

Caveat: several PDFs were regenerated *during* this audit window by concurrent sibling auditors
(D2, D6, D7, L2 carry 2026-08-01 13:10–13:12 mtimes and fresh `.fdb_latexmk`/`.fls` files; D10
12:17; D12 11:51). Those bundles therefore read "not stale" partly because someone else just
rebuilt them in place. The freshness column is a snapshot, not a property of the committed tree.

## 3. Undefined citations — the two named suspects are **false alarms**

- **D8** — 26 `\cite` calls / **0 inline `\bibitem`**, as reported. But D8 does **not** use an
  inline `thebibliography`; it uses the bibtex path:
  `\bibliographystyle{apsrev4-2}` + `\bibliography{bibliography}`, with a git-tracked
  `papers/D8/bibliography.bib` containing exactly the 17 unique keys cited. bibtex runs, produces
  `paper_draft.bbl` with 17 entries, and the final `paper_draft.log` contains **zero**
  `Citation ... undefined`. **Not a defect.**
- **D10** — 13 `\cite` calls (17 unique keys, several multi-key) / 0 inline `\bibitem`. Same
  mechanism: `\bibliography{bibliography}` + git-tracked `papers/D10/bibliography.bib` with exactly
  those 17 keys. Final log: zero undefined citations. **Not a defect.**

`paper_draftNotes.bib` (present in 19 bundles, usually 104 bytes) is **not** a bibliography: it is
REVTeX 4-2's auto-generated `@CONTROL{REVTEX42Control}` / `@CONTROL{apsrev42Control,...}` notes
file. It resolves nothing and requires nothing. Benign artifact.

**Across all 21 bundles: 0 dangling `\cite` keys and 0 `Citation ... undefined` warnings** in the
converged build.

## 4. Uncited bibliography entries

- **D5 — 18 of 27 `\bibitem`s are never cited** (67 % of the printed reference list). Cited (9):
  `BelenchiaLiberatiMohd2014, DESI2025, FinazziLiberatiSindoni2012PRL, FinazziLiberatiSindoni2012Proc,
  HalenkaMiller2020, JannesVolovik2012, ParkRatra2025rd, Verlinde2017dSEmergent, WangYinTension2025rd`.
  Never cited (18): `ADW2019, BK2025, Berezhiani2015, DESI2024, Diakonov2011, Glodkowski2024, KV2008,
  Lean4, LucianoPaliathanasisSaridakis2506, Mathlib, PlazaKraiselburd2025fR, Pretko2017,
  TyagiHaridasuBasak2025, VanWaerbeke2025, Vergeles2025, Volovik2006, Wan2019, YoonGuha2023`.
  With an inline `thebibliography` these all **print** in the reference list, so the paper ships a
  reference list two-thirds of which the text never invokes — including the `Lean4` and `Mathlib`
  entries, i.e. the tool citations a formal-verification paper most needs to actually cite.
  **Size:** `small` (cite them where they belong, or delete).
- **D7 — 3 of 6 never cited**: `BiancoResta2011, YedidiaFreemanWeiss2003, Zurek1985`.
  **Size:** `trivial`.
- All other 19 bundles: 0 uncited entries.

## 5. Overfull/underfull boxes and math-mode errors

**`Missing $` / math-mode errors: zero across all 21 bundles.** The only math-related error in the
corpus is D3's undefined `\Imm` (§1).

Overfull boxes exceeding 20 pt (counts in Table A). The worst offenders — these are text or tables
running visibly into the margin at REVTeX two-column width:

| Bundle | # >20pt | worst |
|---|---:|---:|
| D3 | 56 | 454.6pt |
| D4 | 35 | 489.8pt |
| D5 | 24 | 165.2pt |
| I3 | 24 | 236.6pt |
| F | 14 | 310.4pt |
| D6 | 14 | 200.0pt |
| I1 | 14 | 211.4pt |
| I2 | 12 | 149.0pt |
| D2 | 7 | 133.0pt |
| D8 | 7 | 222.8pt |
| D9 | 5 | 60.3pt |
| D1 | 4 | 124.7pt |
| L1 | 3 | 192.6pt |
| L3 | 3 | 99.7pt |
| L2 | 2 | 37.3pt |
| E2 | 1 | 94.5pt |
| D7, D10, D11, D12, E1 | 0 | ≤14.7pt |

A 489.8 pt overfull box (D4) is roughly two column-widths of overhang — a line of unbreakable
material (typically a long `\texttt{}` Lean theorem name) with no break opportunity. **Size:**
`small` per bundle (`\allowbreak`/`\seqsplit`/`sloppypar` around the long identifiers).

Underfull boxes are numerous (up to 295 in D9) but are a `\raggedbottom`/`\sloppy` interaction, not
a defect class worth itemising; recorded in the method output only.

## 6. Structural content — the zero-figure bundles

Nine bundles contain **no figure and no table at all**: **F, D2, D3, D4, D6, D7, D10, I3** (and D1
has exactly one table, no figure). For F (a 23-pp review article), D3 (59 pp) and D4 (31 pp) that is
a structural fact a referee will notice immediately. Recorded here as a hard count; the editorial
judgement is the sibling auditors'.

Three bundles have **no numbered equation environment at all**: **D7, D8, D9, I1, I2, I3** (six,
in fact). D7 has 1 655 words, 7 sections, 1 subsection, 0 equations, 0 figures, 0 tables.

## 7. Figures referenced nowhere in the text

Every `\includegraphics` target resolves on disk (0 missing across 21 bundles) and no figure file on
disk is unused (0 orphan files). The defect is the other direction: **figures whose `\label` is
never `\ref`'d**, i.e. the body text never points the reader at the figure.

| Bundle | orphan figure labels |
|---|---|
| D5 (7 of 7) | `fig:phase5x_viability_matrix`, `fig:sfdm-money-plot-left`, `fig:adw-veff`, `fig:bbn-conformance`, `fig:zhitnitsky-lambda-qcd-scan`, `fig:ep-violation-matrix`, `fig:lambda-emerg-scan` |
| I1 (6 of 6, + 1 table) | `fig:three_layer`, `fig:firstorderkms_grid`, `fig:gap_counterexample`, `fig:chirality_wall_tree`, `fig:pipeline`, `fig:sentence_clusters`; `tab:stages` |
| I2 (5 of 5) | `fig:i2-jackknife-deps`, `fig:i2-categorical-hierarchy`, `fig:i2-mtc-instances`, `fig:i2-module-deps`, `fig:i2-mathlib-upstream-flow` |
| E2 (4 of 4) | `fig:T_sweep`, `fig:diss_window`, `fig:noise`, `fig:snr` |
| D11 (2 of 4) | `fig:pt`, `fig:effmedium` |
| L2 (2 of 2) | `fig:phase`, `fig:gen_constraint` |
| E1 (2 of 2) | `fig:gain`, `fig:regime` |
| L1 (1 of 1) | `fig:cGW` |
| L3 (1 of 1) | `fig:regime` |

D5 and I1 contain **zero `\ref{}` commands of any kind** (verified: `grep -o '\\ref{[^}]*}'` returns
nothing). D8, D9, D12 are the only figure-bearing bundles whose figures are all cross-referenced.
**Size:** `small` per bundle.

`validate.py --check bundle_figure_integrity` passes but covers **only 7 figures** (D11×4, D12×3) —
the `FIGURE_REGISTRY`-derived roster. The other 21 bundle figures (D5, D8, D9, I1, I2, L1, L2, L3,
E1, E2) are outside the byte-identity / 8 pt-legibility guard entirely.

## 8. Schema conformance (`docs/BUNDLE_DIRECTORY_SCHEMA.md`)

Mandatory per the schema: `paper_draft.tex`, `source_manifest.md`, `change_log.md`,
`append_log.json`, `bundle_metadata.json`.

- **D7 is missing two mandatory files: `papers/D7/source_manifest.md` and
  `papers/D7/append_log.json`.** Consistently, D7's `bundle_metadata.json` carries
  `"source_manifest_last_regen": null` — a schema-required non-null field. D7 is also the only
  bundle with no `audit_log.jsonl`. **Size:** `trivial` (`scripts/bundle_source_manifest.py`).
- All other 20 bundles have the full mandatory set.
- Optional-file gaps (not errors per the schema, but the shape of the corpus): `sentence_state.json`
  is absent from **all 21** bundles; `tables.py` from all 21; `READINESS_GATES.md` present in only
  3 (D5, D8, L2); `bibliography.bib` present in only 2 (D8, D10); `figures/figure_review_report.json`
  present in 8.

## 9. `bundle_metadata.json` internal consistency

Every one of the 21 files parses as valid JSON. Findings:

**(a) Status contradictions — 15 bundles.** The reported D7 pattern (`stage13_status: "green"` with
`blockers_open: 12`) is not an isolated case. Full list of `stage13_status == "green"` **and**
`blockers_open > 0`:

| Bundle | blockers_open | advisories_open | own `readiness` field |
|---|---:|---:|---|
| F | 23 | 89 | RED |
| D1 | 37 | 21 | RED |
| D2 | 19 | 41 | RED |
| D3 | 7 | 50 | RED |
| D4 | 1 | 33 | RED |
| D5 | 17 | 45 | RED |
| **D7** | **12** | 5 | RED |
| L1 | 2 | 3 | RED |
| L2 | 16 | 27 | RED |
| L3 | 6 | 18 | RED |
| I1 | 16 | 25 | RED |
| I2 | 19 | 42 | RED |
| I3 | 16 | 20 | RED |
| E1 | 5 | 7 | RED |

Plus **D11**, which is `stage9_status: green`, `stage10_status: green`, `blockers_open: 23`,
`readiness: RED` (its `stage13_status` is honestly `pending`).

Note the contradiction is *inside a single file*: the same JSON says `"stage13_status": "green"` and
`"readiness": "RED"`. Per `docs/BUNDLE_DIRECTORY_SCHEMA.md` §"Aggregate verdict", 🔴 RED is defined
as "any stage `red` **OR** `blockers_open ≥ 1`" — so the `readiness` field is the correct one and
the per-stage `green` is the false one. **Required end state:** the Stage-13 reviewer must not be
allowed to write `green` while `blockers_open > 0`; add the invariant to
`scripts/bundle_readiness.py`'s writeback and to `validate.py`. **Size:** `small`.

**(b) `null` in schema-required fields.** Only one instance: `papers/D7/bundle_metadata.json`
`"source_manifest_last_regen": null` (the schema types it as a required ISO timestamp).
`stage13_review_doc` is `null` in D11 and D12, which the schema permits (`string | null`).

**(c) Review-doc paths that do not resolve.** Every `stage13_review_doc` **path** exists. Three
**anchors** do not:

- `papers/I1/bundle_metadata.json` → `docs/audits/stage13_attribution_sweep_2026-06-10.md#i1`
- `papers/I2/bundle_metadata.json` → `…#i2`
- `papers/I3/bundle_metadata.json` → `…#i3`

The document defines exactly these anchors (verified by `grep -o '{#[^}]*}'`):
`#d1 #d2 #d3 #d4 #d5 #d6 #d7 #d8 #d9 #e1 #e2 #f #l1 #l2 #l3 #paper10`. There is **no I-bundle
section in that document at all** — I1, I2 and I3 point their Stage-13 evidence at a review that
never covered them, and all three nevertheless carry `stage13_status: "green"`.
(F, D2 and L2 resolve correctly: their anchors live in the combined heading
`## D2 / L2 / F — cleared via paper10 supersession  {#d2 #l2 #f}`. D10's pointer
`docs/review_finding_supersessions.json#review:2026-06-30:D10-stage13` resolves — the key occurs 5×
in that file.) **Size:** `small`, but the underlying question — what evidence backs I1/I2/I3's green
Stage-13 — is `new-work`.

**(d) `last_lift` older than the draft's actual mtime — 20 of 21 bundles.** Only I1 has
`last_lift` (2026-06-10T20:33:51Z) after its `.tex` mtime (2026-06-10T20:32:24Z). Every other
bundle's draft has been edited outside the lift procedure since the last recorded lift, e.g.:

| Bundle | `last_lift` | `paper_draft.tex` mtime (UTC) |
|---|---|---|
| F | 2026-06-10T20:28:10Z | 2026-07-20T14:29:30Z |
| D1 | 2026-05-31T17:24:47Z | 2026-07-20T14:11:02Z |
| D5 | 2026-05-12T13:00:00Z | 2026-07-20T16:52:37Z |
| D7 | 2026-05-26T20:00:00Z | 2026-07-20T13:42:05Z |
| E2 | 2026-05-12T13:00:00Z | 2026-08-01T02:01:18Z |
| D12 | 2026-07-30T21:43:13Z | 2026-08-01T16:51:10Z |

**(e) `freshness_stale` flags.** True in 9 bundles: F, D1, D2, D3, D4, D5, L2, I1, E1 — exactly the
9 that `validate.py --check bundle_source_freshness` flags. Consistent. `stage13_redo_required: true`
in D11 and D12 only.

**(f) Undocumented extra fields.** Every bundle carries 4 fields absent from the schema
(`open_findings`, `blocked_p1_gates`, `readiness`, `readiness_last_computed`); several carry many
more (D7 has 13 extra: `phase6w_contributing_waves`, `headline_theorems`, `remediation_history`, …;
D8 has 13; I2 has 9). The schema doc has not been updated to describe them. Advisory.

## 10. Metadata vs. heatmap agreement — **full agreement**

`docs/BUNDLE_READINESS_HEATMAP.md` was regenerated read-only via
`uv run python scripts/bundle_readiness.py --json` (the `--json` path sets `backfill=False` and
writes nothing; verified by md5-ing all 21 `bundle_metadata.json` plus the heatmap before and after
— identical). Comparison across three sources:

| Bundle | live open / blockers | committed heatmap open / blockers | metadata `open_findings` / `blockers_open` | agree |
|---|---|---|---|:---:|
| F | 112 / 23 | 112 / 23 | 112 / 23 | ✓ |
| D1 | 58 / 37 | 58 / 37 | 58 / 37 | ✓ |
| D2 | 60 / 19 | 60 / 19 | 60 / 19 | ✓ |
| D3 | 57 / 7 | 57 / 7 | 57 / 7 | ✓ |
| D4 | 34 / 1 | 34 / 1 | 34 / 1 | ✓ |
| D5 | 62 / 17 | 62 / 17 | 62 / 17 | ✓ |
| D6 | 0 / 0 | 0 / 0 | 0 / 0 | ✓ |
| D7 | 17 / 12 | 17 / 12 | 17 / 12 | ✓ |
| D8 | 14 / 0 | 14 / 0 | 14 / 0 | ✓ |
| D9 | 0 / 0 | 0 / 0 | 0 / 0 | ✓ |
| D10 | 3 / 0 | 3 / 0 | 3 / 0 | ✓ |
| D11 | 86 / 23 | 86 / 23 | 86 / 23 | ✓ |
| D12 | 148 / 46 | 148 / 46 | 148 / 46 | ✓ |
| L1 | 5 / 2 | 5 / 2 | 5 / 2 | ✓ |
| L2 | 43 / 16 | 43 / 16 | 43 / 16 | ✓ |
| L3 | 24 / 6 | 24 / 6 | 24 / 6 | ✓ |
| I1 | 41 / 16 | 41 / 16 | 41 / 16 | ✓ |
| I2 | 61 / 19 | 61 / 19 | 61 / 19 | ✓ |
| I3 | 36 / 16 | 36 / 16 | 36 / 16 | ✓ |
| E1 | 12 / 5 | 12 / 5 | 12 / 5 | ✓ |
| E2 | 21 / 0 | 21 / 0 | 21 / 0 | ✓ |

**Zero disagreements** on counts and on the computed verdict. `validate.py --check
bundle_metadata_matches_graph` and `--check readiness_verdicts_agree` both pass independently.
The heatmap's own `Verdict` column (15 🔴 RED, 4 🟡 YELLOW, 1 🟢 GREEN — D9 — and D6 YELLOW-blocked)
therefore **contradicts nothing except the `stage13_status` fields inside the same metadata files**
(§9a). The numeric machinery is coherent; the human-set status strings are not.

## 11. Author / affiliation / front & back matter

All 21 bundles have `\author{}`, `\begin{abstract}`, `\maketitle`.

**Missing affiliation — 12 bundles:** F, D3, D4, D5, D8, D9, D10, D11, D12, I1, I2, I3.
(REVTeX 4-2 does not warn about this in these builds; verified `No \affiliation given` appears 0×
in every log — but every APS journal requires one.)

**Author-name and affiliation drift across the portfolio** (all one person):

| Form | Bundles |
|---|---|
| `\author{John Roehm}` | F, D1, D2, D3, D4, D5, D8, D9, D10, D11, D12, I1, I2, I3 |
| `\author{John G.\ Roehm}` | D6, L1, L3 |
| `\author{John G.~Roehm}` | D7 |
| `\author{John G. Roehm}` | L2 |
| `\author{J.~Roehm}` | E1, E2 |

| Affiliation | Bundles |
|---|---|
| `Independent Researcher` | D1, D2, L2, E1, E2 |
| `NetRxn Foundation` | D6, L1, L3 |
| `Independent research, USA` | D7 |
| *(none)* | F, D3, D4, D5, D8, D9, D10, D11, D12, I1, I2, I3 |

Three different affiliations for the same author across a single submission portfolio is a
consistency defect an editor will query. **Size:** `trivial`.

**PACS / keywords: absent from all 21 bundles.**

**Acknowledgements: present in 8** (D1, D2, D11, D12, L2, I3, E1, E2); absent from 13.

**Data-availability statement: absent from all 21 bundles.**

**Code / artifact-availability statement: present in exactly 1 — I1.** I1 has both a
"Code availability" heading (`paper_draft.tex:1777`, `:1780`) and concrete pointers
(`github.com/NetRxn/SK_EFT_Hawking` at `:1788`, `github.com/HEPLean/PhysLean` at `:1797`). The other
20 bundles have nothing. For a corpus whose central claim is *machine-checked formal verification*,
a reader who cannot locate the Lean artifact cannot verify the claim: D12 mentions
`github.com/RemyDegenne/testing-lower-bounds` (someone else's repo, at `:795`), D7 and I3 mention
"GitHub" in passing, and D2–D6, D8–D11, F, I2, L1–L3, E1, E2 mention no repository at all.
**Size:** `small` per bundle (a standard 3-line block), but it is 20 bundles.

## 12. Placeholder text

Grepping every draft for `TODO`, `FIXME`, `XXX`, `TBD`, `\todo`, `??`, `[cite]`, `lorem`,
`\section{}` with empty argument, `PLACEHOLDER`, `[REF]`, `citation needed`, `WIP`,
`\marginpar`, `to be written`, `FILL-IN`:

**Rendered (visible to a reader) — 7 hits, all legitimate subject matter, none are placeholders:**

| Location | Hit | Assessment |
|---|---|---|
| `papers/D11/paper_draft.tex:86` | "explicit in-source TODO" | describes a TODO in Mathlib, content |
| `papers/D12/paper_draft.tex:276` | "sits in an open \texttt{TODO} list" | content |
| `papers/I1/paper_draft.tex:589, 620, 809, 857, 1437` | `\texttt{PLACEHOLDER\_THEOREMS}` | the registry name; I1's subject matter |

No `lorem`, no `[cite]`, no `??` in source, no empty `\section{}`, no `\todo` macro anywhere.

**Unrendered (LaTeX comments) — 86 lines across 10 bundles.** These do not reach the PDF but they
mark unfinished lift work in the source:

| Bundle | comment placeholders | representative |
|---|---:|---|
| D3 | 21 | `:2373 %% TODO: lift content from papers/_phase6n_W1a_lean_only/paper_draft.tex`; plus 6× `%% D3 Stage-13 fix-pass 2026-05-11: header commented out (empty stub).` |
| I1 | 18 | `:312, :461, :545, :975 % TODO: substantive draft. Substrate to draw from:` — four sections whose substantive draft was never written |
| D1 | 13 | `:1185–1187 %% TODO: lift content … / ensure all numerical claims trace … / ensure all citations have primary-source cache entries` |
| D2 | 11 | `:1315 % [2026-05-04 cleanup: Wang2024 placeholder arXiv:2412.XXXXX → arXiv:2312.14928` |
| D4 | 9 | `:1531 %% TODO: lift content from papers/_phase6n_W1b_lean_only/paper_draft.tex` |
| D5 | 6 | `:1502 %% TODO: lift content from papers/_phase6n_W1c_writeup/paper_draft.tex` |
| I2 | 3 | `:1009–1011 %% TODO: lift content …` |
| L1 | 3 | `:384–386 %% TODO: lift content …` |
| D6 | 1 | `:17 %% Source manifest: papers/D6/source_manifest.md (TBD).` |
| L3 | 1 | `:442 %% (TODO content stubs intentionally suppressed — no prose change per lift notes.)` |

Eight bundles (D1, D2, D3, D4, D5, I1, I2, L1) additionally carry commented-out empty `\section`
headers with the boilerplate
`%% (Section heading + label commented out … empty post-bibliography stub from bundle_append.py
default-insertion; bookkeeping anchor preserved as LaTeX comment, no rendered content.)` — i.e.
`bundle_append.py` registered a source contribution for which no content was ever lifted.
**Not a rendering defect; it is a completeness signal.** I1's four `% TODO: substantive draft`
markers are the sharpest instance.

## 13. `validate.py` — paper/bundle-related checks

`uv run python scripts/validate.py --list` reports 63 checks. The paper/bundle-related subset and
its result (all run with `--no-archive`; `--check <name>` one at a time):

| Check | Result | Notes |
|---|---|---|
| `paper_latex_compiles` | **PASS (advisory) with 1 ⚠** | `✗ summary — 20/21 bundle drafts compiled clean … 1 with fatal errors`; `⚠ compile:D3 — D3: 2 fatal — first: ! Undefined control sequence.` Independently confirms §1. Note the check is *advisory* (`passed=True` unconditionally), so a non-building draft cannot fail the suite. |
| `bundle_consistency` | PASS | 3 clusters indexed, 2 cross-bundle; both exact-match, 0 flagged |
| `bundle_source_freshness` | PASS, 11 ⚠ | 9 freshness-stale (F, D1, D2, D3, D4, D5, L2, I1, E1) + 2 `stage13_redo_required` (D11, D12). **Side effect: rewrites 9 metadata files with identical content.** |
| `bundle_metadata_matches_graph` | PASS | 21 blobs vs live graph, 0 drift |
| `readiness_verdicts_agree` | PASS | heatmap and submission gate agree for all 21 |
| `readiness_submission_gate` | PASS, 64 ⚠ | 18 of 21 bundles have ≥1 blocked P1 gate; `FixPropagation` blocks 15, `NarrativeGrounding` blocks D5/D6/D10, `ParameterProvenance` blocks D12 |
| `bundle_registry_consistency` | PASS | 21 codes/tiers match `PAPER_STRATEGY.md` §6; no re-hardcoded rosters |
| `bundle_figure_integrity` | PASS | **only 7 figures checked** (D11×4, D12×3), all ≥8.66 pt; 21 other bundle figures unguarded |
| `citation_primary_sources_present` | PASS, 6 ⚠ | all year-drift advisories (preprint vs publication year): `Brylinski2002, Hietala2020VOQC, KMM2013, Lewis2021VerifQC, ReadRezayi1999, RossSelinger2016` |
| `count_literals` | PASS, 26 ⚠ | 107 hard-coded count literals across 64 papers; bundles affected: D2 (12), I3 (10), I2 (8), D9 (5), F (4), D5 (2), L1 (2), I1 (1), D3 (1) — e.g. `papers/D2/paper_draft.tex:584 "48 theorems"` |
| `numerical_literals` | PASS, 22 ⚠ | 116 inline literals; bundles: D1 (13), D3 (13), D5 (7), L1 (5), F (5), E1 (4), D4 (3), E2 (1) |
| `counts_fresh` | PASS | — |
| `tables_fresh` | PASS | — |
| `claim_clusters_fresh` | PASS | — |
| `axiom_count_prose_consistency` | PASS | — |
| `prose_theorem_reference_coverage` | PASS, 1 ⚠ | `waived:I1:gap_solution_bounded — papers/I1/paper_draft.tex:488` references a theorem that exists only as a commented-out stub at `TetradGapEquation.lean:307-321` |
| `theorem_name_embedded_citations` | PASS | — |
| `paper_toolchain_pin_drift` | PASS, 35 ⚠ | **29 pin-drift sites**; bundle sites: `D10:105` (4.29.1), `D11:546` + `D12:129` (c4843367), `D2:15` + `L2:12` (5e932f97), `D9:1074`, `E1:449/453/454`, `E2:484/485/488/489`, `I1:1182/1196`, `I3:1197`, `L2:387/396` — all against live `v4.32.0 / 81a5d257`. Plus 2 capability-claims in `D6:327` and `D6:787` that assert what the *pinned* Mathlib provides. |
| `review_docs_mint_findings` | PASS | — |
| `placeholder_not_cited` | PASS | — |

Not run (out of mechanical scope / slow, and not paper-readiness gates): `lean_build`,
`notebook_exec`, `graph_integrity`, `atlas_integrity`, and the physics-numeric checks.

---

## Cross-bundle observations

1. **The numeric machinery is trustworthy; the status strings are not.** Three independent sources
   (live regeneration, committed heatmap, per-bundle metadata) agree exactly on open-findings and
   blocker counts for all 21 bundles. The only inconsistency in the whole metadata layer is the
   human/agent-written `stage{9,10,13}_status` string, which reads `green` in 15 bundles that the
   same file's own computed `readiness` field marks `RED`. Any consumer that trusts
   `stage13_status` — including `docs/PAPER_STRATEGY.md` §3's "all bundles cleared GREEN" claim —
   is reading the one field with no invariant behind it.

2. **The compile gate is not enforced.** `docs/BUNDLE_LIFT_PROCEDURE.md` §7 makes a clean
   `pdflatex` a hard precondition for Stage 9. D3 does not build under that command yet carries
   green Stage 9/10/13. `validate.py --check paper_latex_compiles` catches it but is coded
   `passed=True` unconditionally and is skipped in the default suite — so nothing in the pipeline
   can fail on a non-building manuscript.

3. **PDFs are git-ignored build products that are being reviewed as if they were the manuscript.**
   Ten of 21 on-disk PDFs differ from their source; I1's and I3's differ in their *headline
   verification counts* by factors of 2 and 4. Reviews conducted against those PDFs read numbers
   that the source has not asserted since June.

4. **The formal-verification claim is not reader-verifiable in 20 of 21 bundles.** No
   data-availability statement anywhere; a code/artifact-availability statement in I1 only.

5. **Figure discipline splits cleanly.** D8, D9, D12 cross-reference all their figures; the other
   nine figure-bearing bundles cross-reference none or few, and D5/I1 contain no `\ref{}` at all.
   The automated figure guard covers only D11 and D12.

6. **Nine bundles have no figure and no table.** F, D2, D3, D4, D6, D7, D10, I3 (+D1 with one
   table). D3 is 59 pp with 31 sections, 114 subsections and zero visual content.

---

## What I could not check

- **Whether a citation supports the sentence it is attached to.** I verified only key resolution
  (`\cite` → `\bibitem`/`.bib`/`.bbl`), not semantic support. Zero dangling keys does not mean the
  citations are correct.
- **Whether uncited D5/D7 bibliography entries *should* be cited** (i.e. whether the defect is a
  missing `\cite` or a stale `\bibitem`) — that is a content call.
- **Bibliography entry correctness** (author/year/DOI accuracy). `citation_primary_sources_present`
  and `bibitem_title_primary_source` exist for this; I ran the former (6 year-drift advisories) but
  not the latter (it reads primary-source PDF caches and is slow).
- **Whether the fresh page counts are stable.** They depend on the current `docs/counts.tex`, which
  is **uncommitted-modified** in the working tree (`generated: 2026-08-01T00:52:59`, changing
  `test_files` 136→137 and `pytest_cases` 5000→5009). A commit or a `update_counts.py` run could
  shift text and therefore pagination slightly. My page counts are against the working tree as
  found.
- **Freshness of the D2/D6/D7/D10/D12/L2 PDFs is contaminated by concurrent auditors** rebuilding
  them in place during this audit window (2026-08-01 11:51–13:12 mtimes with fresh
  `.fdb_latexmk`/`.fls`). Those bundles read "not stale" for that reason; their pre-audit state is
  unknown to me.
- **REVTeX affiliation enforcement.** I confirmed 12 bundles have no `\affiliation` and that no
  build emits a `No \affiliation given` warning, but I did not check each target journal's exact
  submission requirement.
- **PRL word-equivalent budgets** for L1–L3/E1/E2 (which count figures, tables, captions and
  references, not just words). I report raw `texcount` word counts only; the word-equivalent
  computation is the tier auditors'.
- I did **not** run `lean_build`, `graph_integrity`, `notebook_exec`, or any physics-numeric check —
  outside mechanical scope and slow.
