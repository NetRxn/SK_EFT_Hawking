# Legacy draft compile triage — 2026-08-12

**What this is.** The legacy (non-bundle) `papers/*/paper_draft.tex` corpus, compiled with
`scripts/compile_bundle_pdf.py --all --force` on 2026-08-12: **47 of 64 drafts clean**.
This document files the 14 drafts that fail on fatal LaTeX errors so they enter the
remediation queue with a lane, a target and a verification command (ADR-012 D1/D4).

**Not a new gate, and deliberately not one.** `paper_latex_compiles` already ratchets this
exact population at `LEGACY_DRAFT_LATEX_BROKEN_CEILING = 14`, zero headroom, and the live
count is 14 — the ratchet is correct and holds the line against growth. What it does
**not** do is route the work: no lane, no target, no owner, nothing to schedule or
parallelise on. That gap is the whole reason ADR-012 exists, and filing a second check
beside a working one is the failure C9 names. These findings point *at* the ratchet.

**Severity is `minor`, and that is a measurement rather than a courtesy.** None of these
drafts is a publication bundle; all 21 bundles compile clean. They are legacy source
material, already disclosed as inherited debt whose repair is ADR-010 scope. Filing them
`major` would push a corpus-wide ratchet above its ceiling on arrival, and a gate that
fires on correct work gets switched off — this repository has that lesson recorded twice.

**Three further drafts fail the compile gate on unresolved markers rather than TeX errors**
(`note_rt_ch_bounds`, `paper39_heat_kernel_expansion`, `paper44_riemannian_connection`).
They are filed separately below, because they are a different defect and only one of them
was reachable by any check.

---

## Findings

### 1 — 🔵 `paper11_quantum_group` does not compile: ! Undefined control sequence.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper11_quantum_group/paper_draft.tex`
- **Observed:** 4 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Undefined control sequence.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper11_quantum_group` reports FAIL with
  `tex_errors=4`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper11_quantum_group`

### 2 — 🔵 `paper16_graphene_sk_eft` does not compile: ! Missing $ inserted.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper16_graphene_sk_eft/paper_draft.tex`
- **Observed:** 2 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Missing $ inserted.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper16_graphene_sk_eft` reports FAIL with
  `tex_errors=2`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper16_graphene_sk_eft`

### 3 — 🔵 `paper17_dark_sector` does not compile: ! Undefined control sequence.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper17_dark_sector/paper_draft.tex`
- **Observed:** 6 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Undefined control sequence.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper17_dark_sector` reports FAIL with
  `tex_errors=6`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper17_dark_sector`

### 4 — 🔵 `paper21_majorana_rung` does not compile: ! LaTeX Error: Unicode character ∧ (U+2227)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper21_majorana_rung/paper_draft.tex`
- **Observed:** 22 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character ∧ (U+2227)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper21_majorana_rung` reports FAIL with
  `tex_errors=22`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper21_majorana_rung`

### 5 — 🔵 `paper22_ew_phase_transition` does not compile: ! LaTeX Error: Unicode character Λ (U+039B)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper22_ew_phase_transition/paper_draft.tex`
- **Observed:** 5 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character Λ (U+039B)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper22_ew_phase_transition` reports FAIL with
  `tex_errors=5`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper22_ew_phase_transition`

### 6 — 🔵 `paper25_gravitational_waves` does not compile: ! LaTeX Error: Unicode character Γ (U+0393)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper25_gravitational_waves/paper_draft.tex`
- **Observed:** 13 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character Γ (U+0393)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper25_gravitational_waves` reports FAIL with
  `tex_errors=13`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper25_gravitational_waves`

### 7 — 🔵 `paper26_bh_entropy` does not compile: ! Double subscript.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper26_bh_entropy/paper_draft.tex`
- **Observed:** 6 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Double subscript.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper26_bh_entropy` reports FAIL with
  `tex_errors=6`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper26_bh_entropy`

### 8 — 🔵 `paper2_second_order` does not compile: ! LaTeX Error: Unicode character ✓ (U+2713)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper2_second_order/paper_draft.tex`
- **Observed:** 4 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character ✓ (U+2713)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper2_second_order` reports FAIL with
  `tex_errors=4`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper2_second_order`

### 9 — 🔵 `paper31_vestigial_inflation_no_go` does not compile: ! Double subscript.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper31_vestigial_inflation_no_go/paper_draft.tex`
- **Observed:** 1 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Double subscript.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper31_vestigial_inflation_no_go` reports FAIL with
  `tex_errors=1`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper31_vestigial_inflation_no_go`

### 10 — 🔵 `paper33_ewbg_chirality_wall` does not compile: ! LaTeX Error: \mathsf allowed only in math mode.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper33_ewbg_chirality_wall/paper_draft.tex`
- **Observed:** 9 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: \mathsf allowed only in math mode.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper33_ewbg_chirality_wall` reports FAIL with
  `tex_errors=9`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper33_ewbg_chirality_wall`

### 11 — 🔵 `paper40_higher_curvature` does not compile: ! LaTeX Error: Unicode character ℝ (U+211D)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex`
- **Observed:** 9 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character ℝ (U+211D)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper40_higher_curvature` reports FAIL with
  `tex_errors=9`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper40_higher_curvature`

### 12 — 🔵 `paper43_einstein_cartan` does not compile: ! Double subscript.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper43_einstein_cartan/paper_draft.tex`
- **Observed:** 6 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! Double subscript.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper43_einstein_cartan` reports FAIL with
  `tex_errors=6`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper43_einstein_cartan`

### 13 — 🔵 `paper7_chirality_formal` does not compile: ! LaTeX Error: Unicode character ι (U+03B9)

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper7_chirality_formal/paper_draft.tex`
- **Observed:** 2 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Unicode character ι (U+03B9)`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper7_chirality_formal` reports FAIL with
  `tex_errors=2`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper7_chirality_formal`

### 14 — 🔵 `paper8_chirality_master` does not compile: ! LaTeX Error: Environment theorem undefined.

- **Severity:** minor
- **Lane:** prose
- **Gate:** `paper_latex_compiles` (legacy ratchet)
- **Location:** `papers/paper8_chirality_master/paper_draft.tex`
- **Observed:** 2 fatal LaTeX error(s) under `pdflatex -halt-on-error`. First: `! LaTeX Error: Environment theorem undefined.`
- **Evidence:** `uv run python scripts/compile_bundle_pdf.py paper8_chirality_master` reports FAIL with
  `tex_errors=2`. Measured 2026-08-12 across the whole corpus (47/64 clean).
- **Expected:** the draft compiles to a PDF with zero fatal errors.
- **Fix:** repair the source. The dominant class is a **literal Unicode maths character**
  in text mode (∧ Λ Γ ℝ ι ✓) — replace with its LaTeX command inside maths mode. The rest
  are `Double subscript.` (add braces), an undefined control sequence (missing package or
  a typo), and one missing `theorem` environment declaration (`\newtheorem`).
- **Verify:** `uv run python scripts/compile_bundle_pdf.py paper8_chirality_master`

### 15 — 🔵 Two legacy drafts render an unresolved citation as `[?]` and no check can see it

- **Severity:** minor
- **Lane:** infra
- **Gate:** *(none — this is the gap)*
- **Location:** `scripts/validation/checks/papers_prose.py`
- **Observed:** `compile_bundle_pdf._unresolved_markers` counts two reader-visible marker
  classes: `??` for an unresolved `\ref` and `[?]` for an unresolved `\cite`. Only the
  first has a static check. `note_rt_ch_bounds` and `paper39_heat_kernel_expansion` each
  render a `[?]` in their compiled PDF, and every validation check passes on that tree.
- **Evidence:** `pdftotext papers/paper39_heat_kernel_expansion/paper_draft.pdf -` contains
  `[? ]`; `bundle_cross_references_resolve` reports the legacy corpus at its ceiling, and
  `citation_primary_sources_present` checks `\bibitem` coverage, not `\cite` resolution.
- **Expected:** a `\cite` whose key has no `\bibitem` in the draft's input closure is
  caught before a reader sees `[?]`, on the same terms as the `\ref` leg.
- **Fix:** ⚠️ **NOT auto-approved.** ADR-010 §6a requires establishing what existing
  machinery covers a defect, describing the residue, and asking before building. The
  residue is described here; the cheap option is a third leg on
  `bundle_cross_references_resolve` reusing `draft_input_closure`, at a frozen legacy
  ceiling — but a `\cite` can also resolve through BibTeX rather than a literal
  `\bibitem`, so the leg needs the closure walk to cover `.bbl`/`.bib` before it is sound.
- **Verify:** `uv run python scripts/validate.py --check bundle_cross_references_resolve`
- **Needs-operator:** queue

### 16 — 🔵 `paper44_riemannian_connection` references a section label that does not exist

- **Severity:** minor
- **Lane:** prose
- **Gate:** `bundle_cross_references_resolve` (legacy ratchet)
- **Location:** `papers/paper44_riemannian_connection/paper_draft.tex`
- **Observed:** `\ref{sec:bundle-leviCivita}` has no `\label` anywhere in the draft's input
  closure, so the PDF renders `§ ??` twice. This is the whole live population of the legacy
  dangling-reference ratchet frozen 2026-08-12.
- **Evidence:** `uv run python scripts/validate.py --check bundle_cross_references_resolve`
  names it; `pdftotext` on the compiled PDF shows two `??` sites.
- **Expected:** the reference resolves, or is repointed to the label that exists.
- **Fix:** the D3 precedent is the likely shape — the target section exists under a
  different label and the reference was never repointed. Find the intended section and fix
  the reference; do not add an empty label to silence it.
- **Verify:** `uv run python scripts/validate.py --check bundle_cross_references_resolve`
