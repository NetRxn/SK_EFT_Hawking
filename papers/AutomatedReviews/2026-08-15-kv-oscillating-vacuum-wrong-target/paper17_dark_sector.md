---
paper: paper17_dark_sector
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T00:00:00Z
readiness_gates_version: 1
kind: targeted-citation
sources_of_truth:
  - papers/paper17_dark_sector/paper_draft.tex
  - src/core/citations.py (CITATION_REGISTRY)
  - Lit-Search/Phase-5x/primary-sources/KV2008.pdf
---

# `KV2008` is cited for an oscillating-vacuum mechanism that paper does not contain

## Summary

**1 BLOCKER.** Found while remediating the Phase 6c F-1 Klinkhamer–Volovik
misattribution in the paper32 stakeholder notebook. The same author pair is
mis-targeted a second time, in a different paper: `paper17_dark_sector` attributes
the **oscillating-vacuum** mechanism to `KV2008` = Phys. Rev. D **77**, 085015 (2008),
*Self-tuning vacuum variable and cosmological constant*. That paper contains no
oscillation result of any kind. The oscillating effective vacuum energy density is
the companion paper, Phys. Rev. D **78**, 063528 (2008), *Dynamic vacuum variable and
equilibrium approach in cosmology* (arXiv:0806.2805), which is **not in the
registry at all**.

The claim paper17 makes is correct physics attributed to the wrong source, so this
is a citation fix plus a missing registry entry — not a retraction.

---

### 1.1 — 🔴 BLOCKER — paper17 cites the self-tuning paper for the oscillating-vacuum mechanism

- **Severity:** blocker
- **Lane:** `research`
- **Verify:** `uv run python -c "import re,sys; from src.core.citations import CITATION_REGISTRY as R; t=open('papers/paper17_dark_sector/paper_draft.tex').read(); ks=re.findall(r'oscillating-vacuum mechanism~.cite\{([^}]+)\}', t); sys.exit(0 if ks and all(any(R.get(k.strip(),{}).get('arxiv')=='0806.2805' for k in g.split(',')) for g in ks) else 1)"`
- **Gate:** CitationIntegrity
- **Location:**
  - `papers/paper17_dark_sector/paper_draft.tex:259` — `The companion KV oscillating-vacuum mechanism~\cite{KV2008} would predict an oscillating $w(z)$.`
  - `papers/paper17_dark_sector/paper_draft.tex:120` — the same claim in prose, uncited
  - `papers/paper17_dark_sector/paper_draft.tex:831` — the bibitem
  - `src/core/citations.py` — `KV2008` entry; no entry exists for PRD 78, 063528
- **Observed:** `KV2008` resolves to Klinkhamer & Volovik, *Self-tuning vacuum
  variable and cosmological constant*, PRD 77, 085015 (2008), arXiv:0711.3170. The
  paper16/17 prose additionally states "KV oscillations are Planck-scale in period
  (${\sim}10^{-44}$ s)", a quantitative claim sourced to that bibitem.
- **Evidence:** Measured 2026-08-15 against the cached primary source.
  - `pdftotext Lit-Search/Phase-5x/primary-sources/KV2008.pdf | grep -c -i oscillat`
    returns **0**. The full text of PRD 77, 085015 contains the string "oscillat"
    zero times. It is a *statics* paper: it introduces the vacuum variable `q` and
    shows the self-tuning nullification of the effective vacuum energy density.
  - arXiv:0806.2805 (KV, *Dynamic vacuum variable and equilibrium approach in
    cosmology*, PRD 78, 063528) is the paper whose abstract states the model gives
    "a flat Friedmann-Robertson-Walker universe with rapid oscillations of the
    effective vacuum energy density" that decay over time. CrossRef confirms
    `10.1103/PhysRevD.78.063528` → title, authors, PRD 78 (2008).
  - The 2010 framework paper's own reference list separates the two: `[3]` is PRD 77,
    085015 (self-tuning) and `[4]` is PRD 78, 063528 (dynamic / cosmology).
- **Expected:** The oscillating-`w(z)` claim cites the paper that predicts
  oscillations.
- **Fix:**
  1. Add a `CITATION_REGISTRY` entry (suggested key `KV2008b`) for Klinkhamer &
     Volovik, *Dynamic vacuum variable and equilibrium approach in cosmology*,
     Phys. Rev. D **78**, 063528 (2008), `10.1103/PhysRevD.78.063528`,
     arXiv:0806.2805 — CrossRef-verified 2026-08-15. Cache the primary source under
     `Lit-Search/Phase-5x/primary-sources/KV2008b.pdf` (required by
     `citation_primary_sources_present` once the key is cited).
  2. Repoint `paper_draft.tex:259` to the new key and add the matching `\bibitem`.
     `KV2008` stays cited at lines 80 and 227, where the self-tuning /
     tetrad-determinant claim is the right target.
  3. Re-run `paper17_dark_sector/claims_review.json` for the affected sentence —
     four chain-of-backing records name `KV2008` as target.
- **Blast radius:** measured 2026-08-15. `KV2008` is cited in exactly two drafts:
  `paper17_dark_sector` (3 sites) and `papers/D5/paper_draft.tex:212` (Volovik-style
  equilibrium — correct target, no change). No Lean docstring is affected:
  `lean/SKEFTHawking/QTheoryNoGoTheorem.lean:53` already cites PRD 77, 085015 /
  arXiv:0711.3170 for the 4-form realization, which is the correct target there.
- **Related:** `papers/AutomatedReviews/2026-04-29-0200-notebook-adversarial/paper32_strong_cp_de.md`
  F-1 — the first Klinkhamer–Volovik wrong-target citation, remediated 2026-08-15.
  Both arise from the same cause: the K–V q-theory corpus is a series of closely
  titled papers and the project has been citing whichever one is nearest to hand.
