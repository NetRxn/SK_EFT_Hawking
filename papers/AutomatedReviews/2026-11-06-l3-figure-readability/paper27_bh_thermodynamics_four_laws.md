---
paper: paper27_bh_thermodynamics_four_laws
bundle: L3
bundle_target: L3
reviewer: publication-source-assessment
review_date: 2026-11-06T00:00:00Z
kind: focused-source-consumer-follow-through
---

# Paper27 residual source-consumer findings

ROOT accepts integration ownership. The existing single-file author proposal is
held pending independent source review, actual canonical compilation and fresh
visual acceptance. These findings record residuals observed during the accepted
L3 figure repair; they do not duplicate or close the original physical four-laws
BUILD. The canonical remediation queue retains that original scientific objective.

### 1 — REQUIRED — Long body tokens visibly overflow and clip the compiled source paper

- **Severity:** major
- **Lane:** prose
- **Gate:** ManuscriptLength
- **Location:** `papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex`, Lean Formalization, Cross-wave compatibility and Acknowledgments.
- **Observed:** The actual seven-page PDF has three overfull boxes: 64.35905pt at source481–492, 21.95757pt at522–539 and211.58597pt at595–605. The module/review paths clip at the page edge and the retired theorem name intrudes into the gutter. No claim about when these defects first arose is made.
- **Evidence:** `SCOPED_REVIEW.md` independently inspected all eleven L3/Paper27 pages and located these defects in actual kept compiler logs; `EVIDENCE_R3.zip` preserves the actual compilation and visual evidence.
- **Expected:** Readable, contained body text with no clipped tokens or gutter intrusion, preserving scientific content and the accepted figure.
- **Fix:** Repair the unbreakable references or their reader-facing presentation, force the canonical out-of-tree compiler, and independently inspect the complete resulting paper. Do not waive typography or shrink the font.
- **Verify:** `uv run python -c "from pathlib import Path; from scripts.compile_bundle_pdf import compile_one; ok,msg,n=compile_one(Path('papers/paper27_bh_thermodynamics_four_laws'),keep=True,force=True); print(msg); assert ok and 'overfull=0' in msg"`
- **Cache:** Actual local compiled PDF/pages and retained source review.

### 2 — REQUIRED — The source-paper body contradicts the accepted local-versus-illustrative physics account

- **Severity:** major
- **Lane:** prose
- **Gate:** CrossPaperConsistency
- **Location:** Same manuscript, abstract/introduction, Acoustic branch, mechanics/third-law/entropy account and conclusion.
- **Observed:** The body calls the illustrative exponential the primary leading form/full coupled-ODE implementation, turns a disclosed late-time extrapolation into an infinite-affine-time guarantee, and describes conditional structures as a completed physical four-laws result. The accepted caption and actual implementation distinguish the local affine source calculation from the chosen exponential. Related echoes remain elsewhere in the body.
- **Evidence:** `SOURCE_REVIEW.md` and `SCOPED_REVIEW.md`; actual Balbinot primary sections near-horizon/fate, actual acoustic_evolution implementation, actual BHThermodynamicsFourLaws carrier/proof types and later local-profile declarations. Actual source must outrank stale comments and index misses.
- **Expected:** Accurate attribution and explicit hypotheses throughout the affected body, with the original complete physical objective and separate BUILD obligations retained. Truthful correction is not scientific construction or scope approval.
- **Fix:** Correct the false source/model/endpoint/completion descriptions and their necessary echoes; obtain independent source/prose review. Keep equations, accepted figure, scientific charter and outstanding physical construction intact. Related WKB/Lean attribution remains separate debt; do not infer global substrate absence.
- **Verify:** `uv run python -c "from pathlib import Path; s=Path('papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex').read_text(); assert 'which evolves the full' not in s; assert 'infinite} affine' not in s; assert 'The wave is structurally complete' not in s; assert 'local affine' in s and 'full four-laws' in s"`
- **Cache:** Held primary text and actual implementation; independent report required in addition to this bounded textual regression predicate.
