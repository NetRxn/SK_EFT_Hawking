---
paper: paper40_higher_curvature
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T01:58:00Z
readiness_gates_version: 1
prior_review: papers/AutomatedReviews/2026-04-28-0057-internal-adversarial/paper40_higher_curvature.md
---

# Adversarial Review (Re-invocation) — paper40_higher_curvature

## Re-invocation status

All four prior BLOCKERs and three prior REQUIREDs have closed under
independent verification. Two minor REQUIRED-grade drift residues
surfaced — comment-block references in `src/core/constants.py` and a
figure docstring `Source:` line in `src/core/visualizations.py` still
cite the retired `arXiv:1905.13728` and the wrong Berti venue
"`LRR 18, 1 (2015)`". These are non-load-bearing (comments / docstring
metadata, not consumed by any computation, paper bibitem, or Lean
docstring) but they are part of the same propagation surface that the
prior fix swept; leaving them in place violates the project's
fix-propagation discipline (Gate 11) and is a documented anti-pattern
in `feedback_strengthening_pass_paper_drift.md`. **No new BLOCKERs.**

Verdict: **PASSES at submission gate** for the seven prior findings. The
two new REQUIRED items below should be cleaned up before the next
submission window but do not block the current readiness state for
paper40 itself (the active artifacts — paper bibitems, registry,
provenance, Lean docstrings — are all clean).

## Verification of prior closures

| Prior finding | Verdict | Evidence |
|---|---|---|
| 1.1 (CalmetCapozzielloPryer2019 wrong-target → renamed to 2017) | ✅ closed | `arxiv.org/abs/1708.08253` returns "Gravitational Effective Action at Second Order in Curvature and Gravitational Waves" by Calmet, Capozziello, Pryer; CITATION_REGISTRY entry `CalmetCapozzielloPryer2017` (`citations.py:2111-2132`) carries arxiv `1708.08253`, DOI `10.1140/epjc/s10052-017-5172-3`, EPJC 77:589 (2017), `doi_verified: True`. paper bibitem updated (paper_draft.tex:379-384). All paper `\cite{}` sites use new key. |
| 1.2 (Berti2015 venue Living Rev → CQG) | ✅ closed | DOI `10.1088/0264-9381/32/24/243001` resolves (via IOP) to "Testing general relativity with present and future astrophysical observations", first author Emanuele Berti, CQG 32:243001 (2015). Registry entry (`citations.py:2133-2151`) updated. Paper bibitem updated. |
| 1.3 (six bibitems doi_verified None) | ✅ closed | All six (Vassilevich2003, ChristensenDuff1979, Stelle1977, Lovelock1971, CalmetCapozzielloPryer2017, Berti2015) now show `doi_verified: True` per registry inspection. |
| 3.1 (HC_OBS_BOUNDS not in constants.py; no provenance) | ✅ closed | `constants.py:2461-2464` defines `HC_BOUND_LIGO_C_SQ`, `HC_BOUND_PULSAR_C_SQ`, `HC_BOUND_SRG_R_SQ`, `HC_BOUND_CASSINI_C_SQ` inside `HIGHER_CURVATURE_PARAMS`. `observational_bound_check.py:20-37` imports them via `_load_hc_obs_bounds()`. `provenance.py:2756-2844` carries the four entries with tier=DERIVED, primary-source attribution (PRL 119:161101, PRL 98:021101, ApJ 829:55, Nature 425:374), `llm_verified_date: 2026-04-30`. `human_verified_date` still None — flag for submission gate. |
| 5.1 (Lean docstring "Calmet 2021"/"1905") | ✅ closed | `grep -n "2021\|1905" lean/SKEFTHawking/HigherCurvatureStructure.lean` returns zero hits. Three Calmet references in the file all read "Calmet, Capozziello, Pryer 2017" / "arXiv:1708.08253, EPJC 77:589 (2017)". Module rebuilds clean (`lake build SKEFTHawking.HigherCurvatureStructure` → "Build completed successfully"). |
| 6.1 (H_HC "tracked hypothesis" prose) | ✅ closed | paper §6 (paper_draft.tex:288-296) reads: "Unlike a typical tracked-hypothesis Prop, this predicate is *fully discharged* for B = 10^59 inside the module … The parameterisation over B is a forward-compatibility hook". |
| 7.1 ("62 orders" anchoring) | ✅ closed | paper_draft.tex:253-268 contains explicit `\paragraph*{Anchoring the "62 orders below" claim.}` with `|c_Riem(N_f=27)| = 27/180/(4π)² ≈ 9.49 × 10^{-4}` and ratio computation. `tests/test_higher_curvature.py::TestObservationalBounds::test_largest_predicted_at_SM` PASSES (asserts `1e-5 < v < 1e-2`). |

## Findings (re-invocation, fresh-eye sweep)

### 1.1 — 🟡 REQUIRED — Stale Calmet/Berti references in `src/core/constants.py` block-comment header

- **Gate:** CitationIntegrity (Gate 1) / FixPropagation (Gate 11)
- **Location:** `src/core/constants.py:2419-2422`
- **Observed:**
  ```
  # - Calmet et al., arXiv:1905.13728 — observational bounds on α, β
  #   from short-range gravity (Eöt-Wash) + post-Newtonian (Cassini)
  # - Berti et al., LRR 18, 1 (2015) — GW & pulsar bounds in modified
  #   gravity
  ```
  Both references are retired: `arXiv:1905.13728` is the hallucinated
  graph-NN paper (per Finding 1.1 of the prior review), and
  `LRR 18, 1 (2015)` is the wrong venue (Finding 1.2). The active
  registry, paper bibitems, and Lean docstrings have all been updated
  to `1708.08253` (EPJC 77:589, 2017) and `CQG 32:243001 (2015)` —
  these block-comments did not propagate.
- **Evidence:** `grep -rn "1905.13728\|LRR 18" src/core/` → two hits in
  constants.py (lines 2419, 2421) plus three citation_registry-internal
  hits (in the corrective `notes` field of `CalmetCapozzielloPryer2017`,
  which legitimately mentions the retired ID for traceability) and the
  visualizations.py docstring (Finding 1.2 below).
- **Expected:** Block-comment lines updated to:
  ```
  # - Calmet et al., arXiv:1708.08253, EPJC 77:589 (2017) — observational bounds on α, β
  # - Berti et al., CQG 32, 243001 (2015) — GW & pulsar bounds
  ```
- **Fix:** Two-line edit in `src/core/constants.py`. Non-load-bearing
  but completes the fix propagation per Gate 11.
- **Cache:** N/A (comment-only)

### 1.2 — 🟡 REQUIRED — Stale Calmet/Berti references in `src/core/visualizations.py` figure docstring

- **Gate:** CitationIntegrity / FixPropagation
- **Location:** `src/core/visualizations.py:10212-10213`
- **Observed:**
  ```
  Source: Calmet, Capozziello, Pryer, arXiv:1905.13728 (bounds);
          Berti et al, LRR 18, 1 (2015) (pulsar timing);
  ```
  This is the docstring of the `fig_higher_curvature_obs_bounds` figure
  function consumed by paper40's Figure 1 caption. The docstring
  metadata is not load-bearing for the figure rendering, but it is
  the canonical inline source attribution that any reader scanning the
  visualization module will trust as ground truth.
- **Evidence:** `grep -n "1905.13728\|LRR 18" src/core/visualizations.py`
  → lines 10212-10213. Same pattern as Finding 1.1.
- **Expected:** Docstring `Source:` lines updated to current registry
  identifiers (1708.08253 EPJC 77:589 / CQG 32:243001).
- **Fix:** Two-line docstring edit.
- **Cache:** N/A

### 3.1 — 🟡 REQUIRED — `HC_BOUND_*` provenance entries lack `human_verified_date`

- **Gate:** ParameterProvenance (Gate 3)
- **Location:** `src/core/provenance.py:2771-2772, 2794-2795, 2817-2818, 2840-2841`
- **Observed:** All four entries (`HC_BOUND_LIGO_C_SQ`,
  `HC_BOUND_SRG_R_SQ`, `HC_BOUND_PULSAR_C_SQ`, `HC_BOUND_CASSINI_C_SQ`)
  have `llm_verified_date: '2026-04-30'` and `human_verified_date: None`.
- **Evidence:** Direct read of provenance.py.
- **Expected:** Per Gate 3 ("LLM verification unblocks computation;
  human verification … unblocks paper submission"), `human_verified_date`
  must be set before submission. CLAUDE.md Pipeline Invariant 8
  reinforces this. Acceptable at draft stage.
- **Fix:** Provenance dashboard human-verification pass on each of the
  four entries; populate `human_verified_date`. This is a workflow
  step, not a code edit.
- **Cache:** N/A

### Other classes — no findings

- **Class 2 (parameter drift from primary sources):** Section §3 closed-form coefficients $(\alpha, \beta, \gamma) = (-N_f/(324(4\pi)^2),\, -41 N_f/(4320(4\pi)^2),\, +17 N_f/(4320(4\pi)^2))$ verified by independent linear-system solve against $(c_R, c_{\mathrm{Ric}}, c_{\mathrm{Riem}}) = (-5/2160, +7/2160, -12/2160)$ from Christensen-Duff. Match.
- **Class 4 (cross-paper contradictions):** Vassilevich2003 shared with paper39 — same arXiv ID, same title; ChristensenDuff1979 shared — same DOI; no contradictions surfaced.
- **Class 5 (narrative overclaims):** No "first formally verified" / "first in any proof assistant" claims. The "62 orders below" feasibility claim is now anchored with explicit numerics (Eq. 6 of paper) and reproduced in `tests/test_higher_curvature.py::TestObservationalBounds`. The "tightest by ~3 orders of magnitude" claim is verified arithmetically: $10^{62}/10^{59} = 10^3$. ✓
- **Class 6 (undisclosed assumptions):** `higher_curvature_below_pulsar_bound` carries `0 < N_f` and `N_f ≤ 100`; both disclosed in §5 prose ("natural fermion-count window") and in the §6 Lean code-block (line 232 of paper_draft.tex). ✓
- **Class 7 (count literal drift):** `\higherCurvatureThms{}` and `\higherCurvatureTests{}` macros sourced from `docs/counts.tex` via `\input{}`. No inline count literals. ✓
- **Class 8 (production run health):** Paper makes no claims of Monte Carlo / numerical-simulation evidence. `grep` of "Monte Carlo|numerical evidence|simulation evidence" returns zero matches. Gate 8 N/A.

## QI Candidate

The pattern repeats: a citation-integrity fix sweeps the active code
path (registry, paper bibitems, Lean docstrings, Python docstrings on
formula functions) but leaves stale block-comment headers and
non-essential figure-docstring `Source:` lines pointing at the retired
identifier. This is the same "comment drift" failure mode flagged in
`feedback_strengthening_pass_paper_drift.md` and is structurally
identical to the `feedback_python_lean_refs_drift.md` pattern but on
the comment surface rather than the binding surface.

**Recommended QI:** Extend `validate.py --check formula_lean_refs_resolve`
to also grep all `.py` files under `src/core/` for substring matches
against any *retired* identifier listed in CITATION_REGISTRY entries'
`notes` field (i.e., notes like "Earlier draft … cited a hallucinated
2019 reference (arXiv 1905.13728 …)" should make `1905.13728` itself a
forbidden substring elsewhere in `src/core/`). Same pattern for retired
venues. Cheap grep, catches this exact class of residual drift.
