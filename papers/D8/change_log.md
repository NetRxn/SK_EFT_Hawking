# Bundle D8 — Change Log

_Initial bookkeeping created 2026-05-31T14:04:05Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-31 — Lift-section from `D8_initial_draft` (§1)

- Source title: Kernel-Verified Universal Quantum Gate Compilation
- Lift action: Lift-section
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Sourceless synthesis (D.4): Phase 6p/6t/6u/6x/6x-prime/6y/6z verified-quantum-compilation corpus. Authorized 2026-05-31 per Pipeline Invariant #14.

## 2026-05-31 — §7 draft authored + figures + citations

- Authored full synthesis `paper_draft.tex` (8 sections + verification appendix); 3 schematic figures via `src/core/visualizations.py` (`fig_d8_alphabet_dimension_map`, `fig_d8_su8_density_duality`, `fig_d8_sk_recursion`) rendered to `figures/`.
- §5 citation merge: 10 \cite keys; 7 new bibkeys (BMPRV1999, ReadRezayi1999, Brylinski2002, AaronsonGottesman2004, Mukhopadhyay2024, KMM2013, RossSelinger2016) + 2 prior-art (Hietala2020VOQC, Lewis2021VerifQC) added to CITATION_REGISTRY with cached primary sources; all arXiv IDs web-verified (incl. correction AaronsonGottesman = quant-ph/0406196). LaTeX compiles clean (latexmk, 5pp, 0 undefined).

## 2026-05-31 — Reviewer triple GREEN; Bundle D8 CLOSED at GREEN

- **Stage 9 (figure review):** round 1 found 2 cosmetic Fig-1 text-truncation defects; fixed (`cliponaxis` + right-margin widen + note reword); re-review GREEN.
- **Stage 10 (claims review):** 84 sentences, 0 FAIL, 1 non-blocking WARN (module attribution for `cliffordCCZLiteral_dense`, fixed). All D8 honesty anchors verified. GREEN.
- **Stage 13 (adversarial):** round 1 = 0 BLOCKER / 2 REQUIRED (prior-art positioning vs VOQC/survey; first-claim ledger) / 4 RECOMMENDED. Both REQUIRED + substantive RECOMMENDEDs (6.1 conditional-substrate disclosure, 6.2 dyadic→rational wording) remediated; re-run GREEN (0 BLOCKER, 0 REQUIRED).
- Closures recorded in `docs/review_finding_supersessions.json`; first-claim ledger at `papers/D8/first_claims.md`.
- **Bundle D8 CLOSED at GREEN 2026-05-31** (single-session authoring + review). Heatmap 🟢. Out-of-scope (recorded): runtime compiler / vendor tuning / cert formats / length-optimality (separate engineering deliverable); D4/D6 one-paragraph D8 cross-bridge prose deferred to their next absorption pass (D4 already in the 2026-05-29 stale backlog).
