# Bundle D8 — Change Log

_Initial bookkeeping created 2026-05-31T14:04:05Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-31 — Lift-section from `D8_initial_draft` (§1)

- Source title: Kernel-Verified Universal Quantum Gate Compilation
- Lift action: Synthesize
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

## 2026-06-10 — Synthesize from `_phase6AN_W5_lean_only` (§NEW (verified compiler algorithm layer))

- Source title: `FKLW/CliffordTCompiler.lean`
- Lift action: Synthesize
- Insertion point: §NEW (verified compiler algorithm layer)
- Stage-13 redo required: yes
- Notes: Late absorption (sourceless): Phase 6AN W5 correct-by-construction Clifford+T compiler — Lean-only substrate

## 2026-06-10 — Synthesize from `_phase6AM_W5_lean_only` (§4 (RS efficiency layer + honest prime-density wall))

- Source title: Ross-Selinger **O(log 1/ε) T-count efficiency layer** + axiom-free §6-gate `P...
- Lift action: Synthesize
- Insertion point: §4 (RS efficiency layer + honest prime-density wall)
- Stage-13 redo required: yes
- Notes: Late absorption (sourceless): Phase 6AM W5 Ross-Selinger O(log 1/eps) efficiency layer + axiom-free Section-6-gate Prop + documented prime-density wall — Lean-only substrate

## 2026-06-10 — Synthesize from `_phase6AO_lean_only` (§4–§6 (RS Appendix-C chain + KMM third mechanism + kernel-purity uniformity))

- Source title: T1:** full Ross-Selinger App-C chain (C.2 `9c7781ec`, C.16 `13a7e602`, C.19 `...
- Lift action: Synthesize
- Insertion point: §4–§6 (RS Appendix-C chain + KMM third mechanism + kernel-purity uniformity)
- Stage-13 redo required: yes
- Notes: Late absorption (sourceless): Phase 6AO T1 RS Appendix-C chain + Z[zeta8]-Euclidean + Hyp-8.3 errata + sharp Lemma 4.4; T2 kmm_universal_headline; T3 native_decide elimination — Lean-only substrate

## 2026-06-10 — Synthesize from `_phase6AP_W3b_lean_only` (§NEW (compiled-gate diamond certificate))

- Source title: AKN diamond chain + END-TO-END compiled-gate channel certificate**: `diamondD...
- Lift action: Synthesize
- Insertion point: §NEW (compiled-gate diamond certificate)
- Stage-13 redo required: yes
- Notes: Late absorption (sourceless): Phase 6AP W3+W3b AKN diamond chain + end-to-end compiled-gate channel certificate — Lean-only substrate

## 2026-06-10 — Late-absorption prose authored (D.4 ×4) + citation merge + compile gate

- Authored the four late-absorption sections in full (replacing the `bundle_append.py` skeletons,
  relocated from the post-appendix fallback insertion site into the main body between the
  resource-lower-bound section and the Mathlib-portfolio section):
  - **§7 "From existence to a verified algorithm"** (`_phase6AN_W5_lean_only`): `cliffordTCompile`
    + termination / loop-init / loop-invariant / correctness contract (`cliffordTCompile_correct`),
    honest ε₀-cover word-length-constant residual, runtime-engineering scope reiterated.
  - **§8 "Optimal-length synthesis: the Ross–Selinger grid route and an honest number-theoretic
    wall"** (`_phase6AM_W5_lean_only`): `rossSelinger_log_length_explicit` (≤ N₃ + 8k; O(log 1/ε)
    exponent 1), `gridFindT_isSome_of_residual` + `rossSelinger_synth_of_residual` (the §6
    relative-norm gate made explicit), prime-density wall documented (RS Hyp 8.3 = Selinger Hyp 29);
    explicit-hypothesis-never-axiom posture stated.
  - **§9 "Completing the Ross–Selinger substrate, and a fully constructive third mechanism"**
    (`_phase6AO_lean_only`): §9.1 Appendix-C chain (C.2/C.16/C.19/obstruction/C.20-engine/C.21-iff)
    + Euclidean ℤ[ζ₈] (Mathlib-absent) + ℤ[√2][i]-impossibility catch + primary-source
    (1403.2975v3) verification note + sharp Lemma 4.4 product form (`oneDim_grid_exists_product`);
    §9.2 `kmm_universal_headline` (≤ 50400k+812; squared-ℓ² ≤ 9(2/4^k + 2√2/2^k); no prime-density
    input) as the third mechanism; §9.3 native_decide ×4 elimination → corpus-uniform kernel purity.
  - **§10 "From compiled gates to physical channels"** (`_phase6AP_W3b_lean_only`):
    `diamondDist_unitaryKraus_le` (½-diamond AKN), global-phase caveat AS a theorem
    (`diamondDist_unitary_smul_phase`), PhysLib trace-norm transfer (`traceNorm_eq_physlib`),
    row-sum→L² bridge, end-to-end `diamondDist_cliffordTCompile_le` (≤ √2·ε; √2 = bridge constant).
- Consistency updates (additive; no prior verdict overturned): abstract + intro contribution items
  7–9; Mathlib-portfolio additions (ℤ[ζ₈]-ED, SU(2) Euler Z–X–Z, Kronecker-with-identity L²-opnorm);
  scope §12 future-work paragraph updated (KMM/RS refinement now reported in §§7–10; runtime
  engineering + constant-factor optimization remain out of scope; ancilla-free RS wall stated);
  verification appendix extended (new module families; explicit-hypothesis + no-native_decide note).
- §5 citation merge: 5 new bibkeys — KMM2013ancilla (arXiv:1212.0822, PRL 110:190502), Selinger2015
  (arXiv:1212.6253), GilesSelinger2013 (arXiv:1212.0506), AKN1998 (quant-ph/9806029),
  Meiburg2025PhysLib (arXiv:2510.08672) — queued for CITATION_REGISTRY merge + primary-source
  caching (registry NOT touched in this pass per task constraints).
- `append_log.json` lift_action amended Lift-section → Synthesize for the 4 handles (matches the
  PAPER_DRAFT_MAPPING.md rows; the parser's fallback had recorded Lift-section).
- LaTeX compile gate: pdflatex + bibtex + pdflatex ×2 — 0 errors, 0 undefined citations/references,
  9 pp (was 5 pp). Stage-13 redo flagged (`stage13_redo_required=true`); reviewer triple (Stages
  9/10/13) is the separately queued Stage-F goal.
