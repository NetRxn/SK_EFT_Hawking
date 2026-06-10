# Bundle L1 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-letter from `paper25_gravitational_waves` (§1)

- Source title: GW170817 vs vestigial graviton
- Lift action: Lift-letter
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Initial lift: paper25 → L1 PRL splash (GW170817 vestigial-graviton falsifier; voucher candidate; Phase 6a W2)

## 2026-05-06 — Lift-section from `_phase6o_W1b_lean_only` (§4)

- Source title: G4 Kerr-Schild double-copy on Petrov-D analog gravity
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1b Kerr-Schild single-copy as alternative substrate context to vestigial graviton; cross-ref-only

## 2026-06-10 — Review-fix (review-2026-06-05 L1-EV1 / L1-EV2)

- Source: (none — prose-precision remediation from the 2026-06-05 external review)
- Lift action: Prose-revision (abstract bound precision + Vergeles provenance correction)
- Insertion point: abstract; §1 (intro, c_GW definition); §2 (vestigial-susceptibility natural-range paragraph)
- Stage-13 redo required: no (claims made more precise; numerical content unchanged; body already carried the asymmetric bound)
- Notes: (EV1) Abstract now states the asymmetric Abbott et al. constraint −3e−15 ≤ Δc/c ≤ +7e−16 with the conservative two-sided envelope in parentheses, matching the body (§1 lines ~104-106, unchanged). (EV2) Vergeles attribution corrected against the cached primary source (Lit-Search/Phase-5d/primary-sources/Vergeles2025.pdf, PRD 112, 054509 = arXiv:2506.00036v2 "Unitarity of 4D Lattice Theory of Gravity"): the paper contains NO RPA bubble integral, NO metric-channel susceptibility, and NO [0.1,10] range (keyword-sweep verified: 0 hits for RPA/bubble/susceptib/natural range/vestigial/second sound/graviton). The draft no longer attributes the bubble integral or the range to Vergeles; the RPA closed form is credited to the project's VestigialSusceptibility.lean formalization, the [0.1,10] window is stated as a project-adopted ±1-decade naturalness window about the dimensional-analysis scale O(Λ_UV²/16π²), and the Vergeles citation is retained for what the paper actually establishes (unitarity of the underlying Einstein–Cartan–Palatini lattice theory). The inaccurate "half-decade window" wording was also corrected. NOTE for provenance registry: PARAMETER_PROVENANCE['GW.CHI_VEST_NATURAL_LOWER'/'UPPER'] proposed human-verify notes (src/core/provenance.py ~2697-2750) carry the same misattribution ("Vergeles 2025 ... derives χ_RPA = ...") — flagged for dashboard correction; not edited here (outside this fix's file scope).
