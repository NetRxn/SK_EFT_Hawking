# D3 — First-Claim Ledger

**Bundle:** D3 — Emergent gravity through black-hole thermodynamics: the substrate predictive boundary.
**Gate:** NarrativeGrounding / first-claim (mirrors `papers/D8/first_claims.md` pattern).
**Created:** 2026-06-10, from the review-2026-06-05 D3-Y3 remediation (4 unhedged first-formalization claims; zero "to our knowledge" hedges in the draft).

Each "first" claim in the D3 draft, its location, the prior-art search performed, and the verdict. All claims are now phrased with "to our knowledge" hedging in the draft.

---

## Claim 1 — Centre-matching identity (CFL emergent Z₃ = QCD centre Z₃)

- **Location:** `paper_draft.tex` §17 subsection "Centre-matching identity (first-formalization claim)" (line ~1244).
- **Phrasing:** "To our knowledge this centre-matching identity has not previously been stated or checked in any proof assistant."
- **Search performed (2026-06-10):** the proof-assistant physics-formalization landscape (PhysLean/physlib — Lean 4 physics digitalization; mathlib4; Isabelle/AFP). No formalization of color–flavor-locked (CFL) phase structure, diquark condensates, or QCD centre-symmetry data exists in any of these ecosystems; the published proof-assistant physics corpus covers quantum information, chemical physics, special-relativity axiomatics, and (recently) scattered QFT/GR substrate — nothing touching dense-QCD phase identifications.
- **Finding:** The identity `CFL_emergent_Z3_matches_QCD_center_Z3` is a project-specific bridge (Hirono–Tanizaki topological-order framing carried as a tracked-hypothesis Prop); no plausible prior machine-checked statement located.
- **Verdict:** HOLDS. Hedged.

## Claim 2 — Levi-Civita Christoffel uniqueness on indefinite-signature (Lorentzian) metrics

- **Location:** §22 subsection "Levi-Civita Christoffel uniqueness on Lorentzian metrics" (line ~1790).
- **Phrasing:** "was --- to our knowledge --- not previously formalised on Lorentzian (indefinite-signature) metrics in any proof assistant."
- **Search performed (2026-06-10):** web search for Levi-Civita-connection formalizations (mathlib, Lean, proof assistants generally) surfaced only mathematical references, no indefinite-signature formalization; mathlib's Riemannian-geometry development (which the draft already acknowledges as covering the positive-definite case) and physlib's `PseudoRiemannianMetric` substrate (verified on disk 2026-06-08, `docs/assessments/UpstreamContributionDisposition.md`) provide the metric *types* but not the indefinite-signature uniqueness theorem.
- **Finding:** No prior proof-assistant formalization of Levi-Civita uniqueness at indefinite signature found. Note for future re-verification: physlib's GR substrate is moving quickly; re-run this search before submission.
- **Verdict:** HOLDS under its precise reading (indefinite-signature case; Riemannian case explicitly credited to Mathlib). Hedged.

## Claim 3 — Penrose singularity-theorem hypothesis bundle (predicate-level)

- **Location:** §24 "Penrose singularity hypothesis bundle + Riccati focusing core" (line ~1945).
- **Phrasing:** "To our knowledge this is the first machine-checked formalization of the Penrose singularity-theorem hypothesis bundle in any proof assistant; we state the claim's scope precisely: it is a predicate-level formalization (hypothesis bundle, Riccati-focusing core, and biconditional under an explicit applicability predicate), not a full differential-geometric proof of the 1965 theorem."
- **Search performed (2026-06-10):** four web searches across the Lean/Isabelle/Coq/HOL ecosystems for Penrose-singularity-theorem, GR-singularity-theorem, and Raychaudhuri-equation formalizations. Found NO formalization of any GR singularity theorem in any proof assistant. Closest prior art: (a) Schutz' independent axioms for *Minkowski* spacetime, Isabelle/AFP entry `Schutz_Spacetime` (2021; J. Autom. Reasoning 2022, arXiv:2108.10868) — special relativity axiomatics, no curvature, no singularity content; (b) PhysLean/physlib (Lean 4) — GR/spacetime substrate types, no singularity theorems; (c) mathlib4 — differential geometry (manifolds, bundles, recent Riemannian metrics) with no Lorentzian causality theory.
- **Finding:** No prior art at any scope. Because the project's formalization is predicate-level (trapped-surface/global-hyperbolicity/NEC predicates + the Riccati ODE focusing core + correctness-push biconditional under `IsADWPenroseApplicable`), the draft now states this scope explicitly rather than leaving "first-formalization Penrose" open to the stronger full-theorem reading.
- **Verdict:** HOLDS at its (now explicitly stated) predicate-bundle scope. Hedged and scoped.

## Claim 4 — Cross-bundle bridge mention (D3 ↔ I1 shared first-formalization claims)

- **Location:** §28 subsection "Cross-bundle bridges" (line ~2234).
- **Phrasing:** "share the first-formalization claims (each hedged ``to our knowledge''); I1 is the primary, D3 the supplement."
- **Search performed:** none required beyond Claims 2–3 (this is a pointer to the same algebraic-GR-backbone claims, not an independent claim); I1 carries the primary versions and its own Stage-13 anchor list.
- **Finding:** The mention now signals the hedging discipline explicitly so the bridge sentence cannot be quoted as an unhedged first claim.
- **Verdict:** Pointer only. Hedged by reference.

---

*Searches performed 2026-06-10 during the review-2026-06-05 D3/L1 remediation pass; recorded here as ledger evidence per the D8 Gate-10 pattern. Re-verify all four before submission if competing formalizations appear (physlib GR and mathlib Riemannian geometry are active areas).*
