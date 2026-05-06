# I3 Bundle Change Log

| Date | Event | Detail |
|---|---|---|
| 2026-05-04 | Bundle scaffolded | Pipeline Invariant #14 user-auth granted (Phase 6n Session 4). Bundle architecture goes 13 → 14. Scoping doc at `temporary/working-docs/phase6n/i3_bundle_scoping.md`. Substantive content drafting deferred to Phase 6o.ζ wave start. |
| 2026-05-08 | Substantive prose drafted (Phase 6o.ζ + Phase 7 absorption Session 5) | Full ~16-page software-paper draft authored covering Abstract + Introduction + Architecture + 6 Itô modules + 6 LDP modules + LDPCompatibleSKEFT cross-bridge + D3/D5/E1 cross-bridge positioning + Mathlib upstream coordination plan + Limitations + Reproducibility + Conclusion. Modeled on I2 Tier-3-software-paper template. Anchor-list audit pass against `docs/agents/claims-reviewer-bundle-prompts.md` §I3: (i) "first formalization" claims hedged with backed prior-art survey (Coq awesome-coq + Isabelle/HOL AFP probability-theory listing + Mathlib4 absence; HOL Light/Mizar/Agda not surveyed — explicitly disclosed); (ii) Mathlib substrate primary-source-verified — `Marion 2025 MarkovKernels` carry-forward misattribution corrected to `Degenne 2025 MarkovKernels` (arXiv:2510.04070, single author Rémy Degenne; verified via WebFetch arXiv abstract); Brownian-motion bibitem expanded to 4-author form Degenne–Ledvinka–Marion–Pfaffelhuber (arXiv:2511.20118); (iii) D3/D5/E1 consumer claims hedged — explicitly stated that no Lean theorem in those bundles currently invokes the typeclass; absorption events scheduled for post-Phase-6o unified absorption pass; (iv) Mathlib upstream coordination claims hedged — explicitly stated no Zulip/GitHub artifacts have been opened. Cross-cleanup: same Marion-attribution carry-forward fixed across `docs/PAPER_STRATEGY.md:192`, `docs/agents/claims-reviewer-bundle-prompts.md:290`, `docs/roadmaps/Phase6o_Roadmap.md:371`, `lean/SKEFTHawking/Itô/StochasticIntegral.lean:18`. pdflatex compiles 16 pages clean. |

## 2026-05-06 — Lift-section from `_phase6o_W3b_lean_only` (§1)

- Source title: I3 Itô + LDP-α + LDP-β substrate (`Itô/StochasticIntegral.lean` + `Itô/Quadra...
- Lift action: Lift-section
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: I3 sourceless initial lift (D.4): Phase 6o W3b Itô + LDP + LDPCompatibleSKEFT typeclass; 12 Lean modules; cross-bridge to Phase 6n W2c IsLDPRateFunction + Phase 6n W2a Glorioso-Liu monotonicity
