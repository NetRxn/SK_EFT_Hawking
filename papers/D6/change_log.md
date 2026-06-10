# Bundle D6 — Change Log

## 2026-06-10 — Review-fix batch (D6-EV1/R3): prior-art positioning + first-claim hedges

- Source: external review 2026-06-05 findings D6-R3/EV1 (accuracy fixes only; full bundle lift remains deferred to Phase 6v close per user directive — `stage10_status` stays `skeleton`).
- Lift action: accuracy remediation (no structural lift).
- Insertion point: abstract (hedge + novelty scoping); §1 new `\paragraph{Prior art: formally verified quantum computation.}` between Motivation and Bundle-architecture paragraphs; §5 (BellNegativity claim hedge); bibliography (+3 bibitems, top of list).
- Content: (1) abstract claim hedged "to our knowledge" + precise novelty scope (end-to-end kernel-verified chain code→measurement→compiler→universal logic; circuit-level verified optimizers exist); (2) prior-art paragraph engaging VOQC/SQIR (`Hietala2020VOQC`, POPL 2021, arXiv:1912.02250), Qbricks (`Chareton2021Qbricks`, ESOP 2021, LNCS 12648 pp. 148–177, arXiv:2003.05841, Crossref-verified), Lewis–Soudjani–Zuliani survey (`Lewis2021VerifQC`, ACM TQC 5(1) Art. 1 (2024), DOI 10.1145/3624483, Crossref-verified); (3) BellNegativity "first entanglement measure" → hedged + scoped "to our knowledge, the first kernel-verified entanglement measure"; (4) rendered internal-docs paths (`docs/PAPER_STRATEGY.md` ×2, `docs/PAPER_DRAFT_MAPPING.md`, `docs/BUNDLE_LIFT_PROCEDURE.md`) inlined/dropped (build-infra `\input{../../docs/counts.tex}` + schema comment retained). Registry: `Chareton2021Qbricks` NEW (doi_verified=True, arXiv-PDF cached); `Hietala2020VOQC` + `Lewis2021VerifQC` used_in += D6; Lewis upgraded to published ACM TQC metadata.
- LaTeX compile gate: PASS (pdflatex ×2, zero errors, all citations resolve).
- Citation gate: `validate.py --check citation_primary_sources_present` PASS.
- Stage-13 redo required: NO new substantive claims (hedges narrow claims; prior-art paragraph is positioning) — but the deferred Phase-6v-close full-bundle Stage 13 must cover the new §1 paragraph.

## 2026-06-01 — Phase 6AA absorption into §6 (W-state)

- Source: Phase 6AA — Verified Quantum-Network Substrate (`lean/SKEFTHawking/QuantumNetwork/`, 8 kernel-only modules).
- Lift action: additive subsection §`sec:wstate:envelope` ("Protocol-level extension: a verified network-fidelity envelope").
- Insertion point: end of §6 (W-state), after the SK cross-bridge.
- Content: dB↔Np attenuation identity; Werner swap fidelity + monotonicity; BBPSSW flagship cubic + DEJMPS; Fortescue-Lo finite-round W-state yield; Werner-iterated end-to-end + the `swapChain_fidelity_envelope` capstone (model-independent fidelity envelope).
- LaTeX compile gate: PASS (latexmk clean). Leak-clean (no private-product framing).
- Stage-13 redo required: YES — D6 §6 grew substantively; the Phase-6v-close adversarial pass must cover the new subsection.

## 2026-05-31 — Inline-absorption-record (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Inline-absorption-record
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: D8 cross-bridge absorption 2026-05-31: D6 paper_draft.tex edited to re-point/cross-reference the new D8 bundle (verified-quantum-compilation corpus). D4 retains Fibonacci/topological anchor; D6 consumes D8's SK primitive. Scoped adversarial re-check of the new cross-bridge paragraph only (additive cross-ref to already-GREEN D8).
