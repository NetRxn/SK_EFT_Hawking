# Phase 6a Wave 9 `/goal` prompt — center-bridge C (Frolov–Fursaev induced-gravity 1/4)

Third link of the center-bridge discharge. PREREQUISITE: run AFTER Waves 8 + 7B. Authorized
2026-06-13 with the induced-gravity / γ-irrelevant narrative. Full context:
`docs/roadmaps/Phase6a_Roadmap.md` → "RE-OPENED 2026-06-13" § Wave 9, and the research report
`Lit-Search/Phase-6a/6a-Immirzi-area-gap-independence-for-Wave8.md`.

---

GOAL: Phase 6a Wave 9 (6a.9) — prove the honest, NON-VACUOUS conditional that the Bekenstein–Hawking
leading coefficient is `1/(4 G_N)` in the ADW Sakharov substrate WITHOUT γ-tuning:
`H_Sakharov(fully induced / no bare action) ∧ (S_BH = S_ent) ⟹ leadingCoefficient = 1/(4 G_N)`.
The substantive content is the shared Seeley–DeWitt `a₂` ratio: the SAME `a₂` that induces `G_N`
also fixes the horizon entanglement entropy `S_ent`'s area term, ratio exactly 4 (Frolov–Fursaev–
Zelnikov hep-th/9607104; Jacobson gr-qc/9404039; Susskind–Uglum hep-th/9401070). Closes Gate A.2;
the 1/4 becomes derived (induced-gravity sense), not phenomenological. PREREQUISITE: Waves 8 + 7B
landed. PUBLIC repo (SK_EFT_Hawking). Read CLAUDE.md, docs/WAVE_EXECUTION_PIPELINE.md,
docs/roadmaps/Phase6a_Roadmap.md (RE-OPENED § Wave 9), the research report
`Lit-Search/Phase-6a/6a-Immirzi-area-gap-independence-for-Wave8.md` (mechanism + citations), and
`HeatKernelExpansion.lean` + `MicroscopicCoefficientMatch.lean` FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new project-local
`axiom` — if the conical-heat-kernel area term can't be made constructive, ship a tracked-hypothesis
Prop (the `H_VerlindeKMLiteralSumDerivation` / `H_MicroscopicCoefficientMatch` pattern: witness +
falsifier + register in `PERMANENT_TRACKED_HYPOTHESES.md`), NEVER an axiom, NEVER a `sorry`; NO
`native_decide`; NO `maxHeartbeats` in proof bodies (decompose to `have`); never weaken a statement
to pass. PARALLEL AGENT shares `main`: stage ONLY your own paths (never `git add -A`/`-a`/`.`), never
push, no `rm -rf .lake/build`. Dev loop = lean-lsp MCP; `lean_verify` each new theorem; lean4
semantic search (not grep) for Mathlib/physlib decls.

ANTI-VACUITY (HIGHEST PRIORITY this wave — the research agent explicitly flagged the failure mode):
neither antecedent may contain `S = A/4G`. `H_Sakharov` is the fully-induced / no-bare-action
condition — reuse `α_ADW = 1 ⟺ δG = 0` from `MicroscopicCoefficientMatch.matchResidual_eq_zero_iff_alpha_unity`.
`S_BH = S_ent` is the entanglement identification (Sorkin/Bombelli). The ratio-4 MUST come from the
ACTUAL `a₂` algebra (HeatKernelExpansion's Christensen-Duff/Vassilevich coefficients), NOT be
assumed. Apply preemptive-strengthening checklist #5 (defining-the-conclusion) to the conditional —
if making the entropy function `:= A/4G` would trivialize it, the substantive load must sit in the
`a₂`-ratio lemma, not the definition.

REUSE (the G_N side is DONE — do not rebuild):
- `HeatKernelExpansion.lean`: `a0_dirac`, `a2_R_coefficient`, `G_N_from_a2`,
  `G_N_from_a2_eq_G_N_sakharov`, `DiracHeatKernelAsymptotic`.
- `MicroscopicCoefficientMatch.lean`: Dirac-witness + perturbed-α-falsifier template,
  `H_MicroscopicCoefficientMatch`, `matchResidual_*`.
- `RTReplicaTrickOnMTC.lean`: `topologicalEntanglementEntropy`.
- `LinearizedEFE.lean`: `G_N_sakharov`, `G_N_emerg`. `BHEntropyMicroscopic.lean`: `kaulMajumdarS`
  leading term (for the consistency theorem).

NEW CONTENT:
- C1 — `entanglementEntropyAreaLeading` : the leading area-law-divergent horizon entanglement
  entropy as a function of the SAME `a₂` coefficient used by `G_N_from_a2` (conical-deficit heat
  kernel). If the conical derivation is too heavy, state the `a₂`→area-coefficient relation as a
  tracked-Prop per the no-axiom fallback — prefer the genuine derivation.
- C2 — `H_Sakharov` Prop (fully induced / no bare action; reuse α_ADW=1 ⟺ δG=0).
- C3 — THE THEOREM `frolov_fursaev_quarter_coefficient` : `H_Sakharov → (S_BH = S_ent) →
  leadingCoefficient = 1/(4 * G_N)`, substantive content = the shared-`a₂` ratio-4 (`norm_num`-backed
  where the 4 is load-bearing).
- C4 — consistency theorem: the induced-gravity 1/4 equals the MTC-framing leading coefficient
  (`kaulMajumdarS`'s `A/(4G)` term) — the two routes agree.
- C5 — Dirac witness (free-Dirac instance satisfies `H_Sakharov`, gives ratio 4) + falsifier
  (α_ADW ≠ 1 / bare action present → coefficient ≠ 1/4; OR `S_BH ≠ S_ent` → match fails).

PAPER: update paper26 to the clean division of labor — induced gravity → 1/4 (leading,
γ-independent; corroborated by Bianchi 1204.5122; resolves the Hossenfelder counting-vs-
thermodynamics tension since γ sets neither route's coefficient), MTC counting → −3/2 log.
Bundle-aware (PAPER_STRATEGY / PAPER_DRAFT_MAPPING).

CLOSURE: full validate.py; file-gate + `lake build` of new/changed modules + ExtractDeps;
`lean_verify` axiom-purity on every new theorem; CLOSE Gate A.2 in Phase6a_Roadmap;
update_counts.py + Inventory + Inventory_Index + Wave-9 status; if a tracked-Prop fallback was used,
register it in `PERMANENT_TRACKED_HYPOTHESES.md` + flag for user review; Stage-13 for paper26.

/goal autonomous mode: the stop hook is a GO signal, not coercion — do the next increment THIS turn.
Ship kernel-pure increments across auto-compacts until C1–C5 + paper + closure are done. NEVER
"hold" / "await direction" / "next session" / context-budget reasoning. Blocked on a user-only
decision → diligence first, take the clearly-best option (or the no-axiom tracked-Prop fallback),
flag for review, keep shipping everything else.
