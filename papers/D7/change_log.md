# Bundle D7 — Change Log

_Created 2026-06-10 with the review-2026-06-05 D7-EV3 remediation. Append history accumulates per the bundle-lift convention._

## 2026-06-10 — Continuous loop-correction rate function (review-2026-06-05 finding D7-EV3)

- Source: external review finding D7-EV3 (verified): `loopCorrectionRate` was a `{0,1}`-valued tree indicator dressed as an "LDP rate" (`if IsTreeFactorGraph G then 0 else 1`), disclosed in the draft as a limitation.
- Action: substantive upgrade shipped in `lean/SKEFTHawking/BPLDPSimulability.lean` — `loopCorrectionRate G := ⨆ θ, -log (bernoulliLoopMgf G θ)`, the Cramér/Legendre transform at zero deviation of the log-MGF of the Bernoulli loop-presence observable with success parameter `loopDensity G` (4-cycle density). Closed form `-log(1 - p)` proven via explicit `IsLUB` argument; zero-rate ⟺ tree proven (not definitional); strict positivity on loopy graphs; strict monotonicity in loop density; threshold ⟺ density characterization; exact finite-n Cramér identity; Bernoulli-KL bridge discharging `SKEFTHawking.LDP.IsCramerIIDUpperBound`; worked K_{2,2} value `log(4/3)` (kernel `decide`).
- Headline rename + restatement: `bp_convergence_iff_ldp_below_threshold` → `bp_convergence_iff_ldp_rate_zero` (consumes `loopCorrectionRate G = 0`); `analog_hawking_quantum_advantage_demarcation` restated accordingly (finite factor-graph instances added). Deleted as false-under-upgrade: `ldpSimulabilityThreshold`, `loopCorrectionRate_eq_one_of_not_tree`, `loopCorrectionRate_le_one`, `loopCorrectionRate_below_threshold_iff_tree` (replaced by `loopCorrectionRate_le_iff_loopDensity_le`).
- Draft edits: abstract, intro item 1 (former limitation paragraph → description of the shipped rate function), contribution list, §sec:ldp-bp stub, Discussion scope items (i)/(iii); theorem count 65 → 81; new bibitem `ChertkovChernyak2006LoopSeries` (J. Stat. Mech. (2006) P06009) for the honest residual-scope note.
- Honest residual: rate attaches to the combinatorial loop-presence observable (4-cycle density, the tree-predicate granularity); attachment to the dynamical Chertkov-Chernyak loop-series terms over the BP message space remains future work.
- Stage-13 redo required: yes (anchor list updated in `docs/agents/claims-reviewer-bundle-prompts.md`).
- Deferred to coordinator: `CITATION_REGISTRY` backfill for `ChertkovChernyak2006LoopSeries` (citations.py concurrently owned), ExtractDeps/counts regen.
- pdflatex ×2 clean; `lake build` clean (9248 jobs); headlines kernel-only `[propext, Classical.choice, Quot.sound]`.
