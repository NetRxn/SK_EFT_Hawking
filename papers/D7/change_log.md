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

## 2026-08-17 — Stage-10 full redraft

- Trigger: Stage-10 full redraft. The prior draft was a four-page skeleton of bracketed
  placeholders whose load-bearing claims no longer matched the Lean substrate or the
  primary sources. Every theorem cited was re-read as a statement; both primary-source
  PDFs were read at page level.
- Retitled. The prior title ("Classical Simulability and Quantum Advantage via Tensor
  Networks: A Formally Verified Demarcation") claimed three things the substrate does not
  contain: a simulability theorem, an advantage theorem, and a topological axis.
- **Tree claim withdrawn.** The proven equivalence is zero-rate ⟺ *four-cycle-freeness*
  (`loopCorrectionRate_eq_zero_iff_fourCycleFree`), not zero-rate ⟺ tree. The prior
  abstract, intro item 1 and contribution list all asserted the tree form. A bipartite
  6-cycle is four-cycle-free and cyclic.
- **Chern-bridge warrant withdrawn.** `categoricalChernExpansion`/`realSpaceChernAt`
  evaluate `c0 + c1*x`; the crystalline/quasicrystalline band-edge reading has no
  counterpart in Antão et al., where the Chebyshev argument is a rescaled Hamiltonian
  operator and ±1 are the two band edges of one spectrum. The Chebyshev substrate section
  and the combined-demarcation section were removed as claim-bearing sections; the
  combined theorem survives only as an anatomy inside the limits section. Filed as D7-03.
- **Kibble--Zurek material removed.** `surface_gravity_bounds_kzm_exponent` is equivalent
  to `μ < 1` after the positive factor `κ(1-δ)` cancels; and `νz/(1+νz)` is the
  freeze-out-time exponent, documented throughout `KibbleZurekUnruh.lean` as the
  defect-density exponent `dν/(1+νz)`, which coincides only when `d = z`. Tindall et al.
  measure `μ ≈ 2.70`--`2.75`, outside the `(0,1)` interval the module proves universal.
  Filed as D7-01 and D7-02.
- **Tindall attribution corrected.** The prior draft attached "matches the D-Wave
  Advantage2 annealer" to the 300+ qubit number. In the source the 300+ qubit run is the
  Kibble--Zurek extraction; the annealer comparisons are at 8×8 cylinders and ~50-qubit
  3D lattices, where the classical errors are *below* the annealer's on the cylindrical
  and diamond lattices and *comparable* on the dimerized cubic. Lattice names corrected to
  cylindrical / diamond cubic / dimerized cubic.
- **Substrate ahead of the manuscript, in one place.** The finite-horizon BP convergence
  layer (`rankLocalStep_converges`, `bpStep_rankLocal`, `bp_converges_on_ranked_acyclic`,
  `isFourCycleFree_of_bpRankCert`, `bp_converges_on_star`) was absent from the prior draft
  and is now the paper's headline.
- **Negative result added.** Every factor graph whose factors couple at most two variables
  on a simple interaction graph is four-cycle-free, so the rate is identically zero across
  every lattice in the motivating experiment, including the loop-of-size-three geometry
  whose loop correction that work had to compute. Filed as D7-07 for a Lean witness.
- Metadata: two non-existent names removed from `headline_theorems` (filed as D7-04);
  `apex_theorems` rewritten so no withdrawn claim binds to the abstract; `bundle_counts.tex`
  regenerated against the new closure and wired into the appendix.
- `target_journal` and `length_target` deliberately NOT changed; the mismatch is filed as
  D7-12 so it stays gated rather than resolved by the author who benefits.
- Findings: `papers/AutomatedReviews/2026-08-17-d7-stage10-redraft/D7.md` (12 records,
  every Verify executed and failing at HEAD).
- Compile clean at 10 pages; `bundle_prose_em_dash_free` and `bundle_reader_facing_voice`
  clean for D7.
