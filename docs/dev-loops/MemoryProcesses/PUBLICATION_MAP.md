# D9 finite-memory contribution and evidence map

This work is homed in D9, **Kernel-Verified Quantum-Network and Device-Characterization Certification Substrate**, through `PAPER_DRAFT_MAPPING.md`. The earlier accepted scientific increment is [CALIBRATION_COARSE_GRAINING.md](CALIBRATION_COARSE_GRAINING.md). The extension is owned by [PROCESS_CLOCK_PROGRAM.md](PROCESS_CLOCK_PROGRAM.md); its final aggregate acceptance is separate from component source review.

## Publication disposition

D9's existing metadata has pending Stage 9/10/13 review and requires Stage 13 redo. The existing late-absorption protocol therefore selects D.0: home the contribution, set `absorption_queued`, and await the bundle's own remediation before manuscript absorption. This increment changes neither manuscript prose nor readiness verdicts and does not repair the pre-existing paper corpus. Once the bundle qualifies for absorption, use the existing D.4 sourceless path and Stage F review. This is an explicit publication home, not a new bundle or a submission claim.

## Claim-to-evidence map

| Scoped claim | Exact public evidence | Interpretation and remaining publication work |
|---|---|---|
| Retained environment can preserve distinguishable histories across reset; partial interaction separates reset leakage from environmental contribution | `FiniteMemoryProcess.lean`, `FiniteMemoryPartialInteraction.lean`: `partialPostReset_traceDist`, `partial_no_common_system_model`, `partial_control_gap` | Concrete finite witness with classical realizations. Explain common continuation, intervention and environment-reset control. No quantum-only claim. |
| A fixed binary test controls false positives and has nonzero power for an actual finite model | `BinaryMemorySampling.lean`: `certified_false_positive`, `partial_binary_witness`; `memory_sampling_certificate` | Sampling guarantees condition on valid externally supplied budgets. Preserve the older scope when comparing it with calibrated inference. |
| Fixed calibration and test observations jointly control rejection error with data-dependent reset/readout budgets | `BinaryMemoryCalibration.lean`: `physical_budget`, `calibrated_common_channel_false_positive`, `certified_common_channel_false_positive`, `model_binary_witness`; `memory_calibrated_sampling_certificate` | Trusted standards, diagonal reset structure, stable confusion law and fixed within-group independent trials remain assumptions. No optional stopping. Numerical example has total failure at most `3/256` and model power at least `253/256`. |
| A physically realized collision memory admits exact finite-history approximation and a matching obstruction | `FiniteMemoryCoarseGraining.lean`: `collision_linear`, `collision_density`, `run_traceDist`, `suffix_binary_prediction_bound`, `suffix_predictor_lower_bound`, `no_forgetting_lower_bound`, `finalSwap_readout`; `memory_history_approximation` | Common suffix attenuates initial memory by the retention product. Lower bound concerns arbitrary memory states at the suffix boundary. No arbitrary feedback, retained output records or general compression speedup. |

Module paths above are relative to `lean/SKEFTHawking/QuantumNetwork/`; all CPU functions are in canonical `src/core/formulas.py`. The [usage guide](CALIBRATED_USAGE.md) provides reproducible exact examples. Acceptance tests compare CPU trajectories against independently constructed joint matrix collisions, and scientific reviews distinguish the proved mathematical statement from the experimental applicability contract.

## Position relative to established work

Memory channels and forgetting are established subjects: Kretschmann and Werner, [Quantum Channels with Memory](https://arxiv.org/abs/quant-ph/0502106), study a general memory-channel framework and the decay of initializing-memory influence. Ciccarello and Giovannetti, [A quantum non-Markovian collision model: incoherent swap case](https://arxiv.org/abs/1305.0225), study memory through incoherent partial-SWAP collisions between bath components. These are contextual precedents, not claims that the present fresh-input replacement model reproduces their full setups or coding theorems. Their author-posted abstracts and bibliographic records were checked on 2026-09-10; no equation-level equivalence or exhaustive novelty search is asserted.

The contribution proposed for D9 is the checked connection between physical memory models, calibration-dependent statistical decisions and operational finite-history error/obstruction. The elementary inequalities and replacement-channel contraction are not advertised as newly discovered physics. A claim of first formalization would require a separate implementation/literature comparison; none is made here.

## Absorption brief

A future manuscript section should introduce one intervention experiment, expose its physical and statistical assumptions, state the calibrated exclusion theorem, and then show how a forgetting assumption changes what history must be retained. Use the sharp lower bound to show why truncation is conditional. Keep the exact CPU arithmetic distinct from Lean extraction, and the synthetic count example distinct from observed data.

Before publication: complete D9's existing repair/review cycle; select and review figures derived through the canonical pipeline; reconcile primary references at equation level; review all manuscript claims against extracted declarations; perform the existing disclosure and submission gates. These are bundle-owned obligations, not silently satisfied by this substrate increment.

Detailed section and figure preparation is in [D9_ABSORPTION_BRIEF.md](D9_ABSORPTION_BRIEF.md). Current manuscript labels, rather than historical section numbers, govern placement. The existing D.0 readiness requirement still gates insertion.

## Finite-process extension

The new instrument, process-tree and coherent-example modules extend this queued contribution. Place realized instruments and unnormalized branches in `sec:params`; outcome-dependent process trees and unpostselected prefix invariance in `sec:protocol`; the coherent intervention/reset example in `sec:worked`. Exact backing is `FiniteInstrument.branch_posSemidef`, `sum_trace`, `lift_branch_posSemidef`, `zero_outcome`; `FiniteInterventionProcess.normalized_weights`, `prefix_marginal`, `no_future_signaling`, `feedback_example_weights`; and `CoherentMemoryProcess.coherent_probability`, `measured_table`, `interference_contrast`, `reset_marginal`, `reset_probability`, `control_probability`, `no_common_system_model`.

The coherent default gives uninterrupted probability 49/625, measured 337/625, contrast 288/625 and reset-history probabilities 0 and 256/625. Explicit `coherent_readout_equivalence` and `reset_readout_equivalence` connect the Lean paths to the padded CPU readout shape. The canonical evaluators are `finite_intervention_process` and `coherent_memory_process`; their contracts are in PROCESS_CLOCK_USAGE.md. These results do not extend the older calibration or suffix-approximation guarantees to arbitrary adaptive protocols. Prefix invariance fixes the prefix and sums every future outcome. The reset witness excludes the stipulated common system-only continuation, not arbitrary classical hidden-state explanations.

`FiniteGibbsClock.matrixLog_gibbs` and `modular_eq_heisenberg` remain a separate finite-equilibrium physics follow-on. They are not yet a necessary D9 certification step or a proved bridge to intervention-dependent memory. D9 insertion and readiness remain unchanged behind D.0.
