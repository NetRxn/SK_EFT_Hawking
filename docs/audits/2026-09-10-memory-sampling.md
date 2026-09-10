# Fixed-sample memory inference review

Scope: [SAMPLING.md](../dev-loops/MemoryProcesses/SAMPLING.md). Root files this receipt from independent reviewer reports and separate integration evidence. The scoped increment is accepted locally. No paper submission or public remote publication is part of this receipt.

## Independent design and implementation review

The design reviewer checked the fixed-sample Hoeffding/union-bound contract, exact dyadic confidence certificate, physical budget interpretation and power example. The accepted plan explicitly distinguishes confidence sufficiency, strict empirical separation and externally justified calibration assumptions.

CPU candidate `71a5de1c` passed independent source review, 200 combined memory tests in 0.22 seconds, 1,000 additional asymmetric rational cases, and four exact binomial null enumerations. The nonzero-budget null uses diagonal states with probabilities 1/2 and 5/8, a common identity continuation and measurement, and allowance 1/8. Exact null rejection probabilities checked were 1/32768, 242825/2147483648, 219048866627441/9223372036854775808 and 224723513577529/9223372036854775808. Boundary checks distinguish strict rejection from equality. No substantive findings remained.

The provenance-only follow-up `35aaae56` passed independent review. Its executable AST and tests were unchanged, and all four sampling theorem references resolved in the proof candidate. This source check was not described as a kernel build. Review packets R2 and R3 were fresh at the respective checks.

## Fresh scientific and cross-layer review

A separate fresh-context reviewer accepted proof candidate `7377ad1f` and the CPU implementation at integrated head `47f6add9`, with no findings. The review confirmed:

- Concentration is derived from bounded, measurable observations, centered sub-Gaussian moment bounds and within-group independence; neither tails nor joint coverage are assumed.
- Dyadic conversion, capping at one, joint coverage, confidence gating and strict rejection are consistent with Python's exact rational computation and downward exponent cap.
- The physical false-positive result consumes the existing common normalized channel/common binary effect bound, actual reset-distance hypotheses and separate observation-bias budgets.
- The power theorem consumes actual retained trajectories and post-reset distances. An explicit Bernoulli product law realizes binary sampling with means zero and 5/16 and certified detection probability at least 63/64.
- The usage guide distinguishes an illustrative count pair, a probability theorem, experimental assumptions and implementation verification.

The reviewer also enumerated 256 outcomes with perfectly dependent history groups formed from shared IID bits and their complements. Rejection and coverage-failure probabilities were both exactly 1/128, below the certified bound of 1/2. This independently checks the permitted cross-history dependence. The source-review packet remained fresh. The reviewer made no edits and ran no build, producer, controller or mutating MCP operation.

## Root integration evidence

Controller absorption rebased and integrated the proof as `e59c5051`. The source is identical to the reviewed proof candidate. The CPU source and tests remain identical to `35aaae56`. Aggregate import commit `61acb70d` passed `lake build SKEFTHawking.ExtractDeps` through the controller, producing epoch `e31fc45f9aaea97e6fd4dab7a851fc44f91c1d56e39f5afac17c2522e46e6fd5`. All slots were released. Root's integrated memory suite passed 200 tests in 0.23 seconds.

The proof worker's final diagnostics had no errors or warnings; seven principal axiom closures used only `propext`, `Classical.choice` and `Quot.sound`. Canonical extraction subsequently added 44 records, all in the new sampling module, with no changed or removed existing records. Every new extracted closure uses only standard core axioms, with no project axioms or dependency timeouts. The source has 15 public theorem declarations and three private proof helpers. The mechanical theorem census increases by 20 because it also classifies five proposition-valued structure projections as theorem records; those projections express sampling hypotheses and are not five additional proved statistical results. Counts retain the producer's classification unchanged.

The existing fast sync completed successfully, refreshing counts, dependency evidence and atlas views. It did not run a full citation-cache refresh or establish paper readiness.

## Acceptance

Independent integrated evidence review at `657114c3` found no issues. The reviewer independently confirmed source identity against both accepted candidates and reproduced the 44-added/zero-changed/zero-removed extraction comparison, closure audit and theorem/projection distinction. Its packet remained fresh; no duplicate test run or independent kernel build was claimed.

The `s13-lean` substrate gate passed in 537.3 seconds: 70/89 checks overall and 1,146 warnings, with no Lean/Python substrate failure. The 19 pre-existing paper-corpus failures remain separately reported and outside the owner-authorized scope. This is not a full-pytest or publication-readiness pass, and no gate, ratchet or paper state was weakened. S1–S3 are complete at the local feature-branch boundary; public main and remote were not updated by this increment.

## Interpretation limits

This is a fixed-sample conditional test of a specified comparison class. Valid physical/bias budgets and the sampling law remain hypotheses; a separate calibration failure event needs separate accounting. Adaptive stopping and selection among many tests require additional control. Python is not extracted from Lean, and exact arithmetic does not verify physical inputs or the runtime. No quantum-only memory, architectural identification, hardware demonstration or publication-readiness claim follows.
