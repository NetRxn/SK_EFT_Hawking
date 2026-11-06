# Independent main-based Gaussian polynomial IBP composition review

Task: l1-ibp-main-composition-review-r1; parent: publication-remediation.
Reviewer: /root/l1_ibp_main_composition_review. Acceptance reviewer/notebook writer: ROOT.
Candidate: /Users/johnroehm/.codex/worktrees/l1-main-delivery/SK_EFT_Hawking at HEAD 22da44f3493d946910c866f5cbce8aef187c5706 plus exactly the two assigned source paths.

Verdict: PASS_SOURCE_COMPOSITION. No actionable source, applicability, or composition defect found in the reviewed increment. This is a read-only source review, not fresh kernel checking or native main-candidate certification, full-wave review, merge permission, registry closure, or publication acceptance.

## Packet and custody

Packet: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-ibp-main-composition-review-r1.json
Both actual initial and final `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-ibp-main-composition-review-r1.json` calls exited 0 with `fresh: true`, `changed: []`. The packet says matching input snapshots grant no execution/completion authority. No packet/reference drift required reconciliation during this review. Only the two assigned /tmp report files were written. No repository/index/slot/notebook/artifact/registry mutation or revert occurred.

Read the packet references, primary current roadmap L1 successor scope and current notebook IBP entries, candidate CLAUDE.md, WAVE_EXECUTION_PIPELINE.md (especially theorem quality/build/review boundaries), AGENTS.md, CODEX_CONTINUITY.md, ADR-008, ADR-017, reviewer no-mutation/carrier-strength contract, author brief/raw receipts, author main composition/dependency receipts, and accepted auxiliary construction directly. This is a narrowly assigned source review; it does not purport to run the full paper adversarial-review procedure.

## Independently measured patch and dependency facts

- HEAD is exactly 22da44f3493d946910c866f5cbce8aef187c5706.
- `git --no-optional-locks status --porcelain=v1 --untracked-files=all`: only ` M lean/SKEFTHawking.lean` and `?? lean/SKEFTHawking/ADW/GaussianPolynomialIBP.lean`.
- `git diff --name-status 22da44f3493d946910c866f5cbce8aef187c5706 --`: only aggregate M. `git diff --cached --name-status`: empty. Therefore every other tracked input is unchanged relative to candidate base, with no staged delta; the only additional untracked input is the assigned module.
- Actual module is 3490 bytes, SHA256 ffb651c528b22d256b05e8a5ea5118ff3d6fb5bf917d00cd9544b25daccfb396. Direct bytes equal `git show f597f91e1:lean/SKEFTHawking/ADW/GaussianPolynomialIBP.lean`, /tmp/l1-GaussianPolynomialIBP-r1.lean, and the full source string in /tmp/l1-gaussian-polynomial-ibp-wt1-r1.json.
- Actual aggregate SHA256 8b84989b46fe0c57cef25596fde5cfee91d0e6711587c07d7bc948aa0d01e46b. Direct byte equality establishes it is exactly `import SKEFTHawking.ADW.GaussianPolynomialIBP` plus newline prepended to /tmp/l1-ibp-main-aggregate-preimage-r1.lean. That preimage is itself byte-identical to the HEAD22da aggregate blob. All prior aggregate bytes are preserved.
- lean/lean-toolchain SHA256 2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e; lean/lake-manifest.json SHA256 6620cd482acd9c924acd5715c07cb59f8cb840d605ad211c31c1666839516464. Each actual file is byte-identical to both HEAD22da and current primary counterpart.
- Parsed require arrays and global leanOptions are exactly equal across candidate, HEAD22da and primary. Full raw lakefile comparison shows the sole primary-vs-candidate difference is primary's appended separate NavierStokes lean_lib with its own autoImplicit=true. Existing source/require/global-options sections are byte-exact. The SKEFTHawking proof receives no project-option change; the separate library does not supply an import or premise.
- Direct new-module imports are exactly Mathlib.Probability.Distributions.Gaussian.Real, Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral, Mathlib.MeasureTheory.Integral.IntegralEqImproper, and Mathlib.Analysis.Calculus.Deriv.Polynomial. No project/frontier/physical module is imported. Text search found no pre-existing declarations with the three introduced names in the project source or lean_deps.json outside this module. This bounded search is not a new extracted dependency graph.

## Actual theorem and proof review

The final declaration SKEFTHawking.ADW.integral_mul_polynomial_gaussianReal has the sole binder `(p : Polynomial ℝ)` and states the actual Bochner-integral equality

`(∫ z : ℝ, z * p.eval z ∂gaussianReal 0 1) = ∫ z : ℝ, p.derivative.eval z ∂gaussianReal 0 1`.

Its carrier is actual Mathlib Polynomial ℝ and actual ProbabilityTheory.gaussianReal, not a project-defined averaging functional or desired-value wrapper. The checked local Mathlib source explicitly parametrizes gaussianReal by mean and variance; gaussianPDFReal is `(sqrt (2*pi*v))⁻¹ * exp (-(x-μ)^2/(2*v))`. Thus this is mean zero/variance one, without a shifted or fitted convention. There is no degree restriction, assumed integrability, moment hypothesis, Stein premise, abstract averaging, positivity of W, or nonzero denominator premise.

The integrability helper uses Polynomial.induction_on' over arbitrary sums and monomials. Every monomial degree n is arbitrary natural, so its real exponent satisfies -1<n. It instantiates actual Mathlib integrable_rpow_mul_exp_neg_mul_sq with b=1/2, rewrites real natural powers, and multiplies by arbitrary real coefficients. This establishes absolute Bochner integrability of p times the unnormalized Gaussian for every degree; it is not a finite low-degree moment table.

The weighted helper computes the derivative of exp(-z²/2) as -z exp(-z²/2), uses integrability for X*p (with a sign), derivative p, and p, then calls actual Mathlib integral_mul_deriv_eq_deriv_mul_of_integrable. I directly read that local theorem's type: all three product-integrability obligations are required. They are supplied here, and pointwise polynomial/Gaussian derivatives satisfy its support-local derivative requirements. Sign cancellation produces the stated positive equality. No boundary term is silently dropped: the invoked whole-line theorem discharges it from exactly these hypotheses.

The final proof rewrites both integrals via actual integral_gaussianReal_eq_integral_smul at nonzero variance one, unfolds the actual density, pulls out its common scalar normalization, and applies the weighted helper. Factoring the same normalization and applying congruence uses no division by W or potentially zero quantity. The integrability helper also applies to X*p and derivative p, so neither side is an accidental nonintegrable Bochner zero. Source contains no new axiom, sorry, native_decide, heartbeat override, or project/physical/tracked-assumption binder. Author receipts contain successful actual matching-slot diagnostics and standard-three-axiom outputs for all three declarations; those remain author/alternate-checkout evidence, not fresh independent or native-main evidence from this reviewer.

Mathematical normalization controls: p=X gives E[z²]=E[1]=1; p=X³ gives E[z⁴]=3 E[z²]=3. These are deductions from the reviewed statement and known probability normalization, not separately executed Lean control tests.

## Applicability to accepted Eq11 and exact remaining work

Directly read accepted ADW_EXACT_AUXILIARY_IDENTITY.md; SHA256 e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8 matches the brief. Its Eq11 is the undivided identity `∫ dμ W h_i exp(h.T) = sigma² ∫ dμ [partial_i W + W T_i] exp(h.T)`.

The new theorem is the correct one-dimensional standard-Gaussian brick for coefficientwise use: after finite nilpotent expansion, each real coefficient polynomial can be used as the entire insertion p. Applying differentiation to that entire insertion retains the derivative-of-W contribution. The theorem does not itself introduce W or the finite coframe algebra, prove multivariate/complex-coefficient lifting, or derive Eq11 at general sigma. Those are subsequent composition obligations, not hidden premises or completed claims.

All-degree Hermite lowering, factorial/parity identities, sigma scaling, the actual constructed finite signed/complex W and its compensation identity, original 128-generator coframe grading/nilpotence, C2 source/test preservation, and the full undivided observable construction remain owed. Physical B3 susceptibility/window, physical state/product/adjoint/metric, microscopic dynamics, physical frequency/transport, original scientific BUILD objectives, protected main integration, full required native/scientific/derived/publication gates and human publication review remain open. No original statement/permission/gate/registry/dependency was weakened or changed by the candidate.

## Verification boundary and commands actually run

Read-only shell operations: cat/sed/rg and rg --files for named contracts, packet references, source and local Mathlib definitions; continuity check twice; git rev-parse HEAD, --no-optional-locks status, diff --name-status, diff --cached --name-status, diff -- aggregate, show named commit:path, and ls-files for the new module. Python standard-library pathlib/hashlib/json/tomllib/subprocess/difflib compared the actual source/preimage/commit/receipt bytes, dependency bytes/parsed options, raw lakefile difference and accepted-construction hash. A quick MEMORY.md keyword search had no relevant hits and supplied no review evidence.

No Lean MCP call, tests, project validators, graph generation, native/scientific imports, slotctl, build, external fetch, source edits, staging, commit, lifecycle action or integration was performed. The two continuity adapter calls check snapshot freshness only. ROOT still needs the separate fresh matching-slot independent kernel review and authoritative exact-main-candidate gates; this report must not be relabeled as either.
