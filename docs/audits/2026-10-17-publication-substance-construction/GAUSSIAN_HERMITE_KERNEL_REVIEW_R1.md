# Independent ordinary L1 Gaussian-Hermite source/kernel review R1

Verdict: PASS_SCOPED_SOURCE_AND_KERNEL. No actionable mathematical or kernel finding in the assigned increment. This is an independent review of one-variable real polynomial support, not acceptance of the complete auxiliary transform, physical B3, a publication, or a global build.

Candidate: public wt1 at bfb8ca2576ccdfb25ad2ebf3bebc1a2bfb7d9fc0, parent f597f91e12704b30e8b31ace0f38bd32f2e6aff3.
Only commit change: lean/SKEFTHawking/ADW/GaussianPolynomialHermite.lean, 135 insertions, 7011 bytes.
SHA256: 2d4f1dee5432252a28aca49038f870ecdb98ea06122eafa1cfa121d1f27c5893.
Imported project IBP module SHA256: ffb651c528b22d256b05e8a5ea5118ff3d6fb5bf917d00cd9544b25daccfb396.
Toolchain manifest: leanprover/lean4:v4.32.0; Mathlib inputRev 81a5d257c8e410db227a6665ed08f64fea08e997.

## Custody and actual checks

The exact assigned continuity packet was checked independently before source/MCP review and after the calls. Both returned fresh=true, changed=[], exit 0. No packet refresh was performed.
Packet:
 /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-l1-hermite-kernel-review-r1.json
Assigned slot:
 /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/wt1

ROOT supplied admission, supported by its prepare receipt: public wt1 ACTIVE, matching endpoint skeft_wt1, epoch 03a2919fc0e331e6b2a3d731b4055c90d9a03e69c0293156ac90a8b3ceb3cbbd. Its live-status receipt reports capacity_complete=true with no capacity errors/conflicts. I did not rerun controller or process discovery. Actual matching MCP calls succeeded, despite the stale registered tool description claiming no lease. This establishes working matching diagnostic access during this review, not an independently reissued lease or machine-wide capacity certification.

Actual independent calls:
- lean_diagnostic_messages on the new module: success=true, timed_out=false, items=[], failed_dependencies=[].
- lean_verify(scan_source=true) on every 16 exports listed below, each with exactly propext, Classical.choice, Quot.sound and warnings=[].
- lean_goal at lines 23,54,63,69,76,83,100,126,133: goals_after=[] at each. The general induction successor at 63 and public identity at 69 close with arbitrary n and p.
- lean_hover_info on the core identity, bounded coefficient corollary, squared norm, gaussianReal, and Mathlib hermite: actual elaborated types agree with the source.
- Additional independent diagnostics and lean_verify on all three project IBP declarations: clean diagnostics, same three axioms, warnings=[].
- Author's axioms/diagnostics receipts were inspected as corroboration, not substituted for independent calls.

All full actual MCP inputs and outputs, including content and structuredContent, are retained in the companion JSON.

## Mathematical source review

Read the entire new module and entire GaussianPolynomialIBP module, the original accepted ADW_EXACT_AUXILIARY_IDENTITY.md (SHA256 e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8), relevant live notebook/roadmap scope, governing role and continuity documents, and the imported Mathlib definitions and whole-line IBP theorem.

1. The measure is ProbabilityTheory.gaussianReal 0 1 : Measure ℝ. Its second argument is variance, and 1 is nonzero. Mathlib defines it by volume.withDensity gaussianPDF and supplies IsProbabilityMeasure. It is neither a custom expectation nor a zero-variance Dirac measure.
2. integrable_polynomial_gaussianReal proves genuine integrability for every real polynomial by the withDensity criterion and the existing unnormalized Gaussian polynomial theorem. That imported theorem uses a genuine Gaussian integrability estimate for each monomial, then polynomial induction. The derivative polynomial and every product in the recurrence are covered. No totalized nonintegrable integral escape is used.
3. realHermite is precisely Mathlib's integer hermite mapped into ℝ[X], with evaluation identified with aeval. Mathlib hermite starts at 1 and uses X*p-p.derivative, hence He_1=X and He_2=X²-1. This is probabilists' scaling and correct sign.
4. The successor proof applies actual Gaussian IBP to realHermite n * p. Product differentiation produces both He_n' * p and He_n * p'; the former cancels the recurrence term. Its uses of integral_add/sub have explicit integrability proofs. The imported IBP proves the Gaussian derivative and uses whole-line integration by parts with integrability, rather than assuming Stein's identity.
5. integral_realHermite_mul and integral_hermite_mul quantify every n : ℕ and p : ℝ[X], with no Stein premise, moment premise, or degree cap. Their RHS is the actual integral of (derivative^[n] p). No hidden section binders or vacuous antecedent occurs.
6. integral_hermite_mul_pow holds for every n,k. It gives k.descFactorial n times the actual moment of z^(k-n), with natural subtraction harmless when k<n because the descending factorial vanishes. It is a reduction to actual Gaussian moments, not a newly proved closed formula for all those moments.
7. The bounded coefficient corollary assumes p.natDegree≤n and correctly yields n!*p.coeff n. This bound is necessary: for larger degree, higher polynomial terms can contribute (e.g. n=0,p=X²). It is not a bound on the carrying all-order identity. Below-degree vanishing follows from the actual iterated derivative being zero; n=0 does not make the general theorem vacuous.
8. Monicity/degree are inherited from Mathlib. Off-diagonal orthogonality splits n<m and m<n and uses commutativity appropriately. Diagonal squared norm equals n! for all n. No finite degree ceiling occurs.
9. Source scans and full proof reading show no sorry, native_decide, new axiom, heartbeat override, or truth-placeholder trick. Transitive axiom checks on every export and all imported project theorems contain only the standard three.

## Export inventory

Every name below is under SKEFTHawking.ADW and independently lean_verify checked:
integrable_polynomial_gaussianReal;
realHermite (noncomputable abbrev);
eval_realHermite;
realHermite_succ;
integral_realHermite_succ_mul;
integral_realHermite_mul;
integral_hermite_mul;
integrable_hermite_mul;
integral_hermite_mul_pow;
integral_hermite_mul_eq_zero;
integral_hermite_mul_eq_factorial_coeff;
integral_hermite_mul_pow_eq_zero;
integral_hermite_mul_pow_self;
natDegree_realHermite;
integral_hermite_mul_hermite_of_ne;
integral_hermite_mul_hermite_self.

Imported project checks:
integrable_polynomial_mul_gaussian;
integral_mul_polynomial_gaussian_weight;
integral_mul_polynomial_gaussianReal.

## Relationship to original accepted construction and remaining debts

Eq.6: the new all-n,k mixed monomial result supplies a genuine one-dimensional coefficient identity underlying E[He_n(z) exp(tz)] = t^n exp(t²/2). It does not itself assert an exponential-integrability theorem, equality of formal series, the multivariate product identity, arbitrary sigma scaling, or the complete weighted transform.

Eq.11: the imported polynomial IBP correctly differentiates the full polynomial insertion. Applying it coefficientwise to W times a truncated exponential is compatible with the derivative-of-weight term; dropping that term is not licensed. The new Hermite result extends these coefficient identities to all Hermite orders, but does not assemble Eq.11 with arbitrary variance and complex multivariate W.

Still required for native formal acceptance of the complete accepted construction:
- arbitrary sigma>0 scaling, inverse sigma factors and measure change;
- independent finite-dimensional product Gaussians, multivariate polynomial integrability/Fubini, multi-index derivatives/factorials and Hermite products;
- complex coefficients and signed/complex W without positivity assumptions;
- precise finite truncation P, formal exponential coefficient equality, multiplication and cancellation, then evaluation into the actual commuting even nilpotent Grassmann algebra with the correct degree bound;
- actual source coframes, compact Spin(4) links, oriented plaquette/action conventions and couplings; fermion/Berezin orientation and determinant assembly; finite compact link integration/exchanges;
- composite-source normalization and response/Legendre assembly and nonzero Z where normalized correlators are claimed.

Unchanged physical L1/B3 debts include state/order/background, physical metric-channel susceptibility and independently justified normalization/stability window, constrained tetrad fluctuations and propagating modes, spin/polarization and matter coupling, matched retarded/Kubo transport with units/band control, calibration/vacuum scale/uncertainties, and thermodynamic/continuum/simulation qualification. No positive RHMC measure, scalar-potential derivation, Majorana/Pfaffian identification or physical gravity closure follows here.

## Commands and acceptance boundary

Read-only source/history commands included:
git show --stat --oneline HEAD
git log -3 --format='%H %P %s'
git status --porcelain=v1
git diff HEAD^ HEAD --check
git diff HEAD^ HEAD --numstat
shasum -a 256 lean/SKEFTHawking/ADW/GaussianPolynomialHermite.lean lean/SKEFTHawking/ADW/GaussianPolynomialIBP.lean
python3 scripts/codex_continuity.py check <exact packet path above> (twice)
plus cat/sed/rg/nl source inspection.

The candidate stayed clean; diff check emitted no errors. Only /tmp/publication-l1-hermite-kernel-review-r1.md and .json were written. No source, notebook, registry, cache or dependency writes; no commits; no Lean build, raw Lean invocation, import aggregate, extraction, controller/process call, or scientific simulation.

ROOT retains authoritative build, absorption, acceptance and any existing closure action. This report recommends acceptance of the scoped mathematical/source/kernel increment subject to those gates. It certifies neither a full-tree build nor full auxiliary/physical/publication completion.
