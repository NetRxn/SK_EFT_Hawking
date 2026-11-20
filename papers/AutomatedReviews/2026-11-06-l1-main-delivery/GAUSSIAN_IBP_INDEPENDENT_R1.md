# Independent Gaussian polynomial IBP review

Verdict: PASS for the assigned mathematical/source and fresh per-file LSP scope. No actionable defect found. ROOT remains acceptance reviewer; no aggregate/project build, integration, physical/scientific BUILD, publication or human acceptance is certified.

Task `l1-gaussian-polynomial-ibp-independent-r1`, parent `publication-remediation`. Reviewer `l1-ibp-independent-review`, independent of the author. Owned writes: this report and `/tmp/l1-gaussian-polynomial-ibp-independent-r1.json` only. Notebook `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-remediation-notebook.md`, designated writer ROOT. Owning roadmap `docs/roadmaps/Phase6a_Roadmap.md`. Assigned candidate `f597f91e12704b30e8b31ace0f38bd32f2e6aff3`, sole parent `4fca5970f4f4cb0b408ea33243076c72058f6e56`.

## Continuity and source identity

Packet `.codex/continuity/l1-gaussian-polynomial-ibp-independent-r1.json` SHA256 `8df54a93e2f27e21aeca2714b49b3d3e94701542e8b3c692f01fb842f2da3e60`. Both initial and final `python3 scripts/codex_continuity.py check <absolute packet>` returned exit 0, `fresh: true`, `changed: []`. Notebook, roadmap and every packet authority hash matched. The assigned continuity/Lean worker/Lean4 skill contracts and relevant governing/scientific source were inspected. No packet/notebook/controller/source writes.

Slot source SHA256 `ffb651c528b22d256b05e8a5ea5118ff3d6fb5bf917d00cd9544b25daccfb396`; aggregate SHA256 `08e8b0d3746c25f6511b6f5c4957731e617a566146e7c5c8e2f95f24c5a77d5e`. Read-only Git log/diff/status confirmed exact candidate and parent, exactly two changed files (70 new module lines and one aggregate line), clean status. Direct bytes comparison using the base aggregate from `git show` proved the new aggregate equals exactly `import SKEFTHawking.ADW.GaussianPolynomialIBP\n` prepended to every prior byte. No dependency/toolchain/policy/other source delta.

## Mathematical review

The exact theorem `SKEFTHawking.ADW.integral_mul_polynomial_gaussianReal` states, for EVERY `p : Polynomial ℝ`,

```lean
(∫ z : ℝ, z * p.eval z ∂ProbabilityTheory.gaussianReal 0 1) =
  ∫ z : ℝ, p.derivative.eval z ∂ProbabilityTheory.gaussianReal 0 1
```

There are no integrability, moment, Stein, degree-limit, conditional-physics or extra typeclass hypotheses in this real-polynomial statement. The claim is substantive, not a totalized-integral zero equality induced by missing integrability.

1. `integrable_polynomial_mul_gaussian` proves absolute Bochner integrability of each polynomial times `exp(-z²/2)` by polynomial induction. The monomial step instantiates Mathlib's genuine whole-real-line `integrable_rpow_mul_exp_neg_mul_sq` at `b=1/2>0`, `s=n>-1`, then converts real natural powers and scales by the coefficient. This includes negative arguments through the imported theorem, not a positive-half-line substitution.
2. `integral_mul_polynomial_gaussian_weight` differentiates the actual Gaussian weight to `-z exp(-z²/2)`, uses polynomial differentiation, and discharges the generic whole-line integration-by-parts premises separately: `p * v'` from the NEGATIVE of the `(X*p)` integrability theorem, `p' * v` from `p.derivative`, and `p * v` from `p`. The signs simplify correctly to `∫ z p v = ∫ p' v`. The generic API has no assumed Gaussian/Stein identity. Its inspected bilinear implementation derives endpoint limits zero from the integrability premises; the proof has no omitted boundary obligation. Real completeness holds; Mathlib's generic incomplete-space branch is irrelevant here.
3. `integral_mul_polynomial_gaussianReal` uses `integral_gaussianReal_eq_integral_smul` with actual nonzero NNReal variance 1. The inspected definition is `(sqrt(2*pi*v))⁻¹ * exp(-(x-mu)^2/(2*v))`; hence mean 0, variance 1 gives the genuine normalized standard density. The shared normalization is factored from both sides. Integrability transfers to probability density products by constant scaling of the proved polynomial integrability, so normalization is not masking undefined integrals. No altered density or integral definition is introduced.

As mathematical controls (not extra executed Lean specializations), p=X gives E[z²]=E[1]=1; p=X³ gives E[z⁴]=3 E[z²]=3. The signs and variance convention agree.

## Fresh independent Lean evidence

Only matching actual `mcp__skeft_wt1__*` proof-state tools were used. Catalog idle prose was stale observation: actual matching calls succeeded. ROOT retained lifecycle authority; no slotctl/primary health probe, build, repair or fallback invocation occurred.

- `lean_file_outline` returned all three substantive signatures, with exactly the four direct Mathlib imports in source.
- `lean_hover_info` at line 48 confirmed the generic whole-line integration-by-parts signature and all three integrability premises; at line 61 confirmed the actual Gaussian density-conversion signature.
- Fresh `lean_diagnostic_messages` for the module: success=true, timed_out=false, items=[], failed_dependencies=[].
- EACH of `SKEFTHawking.ADW.integrable_polynomial_mul_gaussian`, `SKEFTHawking.ADW.integral_mul_polynomial_gaussian_weight`, and `SKEFTHawking.ADW.integral_mul_polynomial_gaussianReal` was independently checked by `lean_verify(scan_source=true)`: exactly `[propext, Classical.choice, Quot.sound]`, warnings=[]. No new axiom/sorry/native_decide/maxHeartbeats.
- `lean_goal` at final line 68 showed the two remaining integral-reassociation goals BEFORE and goals_after=[] AFTER the final tactic.

Raw structured outline/hover/three verify results and concise diagnostics/goal observations are in the companion JSON. No whole-project/native build was run; aggregate import elaboration and authoritative project gates remain ROOT's responsibility.

## Scientific use and preserved obligations

The accepted signed auxiliary construction's Eq11 needs Gaussian IBP applied to the ENTIRE polynomial insertion, coefficient by coefficient in a finite nilpotent exponential. This theorem supplies its standard one-variable analytic brick: the derivative acts on both W and the exponential coefficient, so the derivative-of-W contribution must survive. It neither divides by W nor assumes W positive. No missing normalization or boundary term was found in this brick.

Still owed: all-degree Hermite lowering and factorial/parity identities, sigma scaling, actual constructed finite signed/complex W and multivariate/coefficient assembly, original128-generator coframe grading/nilpotence, C2 source/test preservation, and full formal undivided observable correction. No whole Eq11 formalization or Eq7-10 construction is completed by this module alone. Physical CAR, B3 susceptibility/window, source/state/metric/dynamics/matter/transport and all scientific/publication/main/human acceptance obligations remain open at their existing scopes.

No source edits, Git mutation, controller/lease/cache operation, build or shared record modification was performed. The only written files are the two assigned `/tmp` review artifacts.
