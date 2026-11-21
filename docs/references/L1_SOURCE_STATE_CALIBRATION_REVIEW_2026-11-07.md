# Independent reviews of L1 source/state-calibration research

Date: 2026-11-07. Coordination: [issue #121](https://github.com/NetRxn/SK_EFT_Hawking/issues/121); [PR #123](https://github.com/NetRxn/SK_EFT_Hawking/pull/123).

Reviewed immutable note: [L1_SOURCE_STATE_CALIBRATION_RESEARCH_2026-11-07.md at 4449b08b42b7530bb8bb083d32874dee203fbc85](https://github.com/NetRxn/SK_EFT_Hawking/blob/4449b08b42b7530bb8bb083d32874dee203fbc85/docs/references/L1_SOURCE_STATE_CALIBRATION_RESEARCH_2026-11-07.md), Git blob `11269cd7d6455157b2b37afbd6f62642ddb9e6c7`. Remote readback matched the authored text before review.

Two separately dispatched cloud reviewers, neither authoring the note, returned the following verdicts. This file preserves their reports; it is not a GitHub approval by another account or a scientific/project gate receipt. Neither reviewer mutated the repository or used local execution.

## Mathematical review

**ACCEPT** as bounded manual mathematical research. No mandatory corrections.

Independently checked against the pinned parity and matching-decomposition inputs:

- Equation (1): the smooth, source-independent calibration has zero strain tangent when B=0.
- Equations (3)–(6): coupling scaling, parity expansions, inverse-kernel expansion, singular-value bound and conditional Schur-complement identity are correct.
- Equations (8)–(9): all reconstruction and kernel derivatives are retained; the commutator and Maurer–Cartan signs are correct.
- Equation (10): the nonlinear-source Hessian includes the necessary second-source-map derivative.

Two optional clarifications: explicitly keep the derived quotient/retained coordinate chart fixed throughout the x-neighborhood; distinguish rectangular B from the symmetric Hessian blocks. The author records both here: the fixed-basis expansion and inverse in (3)–(5) require one fixed derived quotient/coordinate chart throughout the neighborhood, and B is generally rectangular, whereas A and D are symmetric. The formulas and immutable reviewed note are unchanged.

The obstruction remains appropriately restricted to the stated finite branch and calibration hypothesis. This review establishes neither a positive physical state nor calibration, scientific implementation, kernel verification or project/publication qualification.

## Physics/source review

**ACCEPT** the bounded physics/source research note. No mandatory corrections.

Independently checked the pinned collective-body parity/acceptance, matching decomposition, kinetic-normalization correspondence, and one-slice-source acceptance. The note correctly:

- Reuses established G=B=0 results and restricts its calibration obstruction to smooth, source-independent F(G) on the specified finite pure-g2 branch.
- Preserves matter-backreaction, explicit-source, singular-calibration and thermodynamic-limit alternatives.
- Treats Gamma_jj=0 as an additional hypothesis; it does not assert a computed nonzero D0.
- Separates connected, inverse, dressed and momentum-dependent kernels and retains absolute B3 calibration as unresolved.
- Requires physical reconstruction and complete source contacts rather than inferring them from auxiliary channels or Ward identities.

Primary HTML checks support the stated comparisons: Vladimirov–Diakonov VIII, Eqs.77–79; Volovik III, Eqs.18–22; Moore–Sohrabi II–III, Eqs.9–15. The Legendre-sign crosswalk and applicability limits are accurate.

Acceptance covers source fidelity and scoped manual physics reasoning only. No physical state, numerical coefficient, controlled limit, B3 interval, scientific implementation or project/publication qualification is certified.

## Lead disposition and verification boundary

Preserve the note and both independent scoped ACCEPT verdicts as research handback. No required correction remained. No scientific evaluator, test/build, Lean, harness, worktree or notebook operation was requested or performed. Full project/wave qualification, source-selected physical construction, finding closure and publication/main integration are not certified by these reviews. The initial draft hold for publication-owner intake was a precaution, not an identified separate filing approval. The user subsequently reaffirmed authorization to merge reviewed research where appropriate. The pipeline's research lane calls for a cited report vetted by the lead before filing; that scoped review is recorded above. AGENTS.md requires gates for the actual change and warns against inferring new approval requirements. These files add no scientific implementation or qualified manuscript result.

Merge diligence on 2026-11-07 found the PR conflict-free; no Actions workflow runs or commit statuses exist for its head, and main's published branch metadata lists no required status-check contexts. Both accessible active repository rulesets were read: main prohibits deletion/non-fast-forward updates, while the second ruleset protects frontier branches. Neither ruleset requires a review count or status check; both disallow bypass. The connector could not read the separate classic-protection endpoint (403); its ordinary merge operation remains subject to GitHub enforcement.

The general verify_scope.py merge gate includes full tests, validation and a Lean build even for a merge candidate; none was run or claimed passed here. The user's explicit cloud-only/no-Lean research instruction takes precedence for this documentation handback. This admission concerns filing reviewed cloud research only, with source/readback/diff checks and independent manual reviews; it certifies no full scientific wave, native substrate, manuscript, B3 or publication gate. The PR may be merged by the normal SHA-guarded GitHub merge operation without changing protections, force-pushing, or touching the harness.
