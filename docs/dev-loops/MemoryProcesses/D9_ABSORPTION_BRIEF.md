# D9 finite-memory absorption brief

Status: preparation only. Earlier accepted calibration/coarse-graining source bbdbe40d; the finite-process extension has its own acceptance record in PROCESS_CLOCK_PROGRAM.md. D9 manuscript insertion remains blocked by existing D.0 readiness prerequisites. This brief neither alters the manuscript nor closes its pending reviews. Root owns integration; component and final preparation reviews are recorded in the owning program.

## Scientific thread and placement

Use one connected argument: a controlled system reset need not erase its environment; calibrated observations can reject a specified common-system-channel explanation; discarding old history then requires an explicit forgetting assumption.

- `sec:params`, adjacent to readout characterization: realized retained-environment experiment, system reset and environment-reset control, followed by the partial-interaction separation of residual system error and environmental memory.
- `sec:params` / `sec:readout`: six-group calibration contract and the directly proved random-budget rejection guarantee. Keep trusted standards, diagonal reset structure, stable binary confusion law, fixed sample design and within-group independence visible. Basis measurements do not establish diagonality.
- `sec:worked`: exact synthetic observations and conditional statistical decision. Separate the illustrative sample from the theorem about power over a finite probability law.
- `sec:protocol`: replacement-collision model, product contraction, suffix prediction error, arbitrary boundary-state lower bound and no-forgetting endpoint.
- `sec:breaks`, `sec:related`, `sec:discussion`: limitations, established precedents and the contribution of connecting formal evidence layers.

The stable sourceless handle is `D9_memory_processes_lean_only`. Follow the existing D.4 append machinery only after D.0 clears. Do not introduce a separate paper or treat section numbering from historical plans as current.

## Claim and evidence contract

The source-to-theorem mapping is PUBLICATION_MAP.md. Canonical CPU functions are `memory_calibrated_sampling_certificate` and `memory_history_approximation` in `src/core/formulas.py`. Do not replace these with independent plotting formulas.

The six illustrative counts are 320,320,320,10480,80,6430, in false-positive, false-negative, reset0, reset1, main0, main1 order. Four calibration groups each have 81920 observations and radius1/128; main groups each have20480 and radius1/64. False-negative counts mean reported zero on the trusted one standard. Exact output has failure bound3/256, requested level1/64, margin173/2048. The separate model theorem proves power at least253/256 with worst-coverage margin13/2048. These are synthetic data and conditional model guarantees, not measured hardware performance.

For the collision model, each retention lies in[0,1]; the same suffix acts on the compared states. Trace distance contracts by the retention product. The upper prediction error applies to the actual suffix approximation; the matching half-product scalar-predictor lower bound ranges over arbitrary states at the suffix boundary, not necessarily states obtainable after a chosen fixed prefix. No arbitrary retained measurement records or adaptive testers are included in that result.

## Two-panel figure specification

Panel A: exact calibrated empirical gap and rejection threshold, annotated with total failure allowance. Show the combined calibration-plus-main guarantee, not a main-only confidence number. The accompanying caption distinguishes the observed-count margin from the separate power bound.

Panel B: exact full-versus-suffix prediction error and proved bound across suffix lengths for a fixed finite driving sequence; include retention one as the no-forgetting control. Use canonical CPU outputs for all plotted values. Count full and suffix updates separately; do not imply the diagnostic Python function itself runs in suffix-only time.

Use the existing figure registry/generation and review path once this figure brief is admitted. No standalone plotting harness, publication-quality figure claim or completed figure is asserted here.

## Review and repair path

1. Reconcile live D9 findings and readiness against the current manuscript. An empty planner result is not evidence of clearance.
2. Independently review this section/figure brief and its links to accepted sources. Read primary precedent sections before drafting equation-level comparisons; current abstract-level contextual citations do not suffice for equivalence claims.
3. Keep content queued until D.0 prerequisite reviews close. Existing D9 repairs require a separately bounded scope decision; owner excluded unrelated pre-existing corpus repairs.
4. When eligible, append through D.4, run whole-manuscript prose review, canonical figure and claims prerequisites, then the bundle adversarial review.
5. Route resulting Lean, Python, research or prose repairs through existing grouped findings and closure writers. Update manifests and readiness only from actual accepted evidence.

No quantum-only memory, unusual-time physics, general simulation speedup, tomography, firstness or submission readiness is claimed. Broader horizon and clock connections belong to their own accepted results.

## Queued finite-process extension

Precede calibration with realized instrument definitions in `sec:params`, including subnormalized zero branches. In `sec:protocol`, introduce the normalized outcome-dependent tree and show that summing every future outcome preserves an earlier probability. Use the coherent example in `sec:worked`: final probability 49/625 without the intermediate computational-basis (Z-basis) measurement, 337/625 with it, contrast 288/625; system-reset history probabilities 0 and 256/625 with an environment-reset control. Exact declaration links are in the finite-process section of PUBLICATION_MAP.md.

In `sec:breaks` and `sec:discussion`, preserve the fixed-prefix/all-futures requirement, default-coefficient scope, common-system-only exclusion and absence of a general adaptive calibration/approximation theorem. Readout padding has explicit Lean bridges; Python and Lean remain independently implemented. The clock comparison stays a separately scoped physics follow-on rather than an inserted D9 clock section. These additions are preparation only, with no new figure deliverable, manuscript edit or D.0 waiver.
