# Channel cost and source pins — bounded supplemental check

Task l1-channel-act-r2. FIRST SAME check fresh, changed []. This is read/hash-only; no scientific evaluator, test, build, process inspection, pickle inspection, review verdict, or modification of the earlier scout report.

## Exact current SHA-256

Paths below are relative to the assigned checkout unless absolute.

- docs/audits/2026-10-17-publication-substance-construction/l1_direct_a_haar.py: ab628660108b9f795c6acea9267fdcf2648f96dacbbc8d9d6eb99f11d505c588
- docs/audits/2026-10-17-publication-substance-construction/l1_direct_b_haar.py: 535d4233a51b89e44f8b9d9b8d01ed624b659d68f1ee9e10ec14efea060900b1
- docs/audits/2026-11-05-l1-physical-bridges/leading_metric_response_source_r2.zip: 533bc1ba63ee8e6e2c69c6137d565e0ac1a25b14b1088c55f2353d4e8d3963fb; filesystem size 126068 bytes. Adjacent manifest records 27 members, design SHA 405a556e38abaa97d8d297fdb593cb80813caf4fa7e9b6ef58a022c24491317d, and source-pin manifest SHA d6efcd03049d968fb247e5e2beca1ebc6948cb2f2495c04608312c4b16a0d5a6. I did not independently enumerate archive members.
- Adjacent leading_metric_response_source_r2_manifest.json: 5fd7c167897e38b05ff3f7c2f503e8fb82754a13bf232065b41c654e0cf0823f.
- LEADING_METRIC_ATTEMPT1_FAILURE.md: c5a866dcd8a25b9b6774adfa423787d7ed9fdfd829f72d7e847df14ca6fcbc6a; ATTEMPT2_FAILURE.md: 1a6276dbfafe1abeddabd646956216ee8af139e2e5010e724edd991bfe4a3981, both under the same physical-bridges audit.
- N16_TEMPORAL_BOUNDARY_IDENTITY.md: 82197710fb69018810f321dff0ef9f14f9556e47a5b8fab6725b26d1b4c58c49. Section 1 points to original equation (1) coframes with quarter and identifies S2's ordered world indices and closed plaquette, and S4's internal epsilon determinant. Sections 2 and 4 preserve S4 and time-split action; § bounds records degree limits. Use this actual source and its cited original closed-action reference for exact orientation/sign reproduction.
- /private/tmp/l1-dense-resume.bbZW6V/checkpoint/REPRODUCE.md: 487c8007f854561fd6903466456121351d20256e983d1420ad136020a3ca8cbc.
- Prior /private/tmp/l1-channel-act-contraction-intake-r1.md remains SHA 12b7c0767ae7fd35237b733cffc4242ad1e7032fd63c2c1270d051860ceade3a, unchanged from original handoff.

## Source-derived degree bound, not timing

Under the original polynomial realization in which each coframe contains one compact-link matrix factor, S4 contains four coframes, and S2 contains two coframes and the closed four-link plaquette, an individual monomial of S4^a S2^b has total compact-coordinate degree at most 4a+6b. Insertion q adds at most 2, q² at most 4, n_xL² and n_xL n_yR add 0, and q n_xL n_yR adds at most 2. The bound is a direct degree count, independent of cancellation and does not change anchor independence or trace order. It is not a row-count, time, feasibility or truncation-error estimate; verify actual quaternion/adjoint polynomial conventions when adapting an engine. The cited N16 identity independently records for each truncated W_x the conservative bound 128 compact degree for h degree <=64, using at most 32 four-link plaquettes; that bound is for its auxiliary weight, not this insertion's measured cost.

## Observed old work, new work unknown

Attempt 1 records 47.2634 s preparation, 49.0339 s parent, and refusal at 120001 > 120000 live rows; its known normalization word peaked at 1536 rows. Attempt 2 records 52.5218 s preparation, 52.8016 s parent and the same row-cap refusal. Neither returned a complete tensor. These are previous N4 leading-metric jobs and do not predict the proposed N16 coefficients.

Dense REPRODUCE records branch 128: 88 factors and 1792198 starting rows; two quotient sweeps to 435604; later 12-factor frontier 1067872 stored rows; next join refused before mutation at 1439712 predicted matched products. No signed coefficient. This is separate c0 work; it is neither a lower bound nor a forecast for the new source channels. Full c0 remains open.

Lead's proposed eight A, eight c, eight u scalar coefficients plus nine Z, determinant-four 16 blocks and cross-four 15²16² products are planning counts supplied in the assignment, not measured operations or a cost result. Runtime, intermediate width and feasibility are UNKNOWN. No runtime authorization is implied by this report.
