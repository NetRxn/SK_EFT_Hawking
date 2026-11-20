# Independent consumer applied-source review R2

Verdict: REQUIRED METADATA REPAIRS. The current assigned TeX repairs are ACCEPT at scoped consumer scientific-source level; the complete three-file package cannot yet receive ACCEPT because three metadata claims still overstate the actual formal backing. No full D3/L1 gate, physical construction or semantic closure is inferred.

Packet l1-consumer-source-review-20261106-r2.json was checked FIRST from the assigned checkout; result fresh=true, changed=[]. Candidate parent remains f86e4b37f99cb0d4e90ddad4f8bf0f99b50726d3 with frozen uncommitted author changes. No source/repository/Git/ledger/notebook/native/controller/test/build changes were made; only this permitted /tmp report was written.

## Exact remaining repairs

All are in papers/D3/bundle_metadata.json:

- Line131, natural_endpoints_violate_ligo_for_every_c: replace “frame-independent endpoint falsifier” with “reference-speed-independent endpoint falsifier under the adopted scalar speed law”. Actual c_GW_relative_deviation_eq and the endpoint theorem quantify real c≠0 and establish scalar cancellation; no frame transformation is present. Paper25 now correctly uses reference-speed-independent language.
- Line21, ADWMechanism.pos_C_gives_full_tetrad: replace the physical exclusivity clause “the only one admitting classical gravity” with a faithful finite-classification claim, e.g. “positive C is classified as full_tetrad for either metric-fluctuation flag”. The actual theorem229–232 unfolds classify_phase223–226 and proves only that classification. It has no matter action, propagator or physical classical-gravity exclusivity premise/conclusion.
- Line136, VestigialGravity.phase_count: replace “only the full-tetrad phase admits classical gravity” with “the displayed list of three named phase constructors has length3”. The actual statement50–53 is literally List.length [pre_geometric,vestigial,full_tetrad]=3. It proves no exclusivity or physical emergence claim. Update this claim's stale §6.2 locator to §IV.A if retaining a section locator.

The latter two retained metadata claims directly contradict the newly repaired scientific distinction in §IV.A and Volovik's metric-GR vestigial proposal. This is consumer claim correction, not new Lean proof work or a request to retire accepted finite classification/count results. All other assessed changed metadata claims are acceptable under their now-explicit adopted-model context. The previous catalog8units is not a complete-paper coverage certificate.

## R1 reconciliation and scientific assessment

D3 abstract, proposed quartet-correlator phase opening, entire vestigial section and following transition now explicitly constrain an assumed kinematic law. They no longer derive/admit/exclude the physical phase from interval algebra. The full affected Scope subsections preserve finite compatibility, avoid exact-unity pinning and avoid exclusion from another event's timing without its own premises.

D3 §IV.A correctly distinguishes assigned finite classifier flags from physical matter/source correspondence and trajectories. It correctly allows the connected metric contribution in Volovik2024 III(21)–(22) to survive tetrad condensation, so a nonzero tetrad expectation does not itself guarantee physical WEP restoration. The statements preserve all accepted classifier results and make no new theorem-absence claim.

D3 GW paragraph now faithfully states26Mpc as conservative lower90% credible-distance bound, simultaneous emission for the positive side and gamma-ray emission10s after GW for the negative side. Its alternative-emission caveat and revised lattice paragraph carry the conditional observational premises. These agree with the held Abbott L13 complete §4.1 read in R1.

Paper25 title/abstract/introduction/setup now correctly distinguish Volovik2024 quartet-metric proposal from Volovik2026 de Sitter luminal collective sound and its open spin/helicity interpretation. The spin-two interpretation, dimensionless normalized speed-response law and [0.1,10] comparison range are adopted rather than physically derived. Conditional RPA bare response/coupling inputs remain unevaluated; no Vergeles-derived interval is claimed. The formal nonnegative-domain interval, width4tau, center1+tau², half-width2tau, nested/nonempty compatibility, endpoints and prior dependence remain intact. The three-clause Prop's dependence and all four nonexclusive counterexamples remain correct. No H1-impossibility or branchwide no-go is asserted.

Paper25's acoustic SI dimensional addition is correct against the actual SecondOrderSK.GammaH source: gamma1,gamma2 carry m²/s, kappa is s^-1, cs is m/s; hence (gamma1+gamma2)*(kappa/cs)^2 has units s^-1. Dividing by physical cGW² with units m²/s² gives s/m², whereas a coefficient multiplying physical frequency into a dimensionless correction requires seconds. Natural units or an independently normalized matching dictionary could change the comparison, but the text appropriately does not choose either to manufacture a physical coefficient. It explicitly keeps source/state/unit matching open. Distinct acoustic gamma1,gamma2 versus abstract additive real a,b avoid conflating the meanings.

The literal numerical probe100, adopted1e-30 coefficient bound and1e-28 correction bound are correctly distinguished from measured physical frequency/coefficient/band. The correction-only biconditional, reverse-triangle exclusion |d0|>tau+B, and freely signed near-boundary restoration witness are correct and leave physical sign/dynamics unresolved. The figure text correctly separates unresolved pixels from the exact width algebra. Companion alpha*=Nf/(12pi) remains conditional matching algebra, with defined species parameter, Dirac/Weyl and coefficient-normalization caveats. Corrected Diakonov title and concise L13 collaboration attribution agree with the held title pages read in R1. Reader voice improvements add no physical claim.

The original B3 metric/source/projector/regulator/normalization and derived window/domain, positive physical state, constrained tensor propagator/polarizations, common matter/light reference and controlled matched transport remain OPEN BUILD. This review preserves the original acceptance and previous accepted scalar mathematical results; corrected prose does not discharge those requirements. It does not certify compilation/rendering independently: ROOT's stated compiles are separate evidence.

## Scope and frozen hashes

R2 reread full Paper25 TeX1–end including caption and bibliography; complete D3 vestigial section866–1110, abstract34–66, transition1112–1128 and complete affected Scope2430–2575; every actual current TeX/metadata diff (initial broad diff had output truncation, supplemented by full current sources and focused diff chunks); current changed metadata region1–175. R1's scientific primary-source and actual Lean depth-reading remains applicable because the governing L1 and relevant Lean hashes are unchanged; actual acoustic definition and actual phase_count/classify_phase/pos_C statements were freshly read in R2. No new kernel/absence claim was attempted.

SHA256:
- D3 TeX9db0ddb25df43f34087cf8ebafb28fd58369cacc23c6c46b6bdfe19b5d62b231
- D3 metadata f4d0f090da95ccc8c36ff9ab729a98314b8ef216507f21bc3a497c454637989d
- Paper25 TeX760c21f1295b72cb3fd5bfc66adb09320ef9d5e65da0074215bdfa871675f2ff
- D3 PDF068865fed7b29e92c7603162d9ff5c878a24e8b46f6df8bf5f233043dad96390 (hash only)
- Paper25 PDF79dd5f5b37b9de94908824ee57df3c6dea0321e05811bae65b4ef2512ae93580 (hash only)
- L1 TeX29f926fef642a352ffb24b2d1fb0d851c1fb58d5c2a50ba7ffaf3083e3c1c5a2
- GW Lean eab4cd660adb486d6b057e8036d2d952bdea55e7ab7686e568cb79ae6a02285d
- VestigialSusceptibility Lean cf5a4584ad51f44a232c7da2d4fe9300ea14c322a416b2843e7ef3c2032bf721
- VestigialGravity Lean4c057448a02f8dc0a55f6048bd5b9521cc08c66ee8aa6c3fc7359610cf240f47
- SecondOrderSK Lean393179be9e2a27660e5c0e5ad53ffe9089633f5f397e85c35bd7ae55048f8bb4
- ADWMechanism Lean025eb5c3934b1b0866b0a85aabf0cb3c0bec263a0f9970092e32dad3d5428e24

Held primary PDF/body hashes and exact primary read scopes are recorded in the frozen R1 report. Their physical source findings were preserved, not replaced by a new abstract-only check.

## Every R2 shell command

All from assigned checkout /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103. S below denotes /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking. Repeated filename shorthand refers to the exact paths in the first command group.

1. python3 scripts/codex_continuity.py check S/.codex/continuity/l1-consumer-source-review-20261106-r2.json
2. git diff -- papers/D3/paper_draft.tex papers/D3/bundle_metadata.json papers/paper25_gravitational_waves/paper_draft.tex
3. sed -n '1,220p' papers/paper25_gravitational_waves/paper_draft.tex; sed -n '1,175p' papers/D3/bundle_metadata.json; sed -n '34,66p' papers/D3/paper_draft.tex
4. sed -n '220,525p' Paper25TeX; sed -n '866,1128p' D3TeX
5. sed -n '2430,2575p' D3TeX; git diff -- D3TeX | tail -100; rg -n -A8 -B5 'theorem phase_count|theorem pos_C_gives_full_tetrad|def classify_phase|def phase_count' lean/SKEFTHawking/VestigialGravity.lean lean/SKEFTHawking/ADWMechanism.lean; sed -n '390,405p' lean/SKEFTHawking/SecondOrderSK.lean; shasum -a 256 D3TeX D3Metadata Paper25TeX lean/SKEFTHawking/SecondOrderSK.lean; cat S/.codex/continuity/l1-consumer-source-review-20261106-r2.json | head -55
6. git diff -- Paper25TeX | sed -n '1,180p'; shasum -a 256 papers/L1/paper_draft.tex lean/SKEFTHawking/GravitationalWaves.lean lean/SKEFTHawking/VestigialSusceptibility.lean lean/SKEFTHawking/VestigialGravity.lean lean/SKEFTHawking/ADWMechanism.lean papers/D3/paper_draft.pdf papers/paper25_gravitational_waves/paper_draft.pdf; rg -n 'frame-independent|only.*classical gravity' papers/D3/bundle_metadata.json
7. cat > /tmp/l1-consumer-source-review-r2.md <<'EOF' (this report).

All commands exited0. Some combined output was truncated as noted; source scopes were recovered with smaller reads. No test/evaluation/build/native action or repository write occurred.
