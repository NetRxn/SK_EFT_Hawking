# L1 consumer reader/render review R1

Verdict: REQUEST CORRECTIONS. Full Paper25 reader/render review and scoped D3 vestigial section plus affected Scope paragraphs/render only. No full D3 reader acceptance, scientific closure, publication acceptance or human approval.

## Identity and procedure

Checkout: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103`, HEAD f86e4b37f99cb0d4e90ddad4f8bf0f99b50726d3 with assigned working diff. Continuity packet `l1-consumer-reader-render-review-20261106-r1.json` checked via `scripts/codex_continuity.py check`: fresh=true, changed=[]. Initial attempt at nonexistent tools/continuity.py failed before the actual check; no mutation.

Read shared authoring prohibited-pattern floor and prose/figure reviewer contracts, workspace and repository guidance, notebook/current Phase6a scientific obligations and consumer SOURCE_ASSESSMENT. Read Paper25 source in order, lines1–522 through enddocument including references. Read all of D3 source vestigial section869–1111 and Scope2425–2574, plus metadata. The historical assignment calls this D3 §6; actual manuscript/PDF calls it IV, and the metadata still uses historical §6 locators. This report resolves scope by the source label sec:vestigial, not the obsolete number.

Actual compiled artifacts inspected, no rebuild:
- Paper25 `/var/folders/qn/14hsg1xs2cdg_017yb6f9wq40000gn/T/skeft-paper25_gravitational_waves-657h_yag/paper_draft.pdf`, all five pages rendered with pdftoppm and visually viewed.
- D3 `/var/folders/qn/14hsg1xs2cdg_017yb6f9wq40000gn/T/skeft-D3-36i2oep5/paper_draft.pdf`, actual66pagePDF; visually viewed pages19–23,52,54,63. Temporary renders also produced for24,53; those two are not claimed visually viewed. Figure1 is deferred to page63. No full66page render/read verdict.

Source SHA256:
- Paper25 TEX e70adab5df808dc5e8bd7247b245381ec7b2b3452fe058ee1678d2fb6e24de0b
- Paper25 working PDF and actual compile PDF both 7a7af251cb66768c15f40702e2fbcf08bfdf5dfdf1cd43314dad9c277951fe60
- D3 TEX a8887aba59cf2ea16ad8a0505ef8544b1420d6a4ac81190639f1a47969a0027c
- D3 metadata 69771c9a28d4ad46cc90abf7e92c56a8d09c2010ffdb2b4770aad99688b17c17
- D3 actual compile PDF 961833b9eb33a331fac6f5a9c864b6b5593a3a0ab3619219635f051bcbab6953

## Necessary correction1: D3's section entrance contradicts its repaired premises

D3 lines869,875–882; actual PDF pp19–20. The title still announces that the physical mode is confined. The entrance says the section “derives the propagation speed” of a spin-two disturbance and that the datum admits the branch only on the stated interval. The actual repaired argument on p21 explicitly assumes that mode and speed law and does not construct the physical response. A reader reaches the unsupported physical result before the qualification. This is the first stop in the scoped D3 read.

Restructure the entrance and title around a conditional scalar speed-law constraint. Explicitly adopt the interpretation/law and comparison interval before giving the interval conclusion. Do not call the physical branch admitted or confined, or imply a naturalness-derived domain. Preserve all existing exact endpoint and interval algebra. Ensure the downstream opening of the next section at1115 (PDFp23, “vestigial branch having been confined”) does not reintroduce the physical claim when transitioning.

## Necessary correction2: Paper25 retains internal process voice

Paper25 lines180–183, actual PDFp2, retains the parenthesis beginning “Lean line150 ish” and calling the proof one of the cleaner nlinarith uses “we have shipped.” Delete that parenthetical while retaining the actual proof explanation. The first Paper25 reader stop is here: an otherwise precise mathematical argument switches into an informal repository progress report.

Paper25 lines228–231, PDFp2, introduces internal “Wave1” methodology and bundling language. State the mathematical role of the tracked conjunction directly, with a normal companion-paper citation if needed. Reference11 on PDFp5/source513–514 also carries “Phase6a Wave1 ... this series, paper23”; remove internal publication taxonomy while retaining the title and appropriate bibliographic status. Paper25 line199, PDFp2, retains one em-dash. It violates the shared floor; rewrite the sentence with ordinary punctuation, preserving the factor10^14 assertion.

## Necessary correction3: distinguish arithmetic width ratio from what the figure shows

Paper25 lines383–387, actual PDFp4, says the unresolved amber band is “demonstrating the14-order-of-magnitude separation.” The actual p3 plot cannot resolve the width and does not visually establish its ratio. The caption already makes the unresolved interval explicit, and D3's p63 caption correctly says the ratio cannot be read off the figure. Replace the final visual claim with a statement that the curve crosses the cap within the adopted range, while the exact width ratio comes from the interval arithmetic/theorem.

Both actual figures otherwise render correctly: labels, monotonic curve, endpoint arrows and signed values agree, adopted range is labeled, the star is an anchor rather than a claim that the compatible set is a singleton, and the title says “Assumed metric-channel speed.” No new figure asset repair is required by this inspection. Paper25 p3 is legible but dense; D3 p63 has readable axes/caption and no clipping.

## Necessary correction4: define imported acoustic symbols and clarify the adopted interval

Paper25 source308, PDFp3, introduces gamma1,gamma2,kappa,c_s without defining their acoustic meanings. They then recur as generic coefficient arguments in the immediately following linearity identity, inviting a false identification. Define the imported acoustic parameters, or use a brief verbal description of Gamma_H that preserves its unmatched acoustic origin; use distinct dummy names for the generic additivity identity if necessary. N_f at422/PDFp4 should likewise be explicitly identified as the companion's fermion count with its unresolved count convention.

Paper25 conclusion453–455/PDFp4 says “The susceptibility window is adopted ... deriving it remains ...”. Name the adopted comparison range [0.1,10] explicitly so it cannot be read as retracting the derived finite GW-compatible interval. This is a clarity correction, not a change to the mathematics.

## Reader outcome and preserved results

Paper25 is actually about exact scalar interval/endpoint algebra under an assumed speed law, supplemented by a carefully scoped unmatched correction ansatz. The revised title and abstract now say that clearly. The abstract leads with the result. The core sequence Setup → finite interval/endpoints → conjunction and four pointwise failures → unmatched transport example → physical scope is understandable. The source's separate “Result figure” section is thin and could be merged near the first interval result, but that is optional; the floating figure on p3 does not prevent comprehension.

The finite interval [(1-tau)^2,(1+tau)^2], center1+tau², half-width2tau, width4tau, nonempty anchor1, exclusion of endpoints0.1/10, prior dependence, and redundancy of P3 relative to P2 survive in the text. All four pointwise failures remain. The transport revision preserves the real-product algebra and now distinguishes a correction-only bound, signed additive total, robust exclusion for |delta0|>tau+B, and permitted near-boundary cancellation without asserting a physical source. The count discussion now marks the exact matching locus conditional and preserves unresolved Weyl/Dirac normalization. No accepted scalar result is weakened by the necessary corrections above.

D3's repaired inner speed passage, adopted comparison range and Scope paragraphs on pp21–23,52,54 are readable and appropriately retain missing physical response/mode/matter constructions. The entrance/transition residual is why this scoped review does not accept the complete applied consumer repair.

Symbol verdict: Paper25 needs correction4. Process-voice verdict: needs correction2. Section-argument verdict: mostly carries, with corrections1/3. Full Paper25 length charter verdict: UNMEASURED, because this legacy draft has no bundle metadata/length_target; its actual output is five pages, which alone does not establish a charter budget. D3 metadata length_target30–75 and compiled_pages66 agree with actual66pages; only that numerical budget comparison is accepted, not full D3 prose or publication readiness. Three changed D3 metadata claims correctly distinguish scalar phase classification, exact luminality and finite tolerance; the historical §6 locators deserve reconciliation to actualIV.

## Render residuals and limits

Actual Paper25 rendered pages have no clipped equations/labels or unresolved references; provided compile reports zero overflow/errors/unresolved. Large RevTeX vertical spacing around headings is visible but readable, not a new acceptance blocker here.

D3 has twelve actual overfull reports. Read ROOT's baseline receipt `/tmp/l1-d3-baseline-compile-r3.json` and both actual logs. The ordered twelve reported widths are identical between baseline f86 archive compile `skeft-D3-mfo_9hrj` and candidate `skeft-D3-36i2oep5`; line locations shift consistently after edits. Candidate source spans are97–105,251–257,381–396,633–644,1293–1308,1471–1476,1850–1855,2018–2029,2030–2045,2082–2092,2261–2271,2622–2637. None is the changed consumer passage. This is direct comparative log evidence, not an assumed baseline. All twelve remain unresolved and unwaived. It does not certify unviewed pages. Figure deferral to p63 is disclosed; broader float placement is outside this repair acceptance.

No source, Git, registry, notebook, environment, build, test, native or controller mutation performed. Only this report, /tmp/l1-*-reader.txt and /tmp/l1-*-render-*.png written. The reports are read-only review evidence and ROOT owns any canonical reconciliation. Original B3 physical normalization/[0.1,10] derivation, positive state, physical tensor/matter and matched transport objectives remain OPEN. Necessary source repair is not science closure. Final human review remains required.
