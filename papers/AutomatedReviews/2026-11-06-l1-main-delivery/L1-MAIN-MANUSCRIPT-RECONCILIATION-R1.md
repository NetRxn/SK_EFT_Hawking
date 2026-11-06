# L1 main manuscript reconciliation — read-only author-composition advice

Assessment date: 2026-11-05. No repository edits, builds, tests, dependency/backend/slot actions, review ingestion or lifecycle writes performed. Initial required continuity check returned fresh:true, changed:[] for primary `.codex/continuity/l1-main-composition-455358-r1.json`. This report is advice for composition, not independent acceptance of the eventual candidate.

## Exact pins and source boundary

- Main: `ce194cdc4bf939b108c17edc9530a7f0a14565f9`.
- Current composition checkout: `455358440ab0c16dee043de0d574eff13dec7a78`.
- Publication donor: `1805e33581cb81229e8568c450875e454d0afdd9`.
- `git diff ce194cdc4 455358440 -- papers/L1 src/core/visualizations.py tests/test_gravitational_waves.py` is empty. Therefore the donor manuscript and its numerical/figure support have NOT already arrived through this current main composition. This empty scoped diff is not an ancestry or full-tree acceptance claim.
- Read actual donor manuscript and deltas, main numerical functions, main mapped scalar spec, actual donor metadata delta, source-authoring instructions/prohibited patterns, claims-reviewer contract, mapping/anchor documents, donor source/render/catalog scope and current whole-paper prose disposition. Consulted referenced primary notebook, Phase6a roadmap, original repair-disposition map and continuity authorities. The roadmap is historical phase execution material, not authority to close the original publication BUILDs.

## Recommendation: smallest scientifically complete incremental source composition

Compose the existing donor `papers/L1/paper_draft.tex` with its complete scientific caveats, exact stronger results and ordinary supporting appendix. Pair it with the bounded numerical/figure dependencies below and the nine semantic apex corrections. Do not copy donor claims/prose/audit/stage/closure/human state. Retain main's RED/stale/pending acceptance posture until fresh candidate-specific writers and reviews establish changes.

This is an incremental source checkpoint with the full original physical programme still open, not a recharter as a finished conditional letter. The current title's “its natural range” implication remains an explicit whole-paper acceptance issue: the body states that `[0.1,10]` is adopted, while the original charter requires deriving it. Preserve the original requirement; cosmetic caveating alone cannot make the physical paper accepted.

## Scientific repairs carried by the donor manuscript

1. **Assumption and attribution:** spin-2 substrate identification and `c_GW=c sqrt(chi)` are assumed here. Volovik's de Sitter Landau/stiff-component model gives luminal second sound and leaves graviton interpretation open. His vestigial/gravity counting does not independently derive this substrate's propagating spin-2 mode. The draft keeps actual primary-source distinctions rather than assigning this susceptibility law to Volovik.
2. **Source-qualified observation:** the asymmetric `[-3e-15,+7e-16]` interval and symmetric `tau=3e-15` envelope inherit source-emission/distance assumptions. This is not an assumption-free universal arrival-time measurement of the model.
3. **Normalization/range:** normalized dimensionless chi is free; RPA is `chi0/(1-gamma_star chi0)` with unevaluated inputs. Remove inverse-cutoff units from the normalized speed-law parameter. The adopted `[0.1,10]` comparison is not computed by Vergeles or obtained from the RPA closed form. Alpha_ADW is distinct from chi; no identification between their free normalizations follows.
4. **Correct exact result and numerical interpretation:** fixed `tau`, domain `chi>=0`, finite compatible interval `[(1-tau)^2,(1+tau)^2]`, exact width `4tau=1.2e-14`, natural width9.9 and compatible fraction `4tau/9.9`; probability requires a specified prior. Exact luminality at1 does not turn the finite compatible set into a singleton. Endpoint factors differ: approximately2.28e14 below and7.21e14 above; the interval is not excluded.
5. **Retain stronger endpoint theorem:** every real `c!=0` for the actual relative deviation, including physical `c>0`. Do not weaken this to a positive-c-only or purely c-free definitional statement.
6. **Predicate dependence:** P2 implies P3' and, on the stated nonnegative domain, P1. Endpoint/zero/quarter witnesses refute conjunctions; none isolates a uniquely failing conjunct. Quarter establishes P1 alone does not imply P3', while P2 also fails there. Keep all four counterexamples.
7. **Frequency scope:** `gamma*omega` is an assumed algebraic product, literal100 is a numerical probe, `1e-30` is a placeholder bound. Ordinary/angular frequency, units, Gamma_H identification and physical transport remain unmatched. The correction-only bound does not bound total deviation. Retain additive reverse-triangle exclusion `|delta0|>tau+B`, `B=1e-28`, and opposite-sign near-boundary restoration.
8. **Companion comparison:** `alpha*=N_f/(12pi)` at adopted unreduced Planck anchor is an algebraic matching locus. Rounded0.40–1.27 is input-count dependent. Dirac kernel versus Weyl count choices and microscopic coefficient selection remain unresolved.
9. **Literature/reader structure:** four 2017 action-level comparisons retain their actual model/background/matter qualifications; remove unsupported immunity-to-operator-escape rhetoric. The result-first abstract, ordinary theorem headings, physical ending and same-source appendix preserve all support while meeting existing source/render conventions. Keep the named appendix hyperlink, which repaired an actual empty printed reference despite clean compilation.

## Required numerical, figure and provenance dependencies

A full donor-file copy of shared modules is unnecessary and risks importing unrelated changes. Compose the exact relevant hunks:

| Path | Required contribution and reason |
|---|---|
| `src/core/formulas.py` | `c_GW_from_chi_vest`: direct sqrt(chi), preserving NumPy wider scalar until final return rather than cancellation in `1+(chi-1)`. `c_GW_deviation_from_c`: rationalized `(chi-1)/(sqrt(chi)+1)` for finite roots, preserving nonfinite behavior. Correct Abbott Eq.(5) to Eq.(1). The tiny compatible interval needs accurate near-unity deviations. |
| `src/gravitational_waves/ligo_constraint_check.py` | Finite/nonnegative cap validation, correct nonnegative preimage for caps>=1, fsum endpoint evaluation and explicit rounded-endpoint/exact-width distinction. Do not use subtraction of rounded endpoints as exact4tau certificate. |
| `papers/D3/tables.py` | `_chi_window_ratio`: use exact algebraic `4*tol` for tol<=1 (and correct full nonnegative preimage width above1). The added GW tests import this existing mapped-consumer spec. Main currently subtracts rounded endpoints and obtains a biased width ratio. Regenerate its existing scalar output through the existing writer if its bytes change; do not handtype a table. |
| `tests/test_gravitational_waves.py` | Bring the complete reviewed relevant numerical/source/figure regression package if retaining the donor's89-case claim: endpoint rational references, rounding budgets, invalid/large caps, near-unity and scalar precision, independently sourced cap/provenance, endpoint display/factors, non-singleton interior witnesses and Plotly data/callout/scale checks; correct stale disjointness/isolated-P3 descriptions and assertions. |
| `src/core/provenance.py` | The GW upper/lower-bound source records need actual printed Eq.(1), not main's Eq.(5). Donor added tests explicitly require Eq.(1). Source qualification must include observation assumptions. Compose source/notes/key-claim and L1 dependency declarations as needed while preserving existing human fields; do not import donor verification dates/human state. |
| `src/core/visualizations.py` | Exact `fig_c_GW_vs_ligo_constraint` hunks: repair scientifically false “chi=1 ±3e-15” annotation and speed-vs-chi tolerance confusion; distinguish assumed law/adopted range and unresolved finite compatible interval; improve readable callouts/legend/layout. |
| `papers/L1/figures/fig_c_GW_vs_ligo_constraint.png` | Regenerate from the composed canonical producer or establish exact donor image/producer match and perform fresh figure/render review. Main's image can retain the incorrect susceptibility offset. Donor manuscript caption expects the repaired compatible-interval label and adopted-range geometry. |

The L1 TeX has no separate table input: only `../../docs/counts.tex`, one local PNG, and inline bibliography. There is no `papers/L1/tables.py`. Do not create an L1 table subsystem just to lift this manuscript. The D3 existing scalar spec is a real dependency of the numerical test composition and mapped width result, rather than an L1 typesetting dependency.

### 89 versus49: cannot copy the statement alone

Main L1 currently says49 cases; donor L1 says89. Donor contains substantial new parametrized numerical/source/figure cases and changes existing precision expectations. Its source records say actual89 passed on its own pinned publication candidate. Those historical executions are not candidate455358 evidence. Carrying donor prose with main tests would misrepresent test population and omit the numerical repairs needed by the new cases. Either carry and actually qualify the complete dependency package then derive the current count, or revise the reproducibility sentence to an accurate evidence-supported description without a stale count. Do not “fix”89 back to49 while leaving genuine numerical defects untreated. Also avoid interpreting “cross-checking every numeric quoted” as exhaustive physics validation: these tests check the conditional model and figure inputs, not microscopic normalization, tensor modes or physical transport.

No runtime parameter change or broad constants delta is needed: donor `src/core/constants.py` differs in an unrelated citation-title ceiling only. Do not import that unrelated delta to support L1. No new theorem/proof is needed for this manuscript's already-existing exact algebra. Donor has valuable **comment-only** `GravitationalWaves.lean` repairs correcting physical attribution, fixed predicate arity/tolerance, dependent conjuncts, offsets and matching; those should be reconciled as an appropriate Lean/source-documentation dependency rather than retaining contradictory claims beside the new manuscript. Native/build qualification for any such Lean-path composition remains ROOT-owned; this assessment did not run it.

## Exact metadata semantic composition

`papers/L1/bundle_metadata.json` donor changes NINE `apex_theorems[*].claims` strings. Keep every apex name and declared date:

- `c_GW_match_iff_chi_close_to_one`: add nonnegative-chi and fixed `tau=tolGW170817=3e-15` domain.
- `H_VestigialModeIsGraviton_fails_at_natural_lower` and `_upper`: failure uses P2; P1 holds and P3' also fails, so remove “isolating”.
- `_fails_at_zero`: P1 fails and P2/P3' also fail.
- `_fails_at_quarter`: P1 holds, P2 and P3' fail; only P1-alone=>P3' is refuted.
- `natural_endpoints_violate_ligo_window`: c-free endpoint statement; attribute actual c-rescaling result to companion `_for_every_c`.
- `natural_endpoints_violate_ligo_for_every_c`: every real c!=0 and actual relative deviation, not merely c>0/frame-independent wording.
- `ligo_confines_chi_vest_within_natural_range`: include nonnegative/fixed-cap domain and exact interval.
- `ligo_window_width_lt_natural_range_width_by_1e14`: actual strict10^14 width inequality; do not overstate the theorem as an exact one-part-in10^15 claim.

Do NOT transplant donor `advisories_open`, `open_findings`, blocked gate roster, readiness dates, compiled_pages, compile_gate_ok, stage dates/statuses, or any other derived acceptance field. Five pages and3518/3750 are donor instrument outcomes for the donor TeX/PDF and input closure, not candidate outcomes. Preserve main's preexisting historical summaries and human state; fresh canonical composition-specific writers are responsible for deriving current compile/readiness/catalog facts.

## Existing acceptance is bounded, not transferable

Actual donor `prose_review.md` explicitly ACCEPTs ordinary restructuring/two repairs and current five reader questions, but BLOCKs whole-paper publication on physical charter/title. R2 was a bounded delta check plus five page views by the R1 reviewer; it was not a new independent fresh-context whole read. Donor appendix scope says151 catalog units with all134 predecessor records preserved, four scientific blockers and54 candidates/human state retained, one canonical intake and zero automatic closure. Do not copy these151 units as current review coverage.

The donor mapped-consumer scope accepts assigned Paper25 and D3 passages only; canonical FixPropagation remains OPEN. Its89-test and successful scoped compile receipts are historical. Its broad default run is expressly RED (61 failed/7081 passed/40 skipped/30 errors), with environmental and actual corpus failures separated; the earlier19-failure receipt is another distinct measurement. Nothing establishes current full-main acceptance. Do not copy donor `claims_review.json`, `audit_log.jsonl`, `prose_state.json`, prose/figure review reports, compiled aux/log/PDF, review supersession/closure rows or stage fields as if their decisions apply to the new composition.

Mapped consumers remain scientific source obligations: Paper25 and D3 must not contradict the repaired L1 speed-law/adopted-window/finite-interval/matter/units scope. Their donor source repairs can be composed independently at bounded scope, but the large D3 manuscript should not be lifted wholesale with unrelated publication work; preserve its unrelated content and known12 overflow boxes until separately addressed. The shared figure should propagate consistently to the mapped figure copies where included. Existing source mapping identifies Paper25=>L1 plus D3§6 and F; the current bundle anchor's “falsification factor in the natural range” must be read as endpoint-only, not interval exclusion.

## Original scientific BUILD debts retained in full

The actual disposition map has THREE distinct L1 constructions:

1. **B3 physical susceptibility/normalization/window:** actual metric/source/projector/multiplicity/regulator/subtraction and numerator/normalization, RPA coupling and physical domain; derive original O(Lambda²/16pi²) normalization AND `[0.1,10]` as a result. A chosen normalization, positivity or a scalar bubble alone does not satisfy this. A different computed interval requires operator-specific disposition.
2. **Microscopic propagating mode and matter bridge:** derive quadratic action/retarded propagator, constraints/poles, stable positive norm and tensor polarizations relative to the same matter/EM reference. Scalar law definitions, endpoint proofs and chi=1 witnesses do not derive this.
3. **Physical frequency/transport matching:** actual response/Kubo coefficient matched to observable propagation with scales, units, frequency convention, controlled remainder and nonempty band; resolve rate Gamma_H versus velocity coefficient and physical100Hz.

Reviewed scalar bubbles, finite Hessians/Haar and Ward controls, finite-source sign obstructions, conditional retarded poles and matter constructions retain their own bounded evidence; none closes these three original requirements. These are distinct from the separate shared D1/E1/E2 physical quadratic-dispersion law. ROOT retains all ordinary L1 scientific/code/prose/figure/citation/catalog/closure/gate/main responsibilities; Executor only receives explicitly bounded deeper construction packages.

## Release

Read-only assessment is complete and the packet may be released for ROOT composition. No source was changed. Required next evidence is fresh actual candidate source/claims review, relevant numerical/provenance/figure qualification, canonical compile with individual rendered pages and existing length/style instruments, followed by required broader gates and protected main integration at their stated boundaries. This report itself certifies none of those future outcomes.
