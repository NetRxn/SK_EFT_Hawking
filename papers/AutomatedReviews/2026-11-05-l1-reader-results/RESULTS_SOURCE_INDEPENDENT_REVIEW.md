# Independent L1 results and observational-source review

ACCEPT the exact r2 proposal at the mathematical/source-fidelity and preservation boundary. Required corrections: none. This is not a whole-prose, rendered-layout, stage, physical-construction, main or publication verdict. ROOT remains sole integrator and notebook writer.

## Authority and exact candidate

First action attempted the existing continuity check with `python` (unavailable); immediately repeated with `python3`: fresh=true, changed=[]. Snapshot does not confer execution authority. Read workspace/repository instructions, current ROOT notebook and repair queue, canonical prose review, paper-authoring and prohibited-pattern/dispatch contracts, claims-reviewer and Lean-worker backing/type-discovery guidance. Assignment is read-only except scratch reports. No tracked, Git or notebook writes were made.

Candidate HEAD: `7258784b74dcdd34e8ca1a56f5d7ff67a366a292`; tracked status was empty on readback. Canonical manuscript SHA256 `208a06c5ca352ed209cfd221262e4f4099dae58d3c310c42bd1369b0df45ff8d`. Exact reviewed full proposal `/tmp/l1-results-observation-725-r2-full.tex` SHA256 `911fef6ae5b1a6037a98afc483f185885e38e5cf16321aaa8dc42b6204d78338`. Original author's section `/tmp/l1-results-reader-author-725-r1.tex` SHA256 `e559653974c93f37466c5dc2e7a2a62814e304ac8f0fed1b257a8a6ebde8ed79` is preserved.

Two logical replacement regions only: original Introduction 94–100 becomes proposal 94–102; original leading-order results through before Discussion 191–338 becomes proposal 193–339. A byte comparison of the three complementary slices is identical. Thus title, abstract, first RPA/natural-range paragraph, remaining Introduction and entire Discussion/bibliography/end-document suffix are unchanged. All label definitions and citation/bibliography inventories remain; figure path remains unchanged. References still target existing labels. Literal cross-reference multiplicity changes as described below.

Against the original author's section, ROOT r2 scopes both strict monotonicity and zero-iff to the nonnegative domain; makes the nested display conditional on compatibility; splits the conjunction display across an extra aligned line; the separator belongs to the unchanged full-document suffix. No other scientific change.

## Primary observational source, independently read

Read the supplied complete body extraction and independently extracted printed PDF page 6 using `pdftotext -f 6 -l 6 -raw`, then read the whole section 4 introduction and WHOLE 4.1 including its right-column closing continuation before 4.2. This was body reading, not abstract substitution. Own extract: `/tmp/l1-results-review-abbott-p6.txt`.

Abbott's section uses the observed lag, source distance and an assumed emission offset. It chooses 26 Mpc as the conservative lower distance limit. Simultaneous emission supplies the upper velocity endpoint; a 10-second delayed gamma emission supplies the lower endpoint. Its Eq. (1) is exactly the asymmetric interval retained in the proposal. It explicitly allows longer/post-merger and pre-merger alternatives, illustrating a broader admissible range, and closes by distinguishing source-emission timing from propagation timing. Therefore the added source-assumption qualification and possibility of weakening are faithful. The symmetric fixed tau is clearly this manuscript's envelope, not a newly universal observational result. No source-lag likelihood, inferred emission clock or parameter API is introduced.

## Actual carriers, statements and proof bodies

Personally read `lean/SKEFTHawking/GravitationalWaves.lean`, definitions and proof bodies, not merely names/docstrings, and filtered the existing typed `lean/lean_deps.json` for this module. Its underlying carriers are ordinary Mathlib `Real`, `Set.Ici`, `Set.Icc`, conjunction, and predicates on real deviations: no opaque substitute physical carrier establishes a microscopic mode. Existing typed extraction has the same fixed tolerance, real nonzero-c bridge, nonnegative biconditional and endpoint disjunction as the source. Its recorded project-axiom lists for these entries are empty; this is existing extraction evidence, not a fresh Lean/kernel run.

The strongest endpoint source is the actual `natural_endpoints_violate_ligo_for_every_c`, not just the c-free endpoint theorem. Its proof rewrites using `c_GW_relative_deviation_eq hc`, splits the endpoint disjunction, and invokes the concrete lower/upper falsifiers. The manuscript now states that stronger relative-speed result with every real c != 0, includes c > 0, and does not promote it to interval-wide exclusion or microscopic no-go. Existing bundle metadata apex includes both endpoint results. Removed main-text/caption witness names still correspond to extant source and metadata; removing inventory has not removed a scientific quantity or demoted the strongest result.

## Complete scientific preservation map

| Scientific content | Exact backing and retained proposal expression |
|---|---|
| Assumed speed law and positive physical speed | `c_GW : Real -> Real -> Real := c * Real.sqrt chi`; `c_GW_pos` requires chi>0 and c>0. Proposed leading paragraph retains both conditions and positivity. Earlier assumed-law equation is byte-identical. |
| Relative-deviation bridge | `c_GW_relative_deviation_eq` requires only real c != 0 and proves `(c_GW chi c-c)/c=sqrt(chi)-1` by division cancellation/ring. Proposed display explicitly retains every nonzero c. |
| Nonnegative strict monotonicity and exact-zero anchor | `StrictMonoOn ... (Set.Ici 0)` and zero-iff theorem with chi>=0; proof uses sqrt strictness and square identity. Proposed scope explicitly covers both statements; finite tolerance is distinguished from exact luminality. |
| Fixed-tau exact compatible interval | `LigoSatisfied delta := abs delta <= tolGW170817`, `tolGW170817 : Real := 3e-15`; theorem assumes chi>=0. Proposed theorem retains fixed tau, both squared endpoints, closed inequalities and label `thm:bicond`. No generic-tolerance theorem is claimed. |
| Mathematical proof of biconditional | Forward: absolute bound gives sqrt bounds; tau between zero and one permits squaring, using sqrt squared=chi. Reverse: monotonic sqrt and sqrt of the nonnegative bound squares. Proposed mathematical argument preserves all these steps, replacing tactics with the actual reason. |
| Strict nesting and nonempty finite interval | Source strict endpoint comparisons, subset, confinement and unity membership; proposed conditional nested display has 0.1<lower<=compatible chi<=upper<10. Unity is inside and width nonzero, not singleton. |
| Exact widths and strict comparison | `ligo_window_width_eq` ring identity 4tau; `natural_range_width_eq` gives 99/10; `...by_1e14` reduces exact constants by norm_num. Proposed exact width 1.2e-14, adopted width 9.9 and strict 1e14 multiplication inequality retained. No subtraction of rounded binary endpoints is used as exact proof. |
| Lower endpoint and ratio | Existing formula/constants/tests use sqrt(0.1)-1 and tau=3e-15; proposed -0.6838 and 2.28e14 remain identical rounded literals. Lower proof's sqrt(1/10)<=sqrt(1/4)=1/2 argument retained, yielding contradiction to the cap. |
| Upper endpoint and ratio | sqrt(10)-1, +2.1623 and 7.21e14 retained. Upper proof's sqrt(10)>=sqrt(4)=2 argument retained. Both `thm:falsifier-*` labels and simultaneous endpoint failure remain. |
| Exact conjunction | Actual definition is chi>0 AND LigoSatisfied(deviation chi) AND abs(deviation chi)<1/2. Proposed displayed definition retains every conjunct and strictness; P1/P2/P3' meanings retained. |
| Dependence and compatible set | At this tau, P2 implies P3' because tau<1/2. On chi>=0, P2 forces strictly positive interval, hence P1. Conversely interval gives P2 and the others, including unity. Proposed set equality is a mathematical consequence of actual definitions/interval theorem, not a new typed theorem or independent-clause assertion. |
| Four explicit counterexamples | Lower/upper fail P2; zero fails P1 and lies outside adopted range; quarter is interior, has sqrt(1/4)-1=-1/2, satisfies P1, fails P2 and strict P3'. P1 alone insufficient, no uniquely failed clause or independence inference. All retained. |
| Prior caveat and conditional uniform mass | No probability follows from widths without prior; uniform prior on adopted [0.1,10] gives 4tau/9.9 because the whole compatible interval is inside. Retained verbatim in mathematical content, moved earlier. |
| Stronger nonzero-c two-point exclusion | Actual theorem's `not LigoSatisfied` at either endpoint implies strict abs(relative deviation)>tau over Real; proposed display preserves the full endpoint disjunction and c!=0. c=0 is excluded; no choice of nonzero c rescues an endpoint. |
| Figure content | Same PNG include path, equation, cap, adopted range, endpoint deviations, finite width, 9.9 comparison, unresolved scale, gold unity anchor and nested/not excluded interpretation. Only symmetric-envelope wording and removal of three Lean witness names change caption. No figure-generation or pixel mutation requested/performed. |
| Scope and original physical requirements | Both endpoint statements remain conditional on assumed speed law and quantify neither actions, propagators nor matter couplings. No dynamical impossibility inference. Added final sentence explicitly retains normalization/domain, physical state, propagating tensor against same matter/light reference, controlled transport/frequency matching, units/errors. Earlier RPA/range provenance and complete original Discussion unchanged. B3/microscopic/state/tensor/matter/transport obligations remain OPEN. |

## Numerical/source inspection scope

Read actual implementations in `src/core/formulas.py` (speed, rationalized deviation, absolute-cap checker and endpoint range), fixed `GW_PARAMS` in constants, `src/gravitational_waves/c_GW_computation.py`, `ligo_constraint_check.py`, endpoint and compatible-window tests, and the carrying `fig_c_GW_vs_ligo_constraint` code. Endpoint ratios derive from absolute deviations divided by the same cap. Exact interval width derives from algebra over real constants, not floating point endpoint subtraction. Existing helper explicitly documents returned rounded endpoints. No new calculation, test, native execution, scientific run, proof build, LSP or slot activity was performed. Pins for all these inspected sources are included in the JSON companion.

## Acceptance limits and corrections

No required scientific/source correction identified in the exact proposal. This accepts source fidelity and preservation, not prose efficacy, page budget, layout, current all-project tests, missing physical construction, full stage readiness, or publication. Independent prose/rendered review and ROOT's existing integration/claims/closure process remain necessary. No missing-proof inference was made. No new authority/measurement system was created.

The module has stale aggregate comments claiming conjunct independence or misdescribing the fixed cap; the actual definition/proofs and revised manuscript correctly keep dependence and fixed tolerance. The current queue already retains the source-comment obligation separately; this review does not silently close it or mutate Lean source.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No scientific contradiction in the reviewed candidate. One literal precision correction to the brief: all label definitions and all cross-reference targets remain valid, but the cross-reference occurrence sequence is not byte-identical. Three original `thm:bicond` occurrences become two, and an explicit `fig:cGW` reference is added. This removes a duplicate reference while retaining its scientific content and adds a valid figure reference; it is not a required candidate correction.
