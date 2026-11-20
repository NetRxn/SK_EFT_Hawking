# Independent implemented-source and kernel review: finite complex compensation r1

Verdict: **ACCEPT** for complete ordinary design A / original Eq4.

Task `publication-compensation-independent-review-r1`; parent `publication-remediation`; acceptance reviewer ROOT. I did not author this candidate. Owned outputs are only this Markdown and its JSON companion in /tmp. No repository/notebook/source edits, commits, builds, slot/controller operations, cache repair, dependency repair or integration occurred.

Candidate wt1 HEAD: `a680ec6758713e9ee2f3d964d7fde8c892ae5ae8`.
Source: `lean/SKEFTHawking/ADW/GaussianAuxiliaryCompensation.lean`, all 702 lines read.
SHA256 before and after: `99a40ad1f4304547b2701845e14f168fd3cfcaf2a7526b07eed4eaa7aaead2b6`.

## Authority and independence

The initial and final checks of the SAME assigned primary-local packet `publication-compensation-independent-review-r1.json` both returned exit0, fresh=true, changed=[]. The primary notebook is `.codex/continuity/publication-compensation-independent-review-r1-notebook.md`, designated writer ROOT. Owning roadmap is primary `docs/roadmaps/Phase6a_Roadmap.md`. ROOT owns authoritative acceptance and the running full merge gate; no leaf build was performed.

I read the continuity contract and notebook, governing CLAUDE/pipeline and slot/continuity authorities, the original design and prospective independent design review, the original complete ADW_EXACT_AUXILIARY_IDENTITY.md, the source and its actually called dependency definitions/proofs. The original prospective review filename resolves to AUXILIARY_COMPENSATION_GRASSMANN_DESIGN_REVIEW_R1.md; the initially tried shorter filename did not exist. This was a filename lookup, not an unavailable acceptance requirement. The installed lean4 skill and lean-worker profile were consulted under the stricter review assignment.

ROOT supplied current ACTIVE/public/codex wt1 admission. The static idle tool description was not treated as runtime authority: actual matching wt1 calls succeeded. The initial generic skill-path lookup did not exist; the installed listed skill path was then read. Neither lookup failure was a Lean endpoint, Git or slot failure.

The human author handoff prefix was read only through its first55lines. Its separate raw JSON remains intact at SHA256 `35ed48993a5e62507de82b162e7e67960b36a95fb5d5b065d746b0f197b256e1`. I independently reproduced the evidence below instead of substituting the author's green summaries.

## Mathematical assessment

The definition is literally P=truncTotal(M+1)(e(S)e(-Q)), with Q=sum_i C(sigma²/2) X_i² and e defined using the actual PowerSeries exponential substitution. The finite coordinate type can be empty; M is arbitrary including0; S has arbitrary complex coefficients and arbitrary finite degree with only constantCoeff=0. Algebraic sigma is arbitrary real; actual Gaussian integral claims require sigma>0 and the actual variance v=sigma².

auxiliaryFormalExp_coeff proves that powers above the target degree vanish using the order lower bound for zero-constant series. This is the necessary finite-support justification, rather than an assumed analytic exponential interchange. The finite algorithm theorem replaces both exponentials by powers0..M, multiplies them as ordinary polynomials, then truncates. The rectangle coefficient algorithm is explicitly permitted by the prospective design. The negative quadratic sign is present in the polynomial powers.

The coefficient formula and total-degree bound retain exactly degrees<=M: mathlib truncTotal is exclusive, so M+1 is essential. Multiplication locality is proved by the actual multiindex antidiagonal and component degree bounds. Truncation is never incorrectly asserted to be an ordinary polynomial algebra hom.

auxiliaryFormalExp_neg explicitly identifies substitution of evalNegHom(exp) with e(-U), including powers of -1. auxiliaryFormalExp_mul_neg applies the actual substitution AlgHom to exp*exp_neg=1. Compensation then commutes the formal series and cancels the quadratic pair. This supplies every retained coefficient and the aggregate truncation identity without claiming equality in the tail.

The unused _hS premise in compensation_series_coeff is **not a gap**. Its proof only needs substitution at the zero-constant quadratic Q: cancellation holds for the arbitrary formal-series factor F=e(S) already defined by Lean. No exp-add or substitution homomorphism at S is used there. The source-zero premise is genuinely used in the finite algorithm, finite coefficient and source locality results; it keeps the exported compensation API within the intended source domain. Removing it from the cancellation theorem would be optional strengthening/clarity cleanup, not a required correction. This does not justify analytic-exponential semantics for nonzero-constant S.

The normalized integral is the actual Bochner integral against Measure.pi(gaussianReal 0 v), divided by product_i(beta_i!). It calls the accepted full auxiliarySeries identity, whose series coefficients are independently defined by these integrals. The raw theorem proves the factorial product nonzero and multiplies back with the correct factor. integrable_compensation_monomial separately calls integrable_auxiliaryWeight_mul_monomial. That dependency proves integrability via the finite Hermite support sum and integrable affine Hermite monomial products, without a conclusion-valued integrability hypothesis or integral-by-default-zero shortcut. The accepted dependency hash is `91b9884a4194980538b2889f8b57f6c09cf995dfdfa1db71241c00723472375f`.

Source locality is correctly proved by finite coefficients and truncTotal power locality. It includes source terms above the cutoff. No positivity, reality, degree-four restriction, nonempty-coordinate restriction, conjugation of source coefficients or fitted-weight assumption occurs.

## Discriminating controls

With q=sigma²/2, direct multiplication independently gives:

- S=iX,M3: P coefficients (1,i,-1/2-q,-i/6-iq); compensation gives (1,i,-1/2,-i/6). Both complete retained vectors are proved in the candidate.
- S=(1+i)XY,M4: degree2 coefficients are (-q,-q,1+i); degree4 coefficients are q²/2 at X4/Y4, -(1+i)q at X3Y/XY3, and q²+i at X2Y2. The complete displayed coefficient vector is proved, using decomposed homogeneous coefficient lemmas. The compensated (2,2) coefficient is i and the actual raw integral is 2!*2!*i=4i, not 4!*i.
- S=iX7,M7: P coefficients are (1,0,-q,0,q²/2,0,-q³/6,i); compensated coefficients are1 at0, i at7, zero at1..6. The actual seventh raw integral is7!*i=5040i.
- The degree7 source survives at M7 and is discarded at M6. An added nonreal degree8 source term changes no M7 compensation polynomial. The general locality theorem supports arbitrary such source tails.
- M0 gives P=1 and actual degree-zero integral1. The empty-coordinate theorem proves S=0 and P=1 for every M; generic actual integral/integrability theorems include this case with no Nonempty premise. Zero source is explicitly identified with the truncated negative Gaussian exponential.
- Actual raw integrals at sigma2/variance4 and sigma1/2/variance1/4 both give5040i. Intermediate P coefficients depend on q while retained source moments cancel that dependence.
- S=0,M0,sigma2 has transformed degree2 coefficient2. This is an explicit nonzero tail and a counterexample to the unclaimed global formal-series equality.

These checks confirm the intended finite algorithm and normalization, rather than a scalar or real-only substitute.

## Actual independent matching-wt1 evidence

The companion JSON retains the exact frozen source and every complete actual request/response from this review, including all line contexts and pre/post goal states.

- Initial and final full-file lean_diagnostic_messages: success=true, timed_out=false, items=[], failed_dependencies=[].
- One ROOT-authorized lean_run_code invocation contains the **exact full frozen source prefix** followed by all40 public #print axioms commands. It returned success=true, timed_out=false and precisely40 distinct named info reports, all with [propext, Classical.choice, Quot.sound]. No warning/error diagnostic occurred.
- Six actual lean_verify checks with scan_source=true cover compensationPolynomial_eq_finite, compensation_series_coeff, integrable_compensation_monomial, integral_compensation_normalized, integral_compensation_raw and compensation_source_truncation. Each returned exactly the standard3 axioms and warnings=[].
- Forty independently selected final closing-line lean_goal queries returned goals_after=[] for every public theorem, including the deeply indented final support contradiction in auxiliaryFormalExp_coeff.
- The frozen source SHA256 was checked before the batch and after the final diagnostics. It is unchanged. Final identical continuity check is fresh=true.

No matching MCP failures, new axioms, sorry, native_decide or heartbeat overrides were encountered. The exact-source batch kernel check is complete public-export coverage; the six lean_verify calls are additional actual headline checks and are not represented as40 sequential verify calls. This is scoped kernel evidence, not a full-tree build result.

## Acceptance boundary

No necessary correction or counterexample to the claimed A/Eq4 result was found. **ACCEPT** this implemented ordinary compensation package for ROOT's subsequent authoritative absorption and gates.

Actual original Grassmann Eq7/design B+C remains OPEN: genuine8V-generator algebra, original coframes/source conventions, global joint nilpotence, evaluation bridge and actual G-valued integrability/equality still require their own implementation and review. Original Eq9–11 matrix/sign assembly, Berezin determinant/orientation, Haar/Fubini, insertions, nonzero Z, phase/sampling, physical source/Legendre/state/domain/B3/modes/transport, limits and simulation remain open. No entire-publication green state is inferred.

Memory was used only for project discovery discipline and separation of local acceptance from publication; current candidate/kernel conclusions above were independently verified live.
