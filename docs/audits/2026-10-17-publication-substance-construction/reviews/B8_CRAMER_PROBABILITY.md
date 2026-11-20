# Independent actual-iid Cramér probability review

**Verdict: SCOPED COMPLETE MANUAL PROBABILITY ACCEPTANCE. No mandatory correction found in the declared finite-all-real-MGF theorem or its source countercontrols.** I did not author this proof. I independently challenged every section of CONSTRUCTION.md54c15572f967565c6df318ed0455a0c7257d830e550958c11a10011134b97e59. This accepts a complete manual proof of separate closed-set limsup and open-set liminf bounds for the stated class, not a Lean/kernel theorem, installed source, Novikov result, full I3/B8 closure, physical consumer or publication acceptance.

The declared class is a Borel probability on R whose ACTUAL MGF is finite at every real parameter. It includes the original genuine sub-Gaussian charter; a finite global sub-Gaussian exponential bound immediately gives those moments. The broader classical theorem assuming MGF finiteness only near0 is expressly not proved here. No broader original I3 consumer is waived or silently reduced to this class. The stronger hypothesis is the scope of this accepted milestone, not a newly imposed completion gate on other work.

## Actual objects, normalization and dominated derivatives (§§1–2)

I verified that the note begins with a probability measure, actual coordinate/product laws and actual exponential expectations; it neither supplies the desired LDP as a field nor calls an arbitrary function an MGF. For t=0 the integrand is1, so M(0)=1. Positivity gives M(t)>0, allowing the real logarithm. Probability measures supported on a constant still have positive MGF; the zero-function structural witness cannot be an actual degenerate law.

The local domination argument is sufficient for every derivative it uses. Explicitly, take |t-t0|<=delta. For each fixed integer k, |x|^k<=C_delta,k exp(delta|x|). Splitting x by sign bounds |x|^k exp(tx) by a constant times exp((t0+2delta)x)+exp((t0-2delta)x), whose integrals are finite by the declared all-real assumption. The same bound on nearby difference quotients justifies dominated differentiation. Thus M is smooth, all tilted first/second moments exist, and lambda'=M'/M and lambda''=M''/M-(M'/M)^2 are actual mean and variance identities.

The Esscher density exp(tx-lambda(t)) integrates exactly to1 and is strictly positive; the tilted and original laws have the same null sets. Multiplying the n coordinate densities proves the exact product Radon–Nikodym derivative exp(n[tL_n-lambda(t)]). Its inverse is valid because of equivalence and also integrates to1 under the tilted product. Product expectation factorization follows from the actual iid product and positive integrands, not from continuity of a predicate.

Jensen gives lambda(t)>=tE X for either sign t. Taking t=0 gives I>=0 everywhere, and Jensen plus that lower bound gives I(E X)=0. The extended supremum is convex/lower semicontinuous and proper, since it is finite at the mean. The two affine lower bounds at t=+1 and -1 make every finite sublevel bounded; lower semicontinuity makes it closed, hence compact. Negative sublevels are empty and compact. Infinite rates and empty sublevels are not replaced by arbitrary real values. No all-R finite continuity or zero-at-origin premise is imported.

## Upper bound: actual local Chernoff, tails and finite cover (§§3–4)

For every real t, the expectation of exp(ntL_n) is exp(nlambda(t)). On an event whose points satisfy ty-lambda(t)>=ell, the exponential is at least exp(n[ell+lambda(t)]). Integration gives P(event)<=exp(-nell), including t<0: the argument bounds the affine statistic directly and does not reverse the sample-mean inequality incorrectly.

The positive and negative t=1 tail estimates combine to the stated two exponential terms. Since lambda(+/-1) is finite, choosing K>=A+max(lambda(1),lambda(-1),0) bounds them by2exp(-nA). This proves exponential tightness at speed n for unbounded empirical means, not bounded support. The factor2 is retained and disappears only after log/n.

For a nonempty closed F, I independently checked every step of the compact-cover argument. For any finite ell<inf_F I, each x in the compact F intersect[-K,K] has some finite t_x with t_x x-lambda(t_x)>ell. A small interval preserves the non-strict lower threshold ell. A finite subcover has r independent of n. Adding the tail with A>max(ell,0) gives (r+2)exp(-nell); this is a legitimate finite-n prefactor, not a false prefactor1 assertion. If the compact intersection is empty, r=0 and the same tail estimate works.

Taking limsup gives at most-ell. Letting ell increase to a finite infimum, or increase without bound when the infimum is infinite, proves the entire closed upper bound. For infimum0, negative ell suffice and their limit is0. F empty has log probability minus infinity immediately. The proof therefore includes unbounded closed sets, infinite-rate sets and zero events without forgetting a compactness tail.

## Strict tilted mean range and actual optimizers (§5)

For a non-Dirac law, zero tilted variance would force X constant under an equivalent tilted measure and therefore under the original law, a contradiction. Hence lambda''(t)>0 for every finite t. Lambda' is continuous and strictly increasing, with finite values.

Let b be the essential supremum. For finite b, X<=b almost surely gives lambda(t)<=tb for t>0. For every finite y<b, P(X>=y)>0 supplies lambda(t)/t>=y+log(P(X>=y))/t. These inequalities give lambda(t)/t->b; if b=+infinity, the same lower bounds for arbitrarily large y give divergence. The average identity lambda(t)/t=t^-1 integral_0^t lambda'(s)ds identifies the same extended limit with that of the monotone derivative: for a finite monotone limit its Cesàro average has that limit, and for an infinite limit the average eventually exceeds any finite bound. Reflection gives the lower endpoint a at t->-infinity.

At a finite essential bound, equality of a tilted expectation with that bound would force a constant law; infinite bounds are automatically strict since tilted moments are finite. Thus lambda' maps R continuously and strictly increasingly ONTO(a,b). Each interior x has a unique finite t. The convex tangent inequality proves tx-lambda(t) dominates every other dual value, so I(x)=tx-lambda(t)<infinity. The optimizer is derived, not assumed as an exposure hypothesis or a supplied Legendre identity.

## Open lower bound, endpoints and degeneracy (§6)

For an interior x in open G, choose its actual optimizer t and a sufficiently small ball inside G. Under the genuine Esscher product, independence makes the variance of L_n equal lambda''(t)/n; centered cross terms vanish and the finite tilted variance was proved already. Chebyshev gives Q_n(ball)->1. The bound may be negative for small n, which is harmless: it supplies eventual positivity and log Q_n(ball)/n->0.

The inverse density on the ball is bounded below by exp(-n[I(x)+|t|delta]). Integrating it under Q_n proves the claimed lower bound. This works for both signs of t and for t=0. Letting delta decrease to0 yields liminf>=-I(x). No LDP, full law-of-large-numbers theorem or desired decay rate is assumed; finite-variance concentration is explicitly established.

The endpoint treatment is complete and avoids an unjustified claim that all finite-rate points have finite tilts. For finite b, exp(t(X-b)) is bounded by1 for t>=0 and decreases to the atom indicator. Its expectations converge to p_b. For ANY real t the expectation is at least p_b, so the dual endpoint supremum is exactly-log p_b, including infinity if p_b=0. If the atom is present, the actual all-coordinates-equal-b event has probability p_b^n and provides the endpoint lower bound whenever b belongs to G. If the atom is absent, the endpoint rate is infinite and its pointwise lower requirement is trivial. Reflection proves the a endpoint. Infinite endpoints do not represent omitted real points.

Outside a finite support bound, the appropriate signed t and lambda(t)<=tb or ta make the dual value diverge, so the rate is infinite. Every finite-rate real point is consequently an interior point or a finite endpoint already handled. Taking the supremum of the proven lower bounds over all finite-rate points of G gives-inf_G I even if that infimum is not attained. If no such point exists, including G empty, the required bound is-minus infinity and automatic.

For a Dirac law delta_d, lambda(t)=td and the dual rate is0 at d and infinity elsewhere. Every empirical mean equals d. Both inequalities follow directly for sets containing d or excluding it, including the constant-zero law. This separate case is necessary because strict variance/range arguments fail there; it is explicitly present.

## Exact controls and source contradictions (§7)

I independently verified the Bernoulli tilt solution exp(t)=x(1-p)/(p(1-x)) and substitution yielding binary relative entropy. The endpoint values are-log(1-p),-log p; rates outside[0,1] are infinite; the mean p has zero rate. Centering translates the rate/support and still does not make it finite on all R. Bernoulli genuinely lies in the target sub-Gaussian class: its tilted variance p_t(1-p_t)<=1/4 bounds lambda(t)-pt by t²/8 after integrating twice, for either sign t. Thus this is an internal counterexample to the source's all-R finite continuous-rate requirement, not an out-of-class objection.

For F={0,1}, P_1(F)=1 while exp(-inf_F I)=max(p,1-p)<1. For general n the probability is p^n+(1-p)^n; log/n has the correct max-rate limit. The finite-n prefactor1 statement fails while the actual asymptotic closed upper remains true.

Completing the square in the normalized shifted Gaussian integral gives lambda(t)=mt+sigma²t²/2; maximizing the dual gives (x-m)²/(2sigma²)>=0. Subtracting I(0) produces x²/(2sigma²)-mx/sigma², negative between0 and2m when m>0. That artificially normalized function is not this law's Cramér rate. A different signed fluctuation functional needs a distinct derived meaning.

For standard Gaussian samples, an orthogonal transformation preserves the product density/Jacobian and makes sqrt(n)L_n a standard Gaussian. On G=(c,infinity), c>0, replacing1 by x/c in the positive tail integral gives
P(L_n>c)<=exp(-nc²/2)/(c sqrt(2pi n)).
The ratio to exp(-n inf_G I) tends to0. This refutes a universal relative lower prefactor1+o(1), while preserving the logarithmic lower theorem. A Gaussian singleton has probability0 and finite rate, independently refuting any unrestricted closed-set lower bound. No finite-n or relative-prefactor strengthening is smuggled back into the accepted result.

Finally E exp(0X)=1 for every actual probability law, including Dirac. The source's zero MGF is purely a structural witness. Its continuity and upper-normalization predicates cannot imply independence, product expectation, an Esscher law, nonnegative extended rate or probability decay.

## Actual source, original charter and remaining native/Novikov work (§8)

I personally read COMPLETE CramerIID.lean, CramerLowerBound.lean and Itô/Novikov.lean. Both Cramér predicates are literally the same four-property conjunction Continuous I, I0=0, Continuous mgf, mgf0<=1; their zero-function witnesses and closure theorems are true proofs of that conjunction. They do not contain a probability law, iid means, MGF expectation, Legendre rate, tilted measure or either logarithmic limit. This review preserves their truth and does not rewrite or rename their API. Incorrect probability descriptions in their comments are distinguished from theorem bodies.

Novikov's actual body is0<=T and Continuous theta for deterministic theta:R->R. Its true constant witness/overall conjunction theorem does not construct Brownian stochastic integration, quadratic variation, exponential integrability or a uniformly-integrable exponential martingale. That is a separate original B8 branch. The required filtered probability/Brownian/predictable-integrand/finite-horizon exponential-martingale construction and Novikov criterion remain owed; this Cramér acceptance supplies none of them.

I read the current Phase6s in-repo-authorized/external-gated table, complete Track2 and authority contexts, and Phase6o Wave3b end-to-end. Those preserve original Itô, Cramér, Sanov, contraction, Varadhan and LDPCompatible consumers. Historical substrate/kernel labels are not fresh actual-probability acceptance. In-repo substantive work and separately gated upstream submissions are distinct; old general gate language is not used to invent a new permission gate on already authorized manual work. No external communication or Mathlib submission occurred. No live Mathlib API, theorem availability/absence or current build is inferred from roadmap text.

Next native work remains actual probability/product/independence/exponential-integrability and extended-rate interfaces; Esscher RN/derivatives; upper finite cover/tightness; lower variance/tilting; boundary/Dirac controls and honest consumers, under ordinary ROOT admission and independent source/kernel verification. The broader near-zero-only-MGF theorem, other I3 consumers and actual Novikov remain distinct unfinished work. No new axiom, assumed LDP field, same-predicate witness, finite-rate restriction, infeasibility finding or scientific deferral is accepted as a replacement.

## Evidence, independence and process

I did not author this probability construction. I previously authored unrelated documentary assemblies carrying the B8 owed row; that row is used here only for scope provenance, not independent acceptance of my own mathematics. The lead is the actual proof author. Complete PLAN/CONSTRUCTION/REPORT were personally read; all eight argument sections and controls are reviewed above. R55 and governing contracts were personally read in the immediately preceding assigned work at the same exact current bindings, and those bindings are rechecked here. Complete native bodies and targeted owning-roadmap contexts were freshly personally read. A broad roadmap search display was truncated and followed by complete relevant Track2/Wave3b range reads; unrelated waves were not scientifically re-audited.

The FIRST original check actually returned0/fresh/changed[] before inspection, tool7feccf. Its exact argv/cwd/stdout/stderr/rc are retained; that direct call did not expose separate subprocess UTC endpoints, so timestamps remain null. No timing is reconstructed. A captured stdlib read/hash/stat/JSON operation at2026-10-18T01:36:12.974367+00:00 through01:36:13.011020+00:00 actually returned0. It checks all23 current reference occurrences and64 selected N source pins against the original packet, and binds nine immutable original author/packet/process files. Stat/read/restat comparisons and terminal comparisons establish bounded source preservation observations, not an atomic attestation or mathematical proof. All source pins are hashed; unrelated source mathematics is not audited by hashing.

Only the five assigned ignored review outputs are written. All original author artifacts, failures and first0/final1-owned-only outcomes remain intact. No mathematical software, symbolic/numerical model, project import/test/Verify, Lean/native/MCP/controller/build/compiler/render/network, Git/index/ref/source/holding/registry/notebook/closure mutation ran. The authorized continuity adapter gives freshness evidence only. Actual captured commands preserve argv/cwd/UTC/rc and separate raw/base64 output channels. Direct text reads retain tool chunks without invented missing process metadata. Original final check is recorded without refresh. The historical N raw-index FAIL/cause UNKNOWN remains unwaived.

This is a complete scoped MANUAL probability milestone. It does not accept installed/native source, actual consumer physics, full B8/I3/G4/G5/G11, closure, protected/main integration, external submission, publication or genuine human review.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory correction was found in the actual finite-all-real-MGF proof. The source's zero MGF, all-R finite continuity/fixed-origin normalization and finite-n/relative-prefactor descriptions do not state the actual probability theorem; the construction supplies precise countercontrols and proves the correct separate logarithmic statements. Full stochastic/native/consumer work and any broader near-zero-only domain remain open, without narrowing the original BUILD or creating a new gate.

Terminal ORIGINAL check actually returned1 with changed=["owned-files"] only, stderr empty. All96 bound reference/source/author-file observations preserve hash/mode/size/ns-mtime at terminal capture. The original packet was not refreshed. The five assigned ignored review files are the only authored outputs. Scoped complete manual probability acceptance stands; no native/fullI3/Novikov/closure/publication acceptance follows.
