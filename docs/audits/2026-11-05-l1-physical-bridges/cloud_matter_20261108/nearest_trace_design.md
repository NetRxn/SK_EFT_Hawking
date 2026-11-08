# Candidate nearest transverse-trace contraction

Scope: closed four-site pure-g2 action, fixed bare T=G22+G33 at nearest sites0,1. This is a new contraction design requiring independent source/math review before a full128-word target run. It does not use a remote matter-source frame or the mixed G02 machinery. All geometry, Haar and Berezin conventions are those of the existing audit; no original16-site work is restarted.

## Local exact tensors

The raw coframe used by `l1_transverse_top.py` is4 times the physical coframe. Its raw G is16 times one physical diagonal metric. Conditional integration of a source link gives `E[G_raw]=trace(K)`. For two unused independent collapsed links,

`Q = E[T] = trace(K)/8`.

In the original eight-generator local ordering, Q has masks195,60 with coefficient−6, and masks85,153,102,170 with coefficient−3. These are physical metric units; Q is a degree-four Grassmann tensor, not its top coefficient. In particular its square has top coefficient108=4*27.

Let c_i, i=0,...,5 be the two chiral three-vector components of the original **closed** quaternion commutator `B† A† B A`. The exact normalized product-Haar tensor is

`E[c_i c_j T] = delta_ij (49/216) Q`.

All30 offdiagonal/crosschiral slots vanish. The six diagonal slots have the same six-mask polynomial. Unweighted `E[c_i c_j]=(2/9)delta_ij`. Thus factoring T from curvature would miss49/48. The control directly constructs the closed commutator in the original quaternion convention, integrates each monomial using the exact sphere moment, and separately checks T's two source-link contributions agree. It also independently evaluates the forward commutator `A B A† B†` moments and checks equality term by term for every source monomial consumed. No isotropy assumption is used to discard components. The equality can also be understood by the Haar-preserving change of variables `(A',B')=(B†,A†)`; the bare collapsed G obeys `G(U†)=G(U)`, and T sums the two links symmetrically. The r0 receipt predates this explicit ordering check and is retained separately; its numerical pilot was a forward-order control, not yet an accepted original-source result.

## Exhaustive necessary support and erasure

The existing nearest support is128 unordered action words, each three distinct squared labels, ordered-weight sum11520 and32 orbits under translation0↔1 and transverse exchange. Every word touches both collapsed links at exactly one source site, and neither at the other. D cancels at the unused source; T leaves Q and cannot use that zero proof.

For every word, protect the two active source links and count every actual transport and curvature incidence. Both remote curvature planes admit successive private-Haar erasure. The only remaining plane is the local(2,3) commutator at the active source. Every transport link occurs exactly twice and is distinct from the five other transport links. Consequently all source-free transport factors are the archived `frame_pair` degree-two moments, including their endpoint signs. No shared fourth transport moment or remote matter frame is necessary.

Each remote erased curvature contributes2 in the archived scalar-square convention. The source-weighted commutator contributes `(16/9)*(49/48) Q = (49/27) Q`. The total curvature factor is196/27, multiplying Q0 Q1 and the three archived raw transport-square polynomials. The denominator is

`8^6 * 4^12 * (2!)^3`.

The first factor normalizes six frame-pair cubatures, the second converts twelve raw frames to physical coframes, and the last is the exact exponential multiplicity factorial. Source Q is already physical and contributes no additional16. The result is a raw coefficient of g2^6; divide by the matching Z8*g2^2 only after the full support sum.

## Bounded execution and acceptance

`nearest_trace.py --controls` checks the complete local source tensor and all128 necessary support/erasure/frame-incidence records. `--pilot` evaluates only the lexicographically first orbit representative, retaining its exact word and resource counters. `--orbit N` permits resumable individual representatives after review, and prints orbit size and full-word coefficient. It does not interpret one representative as a full correlation. All joins conservatively precheck candidate products before allocation and enforce120000 rows and3000000 products. The guard is installed into the unchanged archived factories' global wedge binding **before** any frame-pair/square construction. Factory calls/products and final joins/complement lookups are counted separately and combined. Existing exact caches are retained, so actual newly executed calls are charged. The r1 receipt's696 candidates covered only final joins; independent review found40256 additional factory candidates, and that incomplete accounting is preserved historically.

The prospective `--all` flag runs controls and32 representatives in one process, proves disjoint full128-word orbit coverage, and retains every representative. It carries the cumulative product offset into each representative's guard so the3000000 campaign cap is checked before each allocation. Its180-second timer begins before scientific imports. It also sums fixed-bare numerator source jets from the actual action charge of every orbit member, using E=(0,0,1,−1), rather than assuming representatives' charges are shared throughout orbits. The complete target is intentionally not run as part of this design handoff.

Independent review must verify the closed curvature ordering, quaternion-to-curvature convention, all scalar factors, original orientation and source normalization. Review should compare Q^2 against the existing local independent-link cross moment27 and check a deliberately factorized curvature-source replacement changes the pilot by48/49. The final campaign must retain every orbit result and certify128-word coverage before claiming the nearest covariance. Fixed bare observables have no explicit source derivative. The uniform coframe source multiplies each action word by exp(jq), so charge weighting differentiates the complete action product and includes X²+Y. The prospective normalized pair second jet uses the existing reviewed logZ_jj=954400425849600/113846304558673 and h=2sqrt(2)j. A covariance-jet interpretation additionally requires proving the one-point/source-jet subtraction vanishes; no such new acceptance is inferred here. Other source directions require separate derivations.
