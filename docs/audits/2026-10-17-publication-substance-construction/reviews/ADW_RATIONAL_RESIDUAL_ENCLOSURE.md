# Independent ADW rational residual and enclosing-root review

**Verdict: SCOPED MANUAL ALGORITHMIC CONSTRUCTION ACCEPTANCE. No mandatory mathematical correction found.** I independently rederived equations(1)–(11), including both series tails and indices, the sign-or-error stopping argument, exact rational magnitude/output qualifications, Machin branch proof and parameter-uncertainty limits. This pays a real mathematical residual-enclosure premise of the distinct regulated-potential/root7 construction. It is not an implemented evaluator/optimizer, a passing numerical sample, a native proof, physical ADW derivation, source application or publication/closure/main acceptance.

The lead authored this new construction; I am its independent nonauthor reviewer. The accepted antecedent scalar derivation and its full independent review are read and credited at their exact scope. No separate NJL computation or physical species/state/magnitude result is substituted.

## Target normalization, monotonicity and common bracket: (1)

The antecedent exact ansatz has V=A Lambda^4 W_r(z), A=N_f/(16pi²)>0, z=C²/Lambda² and W_r'=f_r=1/r−J. Its positive integral is J(z)=integral t²/(z+t)²dt on[0,1]. Thus J strictly decreases from1 to0, f increases from1/r−1 to1/r and the unique positive root exists for r>1. It is the normalized unrestricted magnitude minimizer; the physical magnitude is C*=Lambda sqrt(z*), with two signed minima±C*. Sharing Gc with NJL does not identify their nonzero roots.

For z<=b, differentiating the positive kernel gives f'(z)=2integral t²/(z+t)³dt>=2/[3(b+1)³]=mu>0. Integration of this lower bound between positive points proves |u−z*|<=|f(u)|/mu. The zero lower endpoint later used is a continuous limiting endpoint; no finite derivative at0 is needed. This checks(1) and its use after bracket refinement. It does not certify a floating logarithm, a raw derivative threshold or a fixed bounded optimizer.

## Positive q-series and exact tail: (2)–(3)

With q=1/(1+z), z+t=q^(−1)[1−q(1−t)]. For z>=1,0<q<=1/2, so the differentiated geometric series converges uniformly for t in[0,1]. Multiplying by t² and integrating gives coefficient (j+1)integral t²(1−t)^jdt. Repeated integration by parts gives the integral2/[(j+1)(j+2)(j+3)], hence the coefficient2/[(j+2)(j+3)]. This yields exactly J=2q² sum q^j/[(j+2)(j+3)] and leading term q²/3.

When S_M includes j=0 through M, the first omitted exponent is q^(M+3) and its denominator is (M+3)(M+4). Every later denominator is larger. Bounding them below by that first omitted denominator and summing the geometric q-series gives E_M=2q^(M+3)/[(M+3)(M+4)(1−q)]. This verifies both indices and the factor2 in(3), including M=0 and z=1. Terms are positive rationals; S_M<=J<=S_M+E_M and E_M→0. This is an absolute exact-arithmetic enclosure, not an evaluated production prefactor or a measured convergence rate.

## Range-reduced logarithm and cancellation: (4)–(6)

Exact rational comparisons choose finite integer k with2^k<=X<2^(k+1), X=1+1/z. Then y=X/2^k lies in[1,2), v=(y−1)/(y+1) in[0,1/3), and log X=k log2+log y. Integrating2/(1−v²) termwise gives2 sum v^(2j+1)/(2j+1). After j=M, the first omitted power is2M+3; replacing all later denominators by2M+3 and summing powers v² proves T_M=2v^(2M+3)/[(2M+3)(1−v²)]. At v=0 both value and tail are exactly0. The same proof at v=1/3 gives a rational enclosure of log2.

Multiplication by nonnegative integer k and addition preserve the displayed ell_lo/ell_hi bounds. Their width tends0 at each fixed rational z>0, even if k is large. In J=1−2z log X+z/(1+z), the negative coefficient −2z reverses the log endpoints exactly as(5) states. Intersecting a valid enclosure with the known[0,1] range preserves J; an empty intersection would be a failure, not evidence to discard. Subtracting J from1 gives h=2z log X−z/(1+z), and 1/r−J=h−(r−1)/r proves(6). The width is2z times the log-interval width. Cancellation affects rational bit size and work, not the validity of the exact enclosure; this does not certify hardware roundoff or an existing log implementation.

## Sign-or-error algorithm and finite termination

Choose a power-of-two integer b with b²>=2r/3. Doubling from1 reaches this for every fixed finite rational r. The strict integral estimate J(b)<1/(3b²)<=1/(2r) gives f(b)>1/(2r)>0, while f(0)=1/r−1<0. Thus[0,b] contains the positive unrestricted root; no C<=Lambda cap or positive minimum search fraction is inserted. The optional lower endpoint from the antecedent remains valid but is not needed for termination.

At midpoint u, f(u) belongs to its rational enclosure. If the enclosure has a strict negative or positive sign, monotonicity justifies discarding the appropriate half. If neither strict sign is certified, R=max(abs endpoints) still bounds |f(u)|, so the common derivative bound implies z* in[u−R/mu,u+R/mu]. Intersecting with the current bracket preserves containment. Under R/mu<w/4 the new width is strictly less than w/2. The endpoints stay nonnegative, and the derivative lower bound remains valid on the smaller interval. Subsequent containment does not require the new endpoints to have separately certified strict signs.

For a fixed midpoint with f(u) nonzero, shrinking evaluator error eventually certifies its sign. If f(u)=0, the enclosure radius R tends0 and the distance alternative eventually fires. Exact R=0 returns u directly. Thus an exact-midpoint root does not trap the algorithm in an infinite sign search, and no irrational-root hypothesis is smuggled in. Every outer step halves width or better; finite refinement reaches any positive rational z-width request. All intermediate quantities in this fixed-r procedure are rational and finite, although their bit sizes/cost are not bounded by an empirical performance claim.

A finite implementation still needs an explicit work budget and truthful unresolved/enclosing output or exception. This is distinct from the mathematical fixed-input termination proof. Exhaustion does not authorize a false root/globality flag, prove physical infeasibility or reduce the original solver obligation.

## Integer square root, represented output and energy: (7)–(8)

For x=n/d>=0 and p>=0, floor(sqrt(floor(n2^(2p)/d))) equals floor(2^p sqrt(x)): integer-square comparisons are unchanged by taking the inner floor. Hence k/2^p<=sqrt(x)<(k+1)/2^p, including x=0 and perfect squares. This proves(7) without evaluating a floating sqrt.

Apply these rational lower/upper bounds at the root bracket endpoints and multiply by positive rational Lambda. The resulting magnitude interval contains C*. Its width is bounded by Lambda[sqrt(b)−sqrt(a)+2*2^(−p)], and sqrt(b)−sqrt(a)<=sqrt(b−a). Shrinking the root bracket and increasing p therefore reach every positive absolute rational magnitude tolerance. The midpoint has at most half-interval error. This is a statement about rational output, not a promise that a fixed binary format can represent every requested tolerance.

For a returned binary value c, its exact represented rational value and displacement from the rational midpoint must enter the error, or its distances to the certified endpoints must be bounded directly. Nonfinite/overflow, zero rounding on a positive branch and an unmet final tolerance remain refusal/unresolved cases. The claim never identifies a rational approximation, an exact square-root expression and a rounded production value. Actual conversion/serialization behavior is untested.

Strong convexity of W on the containing z bracket gives W(z*)>=W(u)+f(u)(z*−u)+mu(z*−u)²/2. Completing the square yields0<=W(u)−W(z*)<=f(u)²/(2mu), and multiplying by A Lambda^4 gives(8) with an enclosing residual bound R. The coefficient, normalization and energy units agree with the antecedent; it is not a bound inferred from small unnormalized V'(C).

If c is rounded, z_c=(c/Lambda)² is a different rational evaluation point. The note correctly requires a containing interval enlarged if necessary and fresh residual/derivative certification there before using(8) for c. A and dimensional/input uncertainty need their own enclosures. A magnitude interval can instead be reported without an unproved energy statement.

Closed cutoff-constrained and unrestricted minima remain distinct. If z*>1, the closed cutoff problem is minimized at its endpoint with the proper derivative/KKT sign, not an unrestricted root. A strict domain can have an unattained endpoint infimum. No capped solver is certified by the unrestricted construction.

## Machin branch, supplied parameters and uncertainty: (9)–(11)

The finite geometric expansion of1/(1+t²), integrated from0 to t in(0,1), produces the alternating arctan partial sum with next-term sign and absolute remainder at most t^(2M+3)/(2M+3). Consecutive partial sums therefore bracket each arctan exactly.

Writing a=atan(1/5), the double-angle formula gives tan(2a)=5/12 and tan(4a)=120/119. For b=atan(1/239), tan(4a−b)=1: numerator and denominator after clearing119*239 are both28561. Branch selection is proved rather than assumed: a>=5/26, b<1/239 give4a−b>0; a<1/5 gives4a−b<4/5<1. Also atan(1)>1/2 by integrating an integrand strictly above1/2 on[0,1), so pi/2=2atan(1)>1. Thus4a−b is in(0,pi/2), where tangent is injective; it equals pi/4. This proves(9) with no decimal pi approximation or imported machine-constant error premise.

Positive rational pi enclosures follow after finitely many terms, with subtraction reversing the arctan endpoints. Since pi is positive, inversion and squaring reverse order as stated in(10): r_lo=G N_f Lambda²/(8pi_hi²), r_hi with pi_lo. If r_hi<=1 the exact ansatz minimum is the origin; r_lo>1 certifies the supercritical branch. An interval touching/crossing the unresolved threshold cannot certify a positive branch or zero merely from nominal input. No exact-threshold termination promise is added.

For a supercritical r interval, f lies between1/r_hi−J_hi and1/r_lo−J_lo, proving(11). A common initial bracket must contain all its roots; choosing the displayed upper-endpoint rule with r_hi supplies it, with a=0. The derivative lower bound is independent of r and valid on that common bracket. Uniform strict signs and the distance alternative then preserve every admitted root. This is the existing bracket-containment premise applied to the interval problem, not permission to keep a too-small bracket derived from a nominal ratio.

When pi is the only uncertainty, jointly shrinking its enclosure and the J error makes the true residual enclosure converge. Conditional on a distinguished branch and finite tolerance, the same sign-or-error argument applies. Nonzero irreducible experimental/input uncertainty need not shrink; refinement cannot erase the resulting root range. Monotonic root dependence dz*/dr=1/[r²f'(z*)]>0 is a valid cross-check. Finite budgets/unresolved precision remain available, not an unconditional inner-loop termination claim for fixed-width uncertain input. A real computed G/Gc treated exactly would otherwise certify only a nearby model. Positive-real N_f arithmetic does not prove a fractional physical species interpretation or a gravitational scale map.

## Sources, controls and remaining full obligation

I read the complete accepted scalar source e3d7054e and its full independent manual review, including strict global/domain/bracket/error/asymptotic and both search-window countercases. Those are inherited at their explicit exact-ansatz scope; this new evaluator construction is independently derived above. The r8 target gap-equation preview was inspected as source, not executed or conflated with current installed source. Its guarded/fixed-window solver is not repaired by this note. Actual later honest scalar-status/reporting and the stronger NJL repair must be preserved during future canonical integration, not transplanted or recertified here.

Controls are mathematically meaningful: q² and first omitted indices prevent false large-z tails; log2's k factor and both tails are retained; z=1 admits either evaluation route; a zero midpoint residual uses distance/exact-root return; r=1 is outside the positive-root branch; zero lower limit does not replace a positive root; roots below the old lower search fraction or above Lambda are not excluded; uncertain input and finite work cannot produce fake successful numbers. Future implementation must exercise the actual evaluator, rounding, solver, wrappers/consumers and corruption/exhaustion controls with independent reference evidence. No such tests or samples ran in this review.

Canonical formula/solver/guard/status/consumer implementation, native integral/monotonicity/minimum/evaluator proofs and all original microscopic ADW/channel/source/state/mode/continuum/physical magnitude objectives remain BUILD. This new manual result discharges a mathematical evaluator premise; it is not their closure, a new gate/tracker, an approved deferral, numerical or physical G4/G5/G11 green, or protected Git/main delivery.

## Process and preservation

The original first packet check returned0/fresh/changed[] with actual separate complete stdout/stderr/base64, argv/cwd/UTC and fresh owned TMP/cache environment. The original packet is not refreshed. Existing r52 notebook and selected source/reference bindings are retained. All arithmetic reasoning above is manual; stdlib is used only for source/text/JSON/hash/process receipts, not mathematical model or symbolic/numerical evaluation.

One bounded read command guessed a nonexistent aggregate evidence filename and returned rc2; its actual native chunk192665/error is preserved. The correct existing installed/independent review inventory was then read without mutating anything. Truncated native displays were followed by bounded source reads. Native metadata is not assigned invented separated channels/UTC; first/final captured child commands retain their actual streams. Only the five owned ignored review outputs and fresh scratch are written. No project/model/test/Verify/native/Lean/compiler/Git/index/ref/source/notebook/holding/network mutation occurred. Historical original failures and raw-index FAIL/UNKNOWN are not erased or attributed.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

Cancellation is a real implementation hazard but not a proof that this residual cannot be enclosed: the positive q-series and rational range-reduced logarithm supply explicit shrinking absolute bounds. Conversely, exact formulas and constructive termination are not a certified production floating evaluator or an implemented global optimizer. The current construction correctly retains that distinction, the exact-midpoint alternative, output-point energy qualification and irreducible physical-uncertainty boundary. No mandatory mathematical contradiction was found within this complete declared algorithmic scope.

Terminal original check: actual rc1, changed=["owned-files"]; no refresh. All20 original references,64 selected current-source pins and the additional complete scalar review retain exact bytes/modes/mtimes=True. Only the five assigned ignored review outputs were created. No source application or numerical/native acceptance follows.
