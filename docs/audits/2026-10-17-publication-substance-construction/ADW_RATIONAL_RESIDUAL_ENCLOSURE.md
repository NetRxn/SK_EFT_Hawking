# Regulated scalar root: an explicit rational evaluator and enclosing algorithm

Scientific author: publication lead `/root`. **Independently reviewed manual algorithmic construction**, with the [complete nonauthor review](reviews/ADW_RATIONAL_RESIDUAL_ENCLOSURE.md). This continues the independently reviewed regulated scalar construction by deriving finite rational residual/error enclosures. No evaluator, optimizer, numerical test, native proof or physical model is executed or installed by this note. The separate NJL repair remains distinct. Full microscopic ADW, unrestricted scalar production optimization, error/consumer qualification and native obligations remain owed.

## 1. The exact target, rather than an optimizer success flag

The antecedent derives, for r>1 and z=C²/Lambda²>0,

    J(z)=integral_0^1 t²/(z+t)² dt
        =1-2z log(1+1/z)+z/(1+z),
    f_r(z)=1/r-J(z).

J is strictly decreasing from1 to0. The unique positive zero z_* is the unrestricted scalar minimum in magnitude. On a positive bracket [a,b] containing it,

    f_r'(z)>=mu=2/[3(b+1)³]>0,
    |u-z_*|<=|f_r(u)|/mu.                              (1)

The original real proof does not certify a floating logarithm, subtractive cancellation or a small raw V'(C). This note constructs finite exact-rational interval evaluations and a sign-or-error refinement that avoids assuming a sign when the root is very close to a midpoint.

First take a positive RATIONAL r>1 and positive RATIONAL Lambda. Every finite binary input can be represented as its exact rational value; that convention does not remove experimental uncertainty or identify the exact physical G/G_c. Section6 separately encloses pi and the actual supplied-parameter ratio. No ordinary float operations are assumed exact.

## 2. Fast positive enclosure when z>=1

For rational z>=1, set q=1/(1+z), so0<q<=1/2. Expanding a nonnegative geometric derivative under the integral gives

    1/(z+t)²=q²/[1-q(1-t)]²,
    J(z)=2q² sum_(j=0)^infinity q^j/[(j+2)(j+3)].        (2)

Indeed the integrated coefficient is

    (j+1) integral_0^1 t²(1-t)^j dt=2/[(j+2)(j+3)].

The beta integral follows by repeated integration by parts, or integrating the finite polynomial; uniform convergence follows from q<=1/2. For M>=0 let S_M contain j=0,...,M. All terms are rational and positive. Since their denominator increases,

    S_M <= J(z) <= S_M+E_M,
    E_M=2q^(M+3)/[(M+3)(M+4)(1-q)].                    (3)

The omitted term starts at j=M+1; bounding all later denominators by (M+3)(M+4) gives exactly the geometric tail in(3). E_M tends0. Thus a finite rational sum supplies any requested positive rational absolute error without cancellation or unproved floating conditioning. It is not a new evaluation of the current production module.

## 3. Logarithm enclosure for 0<z<1

Put X=1+1/z>1. By exact rational comparisons choose k>=0 with 2^k<=X<2^(k+1), and set y=X/2^k in[1,2). Then

    log X=k log2+log y,
    v=(y-1)/(y+1) in[0,1/3).

For 0<=v<1, integrate the geometric series of 1/(1-v²) from0 to v:

    log((1+v)/(1-v))=2 sum_(j=0)^infinity v^(2j+1)/(2j+1).

Writing L_M(v) for the sum through j=M,

    L_M(v)<=log((1+v)/(1-v))<=L_M(v)+T_M(v),
    T_M(v)=2v^(2M+3)/[(2M+3)(1-v²)].                    (4)

At v=0 the value and tail are exactly zero. At v=1/3 the same formula encloses log2. Therefore use the rational interval

    ell_lo=k L_M(1/3)+L_M(v),
    ell_hi=ell_lo+k T_M(1/3)+T_M(v)

for log X. Its width tends0 for every fixed positive rational z and finite k. Different truncation orders for the two series are permitted with their own tails.

The exact closed form yields

    1-2z ell_hi+z/(1+z) <= J(z)
        <=1-2z ell_lo+z/(1+z).                         (5)

Intersect with the independently proved interval[0,1] if helpful; do not silently discard a contradictory enclosure. Near threshold one may instead enclose

    h(z)=1-J(z)=2z log X-z/(1+z),
    f_r(z)=h(z)-(r-1)/r.                               (6)

All operations here are rational, so close cancellation changes required precision/cost rather than correctness. The widths in(5) and(6) are 2z(ell_hi-ell_lo). No computed logarithm, finite hardware mantissa, fixed origin guard or empirical residual tolerance enters these proofs.

## 4. Sign-or-error bracket refinement, including an exact-midpoint root

For the rational r>1 choose an integer power of two b with b²>=2r/3. Starting at1 and doubling terminates for every finite r. The original positive integral bound gives

    J(b)<1/(3b²)<=1/(2r), so f_r(b)>1/(2r)>0.

Take a=0, with the continuous limiting sign f_r(0)=1/r-1<0. The root is strictly inside. The antecedent's positive lower endpoint (r-1)²/(16r²) is an optional improvement, not a fixed minimum search fraction.

At an outer iteration let w=b-a>0 and u=(a+b)/2>0. Compute a rational enclosure [F_lo,F_hi] for f_r(u), using(3) or(5)/(6). Increase the series accuracy until one of these alternatives holds:

1. F_hi<0: set a=u. Monotonicity proves every root of the fixed target remains to the right.
2. F_lo>0: set b=u. The root remains to the left.
3. Neither strict sign is certified and R/mu<w/4, where R=max(|F_lo|,|F_hi|) and mu is(1): replace the bracket by its intersection with [u-R/mu,u+R/mu].

In the third case f_r(u) belongs to the enclosure, so(1) proves containment; the new width is at most2R/mu<w/2. Endpoints remain nonnegative after intersection. If an exact rational evaluation somehow certifies R=0, return the exact root u instead of a zero-width loop.

Each inner refinement terminates in exact arithmetic. If f_r(u) is nonzero, convergent enclosing intervals eventually certify its strict sign. If it is zero, R tends0 and the third alternative eventually holds. This argument does not assume the root is irrational or falsely divide by a small numerical value. Each outer step halves the width or better, so any positive rational z-width target is reached in finitely many steps. Intermediate rational integers may be large; no runtime or complexity benchmark is asserted.

A finite implementation must bound work explicitly and return an unresolved enclosing result or an exception on budget exhaustion, never a fabricated root or global-minimum flag. Such a resource outcome is not proof that the mathematical/physical construction is infeasible or an approved deferral of its repair.

## 5. Actual magnitude enclosure, rounding and energy consequence

For a nonnegative rational x=n/d and integer p>=0, choose

    k=floor sqrt(floor(n 2^(2p)/d)).

Integer square comparison gives

    k/2^p <= sqrt(x) < (k+1)/2^p.                        (7)

An integer-square-root algorithm computes k with exact integer arithmetic. Applying(7) to bracket endpoints encloses

    Lambda sqrt(a) <= C_* <= Lambda sqrt(b).

The combined C interval width is at most Lambda[sqrt(b)-sqrt(a)+2*2^(-p)]. Since sqrt(b)-sqrt(a)<=sqrt(b-a), rational bracket refinement and increasing p reach every positive absolute magnitude tolerance. A rational midpoint of the final C interval has error at most half its width. This is an unrestricted magnitude certificate; the signed exact ansatz has both minima ±C_*.

If a downstream API returns a binary float c, include its exact rational rounding displacement from that midpoint in the error budget, or compare its exact binary rational value directly with the enclosing endpoints. Overflow, a rounded zero on a declared positive branch, nonfinite results or an unmet tolerance require explicit refusal/unresolved status. Do not replace a too-small positive root by the absolute numerical zero guard.

For a chosen z point inside the bracket, the original strong-convexity argument gives

    0<=V(C_hat)-V(C_*)<=A Lambda^4 R²/(2mu),
    A=N_f/(16pi²), C_hat=Lambda sqrt(u).                 (8)

If the returned C is rounded, recompute the exact rational point z_c=(c/Lambda)², enlarge the containing bracket if needed, and reevaluate its residual enclosure and derivative lower bound there before claiming(8) for that returned value. Alternatively retain only the directly proved magnitude interval. A rational C approximation and an exact square-root expression must not be conflated. Dimensional scaling and uncertain A need their own enclosures.

The closed cutoff-constrained problem is different: if the unrestricted root exceeds1 in z, the minimum on0<=C<=Lambda is its boundary, with the correct sign/KKT certificate. The strict cutoff domain may have only an unattained infimum. None of this is a license to return a capped unrestricted root.

## 6. Optional physical-parameter ratio and pi enclosure

For supplied positive rational G,N_f,Lambda, the written ansatz uses

    r=G N_f Lambda²/(8pi²).

Treating an ordinary computed G/G_c as exact would certify a nearby model, not automatically this one. A self-contained rational pi enclosure is available without assuming a platform's pi constant error.

For 0<t<1 the alternating integral expansion gives

    arctan(t)=sum_(j=0)^M (-1)^j t^(2j+1)/(2j+1)+remainder,
    |remainder|<=t^(2M+3)/(2M+3),

with the next-term sign. Hence consecutive partial sums bracket the value. The identity

    pi=16 arctan(1/5)-4 arctan(1/239)                    (9)

can be verified rather than imported as an unqualified approximation: tan(2 arctan(1/5))=5/12 and tan(4 arctan(1/5))=120/119; subtracting arctan(1/239) gives tangent1. The angle is positive and below pi/2 (4 arctan(1/5)<4/5<1<pi/2, while arctan(1)>1/2 follows by its defining integral). It is therefore pi/4. Positivity follows, for example, from arctan(1/5)>=5/26 and arctan(1/239)<1/239. These elementary inequalities also select the correct tangent branch.

Combining the alternating rational bounds in(9), with subtraction reversing endpoints as required, gives 0<pi_lo<=pi<=pi_hi after enough terms. Thus

    r_lo=G N_f Lambda²/(8 pi_hi²),
    r_hi=G N_f Lambda²/(8 pi_lo²).                        (10)

If r_hi<=1, the unique exact-ansatz minimum is the origin. If r_lo>1, a supercritical branch is certified. If the interval straddles1, refine the pi enclosure or report threshold unresolved; do not infer a zero or positive branch. No termination promise for an unresolved exact-threshold question is manufactured from numeric input provenance.

For a supercritical parameter interval, enclose f at any positive z by

    1/r_hi-J_hi <= f_r(z) <= 1/r_lo-J_lo.                (11)

Strict signs are then valid uniformly over that interval. The error alternative in section4 encloses all its roots with the same mu. If pi is the only unresolved parameter, its intervals can be refined together with J; conditional on the actual branch and a requested finite tolerance, the same sign-or-error convergence applies. Genuine nonzero experimental/input uncertainty need not shrink: return the resulting parameter-dependent root enclosure or an honest unattainable-precision result instead of erasing that uncertainty. Monotonic root dependence on r, already proved in the antecedent, supplies a separate cross-check.

The source's real positive N_f arithmetic and the physical interpretation as a number of species remain distinct; neither arbitrary fractional physical species nor a gravitational scale map is derived. This note is not a new physical vacuum-density prediction.

## 7. Proof controls and concrete implementation obligations

- Large-z series(2) starts with q²/3 and positive terms; omitting the q² factor or shifting M's tail index breaks(3). z=1 is admitted on either evaluation route.
- Small-z evaluation keeps the actual logarithm of1+1/z, its range-reduction factor k and both log2/remaining tails. Dropping k would be a substantive residual defect.
- The root at a rational midpoint does not force an infinite sign search; the certified residual-to-distance alternative handles it without guessing.
- r=1 has no positive root and must not enter the r>1 branch. A parameter interval crossing1 remains unresolved until distinguished.
- Zero lower bracket endpoints are mathematical limits, not a positive root replacement. Roots below the old10^-6Lambda floor and aboveLambda remain inside the unrestricted algorithm.
- Series/rational exactness is a mathematical model of an implementation, not proof that Python Fraction, integer-root code, serialization or output rounding is correctly wired. Actual implementation needs independent reference and real entrypoint/consumer/mutation controls, including exhaustion and malformed/nonfinite input refusal.

The accepted scalar analysis supplies the existence/global-minimum/error results; this note supplies a constructive way to discharge its previously open residual-error/sign premise using finite rational operations. It does not repair the current fixed-window scipy optimizer, its canonical potential's flat guard, its phase/report consumers or any numerical source by being written. The next accepted scientific action is independent full mathematical review, then a coherent canonical-formula/solver/consumer implementation under ROOT's ordinary exclusive runtime admission, preserving the stronger NJL and r8 reporting work. Native theorem and all original physical ADW/state/modes/magnitude obligations remain OPEN.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

An exact real residual formula and sparse passing numerical samples do not establish a global error enclosure. Conversely, cancellation is not itself a demonstrated impossibility: explicit positive/geometrically convergent rational series and a sign-or-error bracket give a constructive route. A truthful proposal, exact arithmetic proof or resource-refusal design is still separate from an executed production optimizer, native verification, physical domain and calibrated model.
