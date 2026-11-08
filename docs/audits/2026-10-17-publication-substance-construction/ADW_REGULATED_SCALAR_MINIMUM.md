# ADW regulated scalar optimizer: exact global construction and error contract

**Author acceptance:** publication_e2_landing accepts the scientific author assignment for this bounded manual scalar construction under the original packet and the lead's accepted portfolio responsibility. Status: **MANUAL SCALAR CONSTRUCTION; production numerical/native implementation remains OPEN.** The source-copy change is this status sentence only; mathematical content is the frozen author report96dbe91a690b78b70b7d63ec139091df8935b9931d435a2185ec8a53f2b18c9e. Independent verification is required for acceptance. This is the root7 optimizer obligation, separate from the already accepted NJL root/bracket repair. It constructs exact real mathematics and a prospective numerical acceptance contract; it does not execute or change an optimizer, prove a native theorem, derive a microscopic ADW action or close a finding.

## 1. Existing owner/reference and delivered source

The existing objective is Phase5d Wave2's scalar computation, with the later installed Paper5 scalar-status spec/plan:
- docs/superpowers/specs/2026-10-17-paper5-scalar-status-and-figures-design.md, SHA ed2afb489ad6cb509b253d53dc1c5aacfcdb780ca68750206b338a04eb6f68cd;
- docs/superpowers/plans/2026-10-17-paper5-scalar-status-and-figures.md (full hash in evidence).

Root7 is an audit label, not a canonical finding ID minted here. No root7-specific canonical ID is assumed. The critical NJL substrate-lane finding and its c1343267 accepted numerical repair are distinct; they cannot be silently reused as acceptance of this objective.

Current N src/adw/gap_equation.py already has genuine later work: required domain/report checks, scalar_status, search_diagnostics, selected/unresolved distinctions, actual endpoint tags and explicit stationarity=not_evaluated/globality=restricted_comparison_only. The source returns legacy fields for compatibility, not an unrestricted global certificate. Controlled tests deliberately replace the minimizer and preserve the original objective/method/bounds; they meaningfully test that reporting contract, not the physical or global optimizer theorem. Existing real TestRegulatedScalarCorrespondence controls also address signed derivatives, a selected r=2 stationarity case, near-origin impostors and a root above the existing upper window. These are credited as source and dated receipts, not rerun.

The retained Paper5 runtime report records233 actual ADW cases and100 actual Fig29 rows, with explicit overlap and unverified diagnostic limits. No count is newly reproduced or upgraded by this author package. Later honest reporting does not repair the fixed search on (10^-6 Lambda,Lambda), its zero comparison, its absolute near-origin guard or its unmeasured global error.

Current canonical potential is the exact real ansatz below outside the separately documented numerical zero guard. Its physical HS/tetrad-channel derivation is UNCOMPUTED. Paper5 already distinguishes the regulated scalar stationary law from the NJL fixed-point law. This construction supplies the missing self-contained scalar global proof and a useful future root/error contract without changing any of those sources.

## 2. Domain, normalized objective and derivative

Assume finite real G>0, Lambda>0, N_f>0. The mathematical proof allows positive real N_f, matching the current arithmetic domain; it does not invent a new integrality restriction or claim a fractional physical species count. Put

    A=N_f/(16 pi²)>0,
    G_c=1/(2A Lambda²)=8pi²/(N_f Lambda²),
    r=G/G_c>0, z=C²/Lambda².

For magnitude C≥0 define V_exact(0)=0 and

    V_exact(C)=C²/(2G)-A[Lambda²C²-C⁴ log(1+Lambda²/C²)]
              = A Lambda⁴ W_r(z),
    W_r(z)=z(1/r-1)+z² L(z),   L(z)=log(1+1/z), z>0.       (1)

For signed real C use the even extension. C is not assumed bounded by Lambda in this unrestricted mathematical definition. A physical/EFT validity restriction, if imposed, is a separate constrained problem in §5.

Direct differentiation gives

    f_r(z)=W_r'(z)=1/r-1+2z L(z)-z/(1+z),
    V_exact'(C)=2A Lambda² C f_r(z), C≠0.                  (2)

The logarithmic term tends0 at the origin: z L(z)→0 and z²L(z)→0. For example the elementary bound L(z)<1/sqrt(z), proved in §4, suffices. Thus W extends continuously with W(0)=0, V is differentiable at C=0 with V'(0)=0, and

    V_exact''(0)=2A Lambda²(1/r-1)
                =1/G-N_f Lambda²/(8pi²).                 (3)

These exact-ansatz facts are not derivatives of V_num's flat |C|<10^-15 branch or statements about an arbitrary IEEE program.

## 3. Positive integral identity: monotonicity is proved, not assumed

For z>0 use an ordinary integral of a continuous rational function on [0,1]. Polynomial division gives

    z²/(z+t)=z-t+t²/(z+t).

Since L(z)=integral_0^1 dt/(z+t),

    W_r(z)=z/r-1/2 + integral_0^1 t²/(z+t) dt.             (4)

Differentiation, or direct evaluation of the rational antiderivative, gives

    J(z):=integral_0^1 t²/(z+t)² dt
         =1-2z L(z)+z/(1+z),
    f_r(z)=1/r-J(z).                                     (5)

To verify the last closed form without differentiating under an integral, write
t²/(z+t)²=1-2z/(z+t)+z²/(z+t)² and integrate; the final rational integral contributes z-z²/(z+1)=z/(z+1).

J is strictly positive and strictly decreasing: for fixed t>0 its integrand is strictly decreasing in z, and the strict inequality holds on a nonzero-length interval. Also

    1/[3(z+1)²] < J(z) < 1/(3z²),     0<J(z)<1,           (6)
    J(0+)=1, J(infinity)=0.

The bounds follow by comparing denominators with (z+1)² and z² and integrating t²; strictness holds away from the endpoints. The first limit also follows from the closed form and zL(z)→0; the second from (6). In particular

    f_r(0+)=1/r-1,  f_r(infinity)=1/r,
    f_r(z)<1/r for every finite z>0.                      (7)

The derivative can be checked directly, and its positive integral form is

    f_r'(z)=2L(z)-2/(z+1)-1/(z+1)²
           =2 integral_0^1 t²/(z+t)³ dt >0,
    f_r''(z)=-2/[z(z+1)³]<0.                             (8)

The integral differentiation is legitimate on each positive-z neighborhood: the integrand and parameter derivatives are continuous/bounded on the compact t interval. Alternatively integrate the rational expressions to obtain the same identities. Thus W is strictly convex in z and f is increasing and concave on z>0. V need not be globally convex in C: for r>1 its origin curvature is negative. No blanket monotonicity of V, its signed derivative or a floating evaluator is asserted.

This resolves the brief's proposed overshoot concern: **it is false for the exact f stated in the assignment.** Identity(5) proves that f cannot exceed its limiting1/r; (8) proves global increasing behavior for this residual. That is a derived correction to the brief, not an assumption adopted because a theorem name suggested it. It does not exclude numerical cancellation artifacts in an unvalidated evaluator.

## 4. Exact unrestricted global minima and analytical brackets

### Subcritical and critical r

For 0<r≤1, (1) gives W(z)>0 for every z>0: z(1/r-1)≥0 and z²L(z)>0. Therefore the unique magnitude-domain global minimum is C=0. The signed extension has the same unique origin minimum. At r=1 this minimum is strict but degenerate with zero second derivative, not an inflection.

### Supercritical r

For r>1, (7) and continuity give a zero z_*>0; strict increase gives uniqueness. Before z_* the residual is negative, afterward positive. Hence W decreases from0 to W(z_*) and then increases. Coercivity is explicit from (4):

    W(z)>z/r-1/2 → +infinity as z→infinity.

Thus the unrestricted magnitude-domain global minimizer is exactly

    C_*=Lambda sqrt(z_*)>0,                               (9)

unique on C≥0; on all signed real C the two minima are ±C_* and zero is a strict local maximum. At the root, substitution of f=0 yields

    W(z_*)=-z_*²[L(z_*)-1/(1+z_*)]<0,                    (10)
    V_exact''(C_*)=4A Lambda² z_* f_r'(z_*)>0.

The strict sign in (10) follows by integrating 1/(z+t)>1/(z+1) over0<t<1. This proves negative energy and strict curvature, not merely an optimizer label.

### Sharp-width and sign-margin brackets

At the root J(z_*)=1/r, so (6) gives

    sqrt(r/3)-1 < z_* < sqrt(r/3),   z_*>0.               (11)

For a practical strictly positive lower endpoint, let delta=1-1/r∈(0,1). The elementary inequality log(1+y²)<y for y>0 follows because y-log(1+y²) vanishes at0 and has derivative (y-1)²/(1+y²)≥0, strictly positive except at one point. Set y=1/sqrt(z) to get L(z)<1/sqrt(z). Therefore

    h(z):=1-J(z)=2zL(z)-z/(1+z)<2sqrt(z).

At a0=delta²/16, f_r(a0)=h(a0)-delta<-delta/2<0. Define

    b=sqrt(r/3),
    a=max{delta²/16, b-1}.                               (12)

If b-1>0, (6) also gives f_r(b-1)<0. Thus 0<a<z_*<b with strict endpoint signs. Width b-a≤1 follows from a≥b-1 (strictly less when a>b-1). No search cap C≤Lambda or arbitrarily tiny fixed lower C is used. In C, the bracket is [Lambda sqrt(a),Lambda sqrt(b)].

A deliberately wider upper endpoint B=sqrt(2r/3) gives the stronger analytical margin

    f_r(B)>1/(2r)>0.

This can be useful when a future finite-precision evaluator cannot certify the smaller margin at b. The strict mathematics does not imply that rounded endpoints preserve their signs: future implementation must round/enclose outward or verify the actual represented signs with error bounds.

All formulas above assume r>1. At r=1 no positive root exists and an equality endpoint must not be driven into a supercritical root-finding loop.

## 5. Cutoff-constrained versus unrestricted scalar optimization

If the separate allowed magnitude domain is the CLOSED interval0≤C≤Lambda, set

    d=J(1)=3/2-2log2,  0<d<1,
    r_Lambda=1/d>1.                                    (13)

Then:
- 0<r≤1: unique minimum C=0.
- 1<r<r_Lambda: z_*<1, so the constrained and unrestricted minima coincide at the interior C_*.
- r=r_Lambda: the unique minimum is C=Lambda with stationary derivative0.
- r>r_Lambda: z_*>1 and V is strictly decreasing on0<C≤Lambda; the constrained minimum is C=Lambda, with V'(Lambda)<0. It is a legitimate boundary minimum of that constrained problem, **not an unrestricted stationary point**.

For the strict domain0≤C<Lambda, the endpoint minimum at/above r_Lambda is only an infimum and is not attained. These domain choices must be stated; a UV regulator is not by itself a proof that field amplitude must lie below it.

An exact strong-coupling witness is r=12. From (11), 1<z_*<2, so Lambda<C_*<sqrt(2)Lambda. Equivalently J(1)>1/12 makes f_12(1)<0. This requires no numerical model evaluation.

The existing fixed LOWER search bound can also exclude a legitimate near-critical interior minimum. Let ell=10^-6 be the nominal written ratio, c=ell², and choose

    delta=c L(c)/2∈(0,1),  r=1/(1-delta)>1.

The inequality cL(c)<1 proves the domain. At the lower endpoint

    W_r(c)=c²L(c)/2>0,
    f_r(c)=3cL(c)/2-c/(1+c)>0,

because L(c)>1/(1+c). Hence z_*<c, W is increasing throughout z≥c, and every point in the nominal search interval has positive exact energy. Comparing any such candidate to zero selects zero even though the actual unrestricted AND cutoff-constrained scalar minimum is a strictly negative interior C_*<ell Lambda. This is an analytical countercase to the bounded objective as a full solver, not an observed new runtime failure.

The absolute V_num guard causes an additional distinct model discrepancy. If Lambda<10^-15 then the entire nominal allowed interval is flattened to zero by the written guard, while for any exact r>1 the unguarded ansatz has negative values arbitrarily near the origin. Finite-precision details add further limits. Current source already discloses guard/scaling differences and reports supercritical nonselection honestly; those disclosures do not implement the missing objective repair.

## 6. Residual-to-root, magnitude and energy error

Take any certified positive bracket [a,b] containing z_* and any approximate z_hat∈[a,b]. From (8),

    f_r'(z)≥m:=2/[3(b+1)³]>0 for a≤z≤b.                 (14)

Indeed replace each (z+t)³ by (b+1)³ in the positive integral and integrate t². The mean-value theorem gives

    |z_hat-z_*|≤|f_r(z_hat)|/m.                           (15)

If a future evaluator supplies f_tilde with a rigorous absolute error epsilon_f, use R=|f_tilde|+epsilon_f in place of the true residual. Combining the root enclosure and (15), define E_z=min{b-a,R/m}. For C_hat=Lambda sqrt(z_hat),

    |C_hat-C_*|≤Lambda min{sqrt(E_z),E_z/(2sqrt(a))}.      (16)

The square-root bound remains available if a=0 is used as a limiting endpoint. The direct interval [Lambda sqrt(a),Lambda sqrt(b)] is an independent magnitude certificate; its midpoint has at most half its width error. Rounding/unit conversion must be included before treating a represented output as C_hat.

Strict convexity with the same m also gives a normalized energy-gap bound. Strong convexity applied at z_hat to z_* and completing a square yields

    0≤W_r(z_hat)-W_r(z_*)≤|f_r(z_hat)|²/(2m),
    0≤V(C_hat)-V(C_*)≤A Lambda⁴ R²/(2m).                 (17)

These are exact-real contracts with an evaluator-error premise, not a global IEEE certificate. A raw small |V'(C)| is insufficient: V'=2A Lambda² C f, so it tends0 near C=0 even when f tends the nonzero -delta. The existing near-origin-impostor source test targets this real issue. Normalize the residual rather than accept an arbitrarily small absolute slope.

For a constrained endpoint at r>r_Lambda, do not require f(1)=0: the correct global certificate is the boundary/domain result in §5. Conversely do not relabel that endpoint an unrestricted minimum because a bounded optimizer reports success.

## 7. Near-critical and large-z stability: a prospective evaluator contract

As r↓1, delta↓0 and z_*↓0. For z>0 there is the exact decomposition

    h(z)=2z log(1/z)-z+R0(z),
    R0(z)=2z log(1+z)+z²/(1+z),
    3z²/(1+z)<R0(z)<3z².                                 (18)

The bounds follow by integrating 1/(1+t) between 1/(1+z) and1. Thus h(z)~2z log(1/z), and inversion gives

    z_*~delta/[2log(1/delta)] as delta↓0.                 (19)

To justify the inversion: delta/(2z_*log(1/z_*))→1 by(18); taking logs shows log(1/delta)/log(1/z_*)→1, which yields(19). This is an asymptotic description, not a production stopping tolerance. The root can lie below any fixed positive search fraction. Absolute z residual conditioning improves as f' grows logarithmically near0, but phase classification and relative C accuracy remain sensitive to unresolved threshold/input errors; V's minimum curvature tends0.

For large z the exact positive integral avoids the cancellations in the logarithmic closed form. For z≥2, an optional convergent alternating expansion is

    J(z)=sum_(k=0)^infinity (-1)^k (k+1)/(k+3) z^(-k-2).
                                                                  (20)

It follows by expanding (1+t/z)^-2 and integrating on[0,1]. The integrated term ratios are at most3/(2z)≤3/4, so truncation after k=N has the next-term sign and absolute remainder at most

    (N+2)/(N+4) z^(-N-3).

In particular J=1/(3z²)-1/(2z³)+O(z^-4), with an explicit next-term bound obtainable above, and f=1/r-J approaches1/r from BELOW. A positive-kernel quadrature with justified enclosure is another route. These are analytical evaluation options, not executed code.

A future admitted solver contract should:
1. Admit positive finite supplied parameters and certify the intended threshold/domain. If uncertainty/representation bounds for r straddle1, return an explicit unresolved threshold instead of claiming a physical or exact zero/positive branch. Compute delta without unqualified cancellation and retain the original supplied values. For known r intervals use monotonic z_*(r): differentiating f=0 gives dz_*/dr=1/[r² f'(z_*)]>0, so parameter uncertainty has an explicit root enclosure.
2. For r>1 initialize an outward/certified bracket from(12), or the wider sign-margin upper endpoint. Use the extended f(0)=1/r-1 if an exact-real lower boundary is needed; an underflowed positive lower bound is not a fabricated zero root.
3. Evaluate residuals with certified signs/errors: near small z use h(z)-delta; at large z use1/r-J or a scaled residual1-rJ with the corresponding scaled derivative bound, avoiding uncontrolled cancellation. A real formula and a small test sample alone supply no global floating error enclosure.
4. Refine by sign-certified bisection (or a separately proved safeguarded method). If the residual interval straddles zero, refine the evaluator or use the quantitative error certificate; do not guess a sign. If represented endpoints/midpoints stagnate before the requested accuracy is certified, fail explicitly. This contract does not assume Newton is globally safe.
5. Return a root/enclosure plus a stated magnitude/energy error from(14)–(17), with dimensional scaling and final rounding checked. A width certificate and a residual certificate cross-check each other; either must include its stated evaluator/representation premises. Refuse unrepresentable output or unattainable requested accuracy instead of returning a capped root, flat guard or success flag.
6. State whether the target is unrestricted, closed cutoff-constrained, or a domain-limited approximation; use the right endpoint/KKT certificate. Preserve meaningful scalar_status/search_diagnostics and all consumers' distinctions, rather than silently changing legacy meanings. Actual source/API/testing adoption requires its own coherent allocation/review.

No code, tolerance, new gate or schema is installed by this contract. Independent real-analysis/numerics review and subsequent ROOT-admitted native/formula/consumer work remain required.

## 8. Exact distinction from the NJL fixed point

At the same z and r, the separate NJL scalar residual is

    f_NJL(z)=1/r-1+zL(z)
            =1/r-integral_0^1 t/(z+t) dt.

For z>0,

    f_r(z)-f_NJL(z)
       =z[L(z)-1/(1+z)]>0.                               (21)

Thus sharing G_c does not make the nonzero roots equal. If r>1 and z_NJL is its positive root, then f_r(z_NJL)>0, while f_r crosses0 only once; therefore z_ADW<z_NJL. The NJL cutoff-crossing threshold at z=1 is 1/(1-log2), distinct from the regulated-potential threshold1/(3/2-2log2). Pointwise J_ADW<J_NJL gives r_Lambda,ADW>r_Lambda,NJL. This is a mathematical comparison of the two stated ansatzes, not a new execution/review of the already accepted NJL implementation. Carry the accepted NJL repair forward separately without substituting its root for this potential's minimum.

## 9. Ownership, validation and remaining scientific work

The immediate independent acceptance target is the complete chain(1)–(21): domain/origin extension, positive integral identity, global minimizers, exact constrained threshold, both search-window countercases, positive bracket/sign margins, error bounds and asymptotic/evaluation limits. These are self-contained project-original scalar identities; no new bibliography or primary-source acquisition is required to prove them. A reviewer should challenge strict endpoint cases, signed-C multiplicity, near-critical/large-scale ranges and finite-precision premises, not only a few evaluated points.

A native author would then prove the actual integral/derivative/monotonicity/minimum statements, not assume the desired root property in a predicate. A separately allocated source implementation would require an independent stable evaluator/reference and tests covering near-critical thresholds, r_Lambda and boundary cases, strong r=12, roots below the old lower bound, absolute-guard/scaling, residual-to-error and failure/stagnation, plus actual wrappers/figures/diagnostics. Existing r=2/guard/upper-window/reporting controls should be preserved and credited. This manual work is not that implementation, numerical evidence or native admission.

Microscopic ADW HS/fermion determinant, channel normalization, physical tetrad/metric/mode correspondence, actual domain validity, global coupled-field optimization and empirical gravity/cosmology remain OPEN BUILD. A unique scalar minimum does not prove a Lorentzian signature dynamically, full tetrad state, physical phase diagram, vacuum magnitude or a gravitational spectrum. Current Paper5's adopted flat tetrad/signature, assigned mode categories and existing status disclosures remain separate.

Only the three assigned ignored artifacts and fresh metadata scratch are written. There was no production import/model/numerical/symbolic software evaluation, tests/Verify, native Lean/MCP/build/controller/compiler, direct Git command or mutation, registry/holding/notebook/metadata writer or closure action. All calculus/inequalities and witnesses above were derived by hand; Python was used only for static source/AST/JSON/hash/receipt handling. Existing dated runtime reports are attributed, not rerun or recertified.

## Original packet and preservation

First original supported check returned0 with fresh=true and no changes. The final original supported check returned1 with changed=["owned-files"]. This is exactly the expected three owned-output drift; no authority or source drift was reported. The packet was not refreshed. All53 captured source/reference comparisons and the three additional source pins matched; actual raw command/environment/timing/stdout/stderr are retained in process.json/evidence.json. The comparison scope is the original packet and bounded additional sources, not a new whole-repository/runtime certification.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The overshoot/nonmonotonicity suspicion is incorrect for the exact f in the assignment: f=1/r-J with J>0 strictly decreasing proves f is increasing and strictly BELOW its limit. The correction is established by an explicit positive integral identity; V itself is not globally convex in C, and this does not certify an IEEE evaluator.

Current N already has the later real scalar-status/search-diagnostics reporting contract. It must not be called absent, but it deliberately preserves the restricted objective and makes no global stationarity claim. The exact constrained/unrestricted and lower-window witnesses above explain the remaining optimizer duty without erasing that delivered work.

The underlying reference is Phase5d Wave2 and the installed Paper5 scalar-status spec/plan, not an invented root7 canonical finding. New scientific authorship is accepted in this packet, not manufactured as a historical assignment. The NJL accepted root repair is a separate formula and cannot close this potential's optimization or physical ADW correspondence.
