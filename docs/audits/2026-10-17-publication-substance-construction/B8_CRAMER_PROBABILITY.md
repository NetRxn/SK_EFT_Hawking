# B8: actual iid Cramér upper and lower bounds on the real line

Manual mathematical construction by the publication lead, continuing original B8/I3; independently accepted by publication_checkpoint_source, with lead acceptance 369214e1c0e1ca836527d4892f3522c839219e870ab4b6f20dc7a508dfd06f61 and [full original independent review](reviews/B8_CRAMER_PROBABILITY.md). This accepts the stated actual all-real-MGF closed-upper/open-lower theorem, not native, device, source-installation, closure or publication readiness. The separate finite-horizon Brownian Novikov manual construction is also independently accepted in [its own note](B8_NOVIKOV_STOCHASTIC_EXPONENTIAL.md); it does not close general Itô/Girsanov/native/full I3 work. This is the actual probability/MGF/rate relationship, not a continuity predicate or an assumed LDP.

## 1. Objects, class and precise target

Let mu be a Borel probability measure on R with

M(t)=integral_R exp(t x) mu(dx) < infinity for EVERY t in R.           (1)

This includes every genuinely sub-Gaussian real law in the original CramerIID/CramerLowerBound charter: a bound M(t)<=exp(m t+v t²/2) for all real t, with finite m and v>=0, implies (1). No such numerical bound is needed in the proof below. Merely supplying an arbitrary continuous function called mgf does not satisfy (1): M is the actual expectation under mu. For n>=1 use the actual iid product probability P_n=mu^tensor n and empirical mean L_n=(X_1+...+X_n)/n. Any iid process has these same finite-dimensional empirical-mean laws.

Define lambda(t)=log M(t) and the EXTENDED-valued rate

I(x)=sup_{t in R} [t x-lambda(t)] in [0,infinity].                    (2)

Infinities are permitted; continuity as a finite real function on ALL R is neither required nor generally true. We prove separately:

limsup_n (1/n) log P_n(L_n in F) <= -inf_{x in F} I(x), F closed;
liminf_n (1/n) log P_n(L_n in G) >= -inf_{x in G} I(x), G open.        (3)

Use log0=-infinity, inf(empty)=infinity and -(infinity)=-infinity. These are logarithmic asymptotic bounds, not exact finite-n prefactor1 claims. I has compact sublevel sets. Actual probability normalization is M(0)=1; I vanishes at the mean, not necessarily at0. Extending the theorem to laws whose MGF exists only near0 is a broader classical domain not claimed proved by this note; the original sub-Gaussian target remains fully included. This domain distinction does not waive any independently required broader I3 consumer or native construction.

## 2. Integrability, Esscher law and genuine rate properties

From finite M(delta), M(-delta), all absolute polynomial moments are integrable. More generally, for any compact t-interval around t0 and integer k>=0, |x|^k exp(t x) is bounded by a fixed finite constant times exp((t0+2delta)x)+exp((t0-2delta)x), for sufficiently small delta>0 enclosing that interval. Indeed |x|^k<=C exp(delta|x|), and split x by sign. Dominated differentiation therefore proves M is smooth and gives its actual first two derivatives. M(t)>0 because its positive integrand has positive integral against a probability measure.

Define the Esscher probability

mu_t(dx)=exp(t x-lambda(t)) mu(dx).                                  (4)

Its total mass equals M(t)/M(t)=1. Its density is everywhere positive, so mu_t and mu have the same null sets. Direct differentiation yields

lambda'(t)=E_{mu_t} X,
lambda''(t)=E_{mu_t}(X-E_{mu_t}X)²>=0.                              (5)

These are identities derived from (1),(4), not moments supplied as predicates. In particular lambda is convex, lambda(0)=0, and m=lambda'(0)=E_mu X is finite. Jensen applied to exp[t(X-m)] gives lambda(t)>=t m, so I(m)=0. Selecting t=0 in (2) gives I(x)>=0 for EVERY x. A function negative between zero and its putative fluctuation mean cannot be this probability rate.

As a supremum of continuous affine functions of x, I is convex and lower semicontinuous. Moreover

I(x)>=max(x-lambda(1), -x-lambda(-1)).                              (6)

Hence {I<=c} is closed and bounded for finite c, thus compact on R (the empty sublevel is compact). This proves goodness without assuming rate regularity.

The iid product of (4) satisfies the EXACT Radon--Nikodym relation

 d(mu_t^tensor n)/d(mu^tensor n)=exp(n[t L_n-lambda(t)]).             (7)

This follows by multiplying the n positive coordinate densities; all integrals factor by product probability/Tonelli. Its inverse density is exp(-n[t L_n-lambda(t)]). Nothing about a tilted product is inferred from continuity alone.

## 3. Chernoff local estimate and exponential tightness

For any real t, iid factorization gives E_{P_n}exp(n t L_n)=M(t)^n=exp(n lambda(t)). If U is a Borel set such that t y-lambda(t)>=c for all y in U, positivity and Markov give

P_n(L_n in U)<=exp(-n c).                                          (8)

The proof is E exp(n t L_n)>=exp(n[c+lambda(t)])P_n(L_n in U); it works for negative t as well, without reversing a wrong inequality for L_n. No expectation of a signed exponential is involved.

With t=1 and t=-1,

P_n(|L_n|>K)<=exp[-n(K-lambda(1))]
                  +exp[-n(K-lambda(-1))].                          (9)

For every finite A>0, take K>=A+max(lambda(1),lambda(-1),0), increasing K if desired. Then the right side is at most2 exp(-n A). This is exponential tightness at speed n, derived from the actual product law. It is not a claim of bounded samples or compact support.

## 4. Closed-set upper bound, including unbounded/empty sets

Let F be closed and c=inf_F I. If F is empty its probabilities are0 and (3) holds immediately. Otherwise choose ANY finite ell<c; when c=infinity this means arbitrary finite ell. If c=0, negative ell are sufficient and their limit gives0. Choose A>max(ell,0) and K as in (9). The set C=F intersect[-K,K] is compact.

For every x in C, I(x)>ell. By the definition of the supremum there exists a finite t_x with t_x x-lambda(t_x)>ell. Continuity of this affine function gives an open interval U_x containing x on which t_x y-lambda(t_x)>=ell. A finite subcover U_1,...,U_r of C exists. Equations(8),(9) give

P_n(L_n in F)<=r exp(-n ell)+2 exp(-n A)
                  <=(r+2) exp(-n ell).                             (10)

This also works with r=0 if C is empty. Taking limsup of log/n yields <=-ell, since log(r+2)/n->0. Let ell increase to c if c<infinity; if c=infinity let ell go toinfinity. This proves the first assertion of (3), with no compactness assumption on F and no missing exponential-tightness tail. It never claims the finite cover constant r equals1.

## 5. Tilted mean range and interior optimizers

If mu is not a point mass, (5) is STRICT: variance0 under the equivalent measure mu_t would force X constant mu-a.e. Let a=essinf_mu X and b=esssup_mu X in the extended real line. Thus a<b; lambda' is continuous and strictly increasing. We now prove its range is exactly(a,b), rather than assuming every rate point is exposed.

For t>0, if b<infinity, X<=b a.e. implies lambda(t)<=t b. For every finite y<b the probability p=mu(X>=y) is positive by essential supremum (choose a nearby threshold if needed), and M(t)>=p exp(t y), so lambda(t)/t>=y+log(p)/t. Consequently lambda(t)/t->b, also in the extended sense if b=infinity. Since lambda(0)=0 and lambda(t)=integral_0^t lambda'(s)ds, the Cesaro average of the monotone lambda' has the same extended limit as lambda' itself. Therefore lambda'(t)->b as t->infinity. Applying this argument to -X proves lambda'(t)->a as t->-infinity. For finite t, a<lambda'(t)<b: equality at an essential bound would force X to equal that bound almost surely under mu_t and hence mu. This proves the range assertion.

Every x in(a,b) thus has a unique finite t with lambda'(t)=x. Convexity gives lambda(u)>=lambda(t)+(u-t)x for all real u, so

I(x)=t x-lambda(t)<infinity.                                       (11)

This is an actual maximizing parameter, with (11) proved from the integral MGF. It is not an assumption that a candidate rate equals its Legendre transform. In particular m is interior and corresponds to t=0.

## 6. Open-set lower bound via actual iid Esscher concentration

Fix x in G intersect(a,b), and t as in (11). Choose delta>0 with (x-delta,x+delta) contained in G. Under Q_n=mu_t^tensor n the mean L_n has expectation x and variance lambda''(t)/n: expand the square, use independence to kill centered cross terms, and use (5). Chebyshev yields

Q_n(|L_n-x|<delta)>=1-lambda''(t)/(n delta²) ->1.                   (12)

Let A_n={|L_n-x|<delta}. On this event,
 t L_n-lambda(t)<=I(x)+|t|delta.
Using the inverse of (7),

P_n(L_n in G)>=P_n(A_n)
 >=exp[-n(I(x)+|t|delta)] Q_n(A_n).                                (13)

Because Q_n(A_n)->1, it is eventually positive and (1/n)log Q_n(A_n)->0. Thus liminf log P_n(G)/n>=-I(x)-|t|delta. This holds for arbitrarily small delta>0 inside G; let delta decrease to0. The result is >=-I(x) for each interior x in G. The proof uses a genuine tilted probability and its variance, and handles t=0 as well as both signs.

Endpoint and degenerate controls complete the theorem, rather than hiding them behind a differentiability assumption. Suppose b is finite. Since X<=b a.e., the variables exp(t(X-b)) for t>=0 are bounded by1 and decrease pointwise to1_{X=b}. Dominated convergence gives exp(lambda(t)-t b)->p_b=mu({b}). For every real t the same expectation is >=p_b. Therefore

I(b)=-log p_b, with -log0=infinity.                                (14)

If p_b>0, the product event X_1=...=X_n=b has probability p_b^n and mean b. If b belongs to G this directly gives liminf>=log p_b=-I(b). If p_b=0, I(b)=infinity and the desired pointwise lower bound is trivial. The finite a endpoint follows by applying the same argument to -X. If a or b is infinite there is no such real endpoint. For x>b or x<a with a finite boundary, use t of the appropriate sign and the bound lambda(t)<=t b or lambda(t)<=t a to deduce I(x)=infinity. Thus every real x outside[a,b] has infinite rate; there is no omitted finite-rate point outside the interior/endpoints.

If mu=delta_d, then M(t)=exp(t d), lambda(t)=t d and I(d)=0, I(x)=infinity for x!=d. Every L_n=d surely. Both statements (3) follow directly: sets containing d have probability1/rate inf0; otherwise probability0 and infinite inf. This includes the deterministic-zero law, whose MGF is1, not0.

Finally, for nondegenerate mu we have proved the lower bound >=-I(x) for EVERY x in the open G with finite rate. Taking the supremum over such x gives -inf_G I. If none exists this right side is -infinity and the inequality is automatic, including G empty. This proves the second assertion of (3) for the full class (1), including atomic distributions, nonbounded supports, missing endpoint atoms and all extended-valued cases.

## 7. Exact manual controls against the current source predicates

Bernoulli law: 0<p<1, mu({1})=p, mu({0})=1-p. The actual MGF is 1-p+p exp(t), lambda its logarithm. For 0<x<1 solve lambda'(t)=x, obtaining exp(t)=x(1-p)/(p(1-x)); substitution in (11) gives

I(x)=x log(x/p)+(1-x)log((1-x)/(1-p)).                              (15)

I(0)=-log(1-p), I(1)=-log p, I=infinity outside[0,1]. Direct differentiation at x=p gives I(p)=0; I(0)>0. Thus centering at0 is false for uncentered data, and requiring finite continuity on allR excludes a genuine bounded/sub-Gaussian law. For the centered variable X-p, rate is I_center(y)=I(y+p), with I_center(0)=0, still infinite outside[-p,1-p]. At p=0 or1 use the exact Dirac case, not a formula dividing byp or1-p.

Actual finite-n upper countercontrol: F={0,1} is closed. At n=1, P_1(L_1 in F)=1 but exp[-inf_F I]=max(p,1-p)<1. For every n, P_n(L_n in F)=p^n+(1-p)^n, whose logarithmic rate is correctly log max(p,1-p). This refutes the source's unconditional finite-n prefactor1 form WITHOUT refuting the valid logarithmic upper theorem.

Shifted Gaussian: for density (sqrt(2pi)sigma)^(-1) exp[-(x-m)²/(2sigma²)], sigma>0, completing the square in the actual normalization integral gives M(t)=exp(m t+sigma²t²/2). Completing the square in (2) gives I(x)=(x-m)²/(2sigma²)>=0 and I(m)=0. Subtracting I(0) to force zero at0 instead produces x²/(2sigma²)-m x/sigma², negative for x between0 and2m if m>0. That shifted function is not this law's Cramér rate. If the physical model uses a different fluctuation functional, its meaning must be derived separately rather than declaring true probability rates allowed negative.

Actual relative-prefactor lower countercontrol: take standard Gaussian samples and open G=(c,infinity), c>0. An orthogonal change of variables in the product Gaussian density separates the normalized sum n^(-1/2)sum X_i as standard Gaussian (Jacobian1 and invariant sum of squares). Thus L_n has variance1/n, and integration using x/c>=1 for x>=c gives

P_n(L_n>c)=sqrt(n/(2pi)) integral_c^infinity exp(-n x²/2)dx
 <= exp(-n c²/2)/(c sqrt(2pi n)).                                  (16)

Yet inf_G I=c²/2. The ratio of the probability to exp(-n inf_G I) tends to0, so a claimed universal lower prefactor(1+o(1)) is false. The logarithmic lower statement (3) is correct. No uniform lower theorem for arbitrary CLOSED sets follows: Gaussian F={c} has probability0 and finite I(c).

MGF-zero control: on any probability space E exp(0X)=E1=1. Hence the current source pair mgf=0,I=0 is an inhabitant of its structural predicate but cannot represent any actual law, including a degenerate one. Nonnegativity, mean normalization, extended rate values, independence, product expectation, an Esscher density or probability decay do not follow from that predicate.

## 8. Actual source interface, ownership and native follow-through

Current complete CramerIID.lean and CramerLowerBound.lean define the same four-property conjunction: Continuous I, I0=0, Continuous mgf, mgf0<=1, with zero-function witnesses. Neither contains (1)-(3),(7),(8),(12) or a random variable/product measure. Existing predicate theorems remain true for what they state; this construction does not silently redefine their API or report an actual kernel proof.

Required native construction under ROOT's ordinary ADR-008 admission: actual Borel probability/independence/product means; actual integrable expmoments and tilted measures with strictly positive RN density; dominated first/second derivatives; Jensen/Legendre extended rate; local Chernoff/exponential tightness/finite closed cover; variance/LLN and Esscher lower; endpoint/Dirac/infinity controls; source consumers upgraded from predicate witnesses to actual statements. No new axiom, supplied LDP conclusion or finite-rate restriction can substitute for that work. If existing Mathlib infrastructure helps, reuse its precise signatures through admitted MCP. Absence is a construction cost, not infeasibility or deferral.

The separate [Brownian Novikov construction](B8_NOVIKOV_STOCHASTIC_EXPONENTIAL.md) and its full independent review establish the finite-horizon predictable L² integral/isometry/bracket, exact half-energy criterion, unit terminal mass and class-D stochastic exponential over actual Brownian objects. Native filtered-probability/integral/exponential interfaces and the remaining general Itô, Girsanov drift and full I3 consumers are still owed. A continuous deterministic function and nonnegative T alone are not that stochastic statement. These are distinct accepted manual branches; no Novikov proof is supplied by this Cramér proof. Sanov/contraction/Varadhan/consumer work is not discharged by either branch.

Complete independent manual probability review has accepted the construction, actual source target and countercontrols. ROOT owns the remaining native source/axiom validation, installed integration and canonical closure. External Mathlib PR submission remains separately operator-gated; no external submission or coordination is authorized/executed by this note. Full I3/B8/G4/G5/G11, scientific/native/source/runtime/gates/main/human/publication remain distinct. Original charter is retained; no operator disposition or infeasibility conclusion is requested from this constructive progress.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The current source's zero MGF is not an actual degenerate probability MGF; its fixed-zero and finite-continuous rate clauses do not characterize Cramér rates. Its finite-n closed bound and relative-prefactor open lower formula fail on explicit Bernoulli/Gaussian controls. The valid claims are the separate asymptotic closed limsup/open liminf bounds proved here. The claimed native theorem is not supplied by those existing predicates. Novikov's separate finite-horizon Brownian manual result is accepted; native and broader stochastic content remain owed. These precise contradictions do not establish impossibility or authorize scientific deferral; they identify the actual substrate to build.
