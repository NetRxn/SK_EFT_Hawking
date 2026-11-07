# L1 B3: exact regulated scalar bubble and approximation control

Accepted construction owner: Physics Publication Remediation lead, thread01a13f67-0907-71e2-9a64-64d2f2420e2f, acting on the operator's current substance-first BUILD directive. This is an actual manual mathematical construction proposed for independent verification. It is not a new scientific scope disposition, a native proof, a derived graviton mode/window or full B3 completion. No numerical code or scalar model is silently substituted for the original physical target.

## Original physical objective and this necessary construction

REMEDIATION_PLAN B3 requires deriving the metric response and its normalization so the proposed susceptibility interval is a result. Current canonical adw_bubble_integral identifies its logarithmic definition as the exact sharp-cutoff two-propagator integral and claims positivity for every positive mass parameter. VestigialSusceptibility defines the same logarithm, with positivity only below Lambda^2/e. Before using that kernel to compute a physical window, its regulator remainder and domain must be resolved. This construction derives the EXACT mathematical scalar integral named in the current docstring and an explicit approximation bound; it does not assume this scalar kernel is the ADW metric-channel numerator/projector, fix a physical coupling or identify chi_g with the dimensionless GW parameter.

## Domain and regulator

Let r>0 and Lambda>0 be real. Use the Euclidean four-dimensional spherical sharp cutoff and scalar propagator (|p|^2+r)^(-1), with no channel/spin/flavour multiplicity included. The measure is d^4p/(2pi)^4. Its radial angular factor is area(S^3)/(2pi)^4=1/(8pi^2). The mathematical construction is conditional on this explicit propagator/regulator; physical derivation must still supply them and any numerator, subtractions and multiplicities.

The exact scalar bubble is

  Pi_exact(r,Lambda) = 1/(8pi^2) int_0^Lambda p^3/(p^2+r)^2 dp
                    = 1/(16pi^2) [log(1+Lambda^2/r) - Lambda^2/(Lambda^2+r)].

Proof: set u=p^2, p^3 dp=u du/2. An antiderivative of u/(u+r)^2 is log(u+r)+r/(u+r). Evaluation at u=Lambda^2 and0 gives the displayed expression. The denominator is strictly positive on the compact interval; the integrand is continuous and positive on0<p<=Lambda. Thus Pi_exact>0 on the WHOLE r,Lambda>0 domain.

This is dimensionless when r has momentum-squared units and Lambda momentum units. A separate O(Lambda^2/(16pi^2)) susceptibility scale cannot be identified with it without specifying dimensionful numerator/coupling/field normalization and renormalization. This dimensional boundary is a required original B3 bridge, not an operator-approved narrowed target.

## Exact comparison with the current logarithmic definition

Set x=r/Lambda^2>0 and C=1/(16pi^2). The current logarithm is Pi_IR=C[log(1/x)-1]. Algebra gives

  Pi_exact-Pi_IR = C[log(1+x)+x/(1+x)].

For x>0, integral_0^x dt/(1+t) is strictly between x/(1+x) and x. Therefore

  0 < 2 C x/(1+x) < Pi_exact-Pi_IR < 2 C x.

The non-strict versions are also valid. This is a quantitative absolute remainder, not merely a statement that the forms differ. For x<=epsilon it yields error <=epsilon/(8pi^2); an independently chosen physical error budget must set epsilon, rather than asserting control at arbitrary r.

At r=Lambda^2, Pi_IR=-C while Pi_exact=C(log2-1/2)>0. The last inequality follows from integral_1^2 dt/t>1/2. This concrete analytic witness disproves treating the current logarithm as the exact positive sharp-cutoff scalar integral throughout r>0. It does NOT disprove the physical ADW/L1 programme or the logarithm as an asymptotic approximation.

## Monotonicity, limits and the conditional RPA zero

Differentiating the exact closed form gives

  d Pi_exact/dr = -Lambda^4/[16pi^2 r(Lambda^2+r)^2] <0.

Continuity on r>0 follows from the closed form. As r->0+, the logarithm diverges and the bounded subtraction tends1, so Pi_exact->infinity. As r->infinity, the integral bound p^3/(p^2+r)^2 <=p^3/r^2 gives0<Pi_exact<=Lambda^4/(32pi^2 r^2)->0.

Consequently, for positive u_g,c_D the conditional inverse response

  F(r)=1/u_g-c_D Pi_exact(r,Lambda)

is continuous and strictly increasing from -infinity to1/u_g>0. IVT and strict monotonicity give a unique positive zero. For a positive G_c and r=1/G-1/G_c, that root maps to exactly one G_ves=1/(1/G_c+r_star) in(0,G_c). Thus the qualitative precritical-zero mechanism survives this explicit scalar regulator correction under its stated positive inputs. This is a real constructive result; no existing exponential closed-form root for Pi_IR may be called the exact Pi_exact root.

## Integration and independent acceptance target

1. Independently verify the antiderivative, angular/scalar normalization, strict inequalities, derivative, limits, unique-zero argument and dimensional scope. A mathematical error must be corrected, not hidden by prose.
2. Formalize exact scalar radial-integral equality, positive/strictly decreasing/limit properties and explicit remainder against the existing logarithm in VestigialSusceptibility using ROOT-admitted Lean capacity; original source and old approximation declarations remain separately identified until all consumers are reconciled. No fresh axiom, name-only witness or assumed integral identity.
3. Implement the corresponding stable evaluator and independent radial-integral controls in canonical formulas/tests only after native/formula/source allocation, covering small and large x, r=Lambda^2 and invalid inputs. Test the actual producer/RPA consumers and preserve the original source/edition/parameter boundaries. No test merely restating a copied production expression.
4. Continue original B3: derive the physical metric-channel action/projector, regulator/subtractions, coupling/units and normalization, then obtain a justified chi window with propagated errors. Micro-mode/matter coupling and observed frequency/transport matching remain distinct BUILD rows. This contract cannot close any of them.

Current execution: manual derivation only, no project import/numerical test/native proof or code mutation. Independent review and ROOT native scheduling are pending. Author repair -> independent verification -> recorded closure remains the process; this is the first construction input, not the closure.
