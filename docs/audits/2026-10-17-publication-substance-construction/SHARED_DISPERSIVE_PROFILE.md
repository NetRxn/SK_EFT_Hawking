# Shared dispersive-law BUILD: first source-controlled profile construction

Author: publication lead `/root`, accepting scientific construction responsibility under notebook r40. This is a manual analytical milestone for one declared KdV model. It remains pending independent verification. The original D1/E1/E2 physical dispersive-law objective stays OPEN BUILD. No production formula, theorem, manuscript, source holding or gate is changed here.

## Model and source boundary

Primary input: Coutant–Weinfurtner, arXiv:1707.09651v2, 12 January 2018, held PDF SHA256 `7119b9564fa4fa9dda866f9843148c4be7d2e2643673080d423f8ae722664abb`. The lead directly read physical pages 1–13 and the relevant part of 14, plus conclusions/Appendices A–B through the start of page21. Pages14–17 and the remaining bibliography were not fully read in this interval. The text extractor and exact input/output hashes/argv/streams are recorded separately. This is the held preprint, not a newly acquired journal body.

Its equations9–16 define a counterpropagating weakly dispersive KdV action, stationary mode equation, conserved indefinite norm and plane-wave normalization. Co-propagating modes/greybody coupling are omitted. Appendix A explains why this is a distinct chiral dispersive model and only an approximation to a generic full wave equation. No actual polariton or bilayer reduction, reservoir, detector transfer or quantified greybody error is established here.

Use the subluminal sign and positive A,B,L,lambda, with

    s(x)=c(x)-v(x)=B-(A+B)/(1+exp(x/L)).

Then s(-infinity)=-A, s(+infinity)=B. The white-hole horizon is at x_H=L log(A/B); its positive gradient magnitude is

    kappa=AB/[L(A+B)].                                           (1)

This is independently obtained by differentiating s: s'=(A+B)e^(x/L)/[L(1+e^(x/L))²]. The sign of a signed black/white-hole surface gravity must not be confused with its positive magnitude. Choose a positive background speed c0 and A,B much smaller than c0 if invoking the near-critical regime; actual stationarity and implementability of such profiles in a device remain a physical input to be justified.

The source's action is

    S=(1/2) integral [phi_t phi_x-s(x)phi_x²+phi_xx²/lambda²] dt dx.

Varying and integrating the spatial equation once with zero integration constant gives the stationary equation

    i omega phi+s(x)phi'+phi'''/lambda²=0.                         (2)

At omega=0, psi=phi' obeys

    psi''+lambda² s(x)psi=0.                                     (3)

This is a concrete profile-dependent differential equation, not the desired temperature law inserted as a definition. Units are [s]=length/time and [lambda²]=time/length³. Lambda in the source's quartic dispersion equation6 and lambda in its cubic chiral equation7 have different definitions; neither is silently identified with the repository cutoff.

## Exact zero-frequency mode and asymptotic coefficients

Put y=exp(x/L), l=lambda L sqrt(A), r=lambda L sqrt(B), all positive. Equation3 becomes

    y² psi_yy+y psi_y+(r² y-l²)/(1+y) psi=0.

Writing psi=y^l F(z), z=-y, yields

    z(1-z)F''+(1+2l)(1-z)F'-(l²+r²)F=0.                         (4)

Thus a mode decaying on the left is

    psi=y^l 2F1(l+ir,l-ir;1+2l;-y).                              (5)

The hypergeometric differential equation verifies5 directly. Since F(0)=1, the mode is asymptotic to exp(l x/L) as x→-infinity; the other independent mode grows there. The right connection formula (source AppendixB equationB2) gives

    psi ~ A2 exp(ir x/L)+A3 exp(-ir x/L),
    A2=Gamma(1+2l)Gamma(2ir)/[Gamma(l+ir)Gamma(1+l+ir)],
    A3=conjugate(A2).                                           (6)

The mode phi has a nonoscillating constant A1 on the right after integrating psi from the left, as well as the two integrated oscillatory terms. The raw integral of psi over all real x is not an absolutely convergent integral. A1 is its asymptotic constant/Abel-regularized value, rather than an ordinary improper integral assumed to converge.

For precision, use the Mellin parameter d=l-epsilon with 0<epsilon<l in AppendixB equationB3, so the integral in y is absolutely convergent. Its gamma expression has a finite limit as epsilon→0+, since r>0. That limit is

    A1=L Gamma(l)Gamma(ir)Gamma(-ir)Gamma(1+2l)
          /[Gamma(l+ir)Gamma(l-ir)Gamma(1+l)]
      =pi L Gamma(1+2l)/[l r sinh(pi r)|Gamma(l+ir)|²].            (7)

To connect this Abel limit to the asymptotic constant, subtract the two asymptotic oscillations for x greater than a fixed large R. Their antiderivatives have explicitly known oscillatory terms. The remainder from the hypergeometric connection formula decays exponentially as x→+infinity; the left mode decays as x→-infinity. Integrate that remainder ordinarily. The damped integrals of each explicit oscillatory term tend to minus its antiderivative at R, exactly giving the constant left after the oscillatory antiderivatives are removed. This supplies the convergence interpretation omitted by writing an unqualified integral over the whole line.

Identities used here: Gamma(1+z)=z Gamma(z), conjugation for real parameters away from poles, and Gamma(ir)Gamma(-ir)=pi/[r sinh(pi r)]. The source provides the hypergeometric connection and Mellin identities; this report derives the parameter substitution, convergence restriction/limit and simplification. It does not claim to have independently reconstructed all of special-function theory.

## Flux normalization and a derived low-frequency scale

For the action above the conserved norm is Im integral phi* phi' dx. Unit-frequency normalized plane waves have amplitude 1/sqrt(|k v_g|). The source's equations26–28 match the zero-frequency mode to such waves in the overlap L<<|x|<<c/omega. Their carrying relation is

    beta ~ -i (A2/A1) sqrt[2 B L/(omega r)], omega→0+.            (8)

This matching relation and the chiral-model validity are explicit source inputs. A uniform finite-omega remainder has not been proved here. The proposed calculation does not assume beta or the answer's coefficient as an arbitrary scalar hypothesis; A1 and A2 come from the actual profile equation3. It remains a low-frequency construction, not an error-controlled experimental band.

Using6–7,

    |A2/A1|²
      = l² r sinh(pi r)²/[2 pi L²(l²+r²)sinh(2 pi r)],

because |Gamma(l-ir)/Gamma(l+ir)|=1 and
|Gamma(2ir)|²=pi/[2r sinh(2pi r)]. Since l²/(l²+r²)=A/(A+B), equations1 and8 give

    Theta := lim_(omega→0+) omega |beta|²
           = kappa sinh(pi r)²/[pi sinh(2pi r)]
           = kappa/(2pi) tanh(pi r).                             (9)

Theta is a frequency-valued low-frequency occupation scale. Temperature in kelvin would be hbar Theta/k_B, under the source's low-frequency/equipartition interpretation. It is not a proof that the full spectrum is a Planck distribution. The source's indefinite-norm conservation |alpha|²-|beta|²=1 gives the same leading detailed-balance scale; actual additional channels/greybody factors require separate derivation.

## Explicit dispersive asymptotic bound and profile dependence

For this fixed model and profile family, define delta=1/r and Theta_H=kappa/(2pi). Then the relative deficit is exactly

    R(delta)=1-Theta/Theta_H=2/[exp(2pi/delta)+1], delta>0.        (10)

Hence, with z=exp(-2pi/delta),

    z < R(delta) < 2z,
    0 < R(delta) <= 2 m! [delta/(2pi)]^m, integer m>=0.           (11)

The second estimate follows from exp(t)>=t^m/m!. Taking m>p proves R(delta)/delta^p→0 for every fixed p>=0. This is a controlled exponential correction with a finite explicit upper bound for every delta; its leading nonzero coefficient at delta² is zero. The source reports the exponential character, and11 is an explicit derived remainder bound.

To compare with the repository's D=xi*kappa/c_s, hold positive A,B,c_s,xi,lambda fixed and vary L. Then

    delta=C_profile D,
    C_profile=c_s(A+B)/(lambda xi A B^(3/2))>0.                  (12)

The relative deficit is therefore beyond all positive powers of D within this declared chiral profile family. The conversion is an algebraic fixed-material/profile scaling; identifying xi and lambda with a given physical platform remains a separate material-model derivation. No different source's D convention is substituted. Asymmetry changes C_profile even when the local gradient is matched, so the input profile data cannot be discarded merely because kappa is known.

This result is a useful obstruction to deriving a nonzero universal pi/6 quadratic coefficient merely from “weak dispersion,” but is **not** a full-device counterexample to every original programme target. The omitted downstream/greybody coupling and material/device reduction may produce additional corrections. It would be wrong to use this result alone to request scientific route closure or to overwrite the existing law without an operator decision on a demonstrated target conflict.

## What remains owed

The full original D1/E1/E2 BUILD needs a physical dispersion and operating profile for each platform, full in/out/state/observable and boundary normalization, device reduction and additional-mode/reservoir effects with bounds, a thermal or explicitly nonthermal interpretation, and a uniform remainder on a usable finite frequency interval. This first profile construction gives a concrete comparison problem and explicit asymptotic estimate. It does not establish the current pi/6 law, a universal alternative, an empirical band or physical calibration.

Next substantive actions: independently verify4–12, especially the Abel/asymptotic-constant interpretation and source normalization; derive/bound the full-wave-to-KdV/downstream coupling error on a specified near-critical profile; qualify one actual E1 or E2 dispersion/profile before transporting the result to its prediction. A native statement should encode the actual operator and these assumptions, not make the desired temperature its premise. ROOT retains native/source integration admission. No infeasibility, deferral, closure or gate green is claimed.

Separate source cross-check: the lead read ALL six text pages of held Coutant–Parentani arXiv:1402.2514v2, PDF `96299d47d06bff45b3754ed5f74ae81077ac75d38b4558e0fe93301fcda236d2`. Its equations4–11 give a local-linear near-horizon p-space/WKB result, with left-mover mixing and finite linear-region limitations. That is not an exact globally calibrated device correction. No new all-page pixel inspection or final-edition equivalence is asserted for either source.
