# 10.D — No small-momentum DKM density pole on the compensated finite-loss branch

This result applies to the reviewed homogeneous Falque B1/B2 three-component model, repulsive statically compensated branch, calibrated potential coupled to polariton density, fixed positive polariton half-loss a and reservoir rate g. This concerns the mathematical infrared limit of that response channel. The comparison does not assume the device realizes an equilibrium state.

The reviewed source-model packet E1_DYNAMIC_DARK_RESERVOIR.md (SHA256 a78229756aea77e084b6c0aef59a462027760400b786283579997eee2aebb62c), Eq. (7), (11), (14) and §5, gives the exact density inverse, all three damped modes at q=0 and the laboratory-static compensated limit zero at finite loss. The result below adds a uniform pole-exclusion neighborhood, a response bound there, and a falsifying diffusion scaling for DKM matching.

Write ζ=−iω in laboratory angular-frequency units, d=v·q, E=ε_q=ℏ²|q|²/(2m)>0 at nonzero q, S=E+2B, Ω_q²=ES/ℏ² and k_q=2α₀E/ℏ²≥0. Thus Ω_q² and k_q are O(|q|²). The source model uses

    P(ζ)=(ζ+g)[(ζ+a+i d)²+Ω_q²]+g k_q,
    χ_nn(ω,q)=−(2n₀ E/ℏ²)(ζ+g)/P(ζ).

The sign is the source's positive external potential convention. Let r=min(a,g)/2. For all complex |ζ|≤r, |ζ+g|≥g/2 and |ζ+a+i d|≥|a+i d|−|ζ|≥a/2, for every real d. The reduced denominator therefore satisfies

    |P(ζ)/(ζ+g)| ≥ a²/4 − Ω_q² − 2 k_q.

For every q with Ω_q²+2k_q≤a²/8, this is at least a²/8. In particular P cannot vanish anywhere on that closed complex disk. Throughout it,

    |χ_nn(ω,q)| ≤ 16 n₀ E/(ℏ² a²).

The same fixed r works for all sufficiently small q, and this bound is O(|q|²). The source's existing q=0 decaying-root statement is recovered as a special case. The bound accounts for a finite positive g without needing its quantitative estimate to conclude there is some nonzero r. A numerical frequency width uniform across a device uncertainty set would still require a lower bound on g, or additional proof using the actual cancellation. The pole exclusion is local in complex frequency and does not assert all-q stability.

The [CHHK retarded DKM model](https://arxiv.org/html/2509.18255v2#S3) on its low-frequency branch has denominator D|q|²−τ ω²−iω and numerator χ D|q|² with D,χ,τ>0. For each sufficiently small nonzero q it has a pole ω=−iD|q|²+O(|q|⁴), with nonzero numerator there. This follows from the root near ζ=0 of τζ²+ζ+D|q|²=0. There is also a real-frequency test avoiding complex continuation: along ω=c|q|² with any fixed c>0, the signed imaginary DKM response tends to χ D c/(D²+c²)>0. The compensated B1/B2 imaginary response tends to zero along the same scaling by the bound above. An overall sign convention changes neither the pole comparison nor the absolute discrepancy. The static contrast agrees with the accepted source analysis: at every nonzero q the DKM static limit is χ, while the driven compensated response tends to zero as q→0.

Thus this particular finite-loss potential-to-density response cannot realize the source's positive-compressibility DKM diffusion form on a band containing such frequencies arbitrarily close to q=0. It does not exclude finite-band phenomenology away from the scaling, an effective response of a different conserved density of a closed dilation, a gapless limit with damping and reservoir rates scaled consistently, a noncompensated setting, or an inhomogeneous geometry whose response has not been computed here. Any of those is a separate physical transfer/model question. This scoped exclusion requires neither a rate fit nor a hardware experiment; quantitative finite-band classification continues to require a calibrated response and the other CHHK inputs.

Independent adversarial review accepted the derivation with SHA256 `b69641139ad5fbaa027d2b7922584ba7cd993760352ca5c615626b77da1756a9` at the stated model scope. Synthetic checks compared 1,000 complex-frequency evaluations with the full three-component matrix solve, tested 1,000 cubic root sets against the exclusion disk and exercised 3,000 real-frequency samples over 1,000 diffusion rays. The largest scaled resolvent discrepancy was 1.33e-11. These are arithmetic controls separate from the proof and device calibration.

## Detuned homogeneous branch with nonzero static inverse margin

The same source-model obstruction has a slightly broader form. Do not assume compensation in this section. Write E=E0+ε_q and S=S0+ε_q, where E0=U_eff n0−Δ and S0=E0+2B. The source assumes α₀≥0. Set

    Q(ζ,q)=(ζ+a+i d)²+ES/ℏ²+ (2α₀/ℏ²) E g/(g+ζ),
    Q_* = Q(0,0) = a²+E0(S0+2α₀)/ℏ² = I'(n₀)/ℏ².

Here Q_* is real, χ_nn=−(2n₀/ℏ²)E/Q and P=(ζ+g)Q. Suppose Q_*≠0. In particular the source's strict q=0 dynamical stability implies this condition since the cubic has no zero root; conversely the nonzero condition alone does not prove stability. At fixed finite flow d=v·q, take b=|ζ|+|d|, ε=ε_q and |ζ|≤g/2. The exact algebra of the reservoir difference is

    E g/(g+ζ)−E0=(gε−E0 ζ)/(g+ζ).

Using this identity and subtracting the other two polynomial terms gives |Q−Q_*|≤B_err with

    B_err=2a b+b² + ε(|E0+S0|+ε)/ℏ²
          + (4α₀/ℏ²)(ε+|E0| |ζ|/g).

When B_err<|Q_*| the full cubic has no pole there and

    |χ_nn(ω,q)−χ_nn(0,0)|
      ≤ (2n₀/ℏ²) [ ε + |E0| B_err/|Q_*| ] / (|Q_*|−B_err).

These bounds come from |g+ζ|≥g/2 and |Q|≥|Q_*|−B_err. They are dimensionally in angular-frequency squared for Q_*, B_err and density/energy for χ_nn. At any fixed Q_*≠0 and fixed finite v, a neighborhood of the complex-frequency/momentum origin satisfies the margins. Since χ_nn(0,0)=−(2n₀/ℏ²)E0/Q_* is real, along ω=c|q|² the imaginary part is O(|q|) and tends to zero. A positive-compressibility CHHK response along that ray has the nonzero limit derived above, even when the driven static susceptibility itself is nonzero. This rules out that infrared matching on every strictly stable homogeneous branch of the stated source model. The special compensated bound is stronger, because its full complex response is O(|q|²) and its exclusion condition is independent of d. A turning point Q_*=0, a near-critical limit where the margin vanishes, a different conserved density, a finite band, or an inhomogeneous experiment remains outside this detuned certificate.

Independent adversarial review accepted the derivation at this scope (SHA256 `973d1279bfd73a9244155ff2a64571badca6575d398819adabcc7fb7a1e56889`).

## Exact matching on an open finite band

For the same fixed homogeneous B1/B2 model and Q_*≠0, the diffusion-ray discrepancy also rules out exact equality of the two signed spectral functions on any nonempty open frequency–wavevector domain where the two inverses exist. This is a rational-function identity argument for the model, independent of any assumption of analytic continuation of measured data.

For real ω and real vector q, substitute ζ=−iω, d=v·q and ε_q=ℏ²|q|²/(2m). The real and imaginary parts of the full polynomial P and of N=−(2n₀/ℏ²)E(g−iω) are real polynomials in the components of (ω,q). Thus Im χ_nn=Im(N conjugate(P))/|P|² is a real rational function where P≠0. The DKM signed imaginary response is χD|q|²ω/[ω²+(D|q|²−τω²)²], also a real rational function. For any fixed real nonzero conversion factor between the channels, equality of the signed responses on a nonempty open set forces the cross-multiplied polynomial to vanish identically. A real polynomial vanishing on a nonempty open set vanishes everywhere. One can prove this by taking product intervals inside that set and applying the univariate polynomial identity successively in each coordinate.

Both denominators are nonzero on the small nonzero diffusion-ray samples used above. The B1/B2 denominator is nonzero by the positive local margin, and the DKM denominator is at least ω²>0. The forced global polynomial identity would give equality at each of those samples, contradicting their zero versus strictly positive imaginary limits. A nonzero fixed conversion factor on either side, including reversal of the potential sign, leaves this contradiction.

The conclusion pertains to exact equality with fixed transport and model coefficients on a set with interior in (ω,q), or on a two-variable open patch after fixing one momentum direction and allowing its magnitude to vary. It provides no numerical lower bound on approximation error over a chosen finite band. It does not rule out agreement at finitely many points, agreement along a single dispersion curve, a fit within experimental tolerances, nonconstant unknown detector transfer, or another physical density channel. The original microscopic-to-effective comparison and any approximate fit must declare their norm and error tolerance.

Independent adversarial review accepted the derivation at this scope (SHA256 `9dd166a61776657e7180ac109d6a010606b202be06ae1007ee602396ee31512b`).

Separate normalized synthetic controls compared 3,600 responses against the full three-component matrix, with maximum scaled residual 2.30e-14. All 2,583 certified perturbation cases met the response bound. The margin rule declined 1,017 cases. The controls included 1,200 approaches along the diffusion scaling. The exact open-band assertion follows from the polynomial argument.

## A finite-band separation margin near the diffusion scaling

The existing detuned pole-exclusion bound also gives a conditional error tolerance on a band of nonzero width. Fix a homogeneous B1/B2 branch with real Q_*≠0, positive a, g, n₀, m and ℏ, and α₀≥0 as in the source. Take laboratory frequencies ω=c|q|² and band limits 0<c₋<c₊, 0<q₋<q₊, with c∈[c₋,c₊] and |q|∈[q₋,q₊]. Here c has the units of diffusivity. Allow transport fits with χ≥χ₋>0, 0<D₋≤D≤D₊ and 0<τ≤τ₊.

If τ₊c₊²q₊²≤D₋, throughout this band the DKM imaginary response has the uniform positive lower bound

    Im R_DKM = χDc/[c²+(D−τc²|q|²)²]
               ≥ L_DKM := χ₋D₋c₋/(c₊²+D₊²).

Indeed 0≤D−τc²|q|²≤D₊ on the band. The lower bound still applies to varying fits whose coefficients stay within the specified ranges. No assumed pole continuation or high-frequency model is needed.

For the fixed detuned B1/B2 branch, set ε₊=ℏ²q₊²/(2m), ω₊=c₊q₊², b₊=ω₊+|v|q₊ and

    B₊ = 2ab₊+b₊²+ε₊(|E₀+S₀|+ε₊)/ℏ²
         +(4α₀/ℏ²)(ε₊+|E₀|ω₊/g).

If ω₊≤g/2 and B₊<|Q_*|, the existing bound and the reality of χ_nn(0,0) give |Im χ_nn|≤L_B, where

    L_B = (2n₀/ℏ²) [ε₊+|E₀|B₊/|Q_*|]/(|Q_*|−B₊).

The coefficients of the error majorants are nonnegative, so replacing |q|, |ζ| and |v·q| by their stated upper bounds is valid across the band and all included directions. If a real conversion from this calibrated density response to the DKM normalization has magnitude at most Λ, then at each point

    |Im R_DKM − Im(λ χ_nn)| ≥ G := L_DKM−Λ L_B.

For G>0 and an actual measurement Y with |Im Y − Im(λχ_nn)|≤ε_meas, the residual against every admitted DKM prediction is at least G−ε_meas. An absolute fitting tolerance ε_fit cannot explain such a datum when ε_meas+ε_fit<G. Additional errors in the adopted B1/B2 prediction or normalization must enter the same budget. A complex calibration with unknown phase is not covered by the detuned estimate: it can rotate the nonzero real static response into the imaginary channel. If a complex conversion is known to obey |λ|≤Λ and |Im λ|≤δ_phase, one can instead use |Im(λχ_nn)|≤Λ L_B+δ_phase|χ_nn(0,0)|. This follows by subtracting the real static response before applying the envelope. For compensation χ_nn(0,0)=0, the existing uniform bound on the full response also directly permits bounded complex calibration.

For fixed positive rate and margin, B₊ and L_B tend to zero with q₊. Thus the certificate admits positive finite intervals q₋<q₊ in the fixed model, without taking a measurement at ω=0 or q=0. Actual applicability requires values and uncertainty budgets for the carrying branch, normalization, fitted parameter ranges and a usable frequency–wavevector band satisfying the inequalities. A rate uncertainty extending to zero supplies no common ω₊ by this formula. The condition does not classify an uncalibrated optical signal, actual inhomogeneous data, a different conserved channel, or approximation on an arbitrary band outside this low-momentum region.

Independent adversarial review accepted this conditional bound at SHA256 `456198d7f75803aafaba5cb8ee7806c935756298bf528a39bf504f659d134b25`. A separate synthetic control used seed 61710 to evaluate 3,600 frequency–wavevector points in 120 coefficient boxes. It solved the original three-component source matrix with the potential forcing vector, evaluated the complex DKM formula independently, and applied bounded complex conversion and measurement error. The maximum scaled solve residual was 5.93e-16. Every sampled case met the separation margin.
