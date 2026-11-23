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
