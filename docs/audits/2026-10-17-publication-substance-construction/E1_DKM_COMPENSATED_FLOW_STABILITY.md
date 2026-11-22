# 10.D — Exact homogeneous stability threshold uniform in flow for the compensated model

The independent adversarial review on 2026-11-22 accepted the derivation as written. The reviewed source note has SHA256 `42788b9409311562c3fd4fb5f83437626581d255bd7f9037082d7c41bcf7af9c`. The accepted source-model packet `E1_DYNAMIC_DARK_RESERVOIR.md` has SHA256 `a78229756aea77e084b6c0aef59a462027760400b786283579997eee2aebb62c`. The underlying model follows the laboratory-frame reservoir equation in [Falque et al., arXiv:2311.01392v2, Appendix B.1](https://arxiv.org/html/2311.01392v2#A2.SS1). The source PDF is held in the repository literature corpus.

A separate sampled check evaluated 2,240 below-threshold cases and 800 boundary or growing witnesses. All passed. The maximum scaled residual on the original polynomial was 2.77e-12.

Use the already reviewed `E1_DYNAMIC_DARK_RESERVOIR.md` §4, eqs. (11), (14), with fixed nonzero Fourier mode q, loss half-rate a>0, reservoir rate g>0, and Ω²=E S/ℏ²≥0 in the compensated branch. Define d=v·q, α0=C/g, k=2α0 E/ℏ²≥0. The growth-rate polynomial is

    P(λ)=(λ+g)[(λ+a+i d)²+Ω²]+g k.

The laboratory reservoir factor is unshifted. All a,g,d,λ have units of angular frequency; Ω²,k have its square. Treat d as any real Doppler rate for the model certificate, fixed other coefficients. For a physical regime d, g, k and the background can be correlated. The result is exact for uniformity over all real d and remains sufficient on consistent subsets.

**Threshold.** For every g>0, all roots have negative real part for every real d exactly when

    k < 4a(a+√(a²+Ω²)).

At equality each fixed g has a Doppler value with an actual imaginary-axis root. Above it each fixed g has a Doppler value with a strictly growing root. This supplies a stability test for the homogeneous dynamical model, independent of the unknown reservoir relaxation rate when the static feedback is known. It does not infer inhomogeneous, nonlinear, horizon, quantum-noise or transport stability.

**Necessary lower bound for a right-half-plane root.** Write λ=x+i y with x≥0, b=a+x>0 and z=y+d. For k=0 the roots are strictly stable directly. For k>0 the characteristic equation says -k/Q=1+λ/g, Q=(b+i z)²+Ω², which is nonzero at a root. Positive real part of the right hand side forces Re Q<0. Let t=z²-b²-Ω²>0. Then Re Q=-t, Im Q=2bz and

    k/(1+x/g) = |Q|²/t
              = t+4b²+4b²(b²+Ω²)/t
              ≥ 4b(b+√(b²+Ω²)).

The last inequality is exact, by (√t−2b√(b²+Ω²)/√t)²≥0, with equality at t=2b√(b²+Ω²). Since b≥a, a right-half-plane root requires k≥4a(a+√(a²+Ω²)). For x>0 this inequality is strict.

**Converse for worst-case flow, including an explicit growing root.** Put F(x)=(1+x/g)4(a+x)(a+x+√((a+x)²+Ω²)) for x≥0. It is strictly increasing, continuous and unbounded, with F(0) the threshold. At equality set x=0, and above it choose the unique x>0 with F(x)=k. Set b=a+x, t=2b√(b²+Ω²), z=+√(t+b²+Ω²), Q=-t+i2bz, y=g Im(-k/Q) and d=z-y. These are real finite values, and by construction -k/Q=1+x/g+i y/g. Therefore λ=x+i y is an actual root of the original polynomial (no eliminated-factor artifact). The reflected choice z↦−z gives the corresponding opposite-flow control. At q=0 a flow cannot produce arbitrary d, but the compensated model also gives k=Ω²=0 and the factored base roots. A restricted range of d can remain stable above the uniform bound. The accepted rest-frame Routh criterion remains valid and distinct.

**Carrier-wide sufficient test on the compensated branch.** For every nonzero ε=E>0, S=ε+2B, B>0, so Ω=√(ε(ε+2B))/ℏ > ε/ℏ. Then 4a(a+√(a²+Ω²))>4aε/ℏ. With k=2α0 ε/ℏ², the simple α0≤2ℏa=ℏΓ is sufficient at all declared momenta and all homogeneous flows. In the mathematical unlimited ε model, if α0>2ℏa, the ratio of the exact threshold to ε tends to 4a/ℏ, so some large ε fails uniformity over arbitrary Doppler rates. This is neither a claim of physical ultraviolet validity nor a finding of instability at the source's measured flow. For a bounded admissible q or d range apply the pointwise threshold or solve the actual pole problem with controlled coefficient uncertainty.
