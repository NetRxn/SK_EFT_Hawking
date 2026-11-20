# L1 retarded transport matching

## Conditional construction

Use the Fourier convention exp(i k x − i Ω t), with angular frequency Ω in radians per second. Assume a homogeneous retarded channel with inverse kernel

`Ω² − c² k² + i Γ_H Ω k²`,

where c is a positive speed and Γ_H is a nonnegative diffusivity in m²/s. Set γ = Γ_H/c² in seconds and y = γΩ. For real Ω > 0 the outgoing root is `k = (Ω/c)(1 − i y)^(-1/2)`, on the branch continuous from y = 0. Its imaginary part is nonnegative. The dimensionless linear term y belongs to the imaginary inverse kernel. Its leading contribution to k is imaginary and gives attenuation.

Writing `f(y)=(1−iy)^(-1/2)`, Taylor expansion yields `f=1+iy/2−3y²/8+R` with `|R|≤5|y|³/16`, since `|f'''|≤15/8` on the real axis. The real phase correction starts at quadratic order. For the fixed-frequency group slowness, `c ∂Ω Re k = Re(f+y f')`. The fourth derivative bound `|f⁽⁴⁾|≤105/16` and parity bound the two real Taylor remainders by `35y⁴/128` and `35y⁴/32`, respectively. Thus `|c ∂Ω Re k − (1−9y²/8)|≤175y⁴/128`. At 100 Hz, Ω is 200π rad/s. A coefficient multiplying cyclic frequency is 2πγ.

For comparison with the temporal spectrum at real positive k, set x = Γ_H k/(2c). For |x| < 1 the poles are `Ω± = ±ck sqrt(1−x²) − i Γ_H k²/2`. On the positive branch the derivative of the real pole is `c(1−2x²)/sqrt(1−x²)`. The real-wavenumber pole derivative and fixed-frequency group slowness describe different measurements in a lossy medium.

## Evidence and acceptance boundary

The lead checked the Taylor coefficients through cubic order and the real-pole derivative with exact symbolic differentiation. This conditional result supplies a test for proposed microscopic matching. In this model a real linear correction to the speed does not follow from Γ_H. Other real dispersive operators may change the quadratic term. Connecting the result to L1 still requires a physical retarded tensor channel, the baseline speed and transport coefficient from that channel, and propagation and bandwidth controls for an arrival-time inference. The physical BUILD remains open.

## Independent review

On 3 November 2026, the independent adversarial reviewer `/root/l1_transport_review` accepted the conditional algebra. Factoring the kernel gives the outgoing branch phase `atan(y)/2`, with spatial attenuation for positive Γ_H and Ω. The reviewer independently checked the temporal pole sign, units, frequency conversion, real-pole derivative, and the two parity-controlled Taylor remainders that sum to `175y⁴/128`. The review requires microscopic retarded tensor matching and wavepacket propagation before applying the result to the observational bound. Stage 13 and the physical transport finding remain open.
