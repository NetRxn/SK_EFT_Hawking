# 10.C — Actual finite-difference growth and regulator dependence

Independent adversarial review on 2026-11-22 accepted the derivation at its one-particle periodic pure-kinetic scope. Reviewed note SHA256 `65e318c4e51178dbe69922d7850cffc5792510c87cce3890668622bdcd57d51b`. The accepted BEC construction, SHA256 `1d4df252c786e81877fa2116822868261fcdb55eb46f46e07fb93e7f37ed8cb3`, supplies the physical diagnostic lattice context in §11. The [periodic Lean operator](../../../lean/SKEFTHawking/DKMBootstrap/BECPeriodicCommutator.lean) supplies the comparison continuum modes and differential bracket.

This one-particle, one-dimensional periodic control uses the kinetic and cosine observable already checked in the continuum finite Fourier proof. It specializes the independent BEC construction §11 diagnostic lattice to an actual commutator sequence, rather than using only an upper bound on a local Hamiltonian term. Set a=ℏ²/(2m)>0, period L>0, N≥4 sites, h=L/N. Use the physical discrete norm squared h∑|u_j|² on complex periodic arrays. Let S be the cyclic unitary shift, K_N=a(2I−S−S⁻¹)/h², and M_N multiply by cos(2πj/N). The constant observable has zero commutator at every positive order. This is the pure kinetic periodic branch (a constant potential also cancels), with no contact, state or Fock identification.

## Exact sequence and factorial bound at fixed regulator

On e_n(j)=L⁻¹/² exp(2πinj/N), with n indexed modulo N, the modes are orthonormal, S e_n=exp(2πin/N)e_n up to the convention for shift direction, and

    λ_n=4a sin²(πn/N)/h²,   K_N e_n=λ_n e_n,
    M_N e_n=(e_(n+1)+e_(n−1))/2.

For T_0=M_N and T_(r+1)=K_N T_r−T_r K_N, induction using these actual actions gives

    T_r e_n=[(λ_(n+1)−λ_n)^r e_(n+1)+(λ_(n−1)−λ_n)^r e_(n−1)]/2,

with every zeroth power defined as 1. The shifted modes are distinct modulo N; their individual terms are cyclic unitaries composed with diagonal maps. With Δ_N=max_n |λ_(n+1)−λ_n|, the other shift has the same maximum modulus. Triangle inequality gives ||T_r||≤Δ_N^r; projection onto the first shifted normalized mode gives ||T_r||≥Δ_N^r/2. Also ||M_N||=1 by the j=0 grid point. In particular the actual order-r norm sequence satisfies the factorial bound with ε=Δ_N and n₀ norm 1 for this fixed grid, since r!≥1. It has an even stronger exponential bound. K_N is an energy operator. For the time generator K_N/ℏ replace ε by Δ_N/ℏ.

## No uniform rate in the continuum limit

The actual upward gap is

    λ_(n+1)−λ_n=(4a/h²) sin(π/N) sin((2n+1)π/N).

Choose the nearest integer to N/4−1/2, with phase distance at most π/N from π/2. It follows that

    (2a/h²) sin(π/N)cos(π/N) ≤ ||[K_N,M_N]||
                           ≤ (4a/h²) sin(π/N).

For N≥4, concavity of sine on [0,π/2] gives sin(2π/N)≥4/N, and sin(π/N)≤π/N. Hence

    4a/(Lh) ≤ ||[K_N,M_N]|| ≤ 4πa/(Lh).

Thus no uniform finite ε can satisfy the actual order-one bound with ||M_N||=1 as h→0, even though each fixed grid has all-order bounded growth. The lower bound comes from actual high-mode unit tests lifting with the regulator; a fixed-mode convergence check alone cannot see it. In a second-quantized regulator, any actual number-conserving embedding of this same one-particle sector would inherit its lower bound, but that embedding is not proved by this calculation.

## Fixed physical modes converge with an explicit bound

For a fixed integer n, the continuum energy eigenvalue is λ_n^*=a(2πn/L)^2. The inequalities |sin x−x|≤|x|³/6 and |sin x+x|≤2|x| give

    |λ_n−λ_n^*| ≤ (4aπ^4/(3L^4)) |n|^4 h².

Choose N large enough that the tested modes and both successors have distinct indices modulo N. The two commutator coefficients differ from their continuum counterparts by at most half the sum of the appropriate two energy errors. For any fixed r≥1, the difference of the rth powers of the two gaps is bounded using |u^r−v^r|≤r max(|u|,|v|)^(r−1)|u−v|. Thus T_r's actual response on any fixed such mode converges with a stated O(h²) error at each fixed order, while the full regulator norms diverge at order one. Neither a uniform UV estimate nor an interacting state-dependent limit follows.

For a comparison of norms, use the isometric identification of the finitely many distinct normalized discrete modes and their successors with the corresponding normalized continuum modes. For each sign let `e_j` be the displayed energy-error bound and `M_±` the larger magnitude of the two corresponding discrete and continuum gaps. The norm of the response difference on a tested mode is at most

    (r/2) sqrt(M_+^(2r−2)(e_(n+1)+e_n)^2 + M_-^(2r−2)(e_(n−1)+e_n)^2).

Choose the grid large enough that every label in the comparison has a distinct residue. This identifies only the tested finite subspaces. It leaves the ambient Haar-to-Lebesgue identification separate.

The numerical check composed the finite-difference shift matrix in coordinates and compared its nested bracket with the Fourier mode action, for orders 0 through 7 and grids from 4 to 63 points. It used 60 decimal digits in the recurrence after binary64 roundoff exceeded the comparison tolerance at high order. The 192 operator-norm, 976 coordinate-to-Fourier, 126 fixed-mode energy and 630 signed continuum-response controls passed. The largest scaled coordinate-to-Fourier residual was 1.97e-53. The analytical estimates provide the uniform bounds and limits.
