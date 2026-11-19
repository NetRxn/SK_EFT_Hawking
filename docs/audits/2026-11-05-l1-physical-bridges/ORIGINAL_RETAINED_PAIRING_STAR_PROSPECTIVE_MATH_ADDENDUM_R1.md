# Prospective mathematics addendum — even polar-Riesz refinement

**Verdict: ACCEPT ATTEMPT within the already authorized full-amplitude Riesz/positivity-test route.** The proposed refinement is mathematically valid with the domain, regularity and scope specifications below. It can derive a canonical positive even-sector Gram from the actual symmetric sewing form while proving that its conjugation cannot be a physical exterior-product star. It is prospective review, not acceptance of an unproduced actual derivation. The main prospective report is preserved unchanged.

Task l1-retained-pairing-star-r1; parent publication-remediation-01a13f67/L1-physical-memory-pairing; exact support source 5be6cf792b3d421c4256a60f5f5391858bf530f9. Frozen main brief SHA256 d366f74b96dd77c49e1e591bb111db400d3989b93b9b18aca4daa65e472f4417. This addendum assesses the lead's explicit pre-construction refinement message: on H_even, B=J^2, G=B^(1/2), K=JG^-1, beta(Kf,g)=<Gf,g>, followed by the top-nilpotent star obstruction. My sole owned new artifact is this report; no other review verdict was consulted.

## Continuity and method

The literal FIRST tool invocation explicitly checked the SAME packet, from the assigned checkout:

    python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-retained-pairing-star-r1.json

It returned fresh=true, changed=[]. The frozen original brief, original kernels and governing contracts read for the main review remain controlling. No packet or source was refreshed. Only manual mathematics and ordinary report/continuity/hash bookkeeping occurred; no evaluator, scientific coefficient/matrix/CAS/Haar/exterior/Gram execution, test, Lean/build/slot/controller/process action, Git/repository edit or notebook mutation occurred.

## 1. Positive polar Gram on the even sector

Retain the accepted auxiliary Hilbert convention: the inner product is anti-linear in its first argument and beta(f,g)=<J f,g>. Use the correctly normalized bounded invertible anti-linear Riesz map J=(1/conjugate Z)J0 M_wbar. On the actual real source neighborhood Z>0. The even sewn weight and the even number of pair generators preserve H_even, so J restricts to a bounded invertible anti-linear operator there.

On this sector exterior multiplication is commutative, hence the actual beta is symmetric. This is a bilinear symmetry statement, not positivity. Substituting Jf as an argument gives

    <J^2 f,f> = beta(Jf,f) = beta(f,Jf) = ||Jf||^2.

J^2 is bounded complex-linear. Its quadratic form is real and nonnegative, so complex polarization makes it positive self-adjoint. Invertibility supplies the lower bound J^2 >= ||J^-1||^-2 I. Thus G=(J^2)^(1/2) exists, is positive boundedly invertible and has a uniform gap on a sufficiently small source neighborhood.

J commutes with J^2 by composition. It commutes with G and G^-1 by real-coefficient functional calculus (real polynomial approximation on the positive spectral interval suffices, and anti-linearity conjugates no real coefficients). Consequently

    K^2=J^2 G^-2=I,
    ||Kf||^2=||J G^-1 f||^2=||f||^2.

K is an antiunitary involution. The proposed identity is exact:

    beta(Kf,g)=<J Kf,g>=<J^2 G^-1 f,g>=<Gf,g>.

This defines a positive definite Hermitian Gram with the actual sewing normalization, equivalent to the coefficient norm. It is a constructive improvement over choosing an unrelated auxiliary norm. It does NOT establish that omega(f) is a positive state for the original wedge product, nor that K is its product adjoint, nor that the original evolution is unitary for G. Those require separate equations.

The odd sector must not inherit K^2=I from this argument. The bare complement map squares to parity, and the sewing form is graded-skew on the odd sector. The existing exact invertible Riesz map there is retained without this even-sector conjugation claim.

## 2. Actual C2 regularity and source contacts

Treat derivatives as real derivatives on the proved positive source neighborhood; no holomorphic adjoint convention is inferred. The full two-interface wbar and normalization produce norm-C2 J via the source/denominator formulas in the main review. Set B(q)=J(q)^2. Its first and mixed derivatives are the compositions

    B_alpha=J_alpha J+J J_alpha,
    B_alphabeta=J_alphabeta J+J_alpha J_beta
                  +J_beta J_alpha+J J_alphabeta.

Each composition of two anti-linear operators is complex-linear. These identities are ordinary real product differentiation, so no unlisted higher frame derivative is needed. B is norm-C2 in the open cone of bounded strictly positive operators. Its positive square root is norm-C2. A concrete derivation uses

    G G_alpha+G_alpha G=B_alpha,
    G G_alphabeta+G_alphabeta G
        =B_alphabeta-G_alpha G_beta-G_beta G_alpha.

The inverse Sylvester map exists boundedly by the positive gap; for any bounded RHS X its solution is integral_0^infinity exp(-sG) X exp(-sG) ds. This also establishes the needed derivative continuity without a finite-dimensional spectral-basis assumption on the compact-link L2 carrier.

Writing H=G^-1, use H_alpha=-H G_alpha H and

    H_alphabeta=H G_beta H G_alpha H+H G_alpha H G_beta H
                   -H G_alphabeta H.

Then K_alpha=J_alpha H+J H_alpha, with all four mixed terms

    K_alphabeta=J_alphabeta H+J_alpha H_beta
                   +J_beta H_alpha+J H_alphabeta.

Products are actual ordered compositions; anti-linearity must be retained when moving any complex scalar across J. Every source-dependent argument/test brings its own derivatives. In particular differentiating beta_q(K_q f_q,g_q) requires the K jets as well as beta and both argument jets. A positive Gram at each q is not permission to discard the moving-conjugation contacts or change the original literal source response.

This construction is on the full Hilbert carrier. G and K need not preserve the ORIGINAL polynomial coefficient domain: square roots of link-polynomial matrices generally give continuous coefficient functions instead. Here J, B, G and K are pointwise finite exterior-matrix fields over compact links, so they do preserve continuous coefficient sections. The formal result may use that continuous/Hilbert enlargement explicitly; it must not claim polynomial closure without proof.

## 3. Exact nilpotent obstruction to an exterior physical star

Let e=Theta_a Theta_b be the constant-compact-coefficient full pair top. It is nonzero and even. The actual sewn weight has body one, so normalized original omega_q(e)=1/Z_q!=0 and omega_q(1)=1. The ideal of positive exterior degree is the nilradical of the original polynomial-function/exterior algebra: the compact coefficient algebra is reduced, so a nilpotent element has zero body, and the positive-degree ideal is nilpotent. The same statements hold on the even subalgebra and on continuous coefficient sections.

Any unital conjugate-linear involutive exterior anti-automorphism preserves nilpotents and therefore this nilradical. Hence e-star lies in the positive-degree ideal, giving e-star e=0. If the unchanged original omega were positive for that product/star, its Cauchy–Schwarz inequality with 1 and e would give

    |omega(e)|^2 <= omega(1) omega(e-star e)=0,

contradicting omega(e)=1/Z. This is pointwise in the source, so allowing the star to move with q does not evade the argument as long as it remains an exterior anti-automorphism and the original omega/product are retained. No assumption that the star fixes the compact coefficient subalgebra is needed beyond being an automorphism of the stated algebra and preserving nilpotence.

The polar K itself is incompatible in an equally direct way. The positive Gram gives beta(K e,e)=<G e,e>>0. But if K e had zero body, its product with the top e would vanish and beta(K e,e) would be zero. Thus K e has nonzero body in the continuous coefficient carrier. It is not nilpotent there, so K cannot be a unital exterior anti-automorphism. If K does not preserve the polynomial domain, that already blocks treating it as a star on that domain; the body test shows that even the natural continuous extension cannot make it an exterior anti-automorphism.

## Scope and disposition

The refinement fits the accepted route: derive what positivity the actual symmetric sewing form DOES canonically supply, then test its compatibility with original products and dynamics. It adds a positive even-sector Gram, not a physical state/operator interpretation by declaration. The exact no-go is for a positive state retaining the original exterior amplitude product and normalized full insertion functional with a unital exterior star. A deformed/noncommuting physical product, different amplitude-to-observable map or appropriate physical construction is not excluded.

Original two-interface evolution/source/periodic identities, the retained Phi response, and the full odd-sector Riesz realization remain intact. Microscopic metric product, positive physical quantum-link memory, tensor/matter/EM/light/time calibration, B3/N4 and controlled limits retain their original requirements. Proceed to formal construction and exact ACTUAL review with these domain and contact conditions. ROOT retains scientific disposition and integration.

Final SAME packet check and this report's SHA256 are returned in the handoff; no self-referential hash is embedded here.
