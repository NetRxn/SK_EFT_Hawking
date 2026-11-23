# Planar photon-density bracket in the coupled port model

The one-particle angular-frequency generator is the self-adjoint $K_1=(T_C\oplus T_X\oplus\Omega)+B$, with $T_s=-a_s\Delta$ and $a_s=\hbar/(2m_s)>0$. The bounded matrix $B$ includes a real offset and potential on each spatial diagonal, Rabi multiplication $R$ and its adjoint, and $W,W^\dagger$ coupling photons to the full positive-frequency bath. The incident coherent amplitude enters the preparation. The original interacting Fock family has a nonzero bounded exciton pair interaction, whose pair sum is empty in its intrinsic one-particle sector.

For a real smooth compact profile $f$, set $M=\mathrm{diag}(M_f,0,0)$ and $C=[K_1,M]$ on $D(K_1)\cap M^{-1}D(K_1)$. For a compact smooth $u$, both $u$ and $fu$ belong to the actual planar kinetic domain. For the supported photon test $J_Cu$ its photon projection is
$$
P_C C J_C u=C_f u
=-a_C\sum_{j=1}^2[(\partial_j^2f)u+2(\partial_j f)(\partial_j u)].
$$
The photon offset and potential cancel as multiplication operators. The other two coordinates are $R^\dagger(fu)$ and $W(fu)$. For a general vector $(u,v,b)$ in the common domain, the block form before expanding the kinetic term is
$$
C(u,v,b)=([T_C,M_f]u - M_f(Rv+W^\dagger b),\ R^\dagger M_f u,\ W M_f u).
$$
Compression uses supported inputs and retains both off-diagonal outputs. For $u_q=e^{iqx_k}u$, the photon response is $e^{iqx_k}(C_fu-2i a_Cq(\partial_k f)u)$. Modulation preserves the $L^2$ norm. For any nonconstant $f$, choose a point and coordinate with nonzero derivative and a compact smooth bump $u$ equal to one at that point. The derivative-product has positive $L^2$ norm by continuity on a neighborhood. Thus
$$
\|C J_C u_q\|\ge\| C_fu_q\|\ge 2a_C|q|\|(\partial_k f)u\|-\|C_fu\|.
$$
The input has the same nonzero norm for every $q$, so a bounded extension is impossible. The angular-frequency scale is $2a_C=\hbar/m_C$. The energy commutator $[H,M]$ inserts another factor of $\hbar$.

A constant photon profile is a scalar photon projector. It preserves the graph domain, which is the direct sum of the free coordinate domains. The full constant-photon bracket has the bounded off-diagonal block extension above and can be nonzero when $R$ or $W$ is nonzero. The same constant on all three species gives a multiple of the identity at $N=1$, with zero bracket. Its microscopic lift in the original model is a multiple of total number, which is unbounded at order zero for a nonzero constant and has zero first bracket on the common domain. With no Rabi or port exchange the projected nonconstant obstruction persists. Setting the incident coherent amplitude to zero leaves these operator results intact. These tests give no thermal covariance or laboratory signal prediction.

The reviewed original interacting family has the actual inclusion $j_1$ and projection $p_1$ of the total-number direct sum. For a coupled one-particle common-domain vector $x$, the identified restrictions give $K_{\mathrm{tot}}j_1x=j_1K_1x$ and $d\Gamma(M)j_1x=j_1Mx$. The common-domain witnesses for both compositions are the same sector inclusions, including after applying $K_1$ or $M$. An ambient bounded extension $A$ would give the bounded $p_1Aj_1$ agreeing on the coupled tests. This conclusion uses the independently reviewed manual higher-sector construction and its precise $N=1$ match to the native operator. A native construction of the higher sectors remains separate.

The exact-source adversarial Lean review accepted the [compact photon-density proof](../../../lean/SKEFTHawking/DKMBootstrap/PolaritonDensityCommutator.lean) against the reviewed [coupled generator](../../../lean/SKEFTHawking/DKMBootstrap/PolaritonSpatialGenerator.lean). It checked the Cartesian derivative, compact-support and normalization witnesses, both graph memberships, composition, and the use of the actual photon projection. The final file SHA-256 is `0d99153935ebf5e5d0b7ce8b6fff3075c805309bbef8217f247803ecccb0e053`.

## Numerical control

The calculation used nondimensional compact bumps on a square of side 8 with periodic padding. It independently evaluated both operator compositions with a Fourier multiplier and with a fourth-order centered stencil for the spatial Laplacian. A complex rank-one port and its weighted adjoint acted on finite positive-frequency quadrature, with distinct photon and exciton kinetic coefficients. Both calculations compared to the differential and block formulas on the same grid and quadrature. On the $1024^2$ grid, the relative errors were $1.0969\times10^{-9}$ for Fourier and $3.6259\times10^{-6}$ for the stencil. The analytic compressed response per unit input norm rose from $0.4061$ at $q=8$ to $2.9695$ at $q=64$. Zero input and the total identity gave zero brackets. The photon projector with nonzero exchange gave a nonzero bracket, and the direct block calculation agreed with the formula.

The script SHA-256 is `73f939ccb4b0c370f3ce29027ec0a83ba00e23e9f0730557e63b179ff6c03138` and its output SHA-256 is `c0684dd22ecd7601d0d7ead1281caf26b76a2b5aba52f8e20bdbbc7a72c774c6`. Independent replay reproduced the output byte for byte. The [numerical evidence archive](POLARITON_DKM_PLANAR_BRACKET_NUMERICAL_EVIDENCE.zip) contains the exact script, raw output, environment, and replay command. These fixed-sample comparisons leave physical bath quadrature error, spatial approximation uniform in $q$, and device calibration open. The analytic lower bound establishes continuum unboundedness.
