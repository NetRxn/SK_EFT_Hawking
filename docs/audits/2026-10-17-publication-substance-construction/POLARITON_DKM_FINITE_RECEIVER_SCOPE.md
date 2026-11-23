# Bilateral receiver transfer and finite-record limits

The [native Cauchy receiver](../../../lean/SKEFTHawking/DKMBootstrap/CauchyReceiver.lean) proves an all-order commutator estimate for a bounded observable on a strongly continuous unitary group with its identified forward generator derivative. The positive output case uses the actual output norm as prefactor and may enlarge the growth rate. Device-level use requires the realized receiver and the transfer to the declared density or current.

## Stationary spectral transfer

The reviewed polariton construction §12 (SHA-256 `7d0d2e5a121c3ba8f67bcc50075d556f757b8f5d3170ec02115e5a1a44b6c0f2`) already gives the Cauchy two-point multiplier and inverse gain. The independently reviewed transfer note `f810beb2406807171cbccf3810e14cbbcaeca992bed0097a52ed36b1f10a611e` derives this at the stationary quantum two-point level and quantifies truncated inversion.

Take a bounded self-adjoint observable $A$, strongly continuous unitary dynamics $\alpha_t$, a normal invariant state $\phi$, and a real $L^1$ kernel $h$. Let $B_h=\int h(t)\alpha_t(A)\,dt$ as the bounded weak receiver. Write $C_A(u)=\phi(\alpha_u(A)A)=\int e^{i\omega u}\mu_A(d\omega)$ in angular frequency, with finite spectral measure $\mu_A$. Invariance gives $\phi(\alpha_{u+s}(A)\alpha_t(A))=C_A(u+s-t)$. Absolute domination by $\|A\|^2|h(s)h(t)|$ and Fubini give
$$
C_{B_h}(u)=\int e^{i\omega u}|H(\omega)|^2\mu_A(d\omega),
\qquad H(\omega)=\int h(t)e^{i\omega t}\,dt.
$$
Since $h$ is real, the multiplier is even. It also multiplies the signed commutator measure $\mu_A$ minus its reflection and preserves any existing detailed-balance relation. Detailed balance, stationarity of a pulse preparation, and the dispersive part of a complex retarded response each need separate evidence.

For the normalized Cauchy kernel of scale $\tau>0$, $H(\omega)=e^{-\tau|\omega|}$. Inverting power transfer over $|\omega|\le\Omega_{\max}$ multiplies a spectral measure error in total variation, or a density error in $L^p$, by at most $e^{2\tau\Omega_{\max}}$. This estimate concerns the same observable in the same stationary state.

For the unnormalized restriction to $|t|\le T$ with $T>0$, the omitted mass is $q=1-(2/\pi)\arctan(T/\tau)\le2\tau/(\pi T)$. The receiver-value error is at most $q\|A\|$. Its amplitude error is at most $q$ and the power error is at most $q(2-q)$. If $q<e^{-\tau\Omega_{\max}}$, its power inversion gain is at most $(e^{-\tau\Omega_{\max}}-q)^{-2}$. For the restriction normalized by the retained mass $1-q$, amplitude error is at most $2q$, giving a sufficient margin $2q<e^{-\tau\Omega_{\max}}$. A common time shift cancels from power. A finite-acquisition estimator, optical transduction and noise-floor control must be identified and qualified to use these margins with data.

The hard cutoff at $\pm T$ introduces boundary distributions in the derivatives of the truncated kernel. The value estimate and finite-band conditioning certify their stated errors. A finite-record all-order commutator estimate needs a separate argument.

## All-order scalar certificate for a compact record

The independently reviewed finite-window note, SHA-256 `7fc1675167d7a87cf842d3affed3a01915d562413bc2e7df8771985dce2e8ede`, examines smooth compact replacements for the hard cutoff. Suppose $f:\mathbb R\to\mathbb R$ is compactly supported and smooth, and $\|f^{(k)}\|_1\le M A_0^k k!$ for every $k$, with $M\ge0$ and $A_0>0$. Integration from below the derivative support gives $\|f^{(j)}\|_\infty\le\|f^{(j+1)}\|_1$. The degree-$n$ Taylor remainder at distance $d$ from a center is therefore at most $M A_0(n+2)(A_0d)^{n+1}$. It tends to zero for $d<1/A_0$. All Taylor coefficients vanish at a point below the support. Repeated steps of length $1/(2A_0)$ spread vanishing over the support, so $f=0$. For $A_0=0$, the first derivative vanishes and compact support again gives $f=0$.

A nonzero normalized compact taper therefore fails this sufficient scalar all-order $L^1$ condition. This scalar obstruction leaves operator-norm bounds for a specified Hamiltonian open. Finite-order estimates, energy-window bounds and stationary-tail estimates have their own hypotheses. The spectral inversion margins above remain compatible with this scalar obstruction.
