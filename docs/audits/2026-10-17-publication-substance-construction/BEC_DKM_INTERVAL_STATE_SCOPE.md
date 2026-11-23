# Wave 6v.10 — Fixed-particle state and energy windows for the interval model

This note matches the independently reviewed BEC spatial construction (source SHA256 1d4df252c786e81877fa2116822868261fcdb55eb46f46e07fb93e7f37ed8cb3, whole review 8d933d8427fe3fabfa9ba0d923147f90e27c599929b99a038bd4b53d94b63c53) to the constructed [interval Fock Hamiltonian](../../../lean/SKEFTHawking/DKMBootstrap/BECInteractingWallFock.lean), exact source SHA256 1750d60d5ce2283ff91cc0de06d42949d7b14c6890302ea848733d9608949825. The Hamiltonian and its global first-bracket obstruction have native proofs. The state and energy estimates below have mathematical review scope.

## Identification of the sector

Fix $L=T/2>0$, $N\geq1$, inverse energy $\beta>0$, and $a=\hbar^2/(2m)>0$. Use one spectral wall choice throughout. On symmetric $L^2((0,L)^N,d^Nx)$, $T_N$ is the self-adjoint closure of the kinetic on the finite product wall modes. Their continuous representatives are normalized sine pairs for Dirichlet and cosine pairs for Neumann, including the constant Neumann mode. The sine pair can carry a fixed complex phase of unit modulus. The coordinate second derivative has eigenvalue $-(\pi n_i/L)^2$. Thus the finite actions agree with the usual wall Laplacian, and they agree on the dense symmetric graph core by linearity and permutation averaging. The conventional spectral wall operator extends this core and is self-adjoint, giving equality with the constructed closure. At one particle the Lean family uses the exact transported wall operator directly.

Let $W_N(X)=\sum_i V(x_i)+\sum_{i<j}U(x_i-x_j)$, with real smooth $V$ and real smooth even $U$. They are bounded on the finite coordinate and difference intervals. An admissible nonnegative nonzero pair profile is $U(t)=g e^{-(t/\ell_U)^2}$, with $g,\ell_U>0$. For $A=\|V\|_{\infty,[0,L]}$, $B=\|U\|_{\infty,[-L,L]}$ set $B_N=NA+N(N-1)B/2$. The constructed $H_N=T_N+W_N$ uses the kinetic sector domain. Let $f\in C_c^\infty((0,L),\mathbb R)$ be nonconstant and $F=\sum_i f(x_i)$, the same fixed-sector multiplier used by the Fock density.

## Gibbs state and lower spectral moment

The free product spectrum has finitely many labels below each energy. Its resolvent is compact, and the resolvent identity gives compact resolvent for $H_N$ under bounded $W_N$. The min-max principle gives $E_j(H_N)\geq E_j(T_N)-B_N$ in the symmetric sector. The symmetric free heat trace is bounded by the full product trace. Hence both walls give
$$
0< Z_N(\beta)=\operatorname{Tr} e^{-\beta H_N}
 \leq e^{\beta B_N}\!\left(1+\frac{L}{2\sqrt{\pi\beta a}}\right)^N .
$$
The Dirichlet sum starts at $n=1$ and the Neumann sum at $n=0$. The latter is bounded by $1+\int_0^\infty e^{-\beta a(\pi x/L)^2}\,dx$. Thus $\rho_{N,\beta}=e^{-\beta H_N}/Z_N(\beta)$ is the canonical Gibbs state for this $N,L,\beta$. Its first absolute energy moment is finite. For $X_N=H_N+B_N\geq0$, use $x e^{-\beta x}\leq [2/(e\beta)]e^{-(\beta/2)x}$ and the finite trace at inverse temperature $\beta/2$.

Center the density as $O=F-\operatorname{Tr}(\rho_{N,\beta}F)$. Real smooth $F$ preserves both wall form domains, with bounded first derivatives. The form product rule on each energy eigenvector gives
$$
q_N(F\psi_j,F\psi_j)-E_j\|F\psi_j\|^2
    =a\left\langle\psi_j,\sum_i |f'(x_i)|^2\psi_j\right\rangle .
$$
The multiplication potential cancels against $q_N(\psi_j,F^2\psi_j)$. Write $x_j=E_j+B_N$. Since $|E_k-E_j|\leq x_k+x_j$, the absolute transition sum at each $j$ is bounded by $q_{X_N}(F\psi_j,F\psi_j)+x_j\|F\psi_j\|^2$. The form identity bounds this by $2x_jN^2\|f\|_\infty^2+aN\|f'\|_\infty^2$. Its thermal sum is finite. Pairing the ordered thermal transitions in the accepted $+\mathrm{i}/\hbar$ retarded convention and using angular frequency $\omega=(E_k-E_j)/\hbar$ gives the held Eq. (26) on this sector:
$$
\int_0^\infty \frac{\omega}{\pi}\,\operatorname{Im}\chi_f^R(d\omega)
 = \frac{a}{\hbar^2}\left\langle\sum_i |f'(x_i)|^2\right\rangle_{N,\beta}
 = \frac{1}{2m}\left\langle\sum_i |f'(x_i)|^2\right\rangle_{N,\beta}.
$$
A possible elastic atom in the ordered correlation is killed by the retarded difference. The identity concerns a lower, energy-weighted form moment. Higher spectral moments and instrument PSDs have their own conditions.

## Energy window and retained limits

Assume $U\geq0$ and $v_{\min}=\min_{[0,L]}V$. For $P_E=\boldsymbol{1}_{H_N\leq E}$ with $E\geq Nv_{\min}$, the form inequality gives $\sum_i\|\partial_i P_E\psi\|^2\leq (E-Nv_{\min})\|\psi\|^2/a$. Applying the accepted local first-commutator action on this graph gives
$$
\|[H_N,F]P_E\| \leq aN\|f''\|_\infty
       + 2\sqrt{aN}\,\|f'\|_\infty\sqrt{E-Nv_{\min}} .
$$
This is the one-dimensional specialization of the held Eq. (5). It is finite on each window and can grow with the window. It coexists with the actual global Fock obstruction. A nonzero constant $f=b$ gives the separate exact $bN$ control with zero first bracket. The order-zero density remains unbounded over uncapped particle number.

The held Dirichlet $g_4$ and Neumann $g_3$ divergence examples use separate explicit $N=2$ potentials and domain failures. The Gaussian example certifies an admissible nonzero pair profile and Gibbs existence. The heat bound controls the stated finite $N$ and $L$. Prepared states, material scattering and transverse matching, limits in volume or cutoff, and DKM thermal continuum matching require separate evidence under the roadmap.

Independent exact-source science review accepted this finite-box state and energy argument. The energy-window graph step uses the held construction §3A and its independent review, including the ordinary Dirichlet and Neumann graph preservation by the compact profile.
