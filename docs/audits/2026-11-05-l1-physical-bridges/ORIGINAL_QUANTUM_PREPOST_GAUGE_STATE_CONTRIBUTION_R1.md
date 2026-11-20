# Compact gauge action on the original relative cut and its positive comparison state

Manual mathematical contribution by /root/prepost_gauge_state_synthesis to /root, task l1-quantum-prepost-constraint-construction-r1, parent publicationROOT01a13f67/L1-physical-observable-boundary. Source 1a054ba3e75049cc73117c61c8f741d944d1a4bd. Executor01a1ac65 owns the primary L1FixedControls notebook. The only authored artifact is this private contribution. It supplies source and comparison results for the principal author's reconciliation and fresh ACTUAL review.

The original compact endpoint action induces an invariant faithful comparison state and a fixed unitary implementation on its comparison GNS space. All four marked coframe loops are nonzero. Their outgoing compact representation is trivial and their incoming compact representation carries a vector mark. After the actual periodic identification this implies \(C_A C_B=0\) for every \(A,B\), whereas the original same-kernel \(C_{AA}\) and \(C_Q\) have respective nonzero full-cap values \(-1/8\) and \(-1/2\). These are two differently typed operations. The tested identification fails even inside the faithful positive comparison realization. A covariant open arrow and its associated marked sector survive the test.

## 1. Original endpoint action on relative arrows

Use the original gauge law and measure of ORIGINAL_BOUNDARY_GAUGE_CONSTRAINT §§2–3,6, the polynomial cut cores of ORIGINAL_GRADED_CONSTRAINT_RELATION §§3–7 and ORIGINAL_ORDERED_QUANTUM_CUT_CONSTRUCTION §§1–4, and the exact same source plane and coupling of ORIGINAL_POSITIVE_COMPARISON_STATE_CONSTRUCTION §§1–2. These bodies and the other named source bodies are in docs/audits/2026-11-05-l1-physical-bridges. Each represented vertex group is the original Spin(4), with independent spatial gauge parameters. Its transformations are
\[
 \psi_x\mapsto g_x\psi_x,\qquad
 \bar\psi_x\mapsto\bar\psi_xg_x^\dagger,\qquad
 U_{x,\mu}\mapsto g_{x+\mu}U_{x,\mu}g_x^\dagger .
\]
In particular \(v_a\mapsto g_b v_a g_a^\dagger\). Both represented endpoints are essential. Use the inverse pullback convention \(R_i(g)F=F(g^{-1}\cdot z_i)\) and likewise on the output \(R_o\) and the matching space \(R_D\). This is a representation. Left and right Haar translations preserve the normalized compact measure. The spin and dual spin transformations are unitary on each degree-one coefficient block and hence on exterior powers. Their combined determinant preserves the oriented top. Therefore all these pullbacks extend as unitaries of their original auxiliary coefficient/Haar carriers, preserving the polynomial cores and parity.

The original \(e_i\) (input pullback) intertwines with \(R_D\), and \(p_o\) (old top and Haar) intertwines \(R_D\) with \(R_o\). The latter equality is the change of the old variables under their endpoint transformations, keeping the other groups in their correct carried and new roles. \(w_\sigma=\exp(s_\sigma)\) is invariant under the full endpoint action because the closed plaquette transforms at its base, the EHC keeps its contracted internal tensor, the determinant uses the oriented rotation, and prescribed world-frame sources mix coframes before their internal invariant contraction. Thus the exact relative arrow \(V_\sigma[h]=p_oM_{w_\sigma}M_h e_i\) obeys
\[
 R_o(g)V_\sigma[h]R_i(g)^{-1}=V_\sigma[R_D(g)h].                 \tag{1}
\]
This holds on all polynomial caps. The original bilinear cap pairing is itself invariant under simultaneous gauge pullback, so (1) is also a cap identity. \(K\) acts on a cap and \(D_K=K\Gamma\) on its independent dual test. Transport of (1) uses \(K R K^{-1}\) on vector caps and \(D_K R D_K^{-1}\) on dual caps. These two transported group operators agree when expressed on the corresponding reversed coefficient carrier because \(R\) commutes with \(\Gamma\). This preserves the established odd-cap sign in the unweighted dual law.

Write \(g^\dagger\gamma_A g=\sum_B\Lambda(g)_{AB}\gamma_B\). Then \(\Lambda\) is the real oriented vector rotation. All four temporal hopping blocks at the marked centre transform at their base \(b,r\) by \(\Lambda(g_{b,r})\), and the same is true of \(T_1^A\). With the inverse pullback, \(R_D(g)Y^A=\sum_B\Lambda(g_{b,r}^{-1})_{AB}Y^B\). The pair \(Y^A Y^B\) transforms with both tensor factors. \(Q_s=\sum_A Y^A Y^A\) is invariant. The retained unscaled \(m_a,m_c\) are invariant under the whole group: \(R_-\) and \(R_+\) each rotate at the same base, hence \(d=2 R_-\cdot R_+\) is invariant. \(V_a\) sums the four-component unbarred Euler at an old site, and \(V_c\) uses scalar phase weights on the new barred and unbarred blocks. These derivations commute separately with each original gauge action, so \(V_a d,V_c d\) are invariant. This argument uses the local gauge action, without promoting those endpoint Euler/phase derivations to physical constraints.

For an even gauge Lie algebra direction \(X\), let \(D^g\) be the generator of the inverse pullback on each indicated polynomial core. Differentiating (1) gives
\[
 D_o^g V_\sigma[h]-V_\sigma[h]D_i^g=V_\sigma[D_D^g h].         \tag{2}
\]
Directions at the discarded old node act only by the negative right term. Directions at the introduced new node act only by the left term. Directions at the carried node appear on both sides, with the endpoint actions on the appropriate connectors. For unit, forces and \(Q_s\), (2) gives the inherited old annihilation, new annihilation and carried-node intertwining. For a free mark the right side at the carried marked site is \(-\sum_B t(X)_{AB}V_\sigma[Y^B]\), where \(t=d\Lambda\). Thus a marked component supplies an equivariant arrow when its vector index is included. For example \(v\mapsto\sum_A v_A V_\sigma[Y^A]\) intertwines the vector action \(v\mapsto\Lambda(g_{b,r})v\) with the action on the arrow space. A single marked multiplication acting on an invariant matching vector therefore need not preserve invariance. Invariant \(Q_s\) commutes with these derivations. This distinction is already present on the polynomial relative module.

Each \(D^g\) is a combination of the actual simultaneous link/odd transformations. Its pairing is skew on this core by differentiating Haar/coefficient unitarity. As the derivative of an inverse-pullback representation it obeys the Lie bracket of the node group. This convention does not change the inherited negative bracket of the separate link fields \(D_\tau U=\tau U\) in GCR. Equations (1)–(2) add no graph annihilator: the independent right shared differential action stays present and the prior graded force, divergence and ordering contacts still apply. Only the complete simultaneous gauge variation kills \(s_\sigma\).

## 2. Independent two-step endpoints and their matched comparison loop

Let \(M_A=V_{1,\sigma}[1]V_{0,\sigma}[Y^A]\) and \(M_{AB}=V_{1,\sigma}[1]V_{0,\sigma}[Y^A Y^B]\) prior to the outside closure. Use the actual composition with independent external \((a,b,v_a)\) and \((c,d,v_c)\), internal \(v_b\) integrated jointly, and no \(b/c\) pair integration at the join. The output gauge group on \(c,d\) and the input gauge group on \(a,b\) are independent here. Applying (1) at both steps with the carried actions matched gives
\[
 R_{cd}(g_c,g_d)M_A R_{ab}(g_a,g_b)^{-1}
       =\sum_B \Lambda(g_{b,r}^{-1})_{AB}M_B .                 \tag{3}
\]
The same computation for \(M_{AB}\) has two factors of \(\Lambda(g_{b,r}^{-1})\). The mark at \(b,r\) lies at the input of the two-step arrow. At the first step it is carried, at the second it is discarded, so its covariance cannot be dropped by applying the scalar old Ward law to both steps. The unit/force words and the contraction \(M_Q\) are invariant in (3) under both independent groups.

Equation (3) proves \(\Pi_{cd}M_A=M_A\) and \(M_A\Pi_{ab}=0\), where each \(\Pi\) here denotes the already derived compact gauge projection on the indicated full carrier. For the second identity the vector average is zero. This also follows from the single original half-centre \(z=(-I_2,+I_2)\) at the marked site, since its vector image is \(-I_4\). The half-centre acts differently from the full centre \((-I_2,-I_2)\) used to prove exterior parity support. The outputs at \(c,d\) are fixed for all original node transformations. For a free pair only output fixation and incoming tensor covariance follow. Contracted \(M_Q\) has incoming fixation as well.

After actual periodic cut matching \(c=a,d=b,v_c=v_a\), the exterior/cap convention and outside \(K_0\) are those of ORIGINAL_COMPLEMENT_CONNECTOR_CONSTRUCTION §§1–2,5–6. There is one comparison gauge action \(\mathcal R_g=K_0 R_{ab}(g)K_0^{-1}\) on \(H_{\rm full}\). Set \(\alpha_g(X)=\mathcal R_g X\mathcal R_g^{-1}\). Equation (3) for \(C_A=K_0 M_A K_0^{-1}\) now becomes
\[
 \alpha_g(C_A)=\sum_B\Lambda(g_{b,r}^{-1})_{AB}C_B,\qquad
 \alpha_g(C_{AB})=\sum_{D,E}\Lambda(g_{b,r}^{-1})_{AD}
                         \Lambda(g_{b,r}^{-1})_{BE} C_{DE}.   \tag{4}
\]
All nine unit/force loops, \(C_Q\), and the full algebra identity are fixed. In particular with \(\Pi^K=K_0\Pi_{ab}K_0^{-1}\),
\[
 \Pi^K C_A=C_A,\qquad C_A\Pi^K=0,\qquad C_A C_B=0.             \tag{5}
\]
This uses the same projection only after actual closure. Equivalently \(\mathcal R_z C_B=C_B\), \(C_A\mathcal R_z=-C_A\) at the matched half-centre, so their product equals its negative. The original cap domains remain full and no gauge projection is substituted for a cut map.

## 3. Full original cap witnesses and the ordered test

Here the tests are independent full original input/output polynomials, before \(\Pi^K\) is used as any interpretation. The two-step cap evaluation for a single insertion \(h\) at step0 is the four-slice original full-top/Haar integral of \(e^{s_1+s_0}h\,GF\), by the accepted actual bounded-insertion map and off-shell composition. Use inherited full oriented slice tops \(\Theta_a,\Theta_b,\Theta_c,\Theta_d\). Moving whole 64-letter slice tops across other slice blocks of even degree below gives positive block signs. With \(F=\Theta_a\Theta_b\), \(G=\Theta_c\Theta_d\), the unit has numerator \(1\): each nonconstant weight term repeats an occupied letter, and each normalized Haar factor integrates \(1\). This is an open two-step cap. It does not identify the transfer with the full comparison identity. The transfer loop has \(\chi=0\) and original normalized trace \(1\), while \(\chi(I)=1\).

For a marked component \(A\), put \(B_{ij}=\bar\psi_{b,r,i}\psi_{a,r,j}\), and let \(H_{ij}\) be the uniquely signed complementary input monomial with \(B_{ij}H_{ij}=\Theta_a\Theta_b\). Set
\[
  F_A=\sum_{i,j=1}^4
        \overline{(\gamma_A v_a(r))_{ij}}H_{ij},
  \qquad G=\Theta_c\Theta_d .
\]
Both caps are actual polynomials in their own cut data. The only coframe term filling the two input holes for each \(H_{ij}\) is the original backward term \(-\bar\psi_b\gamma_Av_a\psi_a/4\). New terms repeat a letter of \(G\), the reverse backward term requires a missing old bar and marked \(b\) unbar, and the spatial term has no old unbar. Every positive exterior degree term in \(e^{s_1+s_0}\) is killed by full top saturation. Thus
\[
 \beta_{cd}(G,M_A F_A)
   =-\frac14\int\sum_{ij}|(\gamma_A v_a(r))_{ij}|^2
   =-1.                                                   \tag{6}
\]
The final sum is identically 4 because \(\gamma_A\) and the represented \(v_a\) are unitary. All Haar factors have mass one. This is an exact unnormalized cap, not the periodic state moment. Fixed-cap source numerator jets of (6) vanish throughout the germ, even though the operator jets need not.

A concrete independently ordered gauge/coframe test uses \(X=\gamma_3\gamma_0/2\) at \(b,r\). Its action has \(t(X)_{03}=-1\), obtained from \([\gamma_0,X]=-\gamma_3\), with the other entries in that row zero. Differentiating (3) and taking the corresponding term \(D_o^g\) on \(d,r\) (the matched point after closure) gives \(D_o^g M_0=0\) and \(M_0 D_i^g=-M_3\). For \(F_3,G\) in (6), the two orderings have caps \(0\) and \(+1\). The first identity uses independent output Gauss fixation. The second has the genuine input vector action and must be tested with the right operator order. It is a gauge/coframe derivative pair on the two-step polynomial cut, not a physical coframe-pair dictionary. For an open one-step arrow, (2) supplies the independently typed carried difference with both terms.

For the independent pair witness choose the two upper barred \(b_i=\bar\psi_{b,r,Li}\) and two lower unbarred \(a_j=\psi_{a,r,Rj}\), \(i,j=1,2\), of the original Weyl convention in ORIGINAL_TEMPORAL_Q00_SOURCE_LIFT_CONSTRUCTION §2. Put \(P=b_1 b_2 a_1 a_2\). Choose \(H\) to be the signed input complement with \(P H=\Theta_a\Theta_b\) and use the same output \(G=\Theta_c\Theta_d\). This \(H\) is gauge-invariant: every surviving complete spinor or dual chiral block at each input site transforms by a determinant-one block, and there is no compact coefficient. Primary old-backward \(Y^A\) terms must fill both \(a\) holes, so only their product contributes. On these slots the relevant coefficient matrix is \(q_A U\), \(U=(v_a(r))_R\), with \(q_A=(-i\tau_1,-i\tau_2,-i\tau_3,I)\) in the inherited order. The coefficient of \(P\) in \((\sum_{ij}b_i(q_AU)_{ij}a_j)^2\) is \(-2\det(q_AU)\): the diagonal product passes the first \(a\) through the second \(b\) once, the off-diagonal product has the additional unbarred interchange, and the two orders of each even product agree. Since both determinants are 1, the quarter factors give
\[
 \beta_{cd}(G,M_{AA}H)=-\frac18,\qquad
 \beta_{cd}(G,M_Q H)=-\frac12 .                             \tag{7}
\]
Again, full top saturation eliminates every positive-degree weight term before normalized Haar gives 1. No compact point test, body inversion or sign adjustment enters (6)–(7).

Equations (5) and (7) yield the exact failure \(C_A C_A\ne C_{AA}\) for every \(A\) and \(\sum_A C_A C_A\ne C_Q\). Even the alternative comparison prescription \(\sum_A C_A^\dagger C_A=C_Q\) fails on the invariant test \(K_0 H\), because all \(C_A K_0 H=0\) by (5). The nonzero source cap (7) transports by the unique dual, with no added state. These are failures of loop-product identifications. They use the consecutive two full-period marked loops on one side and the marked pair inserted within a single original step kernel in the other. The exact differentiable source identity remains \(\partial_\alpha C_{\rm unit}=C_Q\), \(\partial_{\alpha\beta}C_{\rm unit}=\partial_\beta C_Q\), with no identification of its right side with loop multiplication.

## 4. Invariant comparison algebra, positive state and GNS generator

The frozen \(F\) is the span of the full exterior monomial roster times all quaternion monomials on the 112 SU(2) factors up to total degree 512, with actual Gram radical removed. The original compact endpoint map left- and right-multiplies each SU(2) quaternion by fixed unit quaternions. This is real linear in its four coordinates and preserves its sphere. Pullback therefore preserves total degree and the actual polynomial relations. The spinor and dual pullbacks act linearly within each odd block, preserving the full exterior roster. Consequently \(R_g\) and its inverse preserve this full span; no claim about the invariance of each element in the selected fixed independent subfamily is needed. \(K_0\) and its inverse preserve the bounded roster too. Their compact actions are the fixed real linear quaternion inversion, Pin conjugation and relabeling, and their exterior actions are the fixed complement, reversal and linear exchange of the carrying connector. Thus \(\mathcal R_g F=F\) and \(\mathcal R_g E=E\) for \(E=F\cap\ker(\Gamma-I)\) by parity intertwining. In the actual synthesis \(T:\mathbb C^n\to F\), its action matrix \(W=T^{-1}\mathcal R_gT\) satisfies \(W^\dagger H W=H\), \(H=T^\dagger T\).

Every frozen polynomial family, genuine source derivative and actual coefficient adjoint transforms by the fixed scalar, vector or tensor action (4), or its adjoint. Since \(\mathcal R_g\) is source-independent, real-source differentiation commutes with its adjoint action. Since the operator polynomials agree on an open real source plane, comparing coefficients extends (4) to each parameter-coefficient generator. Therefore \(\alpha_g\) preserves the exact fixed \(A_*\) and its existing unit and involution. The inverse group element proves equality of the image. Support on the fixed reducing \(E\) and stability of \(F^\perp\) leave the original scalar character \(\chi\) invariant. In particular, applying finite trace cyclicity to each \(E\)-block gives
\[
 \Phi_\sigma(\alpha_g(X))=\Phi_\sigma(X),\qquad
 \tau_0(\alpha_g(X))=\tau_0(X),
 \quad
 \Phi_\sigma(X)= Z_\sigma^{-1}\operatorname{Tr}_E(X|E)
 +(1-\dim E/Z_\sigma)\chi(X).
\]
Here \(\tau_0=\operatorname{Tr}_E+\chi\), with \(Z_\sigma\), original domain and strict margins exactly those of the accepted comparison state. No rank claim is needed. The trace of each vector row vanishes and invariance gives \(\Phi_\sigma(C_{AB})=\delta_{AB}\Phi_\sigma(C_Q)/4\), by the invariant bilinear tensors of the vector action. These statements follow for the corresponding first and mixed source-labelled jets as well.

On the fixed accepted \(L^2(A_*,\tau_0)\), put \(\mathscr U_g X=\alpha_g(X)\) and retain \(\pi(A)X=AX\). This is unitary by invariance of \(\tau_0\), with \(\mathscr U_g\pi(A)\mathscr U_g^{-1}=\pi(\alpha_g(A))\). The accepted central density \(h_\sigma\) is fixed by \(\alpha_g\) by uniqueness of the trace dual of the invariant \(\Phi_\sigma\). Its positive square root \(\Omega_\sigma\) is fixed by functional calculus. The group action is smooth on \(A_*\) since \(\mathcal R_g|F\) acts on finite-degree quaternion/exterior coefficients with smooth group entries. Define
\[
 \delta_X=\left.\frac{d}{dt}\alpha_{\exp(tX)}\right|_{0},
 \qquad Q_X=-i\delta_X .
\]
The derivative is a star derivation and skew-adjoint on this fixed finite space by unitarity. Thus \(Q_X\) is self-adjoint there, \(\mathscr U_{\exp(tX)}=e^{itQ_X}\), \(Q_X\Omega_\sigma=0\), and
\[
 [Q_X,\pi(A)]=-i\pi(\delta_X A),\qquad
 [Q_X,\pi(C_A)]=i\sum_B t(X)_{AB}\pi(C_B),\qquad
 [Q_X,\pi(I)]=0.                                         \tag{8}
\]
The generator in (8) is a derivation on the comparison GNS space. It is not the left action of an assumed physical charge. From (6) and faithfulness,
\(\|\pi(C_A)\Omega_\sigma\|^2=\Phi_\sigma(C_A^\dagger C_A)>0\).
For the specified \(X\), \([Q_X,\pi(C_0)]\Omega_\sigma=-i\pi(C_3)\Omega_\sigma\ne0\). On the unit and transfer loop the infinitesimal commutator vanishes by their scalar transformation. This is the fixed positive-state implementation of the original covariance. It does not assign physical meaning to a comparison product or introduce a cap-to-GNS vector map.

In particular invariance of the cyclic vector is not support on the original coefficient singlets. Let \(S=\sum_A C_A^\dagger C_A\). It is an invariant positive comparison operator by orthogonality of the vector action. It is nonzero by (6), entirely supported on \((\Pi^K)^\perp\) by (5), and has \(\Phi_\sigma(S)>0\) by faithfulness. Compressing to the original coefficient singlets would give zero for this comparison expectation. Likewise \(\pi(C_A)\pi(C_B)=0\) but \(\pi(C_{AA})\ne0\). Faithfulness reflects the R3 distinction between a state-vector property and an operator relation here, with the accepted comparison vector null and representation kernel both zero. It grants no general statement about R3's physical word or external cap nulls.

## 5. Source jets and remaining physical binding

The unit, both coframe beta placements, contracted ordered pair, and both interface placements retain the accepted full source contacts. Explicitly \(s_\alpha=Q_s,\ s_\beta=E_\beta+2\alpha Y\cdot T_1,\ s_{\alpha\beta}=2Y\cdot T_1\). For an inserted \(h\), the first vertex is \(s_jh+h_j\), and the mixed vertex is \((s_\alpha s_\beta+s_{\alpha\beta})h+s_\alpha h_\beta+s_\beta h_\alpha+h_{\alpha\beta}\). For the pair \(h_\beta=T_1^A Y^B+Y^A T_1^B\). In a sewn word \(A B\) retain \(A_{\alpha\beta} B+A_\alpha B_\beta+A_\beta B_\alpha+A B_{\alpha\beta}\) before inactive profiles are specialized. Fixed gauge action, \(K\), and \(D_K\) have no source derivative. Their covariance thus extends through mixed operator/cap contacts. For a moving row \(\Phi_\sigma(A_\sigma)\) the mixed jet has \(\Phi_{\alpha\beta}(A)+\Phi_\alpha(A_\beta)+\Phi_\beta(A_\alpha)+\Phi(A_{\alpha\beta})\), including all derivatives of \(1/Z_\sigma\) and the scalar weight. The original unnormalized cap tests above keep their own status. They are not claims about the mixed normalized value of an unlisted moment.

The accepted reverse for forward even insertions is the actual reflected arrow with \(V^\theta K_+=K_-V^\dagger_{\rm coeff}\). Endpoint gauge transformations are transported along the same actual maps. The reflected construction still carries the separately inverted anchors, reversed arrow and mark order, transported backward curvature, positive alpha and negative beta at the reflected site, nontrivial \(D_{\rm ref,0}=\exp(\Delta_0)\), and its own reflected denominator. The mixed weight retains \(D_{{\rm ref},j}=D_{\rm ref}\Delta_j\), \(D_{{\rm ref},\alpha\beta}=D_{\rm ref}(\Delta_{\alpha\beta}+\Delta_\alpha\Delta_\beta)\) and all crossed placements. Comparison \(^{\dagger}\) is the bounded coefficient/Haar adjoint on its own carrier. On the polynomial differential cores the distinct bilinear transpose and adjoint domains retain the accepted cut definitions. No physical dagger or unknown map is assigned any of these identities by renaming.

A source-compatible continuation keeps the full relative arrow and the shared right derivative, treats a free mark as an associated vector at the open cut, and retains the independently typed two-mark same-kernel tensor before contraction. Compact gauge covariance and a faithful comparison GNS action give controls on that continuation. The exact obstruction (5), (7) rules out factoring the required same-kernel tensor by the product of two fully sewn marked comparison loops, including on the positive comparison space. Physical \(E^A\), its ordered product and its insertion map \(J_\sigma\) still require an independent construction and an all-cap equality against \(V_\sigma[Y^A Y^B]\), with \(J_\sigma[1]\) the original transfer and the separately typed physical forward/reverse cut maps and duals. Original coherent/Bopp scalar and bilinear corrections and the full reverse-order trace dual remain required tests on their stated carrier. Neither loop multiplication, selected Hermitian combinations of loops, nor projection of the original caps into \(\Pi^K H_{\rm full}\) supplies these physical maps. R3's actual generated contexts, common physical domain, \(*\)-closed relations, all-cap positive completion and same original cyclic seam remain open. No completed physical identity, universal failure, B3/N4, dynamics, calibration, controlled limits, formal qualification or publication result is claimed. Page0 remains separately frozen OPEN, unreviewed and NOT RUN.

## 6. Separate comparison-state continuation with gauge-invariant finite density

At the lead's request, test the alternative finite density using the established gauge projection. This is a new comparison candidate alongside the accepted \(\Phi_\sigma\), whose definition and use in §4 are kept. The reducing space \(E\) is invariant under the full unitary group action, so \(P_0=P_E\Pi^K\) is an orthogonal projection on \(E\) and commutes with the gauge representation. Its fixed finite rank \(d_0\) satisfies \(d_0\leq \dim E<Z_\sigma\). On the existing ambient \(B(F)\oplus\mathbb C\) consider
\[
 \Phi^0_\sigma(X)=Z_\sigma^{-1}\operatorname{Tr}_F(P_0 X_F)
                  +(1-d_0/Z_\sigma)\chi(X).
\]
The inherited whole-carrier order and both positive coefficients give a normalized positive analytic family on the same \(A_*\). The finite trace density has gauge-invariant range. The scalar character is the existing scalar coordinate; assigning it an extension with original singlet support requires a separate argument, and no such extension is used here. There is no assumption that \(P_0\) itself belongs to \(A_*\).

For every forward finite row \(G\), including pairs and derivatives, (3) gives \(\Pi^K G=G\) and accepted comparison support gives \(P_E G=G\). Thus \(P_0G=G\). For the actual adjoint row \(G^\dagger\), one instead has \(G^\dagger P_0=G^\dagger\). Finite trace cyclicity proves that this alternative reproduces every frozen row and its prescribed adjoint value, with the original scalar coordinate and SAME \(Z_\sigma\). The invariance of \(P_0\) implies \(\alpha_g\)-invariance, and the exact real-germ equality on the frozen row families implies all their normalized first/mixed contacts. This leaves the weights of comparison products unspecified by the original assigned rows. They do change for this candidate. For each \(A\),
\[
 \Phi^0_\sigma(C_A^\dagger C_A)=0,\qquad
 \Phi^0_\sigma(C_A C_A^\dagger)>0 .
\]
The first follows from the incoming constraint in (5), the second from the nonzero output supported in \(P_0\), and the comparison adjoint reverses those supports. Hence \(\Phi^0_\sigma\) is nonfaithful and nontracial on \(A_*\). Its GNS vector is killed by the left action of \(C_A\), while \(\pi^0_\sigma(C_A)\pi^0_\sigma(C_A^\dagger)\Omega^0_\sigma\) is nonzero because \(\Phi^0_\sigma((C_A C_A^\dagger)^2)>0\). This exhibits the difference between a vector-null left ideal and the operator representation kernel without reducing the original cap space. The pair obstruction persists in this alternative representation: left multiplication still gives \(\pi^0_\sigma(C_A)\pi^0_\sigma(C_B)=0\), and \(C_Q\) is nonzero by (7), with both sides supported in \(P_0\), hence \(\Phi^0_\sigma(C_Q^\dagger C_Q)>0\). This alternative comparison family has its own review boundary. In particular the known frozen rows alone cannot establish the physical state on arbitrary generated contexts.

## 7. Custody

FIRST action from the assigned checkout was the prescribed `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-quantum-prepost-constraint-construction-r1.json`, returning exit 0, fresh=true, changed=[]. Read the ROOT commission, complete packet in bounded carrying ranges, AGENTS, full CLAUDE/WAVE/CODEX_CONTINUITY, current notebook and Phase6a L1 ownership. Carrying sources include the complete original boundary/gauge result, accepted R2 reports and acceptance, graded relation, actual ordered-cut construction and both ACTUAL reviews/acceptance, accepted comparison construction and both ACTUAL reviews/acceptance, the frozen comparison roster and complement connector sections carrying its unitary transport and actual closure, temporal source-lift block and coherent/Bopp and R3 physical-scope passages. Scientific reasoning is manual from canonical sources. No fresh full historical notebook, primary-PDF, archive-wide or remote audit is asserted. The memory lookup furnished no mathematical premise.

Actual work consists of the continuity checker, ordinary pwd/ls/git status --short orientation, cat/sed/rg/tail/wc/shasum/iconv reads and measurements, and a quoted here-document and patch editing this private report only. Signs and exact cap numbers were derived by hand. No science program/import/test/CAS/Haar/exterior/matrix/SDP/rank helper, evaluator/network/native/Lean/build/slot/controller/process/harness/dependency action, Git mutation, repo/notebook/roadmap/queue write or subagent occurred. Final SAME and the exact report bytes/SHA accompany delivery separately. This is contributor evidence for the principal author and lead, with actual independent review reserved for the distinct commissioned reviewers.
