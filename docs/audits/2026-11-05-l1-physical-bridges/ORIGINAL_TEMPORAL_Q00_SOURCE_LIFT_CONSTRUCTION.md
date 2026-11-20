# The temporal quartet on the original cut: endpoint obstruction and two retained forces

**L1-PHYS-Q00-JET-01. Manual construction submitted for independent actual review.** At the literal temporal source, both specified kinetic constraints lose their regular polynomial lifts on the respective endpoint phase algebras. Their differentiated quantum null identities fail on one explicit original compact/Berezin input. The outgoing and incoming first coefficients are \(i/4,-1/4\). At the spatial curvature fibre below their mixed coefficients are \(-g_2/2,-i g_2/2\). Retaining two source-independent functions of the actual matching variables restores these particular identities as kernel insertions. The physical transfer and coincident metric map in kinetic (30)–(31) remain open.

## 1. Original source and its split

The source pin is 2678f1cd280a6398687cb694b5b5fa279260b094. Parent publicationROOT01a13f67/L1-physical-observable-boundary, task l1-original-temporal-q00-map-r1, notebook writer Executor01a1ac65. All calculations below are hand derivations. The original graded relation (1)–(14),(19)–(28), one-slice source kernel (1)–(8),(17)–(22), kinetic normalization §§4–10, EHC reflection §§2–8 and microscopic coherent bridge §§2–7 supply the conventions. The independent reviews of the exact 10,498-byte R2 brief authorized the attempt. They did not certify its results.

Keep the three independent odd slices \(a,b,c\), with 64 generators and 24 spatial Spin(4) links on each slice, and two independent eight-link temporal collections \(v_a,v_b\). The two cut variables are \(B_-=(X_a,X_b,v_a), B_+=(X_b,X_c,v_b)\). The shared \(b\) appears once in their matching algebra. All links remain variables prior to a stated integral or output test. Put \(r=(b,\mathbf0)\). With fields at the indicated spatial origin, the original temporal coframe is \(R=R_-+R_+\), where
\[
 4R_-^A=-\bar\psi_b\gamma_A v_a\psi_a+\bar\psi_a v_a^\dagger\gamma_A\psi_b,\qquad
 4R_+^A=\bar\psi_b\gamma_A v_b^\dagger\psi_c-\bar\psi_c v_b\gamma_A\psi_b .
\]
Write \(T_i=T_{r,i}\) for the same quarter coframe on a spatial direction, including the separately anchored backward terms. Dots sum over the four original internal indices. At \(r\), \(A=1+\beta E_{01}\), \(J_{00}=\alpha\); all other frames are identity and other sources vanish. \(Y_0=R+\beta T_1,\ Y_i=T_i\). The shear has determinant one and time column \(A_{\mu0}=\delta_{\mu0}\). It leaves the determinant density unchanged. A temporal coframe in either of the two EHC slots requires that slot to have world row 0, leaving both curvature indices spatial. In the accepted one-slice split this gives \(B_{\rm E,time}=0\) exactly, including at nonzero \(\beta\). The source matrix \(A^t{\bf J}A\) has \(H_{00}=\alpha,\ H_{01}=H_{10}=\alpha\beta,\ H_{11}=\alpha\beta^2\). This is a diagonal literal source, with the usual \(J_{\mu\nu}/2\) in the symmetric matrix for once-counted off-diagonal coordinates.

Let \(s_0^\pm\) be the full original base pieces of one-slice (6), summed over **all eight** middle centres. Set
\[
 E_\beta={g_2\over4}\sum_{k,l,\mu,\nu,C,D}\epsilon^{kl\mu\nu}F_{r,kl}^{CD}
 [\,\delta_{\mu0}T_1^C T_\nu^D+\delta_{\nu0}T_\mu^C T_1^D\,],
 \qquad T_0=R .
\]
Every surviving term uses only spatial curvature and spatial coframes at \(b\), since an epsilon with two zero indices vanishes. \(F\) is the trace of \(U_{r,l}^\dagger U_{r+l,k}^\dagger U_{r+k,l}U_{r,k}\gamma_C\gamma_D\gamma_5\). The coframe slots and opposite plaquette orientations are both summed. With the incoming piece convention of one-slice (6), the entire source plane on this cut is therefore
\[
\begin{split}
 s^-&=s^-_0+\alpha R_-^2+2\alpha\beta R_-\cdot T_1,\\
 s^+&=s^+_0+\beta E_\beta+\alpha R_+^2+2\alpha\beta R_+\cdot T_1
                           +\alpha\beta^2 T_1^2,\\
 D&=\alpha d,\qquad d=2R_-\cdot R_+,\qquad s=s^-+s^++D .
\end{split} \tag{1}
\]
The EHC term linear in \(R\) has no new \(\beta\) dependence because an attempted second row 0 repeats an index. There is no second-order shear term in the EHC action for the same reason. At the origin the actual first and mixed insertions are \(s_\alpha=R^2,\ s_\beta=E_\beta,\ s_{\alpha\beta}=2R\cdot T_1\); \(D_\beta=D_{\alpha\beta}=0\). In particular the kernel mixed vertex has \(R^2 E_\beta+2R\cdot T_1\).

## 2. The full polynomial image test

Use parity-matched independent momenta over the actual compact polynomial and exterior coordinate algebras, with left odd derivatives and invariant frames on compact links. Write \(k=p_b\) for the free shared covector (denoted \(\kappa\) in graded (14)). In \({\cal C}={\cal A}(X_a,X_b,X_c,v_a,v_b)[k]\), the complete incoming map fixes incoming coordinates and sends \(p_a,p_b,p_{v_a}\) to \(-\partial_a s,k,-\partial_{v_a}s\). The outgoing map fixes outgoing coordinates and sends \(P_b,P_c,P_{v_b}\) to \(k+\partial_b s,\partial_c s,\partial_{v_b}s\). All derivatives here stand for evaluations of \(ds\) in the declared frames, including fields of either parity and spatial-link directions. At base, \(p_a\) has old odd forces \(-\partial_{a,\mathrm{odd}}s^-_0\) and identically zero old *spatial* link forces. The middle-base action contains no old spatial link. The old temporal-link force is \(-\partial_{v_a}s^-_0\). This lists every incoming generator. Its image is exactly \({\cal A}(B_-)[k]\), since all its independent coefficient variables and \(k\) are themselves images.

At the output all new odd and spatial forces are \(\partial_c s^+_0\); in particular the new spatial forces include the forward closed-plaquette derivative. All new temporal-anchor forces are \(\partial_{v_b}s^+_0\), including coframe and plaquette terms. Shared odd and spatial-link momenta go to \(k+\partial_b(s^-_0+s^+_0)\), including both shared force pieces. Consequently the output image is precisely the subalgebra generated by \({\cal A}(B_+)\) and those shifted shared momenta. This statement permits arbitrary finite polynomials, including all graded products and compact polynomial identities. The translation in the freely adjoined supercoordinates \(k\) is invertible over \({\cal A}(D_{\rm match})\). Specializing \(k=-\partial_b s_0\) sends this entire image to \({\cal A}(B_+)\). This test is applied only to a proposed equality of base pullbacks. The actual relation retains the free shared covector.

Let \(V_c=i\sum_i(\psi_{ci}\partial^L_{\psi_{ci}}-\bar\psi_{ci}\partial^L_{\bar\psi_{ci}})\) and \(V_a=\sum_i\psi_{ai}\partial^L_{\psi_{ai}}\), each supported at the stated origin, with four components. The former is the local variation of the actual phase current, the latter an even number-of-unbarred-occurrences derivation, invariant under a change of spin frame there. Neither imposes a physical zero charge. The fixed base constraints
\[
 p_0^+=P(V_c)-V_c s_0^+,\qquad p_0^-=p(V_a)+V_a s_0^-
\]
have vanishing base pullbacks. Their \(\alpha\)-pullback derivatives at fixed symbols are \(+V_cR^2,-V_a R^2\), respectively. A regular first lift demands the opposite values as \(\phi_{+,0}(p_\alpha^+)\), \(\phi_{-,0}(p_\alpha^-)\).

Here is the obstructing coefficient on the unspecialized source graph. Retain the upper two barred components \(b_1,b_2\) at \(r\), the first lower unbarred component \(a_1\) at the old site and the second lower unbarred component \(c_2\) at the new site. At the output anchor \(v_b=1\), leave \(U=(v_a)_R\in SU(2)\) in the old lower block arbitrary. The upper-right blocks of the four Euclidean \(\gamma_A\)'s in the original ordered internal convention are \(q_A=(-i\tau_1,-i\tau_2,-i\tau_3,I)\); lower-left blocks are \(q_A^\dagger\). On this restriction the two columns multiplying the old and new spinors in \(R_-,R_+\) are \(q_A U e_1,q_A e_2\), with prefactors \(-1/4,+1/4\). This follows directly from the FIRST terms in their displayed formulas. There is no old adjoint link in this hopping word. The two squares on a single anchor repeat \(a_1\) or \(c_2\). Each cross product has one exchange of the first unbar with the second bar; the other ordering gives the same product of even coframes. Thus
\[
 [b_1 b_2 a_1 c_2]R^2
 ={2\over16}\sum_A\det(q_AUe_1,q_Ae_2)
 ={1\over8}\sum_A\det(q_A)U_{11}={U_{11}\over2}. \tag{2}
\]
All four determinants equal one (\(\det\tau_i=-1\)). This extends the accepted identity-link coefficient to the actual old-link polynomial. Setting the links to identity now gives the two demanded coefficients \(-i/2,+1/2\). For the output image, specialize the shared momenta as above, then read the coefficient containing the unrepresented \(a_1\); every image has coefficient zero there. For the incoming image hold \(k\) free independently of the new generators (or evaluate at \(k=0\)); every image then lacks \(c_2\). The exterior generators on distinct slices are independent. Hence **neither first equation has a solution in the full regular endpoint phase algebra**. The isolated \(\beta\) equation does lift here, since \(V_c E_\beta=V_a E_\beta=0\). A joint regular lift requires both first equations and
\(\phi_0 p_{\alpha\beta}+\phi_\alpha p_\beta+\phi_\beta p_\alpha+\phi_{\alpha\beta}p_0=0\), so it already fails at order \(\alpha\).

There is also a precise module consequence on the one-parameter dual-number restriction. Over \(R_\epsilon=\mathbb C[\epsilon]/(\epsilon^2)\), take \(M_\pm=\operatorname{im}\phi_{\pm,\epsilon}\) *inside* \({\cal C}\otimes R_\epsilon\). Then \(y_\pm=\phi_{\pm,\epsilon}(p_0^\pm)=\epsilon h_\pm\), \(h_+=V_cR^2,\ h_-=-V_aR^2\). Equation (2) and the image tests show \(h_\pm\notin\operatorname{im}\phi_{\pm,0}\). Hence \(\epsilon y_\pm=0\) but \(y_\pm\notin\epsilon M_\pm\): multiplying an arbitrary image by \(\epsilon\) retains exactly \(\epsilon\) times its base image. For an \(R_\epsilon\)-flat module tensoring \((\epsilon)\hookrightarrow R_\epsilon\) with it is injective, which says \(M/\epsilon M\to M,\ [x]\mapsto\epsilon x\) is injective. The classes \([y_\pm]\) violate that condition. This proves nonflatness of these **projected image modules over the stated dual numbers**. The monic full matching graph is still free over the same base; no physical smoothness, failure in every direction or universal quantization conclusion follows.

## 3. Actual operators and their source derivatives

For a matching polynomial \(h\) put \({\cal V}_s[h]F=\int dH_a\,I_a[e^s hF]\), where \(dH_a\) integrates the old spatial and old temporal links, all normalized, and \(I_a\) takes the 64-generator old top. \(L_s={\cal V}_s[1]\) acts on original cut polynomials (also on the stated compact \(C^2\) coefficient domain). \(V_c\) acts on new variables only; \(V_c L_s={\cal V}_s[V_c s]\). For every monomial surviving the old integral, all four selected unbarred old components occur once. Thus \(I_a(V_a G)=4I_a(G)\), i.e. \({\rm div}_{\rm Ber}V_a=-4\). Applying this to \(e^sF\) gives \(L_s(V_a-4)=-{\cal V}_s[V_a s]\). There is no odd sign in this product rule. Define
\[
 C_+=V_c-M_{V_c s^+},\qquad C_-=V_a-4+M_{V_a s^-},\qquad
 m_c=2R_-\cdot V_c R_+,\quad m_a=2(V_aR_-)\cdot R_+ .
\]
Here \(M\) means exterior multiplication at the named endpoint. More explicitly \(4V_c R_+^A=i(\bar\psi_b\gamma_A v_b^\dagger\psi_c+\bar\psi_c v_b\gamma_A\psi_b)\), and \(4V_aR_-^A=-\bar\psi_b\gamma_A v_a\psi_a\). Derivatives on the opposite temporal half vanish. The exact two operator identities on this plane are
\[
 C_+L_s=\alpha{\cal V}_s[m_c],\qquad
 L_s C_-=-\alpha{\cal V}_s[m_a]. \tag{3}
\]
The source sensitivity lies in the original kernel as well as the endpoint constraints. For clarity at zero put \(u=R^2,\ e=E_\beta,\ v=2R\cdot T_1\); \(L_j={\cal V}_0[s_j]\), \(L_{\alpha\beta}={\cal V}_0[ue+v]\). From (1)
\[
\begin{array}{c|ccc}
  &\partial_\alpha&\partial_\beta&\partial_{\alpha\beta}\\ \hline
 C_+&-M_{V_c R_+^2}&0&-2M_{(V_cR_+)\cdot T_1}\\
 C_-&+M_{V_a R_-^2}&0&+2M_{(V_aR_-)\cdot T_1}.
\end{array}
\]
With undifferentiated operators henceforth at zero, the base products \(C_+L,LC_-\) vanish. For \(j=\alpha,\beta\),
\[
 C_{+,j}L+C_+L_j=\delta_{j\alpha}{\cal V}_0[m_c],\qquad
 L_j C_-+L C_{-,j}=-\delta_{j\alpha}{\cal V}_0[m_a].
\]
The mixed identities, including derivatives of the moving endpoints, are
\[
\begin{split}
 C_{+,\alpha\beta}L+C_{+,\alpha}L_\beta+C_{+,\beta}L_\alpha+C_+L_{\alpha\beta}
 &= {\cal V}_0[e m_c],\\
 L_{\alpha\beta} C_-+L_\alpha C_{-,\beta}+L_\beta C_{-,\alpha}+L C_{-,\alpha\beta}
 &=-{\cal V}_0[e m_a]. \tag{4}
\end{split}
\]
These equalities follow by ordinary even differentiation of (3). At the integrand level differentiating an insertion \(h_s\) inserts \(s_jh+h_j\) and \((s_\alpha s_\beta+s_{\alpha\beta})h+s_\alpha h_\beta+s_\beta h_\alpha+h_{\alpha\beta}\). This gives the right side of (4) with \(h_s=\alpha m\), without dropping the \(v\) term on the left. When \(F=F_s\) moves, the four mixed terms of the product with \(F_s\) must be added, in particular the first residual acting on \(F_\beta\).

## 4. One input and two open readouts

Take the signed 63-generator ordered complement \(\eta_a\) specified by \(\eta_a a_1=\Theta_a\), the accepted old top. Use the actual odd input \(F(B_-)=\eta_a\overline{U_{11}}\), independent of the shared variables. The complex-conjugate matrix entry is in the compact polynomial algebra. At the output read the coefficient \(b_1b_2c_2\), in precisely this order, with \(v_b=1\). The insertion is even so can follow \(\eta_a\); moving \(a_1\) past the two bars costs positive sign. Equivalently \(I_a[\eta_a b_1b_2a_1c_2]=b_1b_2c_2\). Because \(63+4=64+3\), only the unit term of \(e^{s_0}\) can contribute to this readout. There is no pure-link term in the original action, whose terms have odd-field degrees 4 or 8. Any further old component repeats the complement, and any extra shared/new component vanishes in this coefficient. Shared coordinates are counted once, not separately on input and output. Equation (2) supplies \(iU_{11}/2\) in \(m_c\), \(U_{11}/2\) in \(m_a\). Haar invariance under row exchange and the unit norm of the first column give \(\int |U_{11}|^2=\int |U_{21}|^2=1/2\). The other chirality of that anchor, other old temporal anchors and all old spatial links integrate the unit with mass one. The first residuals of (3) therefore read **\(i/4,-1/4\)**, at arbitrary \(g_1,g_2\), even \(g_2=0\).

For the mixed readout keep the same input and \(v_b=1\). At the shared slice choose \(U_{r+\hat1,1}=-I_4,\ U_{r+\hat2,2}=-I_4,\ U_{r+\hat1,3}=H=\operatorname{diag}(i\tau_3,I_2)\); all other shared spatial links are identity. New spatial links may be identity. In the actual \(D^\dagger C^\dagger BA\) order \(H_{13}=I^\dagger I^\dagger H I=H,\ H_{12}=I\), since the three exceptional anchors are distinct on the side-two torus. For \(E_\beta\) only the row-0 coframe is replaced; its companion row \(j\) is spatial. For \(j=1\) the two identical \(T_1\) rows cancel in the internally alternating contraction. For \(j=3\) the complementary \(12\) plane has zero antisymmetric curvature. Only \(j=2\) remains. In the full EHC sum \(\epsilon^{kl\mu\nu}Y_\mu^C Y_\nu^D\) is alternating in \(C,D\) by even commutation. It selects
\(F_{CD}(H)=\operatorname{Tr}(H\gamma_{[C}\gamma_{D]}\gamma_5)\), even if the raw diagonal trace is nonzero. For Spin(4), inverse orientation changes the sign of this antisymmetric curvature: each chiral Clifford block is traceless and \(H_\chi+H_\chi^\dagger\) is scalar. Reversing \(13\) thus changes both curvature and epsilon signs; exchanging \(02\) changes both the internal contraction and epsilon signs. The four surviving ordered placements give
\[
 E_\beta=g_2\,\epsilon^{1302}\sum_{CD}F_{CD}(H)\, T_1^C T_2^D
\]
at this fibre, for this shear. \(\epsilon^{1302}=-1\).

Read the additional four letters \(d_1d_2uv\), the two lower barred components at \(r\) and the first and second upper unbarred components at \(r+\hat1,r+\hat2\), respectively. These neighbor sites are distinct. Each of the two selected spatial hopping coefficients in \(T_1,T_2\) is \(+1/2\): the two coincident neighbor *sites* contribute through different links, with \(U_+^\dagger-U_-=I-(-I)=2I\), divided by four. Hoppings with a neighbor bar or an unbar at the middle cannot yield this word. The lower-left gamma block \(l_C=q_C^\dagger=(i\tau_1,i\tau_2,i\tau_3,I)\) now acts. To see the curvature signs directly, \(\gamma_C\gamma_D\gamma_5\) for \(C\ne D\) has diagonal blocks \(q_C q_D^\dagger,-q_C^\dagger q_D\) in the convention \(\gamma_5=\operatorname{diag}(I,-I)\). Only \(01,23\) and reversals have an upper block along \(\tau_3\); the lower block is traceless. The upper blocks are \(i\tau_3\) for \(01\), \(-i\tau_3\) for \(23\); tracing against \(i\tau_3\) yields \(F_{01}=-2,F_{23}=2\). Write \(D_{CD}=\det(l_C e_1,l_D e_2)\). The relevant column pairs give
\(D_{01}=-i,\ D_{10}=+i,\ D_{23}=+i,\ D_{32}=-i\). For instance \(l_0e_1=(0,i)^t,\ l_1e_2=(1,0)^t,\ l_2 e_1=(i,0)^t,\ l_3 e_2=(0,1)^t\). Thus
\[
 [d_1d_2uv]\sum F_{CD}T_1^C T_2^D
 =-\tfrac14\{(-2i)F_{01}+(2i)F_{23}\}=-2i .
\]
The minus exchanges \(u\) with the second bar. Multiplication by the world epsilon and \(g_2\) gives \(+2i g_2\) in \(E_\beta\).

The ordered output is \((b_1 b_2 c_2)(d_1d_2uv)\). The old top needs exactly \(a_1\); \(e\) depends only on \(b\), and only \(m\) can provide \(c_2\). For these choices the old and new unbars require the two upper bars at \(r\), since the link blocks preserve chirality and gamma switches it. Consequently the temporal factor cannot use either lower bar or neighbor, and the spatial factor must supply exactly \(d_1 d_2uv\). The shear is supported only at \(r\). This excludes competing allocations of letters to factors and any other action centre in \(s_\beta\). The complete degree equality \(63+4+4=64+7\) excludes every positive-degree base action term; extra old, shared or new letters cannot contract down in the exterior algebra. The two even factors can be ordered with \(m\) first, so the old-top orientation is the same as at first order. The compact factor is again precisely \(|U_{11}|^2\) with all other integrated masses one. The mixed readouts of (4) are hence **\((i/4)(2i g_2)=-g_2/2\)** and **\((-1/4)(2i g_2)=-i g_2/2\)**. At identity spatial links every antisymmetric curvature vanishes and this mixed readout is zero. At \(g_2=0\), \(E_\beta=0\) identically; the first obstruction and first operator coefficients still hold.

In each nonzero case the selected compact output coefficient is continuous (a polynomial after the original compact integration). Nonzero at the displayed point implies nonzero on a relatively open set of positive product Haar measure; the coefficient itself can be paired with its conjugate in the output coefficient pairing. Thus the output is also nonzero in the auxiliary coefficient \(L^2\) realization. Point evaluation was used on polynomials. No bounded point bra on \(L^2\), gauge-singlet projection, positive physical norm, nonzero periodic response, or numerical approximation was used. The witness tests the declared full cut domain; a proposed smaller physical domain would require its own descent and state matching.

## 5. Two unscaled forces and their transport

Use \({\cal C}\) itself for a faithful comparison. It carries left and right actions of endpoint coefficient functions by their pullbacks and multiplication; their common shared variables agree. Equivalently, for the two specific lifts one may adjoin even labels \(z_a,z_c\) to the source, mapping them to the explicit original \(m_a,m_c\) of §3, independently of \(\alpha,\beta\). The extended pullback is substitution into the same \({\cal C}\), including the original phase momentum substitutions at each source. If taking an image algebra, divide by the full kernel of this substitution; no freeness or independent physical modes are assumed for the labels. In the full comparison ring the evaluation relations are exactly \(z_a-m_a=z_c-m_c=0\) for these two formal indeterminates. Base coefficients of these channels are visible by (2); their first and mixed source derivatives vanish. The source-dependent excluded forces are \(\alpha m_c,\alpha m_a\), with \(\alpha\)-jets \(m_c,m_a\), zero \(\beta\) and mixed jets. Remembering only the multiples by \(\alpha\) would erase their base coefficient data.

The actual extended symbols with identically vanishing pullback are
\[
 \widetilde p^+=P(V_c)-V_c s^+-\alpha z_c,\qquad
 \widetilde p^-=p(V_a)+V_a s^-+\alpha z_a . \tag{5}
\]
Indeed \(P(V_c)=V_c s^++\alpha m_c,\ p(V_a)=-V_a s^--\alpha m_a\) on the graph. In (5) the coefficients of \((\alpha,\beta,\alpha\beta)\), beyond \(p_0^\pm\), are respectively
\[
 (-V_cR_+^2-z_c,\ 0,\ -2(V_cR_+)\cdot T_1),\qquad
 (+V_aR_-^2+z_a,\ 0,\ +2(V_aR_-)\cdot T_1).
\]
At first order the same-anchor terms subtract the same-anchor force, the new labels subtract the two cross contributions. At mixed order the direct pullback derivative of \(p_0^\pm\) is \(+2(V_cR_+)\cdot T_1\) or \(-2(V_aR_-)\cdot T_1\). In the four-term mixed equation \(\phi_\alpha p_\beta=0\) and \(\phi_\beta p_\alpha=0\), since \(p_\beta=0\) and the first corrections carry only fixed coordinates and constant labels after evaluation. The displayed mixed corrections cancel the remaining force. This constructs a particular joint lift. It does not classify all ideals or prove a smaller algebra stable under repeated insertions, reflection, products and sewing.

For an even bridge insertion \(h\), the **original kernel realization** of the endpoint bimodule actions is
\({\cal V}_s[i_+^*B\,h\,i_-^*A]=M_B{\cal V}_s[h]M_A\) for even endpoint tests (general ordered products use their inherited grading). Directly differentiating or integrating by parts as in §3 yields the stronger transport formulas
\[
 C_+{\cal V}_s[h]={\cal V}_s[V_ch+\alpha m_c h],\qquad
 {\cal V}_s[h] C_-=-{\cal V}_s[V_a h+\alpha m_a h]. \tag{6}
\]
These formulas retain derivatives of the inserted word if it varies along the tested field vector. In particular the corrected kernel identities for \(h=1\) are (3) minus their respective right-hand sides, identically zero. Their \(\alpha\)-jets subtract \(+{\cal V}_0[m_c]\) and \(-{\cal V}_0[m_a]\); their mixed jets subtract \(+{\cal V}_0[E_\beta m_c]\) and \(-{\cal V}_0[E_\beta m_a]\) from the four left placements in (4). This proves restoration on every cut test at these orders. A bilocal force multiplies the integrand prior to old Haar/Berezin integration. The writeup of (6) uses no endpoint multiplication operator for \(z_a,z_c\). The old/new dependence in (2) is a direct check on that distinction.

## 6. Local current, coherent order and normalization

For completeness use arbitrary real site phase \(\chi\) when stating the original current. On a forward anchor \(e=(x,\mu)\) with \(y=x+\hat\mu,\ \delta\chi_e=\chi_y-\chi_x\), let
\[
 B_e^A=\bar\psi_x\gamma_A U_e^\dagger\psi_y+\bar\psi_y U_e\gamma_A\psi_x,\quad
 C_e^A=\bar\psi_y\gamma_A U_e\psi_x+\bar\psi_x U_e^\dagger\gamma_A\psi_y .
\]
The signs of the two reverse hoppings in \(T_{x,\mu}\) and their opposite phase differences give \(V_\chi T_{x,\mu}^A=(i/4)(\delta\chi_e B_e^A+\delta\chi_{e-} C_{e-}^A)\), \(e-=(x-\hat\mu,\mu)\). With \(b_{x,\mu,A}\) the actual coframe force (kinetic (14): derivative of all four determinant slots, both \(g_2 F/4\) coframe slots and both literal metric slots, pulled back by \(A_{\rho\mu}\)), the full current is \(J_e=(i/4)\sum_A(b_{x,\mu,A}B_e^A+b_{y,\mu,A}C_e^A)\). For one step take only its action centres; on the periodic lattice collect both endpoint centres. Then \(C=V_\chi s=\sum_e\delta\chi_e J_e\). At the origin
\[
 C_\alpha=(i/2)\sum_A R^A(\delta\chi_{r,0} B_{r,0}^A+
                                      \delta\chi_{r-0,0} C_{r-0,0}^A),\quad
 C_\beta=V_\chi E_\beta,\quad C_{\alpha\beta}
 =2[(V_\chi R)\cdot T_1+R\cdot(V_\chi T_1)] .
\]
In particular \((J_e)_\alpha=(i/2)\delta_{\mu0}\sum_A R^A(\delta_{x,r}B_e^A+\delta_{y,r}C_e^A)\). For general \(\beta\) along this shear the diagonal source coefficient in the coframe force is \(2 A_{0\mu}Y_0^A\) at \(r\), fixing the mixed current also on direction 1. A first current-vertex jet inserts \(s_j C+C_j\) and its mixed jet inserts \((ue+v) C+u C_\beta+e C_\alpha+C_{\alpha\beta}\). For the new-only \(V_c\), only the forward \(B\) term survives in \(V_c R\). An old *phase* would also act on bars; replacing the one-sided Euler \(V_a\) by that old phase would give a different constraint.

The accepted coherent comparison supplies an exact ordering dictionary for these identities. On a cut the auxiliary coefficient Fock space has a creation \(d^\dagger_\xi=M_\xi\) and contraction \(d_\xi=\partial_\xi^L\) for each original exterior coordinate. Thus the Euler operator is \(\sum_{i\ {\rm old}\ \psi}d_i^\dagger d_i\), with the explicit \(-4I\) in \(C_-\); \(V_c\) is \(i\) times the difference of the two corresponding unbarred and barred sums. The endpoint multipliers are the ordered \(d^\dagger\) polynomials inserted with their actual coefficients. A coherent kernel in this representation is obtained by pairing the matrix elements \([\xi_b^K\xi_c^L]I_a[e^s h\,\xi_a^I\xi_b^J]\) with the coherent output/input basis vectors, retaining old Haar integration and the identity on shared compact coordinates. The convolution measure is \(d\mu(\zeta)e^{-\bar\zeta\zeta}\) with overlap \(e^{\bar\eta\zeta}\); parity in the supertrace keeps the original periodic sign. The 128 pair coefficient occupations and the field-symbol CAR coordinates have different meanings.

For the field-symbol dictionary distinguish the normalization \(\kappa_W>0\) from the free graph covector \(k\). On ordered Majorana monomials \(W_{\kappa_W}(\theta_I)=\kappa_W^{|I|/2}C_I\); \(N_{\kappa_W}(\bar\psi_I\psi_J)=\kappa_W^{(|I|+|J|)/2}a_I^\dagger a_J\), \(N_{\kappa_W}(1)=I\). Define \(\Delta=\sum_i\partial_{\psi_i}^L\partial_{\bar\psi_i}^L\), so
\(N_{\kappa_W}^{-1}W_{\kappa_W}=S_\kappa=\exp(-\kappa_W\Delta/2)\). If unit \(N_1\) is used for an ordinary coherent normal symbol there is the extra degree dilation \(N_1^{-1}W_{\kappa_W}=\exp(-\Delta/2)D_{\sqrt{\kappa_W}}\), \(D_b f(q)=f(bq)\). An endpoint exterior multiplier is represented by an ordered composition of Bopp operations: for each Majorana letter \(c=\sqrt{\kappa_W} C_i\), \(B_i(X)=(cX+\Gamma X\Gamma c)/2\). Its trace-dual is \(B_i^\times(Y)=(Yc+\Gamma(cY)\Gamma)/2\); dualize compositions in reverse order. This reproduces the wedged input, including repeated-letter zeros. Explicitly the transported field-symbol \(C_-\) is \(W V_a W^{-1}-4I_{\rm op}+B_{V_a s^-}\), and \(C_+=W V_c W^{-1}-B_{V_c s^+}\). In scaled normal symbol coordinates \(S_\kappa V_c S_\kappa^{-1}=V_c\) and \(S_\kappa V_a S_\kappa^{-1}=V_a-\kappa_W\Delta_{a,r}/2\), where \(\Delta_{a,r}\) contracts the four corresponding barred/unbarred pairs. Indeed the local phase commutes with each contraction, whereas \([\Delta,V_a]=\Delta_{a,r}\), commuting with \(\Delta\). These Euler actions are superoperators on symbols. An open bilocal insertion acts on the full independent matching word under the kernel before either endpoint reduction. In the sewn field-symbol calculation keep all 128 generators (64 bookkeeping modes), both links and the ordered Bopp operations until the original partial trace/integration; a genuinely spatial single-slice symbol uses 32 modes. No use of the latter can identify old and new spinors in the open test.

For a pair of traceless one-particle coframe matrices \(K_i,K_j\) from the original off-site bilinears \(t_i=\bar\psi K_i\psi\), write \(A_i=\kappa_W a^\dagger K_i a\). The once fixed normal/Weyl dictionary gives
\[
 W(t_i t_j)=\tfrac12\{A_i,A_j\}-\tfrac{\kappa_W^2}4{\rm Tr}(K_iK_j)I,\qquad
 S_\kappa(t_i t_j)=t_i t_j+\tfrac{\kappa_W}2\bar\psi\{K_i,K_j\}\psi
                   -\tfrac{\kappa_W^2}4{\rm Tr}(K_iK_j).
\]
The first normal reordering in \(\{A_i,A_j\}/2\) produces the displayed one-particle anticommutator; the two contractions supply the scalar. It is retained even on diagonal \(Q_{00}\), with both anchors in its temporal matrices; polarizing gives the \(\beta\) contact for \(2R\cdot T_1\). The scalar-test product correction for any insertion \(h\) is \(W(h\wedge h)-W(h)^2\). On general tests it is the entire \(B_h\) and its trace-dual that matter, with all link dependence under the weight. The mixed dual source insertion on the full sewn coefficient family is \(B_{s_\beta}^\times B_{s_\alpha}^\times+B_{s_{\alpha\beta}}^\times\), before marginalizing. Replacing it with a multiplication by a composite matrix or a score would omit contacts.

The established coordinate change \(r_\lambda f(q)=f(\lambda^{-1}q)\) sends \((g_1,g_2,J,j)\) to \((\lambda^8g_1,\lambda^4g_2,\lambda^4J,j)\) in the primed model and transports \(\kappa'_W=\lambda^{-2}\kappa_W\). Then \(W_{\kappa'_W}(f)=W_{\kappa_W}(r_\lambda f)\), including the transported star product. At corresponding sources \(R_{\lambda,\rm out}L'=\lambda^{64}L R_{\lambda,\rm in}\), \(Z'=\lambda^{128}Z\). Odd cotangent components (including those of \(k\)) scale by \(\lambda\), link momenta stay fixed. \(V_a,V_c\) preserve degree, \(r_\lambda m_{a,c}=\lambda^{-4}m_{a,c}\), and \(r_\lambda(\alpha' m)=\alpha m\). Thus (3),(6) intertwine with the same kernel Jacobian, and a literal-source derivative adds \(\lambda^{-4}\), a frame derivative no additional factor. No value of the contraction scale or physical calibration was selected by these tests.

## 7. Reverse cut and two periodic interfaces

Write \(P=\gamma_0,\ E=\operatorname{diag}(-1,1,1,1)\) on world indices, \(\rho(t,\mathbf x)=(1-t,\mathbf x)\). The geometric reflection is antilinear and reverses exterior order; the original spinor/bar exchange uses \(P\) with its transposed index placements. It acts on spatial anchors by Pin conjugation at the reflected site. In the reflected unsewn triple \(a'=\rho c,b'=\rho b,c'=\rho a\), \(v'_{a}=P v_b^\dagger P,\ v'_b=P v_a^\dagger P\). After the actual \(N_t=2\) reflection each temporal anchor goes to its own reflected/inverted anchor, independently; periodic translation is a different identification. The reflected comparison profiles are \(A^\circ=E\overline{A\circ\rho}E,\ {\bf J}^\circ=E\overline{{\bf J}\circ\rho}E\). In particular the real literal \(\alpha\) has positive sign at \(\rho r\), and the shear has \(-\beta E_{01}\) there. Both derivatives are taken with respect to the original real source. The mixed insertion reflects with that frame sign, including its site and coframe transport.

For a full temporal plane based at \(y\), write \(z=y-\hat0,\ A=V_z,\ B=U_{y,i},\ C=V_{z+i},\ D=U_{z,i}\) for anchors in this paragraph. \(H_f(z)=D^\dagger C^\dagger BA,\ H_{\rm back}(y)=B^\dagger CD A^\dagger=A H_f(z)^\dagger A^\dagger\). The compared \(0i\) curvature is \(\widehat F_{0i}=-F(H_{\rm back})=F(A H_f(z) A^\dagger)\), with coframes based at \(y\); spatial curvatures remain forward. The reflected action is \(\widehat S_{s^\circ}\), with this plaquette and the true reflected source. \(\Delta_s=\theta S_s-S_s\) thus includes \(\Delta_0\), whose previously accepted coefficient is \(-4i g_2\) on its own test. The weight ratio is \(e^{\Delta_s}\); the mixed witness in §4 is a different open coefficient.

On the original coefficient test algebras use the *bilinear* complement pairing, no complex conjugation. The transpose is \(L_s^t h=\int dH_c\,I_c[e^{s}h]\) into the old cut. The same formula with an inserted even \(m\) transposes \({\cal V}_s[m]\), with new spatial/temporal anchor integrals in \(dH_c\). Even integration and multiplication preserve the stated ordering. In the cut pairing \(V_c^t=-V_c\) by its zero top charge, \(V_a^t=4-V_a\) by its four selected top factors; even multiplication is its own transpose. Thus \(C_+^t=-V_c-M_{V_c s^+}\), \(C_-^t=-V_a+M_{V_a s^-}\). If \({\cal R}_-,{\cal R}_+\) denote the fixed antilinear maps from \(B_-,B_+\) to the reversed output/input respectively, set \(L^\theta={\cal R}_- L^t{\cal R}_+^{-1}\). Its kernel is \(e^{\theta s}\) with the just displayed anchors and curvature. Writing \({\cal V}^\theta[m]={\cal R}_-{\cal V}_s[m]^t{\cal R}_+^{-1}\), its vertex is \(\theta m\) under that weight, with all bar/psi, old/new and order changes. Transposing (3) and transporting gives
\[
 L^\theta({\cal R}_+ C_+^t{\cal R}_+^{-1})=\alpha{\cal V}^\theta[m_c],\qquad
 ({\cal R}_- C_-^t{\cal R}_-^{-1})L^\theta=-\alpha{\cal V}^\theta[m_a].
\]
In particular the reflected old Euler term counts the corresponding new **barred** components under the fixed spin change, and phase conjugation includes both \(i\mapsto-i\) and bar/unbar exchange. Differentiating these equalities gives the reverse of each first and each of the four mixed placements in (4); the first inserted forces are \(+\theta m_c,-\theta m_a\), the mixed are \(+(\theta E_\beta)(\theta m_c),-(\theta E_\beta)(\theta m_a)\) with base weight \(e^{\theta s_0}\). This uses fixed cut reflection, including its actual site/profile images, never an independently chosen reverse current.

For comparison only, if \(B_{\rm in/out}\) are the invertible real complement matrices and \(C_{\rm in/out}\) coefficient conjugation, \(L^t=B_{\rm in}^{-1}C_{\rm in}L^{\dagger_{\rm coeff}} C_{\rm out} B_{\rm out}\). The coefficient dagger is for the auxiliary compact-Haar coefficient norm. The two conjugate-linear cut maps in \(L^\theta\) give a linear reverse operation; a physical dagger on Hilbert domains is additional data.

Sew only after the two moves with centres 0,1 are composed. Integrate their common connector off shell, impose \(X_c=X_a,X_d=X_b,v_c=v_a\) at periodic closure; all 64 original links (both temporal interfaces) and 128 independent fermion generators then occur. For \(K=L_1L_0\), the first jet is \(L_{1,j}L_0+L_1L_{0,j}\); the mixed jet is
\[
 L_{1,\alpha\beta}L_0+L_{1,\alpha}L_{0,\beta}
  +L_{1,\beta}L_{0,\alpha}+L_1 L_{0,\alpha\beta}.
\]
Each step carries its profile at its own centre; terms with zero profile there evaluate to zero after placement. The reverse product composes the two transported transposes in reversed order, with mixed placements \(L_{0,\alpha\beta}^\theta L_1^\theta+L_{0,\alpha}^\theta L_{1,\beta}^\theta+L_{0,\beta}^\theta L_{1,\alpha}^\theta+L_0^\theta L_{1,\alpha\beta}^\theta\) on the matched reverse cuts. These formulas retain both interfaces even for an insertion involving an old and a new temporal half. \(Z_s=\operatorname{Str}K_s=\operatorname{Tr}(\Gamma K_s)\) is the amplitude seam. Current transport through two steps uses \(J_1L_0+L_1J_0\) for the local phase commutator, and all four placements per product for its mixed derivative, with \(J_j,J_{\alpha\beta}\) as in §6. No identification of a bridge vertex with multiplication at the periodic interface was needed.

Write \(\langle\cdot\rangle_{\rm bare}\) for the top/Haar operation without weight, \(S\) for the full exponent, \(N=\langle e^S X_s\rangle_{\rm bare}\). Moving tests and state/unit contacts use
\[
 N_j=\langle e^S(X_j+ S_j X)\rangle_{\rm bare},\qquad
 N_{\alpha\beta}=\langle e^S[X_{\alpha\beta}+S_\alpha X_\beta+S_\beta X_\alpha+
                 (S_\alpha S_\beta+S_{\alpha\beta})X]\rangle_{\rm bare}.
\]
Set \(X=1\) for \(Z\)'s jets. On \(Z\ne0\), \(n=N/Z\) has
\(n_j=(N_j-n Z_j)/Z,
 n_{\alpha\beta}=(N_{\alpha\beta}-n Z_{\alpha\beta}-n_\alpha Z_\beta-n_\beta Z_\alpha)/Z\).
For a local current Ward test use \(X=V_\chi f_s+f_s V_\chi S\), differentiating both terms, including \(f_{\alpha\beta}\) and both \(f_\alpha C_\beta,f_\beta C_\alpha\). The raw numerator vanishes by the periodic zero-divergence phase change; zero numerator derivatives follow only with these contacts. The periodic Euler at the selected site instead gives \(\langle e^S[(V_a-4)f+f V_aS]\rangle_{\rm bare}=0\), where the derivative acts on that actual sewn site's fields throughout \(S\).

For \(X_s=\theta F_s G_s\) use the same product rule in order. Conjugating its normalized pairing interchanges the tests and uses the weight \(e^{\widehat S_{s^\circ}}=e^S e^{\Delta_s}\), with denominator \(\overline{Z_s}\) and its conjugated first/mixed derivatives. Explicitly, for the reflected weight let \(D=e^{\Delta_s}\); \(D_j=D\Delta_j,\ D_{\alpha\beta}=D(\Delta_\alpha\Delta_\beta+\Delta_{\alpha\beta})\). Insert \(D X_s\) into the numerator rule; for the raw forward-minus-reflected difference use \((1-D)X_s\). Even at zero source this retains \(D_0=e^{\Delta_0}\) and the terms \(S_\alpha D_\beta,S_\beta D_\alpha,D_{\alpha\beta}\) in the reflected weight. Apply each quotient rule with its own denominator. The log partition contact is \(W_{\alpha\beta}=Z_{\alpha\beta}/Z-Z_\alpha Z_\beta/Z^2\), \(W_j=Z_j/Z\) wherever a local log exists; use the conjugate versions on the reflected side.

There is a further matrix-log distinction on the previously proved strictly positive finite *marginal* \(R_s\). With \(G_t=(R_s+tI)^{-1}\), \(H=\log R_s\), its true jets are \(H_j=\int_0^\infty G_tR_jG_t\,dt\) and
\[
 H_{\alpha\beta}=\int_0^\infty
 [G_t R_{\alpha\beta}G_t-G_tR_\alpha G_tR_\beta G_t-G_tR_\beta G_tR_\alpha G_t]\,dt .
\]
Going back through the exponential includes \(D\exp_H[H_{\alpha\beta}]\) and both simplex orders of \(D^2\exp_H[H_\alpha,H_\beta]\) (the ordered integrals of \(e^{(1-u)H}H_\alpha e^{(u-v)H}H_\beta e^{vH}\) and its interchange over \(0<v<u<1\)). For \(\log(R_s/Z_s)\) subtract \(W_j I,W_{\alpha\beta}I\) at the respective order. These inherited log/Bopp formulas apply on their established domains; they assume no positivity of the full link-conditional matrix and give no physical time-adjoint identity by themselves.

## 8. Physical disposition and the next identity

The new failed identity is precise. Each frozen endpoint symbol would need a first literal-source correction in its own polynomial phase algebra, and its perturbed kinetic annihilator would need a null open kernel action on the original cut tests. The failure of the lift in §2 includes all momentum degrees; the kernel failures of §§3–4 concern exactly the differential operators constructed there. The original divergence dictates an ordering contact already in the incoming generator. This argument does not test every possible ordering or prove the nonexistence of a physical map. Equations (5)–(6) give a constructive source-level remedy for **this pair** of failures, with the interfacial word rather than a fitted coupling or a new microscopic degree of freedom.

The next physical test is to represent these two actual insertions before the interface integral, their reverses and moving-map contacts in a single original-matched product and state on specified input/output domains. In particular, for each admitted cut test, kinetic (30), first (31) and the mixed equation require
\[
\begin{split}
 I_o L&=T I_i,\\
 I_{o,j}L+I_o L_j&=T_j I_i+T I_{i,j}\quad(j=\alpha,\beta),\\
 I_{o,\alpha\beta}L+I_{o,\alpha}L_\beta+I_{o,\beta}L_\alpha+I_o L_{\alpha\beta}
 &=T_{\alpha\beta}I_i+T_\alpha I_{i,\beta}+T_\beta I_{i,\alpha}+T I_{i,\alpha\beta}.
\end{split}
\]
Here \(L_\alpha={\cal V}_0[R^2]\) and \(L_{\alpha\beta}={\cal V}_0[R^2 E_\beta+2R\cdot T_1]\) are known. The mixed physical equation must account for both the source weighting and the explicit contact from the shear in the coincident quartet. Its physical observable must be the appropriate internally contracted, ordered \(\widehat E_0^A\widehat E_0^B\) in the derived product at \(r\), with its actual state, physical metric contraction and calibration. The reflected version is \(I_{\rm rev,o} L^\theta=T^{\dagger_{\rm phys}} I_{\rm rev,i}\) on the reversed domains, with the same first and four mixed placements on **each** side, applied to \(I_{\rm rev,o},L^\theta,T^{\dagger_{\rm phys}},I_{\rm rev,i}\) and the actual profiles of §7. Moving adjoint domains/pairings must be identified before differentiating a physical dagger. An original normalized state must return the exact sewn amplitudes for its identified word family, preserve the unit, and satisfy positivity in that derived product and adjoint on its domain. If the constant phase is represented by a unitary group, \(I_B(-iV_{\rm global})=Q_{\rm phys} I_B\) on a justified generator domain. The local \(V_c\) used here has no such assumed unitary interpretation.

Accepted controls for this step retain their original scope:

- The compact input \(f\) has \(L(t)f=t\Theta_b\) even though compact averaging loses the input. The open \(\Phi\) test gives \(3/4\) while its closed second response is zero. These show why collecting a compact average or a periodic scalar cannot validate the new open comparison.
- \(L u=0\) on the established step, but \(g u=-2e,\ \omega(e)=1/Z\); simply dividing by all input step-null vectors loses original products. On the **coefficient-adjoint** operator algebra the constant/top projector has raw cycle value \(-1/2\). Neither fact identifies that projector with a physical observable.
- For the **specified geometric half-pairing**, \(P(F60,F60)=0\) and \(P(F60,G52)=P(G52,F60)=(3645/2)(1125/4)^6 g_2^4\); at the accepted \(Z>0,\ g_2\ne0\) point the unchanged pair cannot be a positive Gram pair. The previously tested diagonal coefficient grouping has Gram trace at least one on its zero-original-trace test. The positive instrument reproduces the original amplitude visibility, but its seam real observable \(\sigma_x/2\) has a negative eigenvalue and using a positive arm projector adds a \(1/2\) background. These are inherited comparisons, each in its own algebra. None was used to compute §4.
- The uncapped \(A_{01}\) has both interfaces and the reflected defect/denominator. Nonnegativity would be necessary under a physical identification with precisely the same normalized source/product and \(q_1=q_0^{\dagger_{\rm phys}}\). The present open readouts impose no such sign by themselves. No page-0 or \(h_{12,6}\) value is needed for (1)–(6).

Diakonov, held 1109.0091v1 (26)–(28) and VI, supplies the compact chiral Haar factors, original top and positive-degree vertices in the exponent. Volovik, held 2312.09435v2 (18)–(22), distinguishes the expectation of a quartet from the product of tetrad means, including its connected part and different matter couplings. Vergeles, held 2506.00036v2 (2.20),(2.26),(4.3)–(4.5),(6.1), uses a contour/substitution, a scalar-product domain and an orthonormal spectral construction for the distinct simplicial model; formal dagger alone does not provide those data for this kernel. No new physical premise from these papers was supplied. If a factorized calibration is eventually derived, \(G_{\rm phys}=c_Q Q,\ E_{\rm phys}=(c_E/a)T,\ c_Q=(c_E/a)^2\) would require \(c_{Q,\lambda}=\lambda^4 c_Q,\ (c_{E,\lambda}/a_\lambda)=\lambda^2(c_E/a)\) and would relate a conjugate physical source by \(J=c_Q K_{\rm phys}\) in the constant linear case. Any moving calibration has its own source jets. This does not set a contraction scale, matter residue, lattice time, absolute units or a positive physical state.

**Review boundary.** New here are the two all-polynomial endpoint obstructions, dual-number projected nonflatness, the open first/mixed Haar readouts and the particular unscaled two-force lifts and insertion identities. Existing graph, action, current, coherent, reverse, periodic and loss-control results were used at their accepted scopes. Original physical product, positive state, adjoint, four physical cut maps, the physical identification and calibration in (30)–(31), causal dynamics, matter/light/transport, B3/N4, controlled limits and publication remain open. ROOT owns their disposition. The primary November 20 notebook authorization, Phase6a roadmap and exact two R2 prospective reports were read. Only this private candidate was written. The continuity check was the first tool action; exact final packet status, report length and SHA-256 accompany delivery. No scientific program, evaluator, import, CAS, scientific test, network, Lean, slot, controller, process operation, notebook or repository change occurred. Independent actual mathematics and original-source reviews of these bytes and lead/ROOT intake are pending.
