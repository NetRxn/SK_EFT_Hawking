# Independent manual review: interacting one-site ADW coefficients

ACCEPT within the exact declared finite model. I independently rederived all equations (1)–(21), including the complete sixteen-source quartic and Hessian. I found no mandatory mathematical correction. This is acceptance of the original one-site periodic, dimensionless, four-complex-Dirac-component Grassmann/Haar calculation and a nonzero-source local inverse witness. It is not a physical-state, vacuum, full-tetrad, scalar-reduction, mode, continuum, magnitude or native verification result.

The candidate is CONSTRUCTION.md SHA256 4a67387106671b28092b62843869adc1b54b54886b6826b20e980d9734c5d9c3, with REPORT.md 235df18f4c3705975dd6b35eb23eed2a364a2321be7b459aba4915dcf8b14752. The exact auxiliary premise is e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8. The original composite-source construction is 6be0e1c5d1423a7bcd9015351567933ed58ff5aed74319f02947e31443b3d738; its separate nonauthor review eabaa5c41afec63defc11b2ec66d5fc9e976d06262d5c0b483572fcc9db0b532 and lead acceptance d27bd53e350aa8d5308d6b8970fec1b179640a8f091ce73de7702b6aa6427c4e are preserved. I authored that earlier composite-source construction, but did not author this interacting coefficient calculation. The derivations below independently verify the latter, rather than treating the prior acceptance or hashes as its proof.

## Coincident links, gamma matrices and saturation: equations (1)–(4)

All four terms in the original symmetric coframe must be retained when forward and backward sites coincide. Their numerator becomes gamma Omega-dagger minus Omega gamma minus gamma Omega plus Omega-dagger gamma. Thus A_mu,A={gamma_A,Omega_mu-dagger−Omega_mu}/4; it does not vanish. The declared gamma convention gives gamma1 gamma2 gamma3 gamma4=diag(I,−I), agreeing with gamma5 and epsilon1234=+1.

Writing the two chiral SU(2) imaginary parts as u,v and s=(u+v)/2,d=(u−v)/2, I obtain A_mu,4 with both off-diagonal blocks −i s.sigma. For A_mu,j the upper block is −s_j I+i(e_j cross d).sigma, and the lower is +s_j I+i(e_j cross d).sigma. Therefore a source row X=(x,t) yields ell=−x.s and b=x cross d−t s, summed across directions, and the full matrix is [[0,ell I+i b.sigma],[−ell I+i b.sigma,0]]. For real sources its lower block is minus the upper adjoint. Its determinant is (ell²+b.b)², with a bilinear dot product when sources are complex. There is no complex conjugation in the holomorphic continuation. The declared Berezin orientation for n=4 has reversal sign (−1)^6=+1, so no additional determinant sign is introduced.

With eight Grassmann generators, top-degree saturation requires 4q+2p+k=4. The only possible contributions are g1 S4, g2² S2²/2, g2 S2(J.T)²/2, and (J.T)^4/24. Independently changing a link's common Spin(4) center sign flips its coframe and leaves every plaquette commutator unchanged. Haar averaging therefore requires an even coframe count in each direction. This kills S4 and products of different unordered coframe pairs in S2². For the mixed term only source rows matching the coframe pair can survive the center test; its remaining complementary-link curvature has zero vector mean, so that term also vanishes. This is a one-site cancellation, not a statement that g1 or curvature is irrelevant on a general lattice.

## All sixteen source coefficients: equations (5)–(9)

For a normalized S3 quaternion, E u_i u_j=delta_ij/4, E|u|²=3/4 and E|u|^4=5/8. Independent chiral factors give E s_i s_j=E d_i d_j=delta_ij/8 and E s_i d_j=0. With Y_X=(ell,b), R=X.X and w=(t,−x), direct expansion gives the covariance (R I−w w^T)/8. In particular E|Y_X|²=3R/8 and tr(Sigma_X Sigma_Y)=[2 R_X R_Y+(X.Y)²]/64. Treating this as an isotropic four-dimensional Gaussian would be wrong.

For a real unit source row, q_X=t I−i x.sigma is SU(2). Conjugation by diag(q_X,I) takes gamma4 to gamma_X and preserves the two independent Haar measures. The one-row quartic is thus proportional to R². At X=e4 it is E|s|^4. Expanding |u+v|^4/16 gives [2(5/8)+2(3/4)^2+4(3/16)]/16=25/128. Real polynomial equality then extends to complex sources.

For distinct independent rows, their center symmetry removes the odd terms in |Y_X+Y_Y|^4. The cross term is 2 E|Y_X|² E|Y_Y|²+4 tr(Sigma_X Sigma_Y), hence 13 R_X R_Y/32+(X.Y)²/16. Consequently the whole quartic is

F(J)=(25/128) sum_mu R_mu²+(13/32) sum_mu<nu R_mu R_nu+(1/16) sum_mu<nu (X_mu.X_nu)².

This verifies every monomial, not just selected parallel rows. A single J_mu,A^4 has coefficient 25/128. Same-row J_mu,A² J_mu,B², A≠B, has 25/64. Distinct-row same-component squares have 15/32; distinct-row different-component squares have 13/32. The crossed monomial J_mu,A J_mu,B J_nu,A J_nu,B for A<B has 1/8. All remaining degree-four monomials vanish. Thus parallel versus orthogonal row coefficients genuinely differ. No extra 1/24 belongs outside this determinant polynomial; taking source derivatives restores the appropriate factorials.

## Full curvature trace and commutator law: equations (10)–(13)

I first retain the complete diagonal term rather than calling the trace antisymmetric. For Omega_kl=diag(c0+i c.sigma,d0+i d.sigma), the trace is 2(c0−d0) delta_AB+L_AB. The antisymmetric part is L_j4=2(c+d)_j, L_4j=−L_j4 and L_jm=−2 epsilon_jma(c−d)_a. The diagonal term is generally nonzero before contraction, but drops out of the epsilon-antisymmetrized coframe product.

For each fixed ordered kl, combining mu,nu with nu,mu produces a factor two and the antisymmetric L. Combining kl with lk produces another factor two: Omega_lk=Omega_kl-dagger reverses its vector parts, while the epsilon sign reverses as well. These two factors cancel the original action's 1/4. The result is exactly the sum over the six unordered coframe pairs Q_mu,nu in the note, with complementary kl and the indicated epsilon sign. Summing both C,D is already part of Q; rewriting it as C<D coframe wedges introduces no further stray factor two. This accounts for all 24 ordered spacetime permutations.

The curvature variable is an SU(2) commutator, not a Haar-distributed SU(2) matrix. Its law is conjugation invariant, so its vector has zero mean and isotropic covariance. Direct quaternion multiplication gives c0=1−2|u cross v|². For independent S3 variables and their independent relative S2 angle, E|u cross v|²=3/8 and E|u cross v|^4=5/24. Hence E c0=1/4, E c0²=1/3, E|c|²=2/3 and E c_i c_j=2 delta_ij/9. The nonzero scalar mean is an important control against incorrectly replacing the commutator with Haar data. Left and right commutators are independent. Summing the ordered L components gives 8|c+d|²+8|c−d|²=16(|c|²+|d|²), so E sum_CD L_CD²=64/3.

## Interaction coefficient: equations (14)–(16)

Conditioning on the complementary curvature links leaves the two coframe-direction link variables independent of L. Differentiating the two-row source quartic gives

E top(T_mu,C T_mu,E T_nu,D T_nu,F)=4b delta_CE delta_DF+2c(delta_CD delta_EF+delta_CF delta_ED),

where b=13/32,c=1/16 and 'top' means the common Berezin top coefficient. This is not a factorization of independent Grassmann systems; the common fermion top coefficient has been computed by the determinant. Contracting with L_CD L_EF gives (4b−2c)||L||²=(3/2)||L||²: the trace contraction vanishes and the transposed contraction is negative by antisymmetry. A single nonzero L14=−L41=ell therefore gives 3 ell², a useful sign/factor check. Each pair contributes (3/2)(64/3)=32. Six pairs and the exponential's 1/2 produce 96g2². Thus Z(J)=96g2²+F(J) with no mixed g2 J² or g1 term, exactly as claimed.

## Full response, exact witness and failure controls: equations (17)–(21)

On J14=j with all other sources zero, let alpha=25/128 and D=96g2²+alpha j^4. The only nonzero mean is t14=4 alpha j³/D. The unnormalized diagonal second derivatives are 12 alpha j², 4 alpha j² in the other three same-row directions, 2(b+c)j² in three same-component other-row directions, and 2b j² in nine remaining directions. All cross derivatives vanish on this axis. Subtracting the mean outer product changes only the longitudinal entry. The connected Hessian eigenvalues are therefore

- longitudinal: 4 alpha j²(288g2²−alpha j^4)/D²;
- three transverse same-row entries: (25/32)j²/D;
- three other-row parallel entries: (15/16)j²/D;
- nine other-row orthogonal entries: (13/16)j²/D.

These multiplicities total sixteen. At g2=j=1 I obtain D=12313/128, t14=100/12313, and eigenvalues 3683900/12313², three times 100/12313, three times 120/12313 and nine times 104/12313. All are positive exact rationals. This establishes an invertible full-source Hessian at a nonzero source, not merely a one-axis susceptibility. The local Legendre derivative there equals that nonzero source; it is not a vacuum stationarity result.

For j≠0, the axis inverse requires both D≠0 and 288g2²−alpha j^4≠0. The respective loci are j^4=−(12288/25)g2² and j^4=(36864/25)g2². At j=0,g2≠0, Z is nonzero but the entire Hessian vanishes. At g2=j=0, normalization fails. For real full sources F is a sum of nonnegative terms and is positive for any nonzero row, so Z>0 except at g2=0,J=0. This does not imply global convexity: the longitudinal eigenvalue changes sign and the real axis mean rises then falls to zero as 4/j, giving a noninjective global map. With g2=0,j≠0 the eigenvalues reduce to −4/j², three times 4/j², three times 24/(5j²), and nine times 104/(25j²), confirming nonpositive Hessian behavior without a zero partition function. A complex null row (1,i,0,0) has F=0 despite being nonzero; that does not by itself make Z zero when g2≠0.

All normalized derivatives are restricted to Z≠0. A holomorphic logarithm and inverse require a suitable local zero-free neighborhood and an invertible Hessian. Complex symmetry is not Hermitian positivity. Positive real Hessian at the witness extends to a sufficiently small real neighborhood by continuity; it is not a convex global physical effective action. The dimensionless T=a ehat and source convention are preserved; restoring physical coframe derivatives requires their spacing factors.

## Evidence, preservation and remaining work

The original supported first check returned 0/fresh=true. Independent static metadata inspection rehashed all 20 distinct bound input files, confirmed their declared hashes and recorded modes, sizes and nanosecond mtimes. The author first/static/final receipt streams agree byte-for-byte with their base64 fields; the author first check is 0 and final check is 1 with only owned-files drift. The author's retained apply_patch context rejection was a documentary notation-preparation failure before changes, followed by a narrow successful rename. Its enclosing native timing/streams were not exposed, and none are reconstructed here. It is not a failed coefficient run. This review used manual algebra; metadata/hash/JSON checks did not evaluate a model or supply a mathematical oracle.

The final original reviewer check and terminal input comparison are recorded in final-check.json, evidence.json and process.json. Expected owned-output drift is retained rather than refreshed. No project imports, numerical/symbolic evaluation, tests, Verify, Lean/native/controller work, compiler/rendering, network, Git mutation, sourceholding or candidate/notebook edits occurred. Preservation is limited to the actual pinned selection and canonical adapter observations; no new repository-wide census is claimed.

The calculation advances the actual finite interacting source polynomial and local response beyond a normalized illustrative toy. Its V=1 periodic center cancellations, fixed orientation and Haar normalization are essential hypotheses. Large-volume or symmetry-breaking limits, full-tetrad physical order, Legendre action selection, scalar reduction, physical modes, continuum/graviton behavior, magnitude and native verification remain BUILD. No source installation, closure, lifecycle, publication or human acceptance is inferred.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory mathematical contradiction was found in equations (1)–(21) under their explicit one-site hypotheses. The principal potential misreadings—zero coincident coframe, Haar rather than commutator moments, discarded diagonal trace before contraction, omitted exponential/pair factors, zero-source Hessian invertibility, global convexity, and finite-volume evidence of physical order—are explicitly excluded by the frozen construction and the derivation above.
