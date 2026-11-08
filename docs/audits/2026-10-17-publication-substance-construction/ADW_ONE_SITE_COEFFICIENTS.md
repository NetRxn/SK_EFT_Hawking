# Exact interacting one-site ADW source polynomial and full response

17 October 2026. **Independently reviewed manual finite-model construction.** See the [complete independent review](reviews/ADW_ONE_SITE_COEFFICIENTS.md); physical and native acceptance remain separate. I accept authorship of this next microscopic composite-source calculation under the original ADW BUILD. The general finite-source identity and insertion rules are accepted premises, not this new coefficient result's acceptance. No coefficient algorithm, numerical/symbolic library, project model, simulation or native prover was executed.

## 1. Actual one-site regulator, action and matrix

Take the accepted finite hypercubic regulator at V=1 with periodic fermions in all four directions, spacing a>0, four independent barred and four independent unbarred Dirac generators. There are n=4 fermion rows and d=16 composite sources. The normalized measure has four independent Spin(4) links

    Omega_mu=diag(U_mu,V_mu),
    U_mu=u_mu0 I+i u_mu·sigma, V_mu=v_mu0 I+i v_mu·sigma,
    u_mu0²+|u_mu|²=v_mu0²+|v_mu|²=1.

Each quaternion is independent normalized S³ Haar. Here V_mu denotes a right-chiral SU(2) matrix, not the volume. Fix

    gamma_j=[[0,-i sigma_j],[i sigma_j,0]], j=1,2,3;
    gamma_4=[[0,I],[I,0]], gamma_5=diag(I,-I),
    epsilon_1234=+1.

Use exactly the accepted symmetric coframe and plus-exponent action, with T=a ehat and dimensionless finite g1,g2,J:

    S=g1 S4+g2 S2,
    S4=epsilon_ABCD T_1A T_2B T_3C T_4D,
    S2=(1/4) sum_(k,l,mu,nu,C,D) epsilon_klmunu
         Tr(Omega_kl gamma_C gamma_D gamma_5) T_muC T_nuD,
    Omega_kl=Omega_k Omega_l Omega_k^dagger Omega_l^dagger,
    Z(J)=integral dHaar dBerezin exp(S+sum_mu,A J_muA T_muA).       (1)

All coincident hopping blocks are ADDED. Forward and backward neighbors coincide, but their link/gamma orders do not cancel:

    T_muA=barpsi A_muA psi,
    A_muA=(1/4){gamma_A,Omega_mu^dagger-Omega_mu}.                (2)

In particular these composites are not identically zero. With s_mu=(u_mu+v_mu)/2 and d_mu=(u_mu-v_mu)/2, write a source row as X_mu=(x_mu1,x_mu2,x_mu3,t_mu), t_mu=J_mu4, x_muj=J_muj. The bilinear source matrix is

    M(J)=sum_mu,A J_muA A_muA=[[0,B],[-ell I+i b·sigma,0]],
    B=ell I+i b·sigma,
    ell=-sum_mu x_mu·s_mu,
    b=sum_mu (x_mu×d_mu-t_mu s_mu),
    det M(J)=(ell²+b·b)².                                      (3)

For example A_mu4 has both off-diagonal blocks -i s_mu·sigma, whereas A_muj has upper block -s_muj I+i(e_j×d_mu)·sigma and lower block s_muj I+i(e_j×d_mu)·sigma. This proves (3) with the original 1/4 factors included. The block determinant sign is (-1)^2=+1. The accepted orientation integral exp(barpsi M psi)=det M agrees with n(n-1)/2=6 even. For complex sources, ell²+b·b is bilinear, not an absolute square; (3) extends by polynomial identity. For real sources the lower block is -B^dagger.

The auxiliary identity, when used, remains Z=integral W(h,Omega) det M(h+J,Omega), with W unchanged and J coupled to original T. The following calculation instead evaluates original-action top Grassmann coefficients directly. It does not shift W, identify h as an order parameter or replace this action by the scalar/NJL potential.

## 2. Saturation and the specific center selection

There are only four barred/unbarred pairs. The exact saturation rule 4q+2p+|k|=4 leaves precisely

    Z=integral dHaar dBerezin [g1 S4+(g2²/2)S2²
                         +(g2/2)S2(J·T)²+(J·T)^4/24].         (4)

There are no other terms, no approximation remainder and no extra factorial from a determinant convention. In particular g2 S2 alone does not saturate; g1 times any other positive-degree term over-saturates.

For any one mu, the Haar-preserving center transformation Omega_mu -> -Omega_mu (both chiral factors) changes T_muA -> -T_muA. Every one-site plaquette commutator is unchanged because the corresponding link and dagger both occur. Thus a surviving term must contain an even total number of coframes from each direction. The S4 contribution contains one from every direction and averages to zero. This is why the new polynomial is independent of g1 at THIS regulator. The cosmological interaction has not been deleted from the action or proved irrelevant at other volumes.

For the mixed g2 J² term, each S2 coframe pair occupies two distinct directions mu,nu. Center selection forces its two source insertions to occupy those same directions, once each. The curvature uses the complementary directions k,l, so its Haar variables are independent of the coframe/source pair. Section 4 below proves that the antisymmetric curvature tensor has zero Haar mean. Therefore the mixed coefficient vanishes. This is an averaged one-site statement; neither S2 nor its unaveraged mixed insertion is identically zero.

For S2², products of two different unordered coframe-direction pairs fail the same center selection. Only the square of each of the six pairs can survive. These restrictions greatly simplify the calculation but do not make this one-site torus a physical large-volume approximation.

## 3. Complete free quartic coefficients

Set g1=g2=0 temporarily and denote a single link's contribution to the real four-vector (ell,b) by Y_X. Normalized S³ moments give

    E u_i=0, E u_i u_j=delta_ij/4,
    E|u|²=3/4, E|u|^4=5/8,
    E s_i s_j=E d_i d_j=delta_ij/8, E s_i d_j=0.              (5)

The same holds for the independent v. For R=X·X=t²+|x|² and w_X=(t,-x), (3) gives the full covariance

    E Y_X=0,
    Sigma_X=E Y_X Y_X^T=(R I_4-w_X w_X^T)/8,
    E|Y_X|²=3R/8,
    Tr(Sigma_X Sigma_Y)=[2 R_X R_Y+(X·Y)²]/64.                (6)

For completeness the off-diagonal covariance E[ell b_i]=t x_i/8 has positive sign: ell=-x·s and b=x×d-t s. It is not an isotropic four-component Gaussian covariance.

The single-row quartic must depend only on R². This follows directly from the gamma/Spin(4) convention: for a real unit X, q_X=t I-i x·sigma is SU(2); conjugation by diag(q_X,I) maps gamma_4 to gamma_X and conjugates each link within its Haar measure. Matrix similarity preserves the determinant. Scaling then reduces a real nonzero X to e4. Polynomial continuation covers complex X afterward. At X=e4, Y=(0,-s), and independence gives

    E|s|^4=(1/16)[2(5/8)+2(3/4)^2+4(3/16)]=25/128.          (7)

Here E(u·v)²=3/16, and the odd cross terms vanish. Therefore E|Y_X|^4=(25/128)R², not a Gaussian fourth-moment substitution.

For two distinct directions, Y_X and Y_Y are independent and individually symmetric. Expanding |Y_X+Y_Y|^4 leaves the cross term

    2 E|Y_X|² E|Y_Y|²+4 E(Y_X·Y_Y)²
      =(13/32) R_X R_Y+(1/16)(X·Y)².                        (8)

The two coefficients are respectively 18/64+8/64 and 4/64. Terms involving an odd count from any other row vanish by its center symmetry. Define, without conjugation,

    R_mu=sum_A J_muA²,   P_munu=sum_A J_muA J_nuA.

The COMPLETE free result is consequently

    F(J)=(25/128)sum_mu R_mu²
       +(13/32)sum_(mu<nu) R_mu R_nu
       +(1/16)sum_(mu<nu) P_munu².                           (9)

As representative checks, two parallel unit source rows have cross coefficient 15/32, whereas orthogonal unit rows have 13/32. More explicitly the complete monomial types are: J_muA^4 coefficient25/128; J_muA² J_muB² (A<B) coefficient25/64; J_muA² J_nuA² (mu<nu) coefficient15/32; J_muA² J_nuB² (mu<nu,A!=B) coefficient13/32; and J_muA J_muB J_nuA J_nuB (mu<nu,A<B) coefficient1/8. All other quartic monomials vanish. These statements specify all sixteen source components, not merely the selected axis.

The free source exponential's 1/24 is already included by its exact Berezin determinant. Thus fourth source derivatives of F insert four T's without any additional factorial division. This matters in the interacting calculation next.

## 4. Curvature trace, antisymmetrization and Haar commutator moments

For k<l write Omega_kl=diag(C,D), with C=c0 I+i c·sigma and D=d0 I+i d·sigma. These are left and right SU(2) commutators, not independent Haar SU(2) matrices. The FULL trace is

    Tr(Omega_kl gamma_A gamma_B gamma_5)
       =2(c0-d0)delta_AB+L_AB,
    L_j4=2(c_j+d_j),  L_4j=-L_j4,
    L_jm=-2 epsilon_jma(c_a-d_a),  j,m in{1,2,3}.             (10)

In particular its diagonal is generally nonzero. It would be wrong to assume the full trace antisymmetric at the outset. First combine the epsilon-weighted mu,nu terms: because even T's commute, they replace T_muC T_nuD by its antisymmetric C,D combination and kill the symmetric delta term. The remaining tensor is L. Next Omega_lk=Omega_kl^dagger, which leaves c0,d0 unchanged and sends c,d to -c,-d, so L_lk=-L_kl. Combining both ordered k,l and both ordered mu,nu cancels the original 1/4 exactly. With {k,l} the complementary pair to {mu,nu}, each pair internally sorted, the result is

    S2=sum_(mu<nu) Q_munu,
    Q_munu=epsilon_klmunu sum_(C,D) (L_kl)_CD T_muC T_nuD.     (11)

Both C,D are summed in (11). Equivalently one may sum C<D and use L_CD(T_muC T_nuD-T_muD T_nuC); there is no extra factor2 in that latter form. For example the j4 wedge has coefficient 2(c_j+d_j), retaining all orientation factors.

The commutator distribution is invariant under simultaneous SU(2) conjugation of its two independent links. Thus c has isotropic distribution and E c=0; likewise E d=0. This proves the zero mean of L used for the mixed term in section 2. The scalar component c0 need NOT have zero mean, which is another reason the symmetric trace term could not be ignored without antisymmetrization.

Here is an explicit derivation of its second moment from the existing Haar moments. For independent Haar quaternions U=u0+i u·sigma and V=v0+i v·sigma, the scalar part of UVU^dagger V^dagger is

    c0=1-2 A,   A=|u×v|².

One way to see the sign and factor2 is to conjugate V's imaginary vector by U, take its scalar product with v in the final V^dagger multiplication, and use Rodrigues' rotation formula; the cross term is orthogonal to v. The S³ imaginary-vector radii have the moments in (5), with independent uniform S² directions. For their relative cosine z, E z²=1/3 and E z^4=1/5. Therefore

    E A=(3/4)^2(1-1/3)=3/8,
    E A²=(5/8)^2(1-2/3+1/5)=5/24,
    E c0=1/4, E c0²=1-4(3/8)+4(5/24)=1/3,
    E|c|²=2/3,  E c_i c_j=(2/9)delta_ij.                   (12)

No external commutator-distribution formula was imported. The independent right sector obeys the same moments. From (10), counting both antisymmetric matrix entries,

    sum_(C,D) L_CD²=16(|c|²+|d|²),
    E sum_(C,D) L_CD²=64/3.                                (13)

These are real squared quantities on Haar links, not absolute squares of complex source coordinates.

## 5. Exact interacting normalization and complete polynomial

For mu!=nu, differentiate (9) twice in each of the two rows. With b=13/32 and c=1/16 the unnormalized top-coefficient tensor is

    E dBerezin T_muC T_muE T_nuD T_nuF
      =4b delta_CE delta_DF
        +2c(delta_CD delta_EF+delta_CF delta_ED).             (14)

The factor4 in the first term is the two independent repeated-square derivatives. The factor2 in the second follows by differentiating P². This uses the unchanged original Grassmann orientation.

For fixed curvature L on the complementary links, contract (14) with L_CD L_EF. Its trace term vanishes by L_CC=0, and L_DC=-L_CD gives

    E_(mu,nu) dBerezin Q_munu²
        =(4b-2c)sum_CD L_CD²=(3/2)sum_CD L_CD².

For a single wedge L_14=ell this reads 3 ell², a direct check of the repeated factors and the crossed minus sign. Now integrate the curvature links using (13): each pair contributes32. Different pairs have already been killed by center parity, and there are six unordered pairs. Hence

    integral dHaar dBerezin S2²=6·32=192,
    (g2²/2) integral S2²=96 g2².                            (15)

The 1/2 is precisely the exponential factorial in (4), not an orientation choice. Together with the vanishing g1 and g2J² terms, the COMPLETE exact answer is

    Z(g1,g2;J)=96 g2²
        +(25/128)sum_mu R_mu²
        +(13/32)sum_(mu<nu) R_mu R_nu
        +(1/16)sum_(mu<nu) P_munu².                         (16)

Every coefficient is explicit. There is no residual Haar integral, undetermined volume factor, Gaussian variance or fitted scalar parameter. Equations (4)–(15) explain every permissible coupling/source type and why the other types vanish. At J=0, real g2!=0 gives Z=96g2²>0: this is an actual interacting normalization, not the earlier toy or a free-source-only witness. The nonzero square also proves the EHC term has not been mistakenly set to zero by the coincident-link simplification.

## 6. Full sixteen-source response at a controlled nonzero source

Let only J_1,4=j be nonzero. Put alpha=25/128 and

    D=Z_axis=96 g2²+alpha j^4.

Assume first D!=0. The normalized mean has just one nonzero component,

    t_1,4=4alpha j³/D,  t_muA=0 otherwise.                  (17)

The FULL unnormalized source Hessian is diagonal at this point. Its entries are 12alpha j² for (1,4), 4alpha j² for (1,i), (15/16)j² for (nu,4), and (13/16)j² for (nu,i), where i=1,2,3 and nu=2,3,4. All off-diagonal entries vanish by direct differentiation of (16), not an assumed mode decomposition.

The connected response C=partial² log Z subtracts t t^T. Its eigenvalues and coordinate eigenspaces are therefore

    lambda_L=4alpha j²(288 g2²-alpha j^4)/D², multiplicity1, (1,4);
    lambda_T=(25/32)j²/D,                multiplicity3, (1,i);
    lambda_P=(15/16)j²/D,                multiplicity3, (nu,4);
    lambda_O=(13/16)j²/D,                multiplicity9, (nu,i). (18)

The labels describe coordinates at this source point, not physical polarizations. They account for all16 entries. No inverse propagator, Hermitian covariance or spin spectrum has been assumed.

An explicit interacting witness is g2=1, j=1, any finite g1. Then

    D=12313/128,   t_1,4=100/12313,
    lambda_L=3683900/12313²,
    lambda_T=100/12313 (three times),
    lambda_P=120/12313 (three times),
    lambda_O=104/12313 (nine times).                         (19)

All are strictly positive real rational numbers, so the full16×16 Hessian is nondegenerate. This is an exact hand calculation, not a numerical tolerance claim. The accepted local holomorphic inverse/Legendre construction now has its nonzero-Z/nondegenerate premises satisfied for an actual interacting instance of the declared microscopic regulator. It supplies a local analytic Gamma near this nonzero-source mean, with gradient equal to the NONZERO source J0 and Hessian C^-1. It is not a zero-source vacuum saddle or a physical scalar potential.

## 7. Exact domains, degeneracies and sign/complex controls

Equation (16) is an entire polynomial in complex g1,g2 and all complex J, using bilinear R and P. Normalized means require Z!=0. Holomorphic responses are symmetric, not automatically Hermitian or positive. On the selected axis with j!=0, the full Hessian is nondegenerate exactly when

    D!=0 AND 288g2²-alpha j^4!=0.                           (20)

For complex parameters the zero-normalization locus on that axis is j^4=-(12288/25)g2²; its Hessian-degenerate locus with D!=0 is j^4=(36864/25)g2². At j=0 and g2!=0, Z=96g2² exists but the entire source Hessian vanishes: the mixed g2J² coefficient really is absent. At g2=j=0 the axis normalization vanishes. These are distinct refusals, not singular-M shortcuts.

For real g2 and real full J, every term in (16) is nonnegative and Z is strictly positive unless g2=0 and every source is zero. At real g2!=0 and nonzero real j, the fifteen nonlongitudinal eigenvalues in (18) are positive. The longitudinal one is positive, zero or negative according as

    j^4 <, =, or > (36864/25)g2².                            (21)

Thus positive real Z does not imply global log-convexity even for THIS actual finite regulator. Along the positive axis t(j) grows up to the zero of lambda_L and then decreases toward zero as j grows; there is no global source-to-mean inverse on that axis. The strictly positive case (19) is a local result and survives in a small real neighborhood, not a global action assertion.

At g2=0,j!=0 the free normalization still exists and the full Hessian is nonsingular, with eigenvalues -4/j², 4/j² (three), (24/5)/j² (three), and (104/25)/j² (nine). Its signature is fifteen positive and one negative on the real axis. Complex nonzero sources can instead be null under the bilinear R/P invariants; for example a single row with components (1,i,0,0) has F=0. No real-positivity statement is extended to arbitrary complex sources.

## 8. What this actually banks and what remains BUILD

This calculation evaluates the complete coefficients of an actual V=1 periodic regulated source partition function. It supplies a real interacting nonzero normalization and a full nondegenerate16-source response point, which were only conditional in the general source construction. It also supplies explicit actual-regulator normalization, degeneracy and nonconvexity controls. The results are independent of auxiliary sigma because the original finite integral was evaluated, and retain the original source instead of a scalar fit.

One-site coincidences, center selection and complementary-link independence are essential to the simplifications. The vanished g1/mixed coefficients are one-site artifacts, not universal statements about the cosmological/EHC interactions, absence of order, gravity or simulation feasibility. A finite source point with positive response is not a gauge-invariant ordered thermodynamic state. The response coordinate multiplicities are not assigned or derived graviton polarizations.

Still BUILD at full original strength: larger-volume coefficients and controlled evaluation/error complexity; physically normalized sources and gauge/state interpretation; zero-source/thermodynamic/ordered-state limits; full tetrad stationarity, constraints and physical fluctuations; microscopic scalar reduction and coupling/cutoff matching; propagating spin2 and other channels, Lorentzian/continuum control; independently derived nonzero physical vacuum magnitude and uncertainty; sampling/RHMC and ordinary native/numerical admission. Neither determinant positivity under its assumptions nor real positivity of this polynomial proves a positive sampling measure or a global real physical effective action. Existing scientific ownership, independent review, protected integration and final human gates remain unchanged.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The coincident one-site coframe is an anticommutator, not zero. The curvature trace has a real symmetric diagonal term; epsilon/coframe antisymmetrization removes it before the curvature-vector average is taken. One-site exact averaging kills g1 and g2J² but leaves the nonzero interacting96g2² coefficient. A complete finite polynomial and the local16-source witness are actual new calculations, while physical state/order, continuum/scalar/modes/magnitude and native qualification remain unconstructed. No no-go, approved deferral or physical completion follows from the finite-volume cancellations.
