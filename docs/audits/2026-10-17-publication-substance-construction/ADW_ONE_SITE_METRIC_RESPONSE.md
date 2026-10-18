# Exact one-site ADW metric sources and ten-component response

17 October 2026. Original manual construction by the publication lead under the microscopic ADW BUILD. **Independently reviewed manual finite-model construction, with the one-site coefficient premise independently accepted.** See the [complete independent review](reviews/ADW_ONE_SITE_METRIC_RESPONSE.md). This note does not establish a physical ordered metric, a graviton spectrum, L1 susceptibility normalization, continuum gravity or vacuum magnitude. No model, coefficient algorithm, numerical/symbolic library or native prover was executed.

## 1. Regulator, premise and invariant observable

Retain the complete original V=1 periodic Euclidean Spin(4) regulator, four barred/unbarred fermion pairs, normalized Haar/Berezin measures, gamma basis, added coincident hopping blocks, plus-exponent and dimensionless couplings of the one-site coefficient construction. In its notation

    T_muA = (1/4) barpsi {gamma_A, Omega_mu^dagger-Omega_mu} psi,
    S = g1 S4 + g2 S2,                         mu,A=1,...,4.

The frozen coefficient premise is the COMPLETE original-action result

    Z_T(J) = D + F(J),     D=96 g2^2,
    F = alpha sum_mu R_mu^2
      + b sum_(mu<nu) R_mu R_nu + c sum_(mu<nu) P_munu^2,
    R_mu=sum_A J_muA^2,   P_munu=sum_A J_muA J_nuA,
    alpha=25/128, b=13/32, c=1/16.                         (1)

There is no complex conjugation in these polynomial invariants. The one-site derivation accounts for the vanishing g1 and g2 J^2 terms, all Haar moments and the nonzero interacting D. Those are essential premises, not independently established by merely differentiating (1). That premise has separate nonauthor mathematical acceptance; see [the complete coefficient review](reviews/ADW_ONE_SITE_COEFFICIENTS.md).

At the single site a Spin(4) transformation U acts by psi->U psi, barpsi->barpsi U^dagger and Omega_mu->U Omega_mu U^dagger. It is Haar-preserving, its barred/unbarred determinant Jacobians are one, and U^dagger gamma_A U=R_AB gamma_B for an R in SO(4). Substitution into the displayed anticommutator gives T_muA->R_AB T_muB. The original S4 and S2 are invariant: det R=1 preserves epsilon_ABCD, while the curvature trace and the two coframes transform together, and gamma5 commutes with Spin(4). No independent rotation of links without the fermions is assumed.

Define the local invariant symmetric composite

    G_munu = sum_A T_muA T_nuA = G_numu.                    (2)

Even T's commute, and R^T R=I proves invariance of G. This is an internal Euclidean delta_AB contraction on this finite regulator. With T=a ehat it is a^2 times the corresponding ehat composite. It is not an already normalized Lorentzian metric, nor a gauge-fixed tetrad expectation. Four independent lattice directions are not a continuum rotational symmetry assumption.

Use ten independent commuting source coordinates H_munu, mu<=nu, with the explicit coupling

    L_H=sum_(mu<=nu) H_munu G_munu,
    Z_G(H)=integral dHaar dBerezin exp(S+L_H).               (3)

Off-diagonal pairs occur ONCE. Equivalently a full symmetric matrix K in sum_mu,nu K_munu G_munu has K_mumu=H_mumu and K_munu=H_munu/2 for mu<nu. This convention matters for all covariance coefficients and coordinate eigenvalues below.

## 2. Exact insertion tensor and zero linear term

Each G contains two T's and hence two barred/unbarred pairs. With only four pairs, the source polynomial is at most quadratic in H. Its possible top-degree terms are g1 S4, g2^2 S2^2/2, g2 S2 L_H and L_H^2/2. Center selection removes g1 as in the premise. The potential linear term g2 S2 L_H also vanishes: a diagonal G gives an odd coframe count in at least one of the two S2 directions, while an off-diagonal G can pass center selection only for the same unordered direction pair as S2. In that latter case its complementary curvature links are independent of the coframes and have zero antisymmetric curvature-vector mean. The symmetric trace was removed by epsilon antisymmetrization BEFORE this average in the one-site derivation. Thus neither S2 nor G was set identically to zero.

Consequently the unnormalized first metric moments vanish at H=0. The second moments require exactly four T insertions; every extra interaction over-saturates. They are fourth J derivatives of F, with no extra Taylor-factor division. For distinct directions mu,nu the exact tensor is

    I(T_muC T_muE T_nuD T_nuF)
       =4b delta_CE delta_DF
        +2c (delta_CD delta_EF+delta_CF delta_ED),           (4)

where I means the unnormalized Haar/Berezin integral; its interaction factors have no effect on this saturated insertion. A single direction instead has

    I(T_muA^4)=24 alpha,
    I(T_muA^2 T_muB^2)=8 alpha,     A!=B.                  (5)

These equations follow by differentiating the fully specified polynomial, including repeated derivatives. They do not assume positive random T variables or use a Wick rule.

Contracting the INTERNAL indices in (4)-(5) gives all ten-component moments:

    I(G_mumu^2)=4(24alpha)+12(8alpha)=75/2;
    I(G_mumu G_nunu)=16(4b)+4(4c)=27,        mu!=nu;
    I(G_munu^2)=4(4b)+20(2c)=9,             mu<nu.         (6)

For the last contraction, in (4) put C=D=A and E=F=B: it is 4b delta_AB+2c(1+delta_AB), summed over sixteen ordered A,B choices. This is different from the diagonal-diagonal contraction. All other distinct-coordinate moments vanish by the link-center parity: two different unordered off-diagonal pairs leave an odd direction count, as does a diagonal/off-diagonal combination. This enumerates the full matrix, not just its trace channel.

## 3. Complete gauge-invariant source polynomial

Order the ten coordinates as four diagonals followed by six mu<nu pairs. Let M be their unnormalized second-moment matrix. In precisely this source basis

    M = diag_blocks[(21/2) I_4 + 27 1_4 1_4^T, 9 I_6].     (7)

The first block has diagonal 75/2 and off-diagonal27, agreeing with (6). The complete source polynomial is

    Z_G(H) = D + Q(H),
    Q(H)=(1/2) H^T M H
        =(75/4) sum_mu H_mumu^2
         +27 sum_(mu<nu) H_mumu H_nunu
         +(9/2) sum_(mu<nu) H_munu^2.                      (8)

No residual Haar integral, uncomputed matrix entry, physical fitting parameter or infinite-volume limit is hidden in (8). The g1 independence and lack of linear H are special one-site facts, not a universal absence of cosmological interaction or metric order. Although a term of the quadratic form can be negative for real diagonal sources of opposite sign, the full Q is positive definite by (7).

The coordinate eigenvalues of M and their actual eigenspaces are

    237/2 : span of equal diagonal coordinates, dimension1;
     21/2 : diagonal coordinates of zero sum, dimension3;
        9 : off-diagonal coordinate subspace, dimension6. (9)

They refer to the ten source coordinates in (3), not to physical mode masses or polarizations. In a Frobenius-orthonormal symmetric-matrix basis the off-diagonal observables are sqrt(2)G_munu and their second moments are18 instead; rank and definiteness persist, numerical coordinate eigenvalues need not. No trace/traceless spin classification is inferred from (9).

## 4. Actual interacting zero-source response and local inverse

For Z_G!=0, normalized mean and connected response are ordinary holomorphic source derivatives:

    q(H)=partial_H log Z_G=M H/(D+Q),
    C_G(H)=M/(D+Q) - (M H)(M H)^T/(D+Q)^2.                (10)

At H=0 and g2!=0,

    q(0)=0,
    C_G(0)=M/(96 g2^2),
    eigenvalues: 79/(64 g2^2), 7/(64 g2^2) (three),
                  3/(32 g2^2) (six).                      (11)

Thus at the actual interacting point g2=1, H=0 (and any finite g1), Z=96 and the complete ten-component response is nondegenerate. For real nonzero g2 it is positive definite as an algebraic matrix. Unlike the nonzero-tetrad-source witness, this metric-observable local inverse is at zero SOURCE. Its mean metric is nevertheless the ZERO matrix, which is degenerate and supplies no physical spacetime background.

The holomorphic inverse-function theorem now gives a local inverse H(q) near q=0. Choose a local log branch; define Gamma_G(q)=H(q)^T q-log Z_G(H(q)). Direct differentiation gives

    partial_q Gamma_G=H(q),
    partial_q Gamma_G(0)=0,
    Hessian Gamma_G(0)=96 g2^2 M^-1.                       (12)

This is a constructed local stationary metric-composite effective function at a degenerate zero metric, not the claimed physical tetrad/scalar effective potential. Real-positive Hessian for real g2 does not establish a positive underlying sampling measure. The metric variable does not contain an invertible tetrad, continuum derivative structure, analytic Lorentzian continuation or gravitational constraints.

For comparison the joint original tetrad/metric generating function is also finite:

    Z(J,H)=D+F(J)
      +sum_(mu<=nu) H_munu sum_A partial_(J_muA) partial_(J_nuA) F(J)
      +(1/2) H^T M H.                                    (13)

The third term is degree J^2 H; the last is already its saturated double insertion. Extra terms exceed four pairs. At J=H=0 the sixteen T means and ten G means vanish. The T-T response block is zero (there is no J^2 term), the T-G block is zero (there is no JH term), and the G-G block is M/D. Hence the full26-observable response has rank10. Introducing the invariant composite does NOT establish an invertible full tetrad response at the zero-source point.

## 5. Exact finite controls and explicit zero-free neighborhood

All formulas are bilinear holomorphic polynomials/rational functions; arbitrary complex sources do not inherit positivity. A matrix determinant lemma applied to (10) gives, wherever Z=D+Q!=0,

    det C_G = det M (D-Q)/(D+Q)^11,
    det M=(237/2)(21/2)^3 9^6.                            (14)

Thus the full metric Hessian is nonsingular exactly when D+Q!=0 and D-Q!=0. At H=0,g2=0 normalization fails; it must not be assigned a finite susceptibility by cancellation. For real g2!=0 and real H, Z is strictly positive. By congruence with M^(1/2), the response has nine positive directions and one direction with sign D-Q. At Q=D it is rank9, and for Q>D it has nine positive and one negative directions. This is an inertia statement, not the unwhitened coordinate eigenvalues at a nonzero general source. The positive polynomial therefore does not imply global log-convexity. At real g2=0 and nonzero real H it is invertible with inertia(9,1), even though its zero-source normalization is absent.

An explicit complex polydisc bound is available without numerical evaluation. If all ten |H_i|<=r, (8) gives

    |Q(H)| <= [4(75/4)+6(27)+6(9/2)]r^2 = 264r^2.         (15)

For g2=1 take r=1/2: 264r^2=66<96=D. Throughout that closed polydisc both D+Q and D-Q are nonzero, so the normalization and full metric response are nonsingular. This proves a finite zero-free/nondegenerate neighborhood. It does not assert that a nonsingular Jacobian on an entire complex polydisc supplies a globally one-to-one map there; only the local inverse in (12) is claimed.

Complex normalization and response-degeneracy controls are distinct. Along any real nonzero source direction scale H by a complex number z. Then Q(zH)=z^2 Q(H). For D!=0, choosing z^2=-D/Q(H) gives Z=0; choosing z^2=D/Q(H) gives nonsingular normalization but singular response. These are exact algebraic controls, not measured model failures. Degree saturation also forces unnormalized moments with three or more metric insertions to vanish; normalized cumulants of order>=3 need not vanish, because log Z is not quadratic.

## 6. Scientific increment and remaining construction

This banks an explicit invariant observable, complete ten-source partition, exact response and a local stationary composite effective function for the declared interacting finite action, after independent mathematical acceptance of both notes. It goes beyond a generic finite coefficient algorithm and avoids treating auxiliary fields as physical order. It supplies a new actual microscopic finite susceptibility; its coordinate normalization is completely specified.

It does not identify this susceptibility with L1's scalar RPA channel or dimensionless adopted window. L1 still needs its own physical projector, state, normalization, coupling, dynamics and transport/frequency matching. The D1/E1/E2 dispersive-law obligation remains separate. A finite invariant Euclidean zero-metric response is not a calibrated physical susceptibility or a derived nondegenerate gravitational vacuum.

Full ADW BUILD remains: larger volume/controlled evaluation and errors; physically normalized/gauge-interpreted sources and state; nondegenerate physical background and thermodynamic/ordered limits; full tetrad stationarity and constrained dynamical fluctuation spectrum; scalar reduction and microscopic coupling/cutoff matching; propagating spin2, Lorentzian/continuum control; independently derived nonzero physical vacuum magnitude and uncertainty; sampling/positive measure and native qualification. One-site cancellations do not prove infeasibility or authorize deferral. Independent mathematical review, protected source integration, actual validation and publication/human gates remain distinct.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The actual one-site tetrad zero-source Hessian is degenerate, but the explicitly constructed invariant metric-composite response is not. Its stationary mean is zero and therefore remains physically degenerate. A nondegenerate observable-source response does not imply a nondegenerate spacetime metric, identify ten coordinate directions with gravitational modes, discharge L1's different susceptibility contract or prove a positive sampling measure. No prior false physical claim is restored by these finite algebraic results.
