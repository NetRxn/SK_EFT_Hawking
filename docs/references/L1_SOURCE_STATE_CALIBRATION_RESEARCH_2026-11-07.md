# L1 physical source/state bridge: a bounded calibration obstruction and next equations

Date: 2026-11-07. Coordination: [issue #121](https://github.com/NetRxn/SK_EFT_Hawking/issues/121).
Status: cloud research for independent mathematics and physics/source review. This is not a physical construction, settled universal no-go, scientific implementation, publication claim, or completed wave.

## Authority and inspected inputs

This handback consumes [PR120](https://github.com/NetRxn/SK_EFT_Hawking/pull/120), snapshot `c31f0f596b807a8c4ed1325393fe35dedf72e8ef`; the [W0–W5 roadmap](https://github.com/NetRxn/SK_EFT_Hawking/blob/c0a775c942fc62528fec2d0b645e4dfe858ae61c/docs/roadmaps/L1_Physical_Bridges_Roadmap.md) in PR115; and the following PR113 snapshot `864f4ec25667e345b90e8a8570a00c10c17b198f` records. The filenames below are relative to `docs/audits/2026-11-05-l1-physical-bridges/` at that immutable snapshot:

- `COMMON_SOURCE_MATTER_INTERFACE.md`, `PHYSICAL_MATCHING_DECOMPOSITION.md`, and `PHYSICAL_MATCHING_ACCEPTANCE.md`: common normalized functional and G,A,B,D/partial-Legendre interface.
- `COLLECTIVE_BODY_PARITY.md`, `COLLECTIVE_BODY_ACCEPTANCE.md`: already accepted finite-volume body/tangent selection rule, not a new result here.
- `ORIGINAL_KINETIC_NORMALIZATION_CORRESPONDENCE.md` and its acceptance: especially Eqs.30–33, actual source-dependent physical intertwining and calibration covariance.
- `ORIGINAL_ONE_SLICE_SOURCE_KERNEL_ACCEPTANCE.md` and its reconstruction research note: full temporal sources retain defect and pair-carrier terms.
- `ORIGINAL_BOUNDARY_ONLY_OPERATORS_ACCEPTANCE.md`, `ORIGINAL_TRANSFER_POSITIVE_PROCESS_RECONSTRUCTION_ACCEPTANCE.md`, and `ORIGINAL_STATE_CANDIDATE_QUALIFICATION.md`: algebraic annihilators/conditional channels do not supply a physical null quotient, original causal evolution, or a positive source map.

The repair map at that PR113 snapshot and main's AGENTS.md, CLAUDE.md and wave pipeline were read. Publication owns original B3, ordinary repairs, canonical gates and integration. Default-branch search for reconstruction/connection was only a breadth screen, not an exhaustive theorem or branch search. No notebook, harness, worktree, evaluator, Lean or paused execution was accessed.

## 1. The existing physical candidate and its finite-branch obstruction

The source-grounded candidate is the collective quartet metric G=<Q>, coupled prospectively to matter through the same collective metric. It is different from the already constructed positive-body configuration family M=gbar+lambda Q. Neither family has been identified with a positive physical state for the original theory.

Use precisely the accepted parity contract: finite N, eight Grassmann generators per site, original closed action S=g1 S4+g2 S2, degrees eight/four, exchange-compatible Spin(4) product Haar/boundaries and fixed Berezin top degree 8N. Set external composite J=0, no matter determinant, and retain the prescribed world-coframe deformation j. Q is the reflection-even quartic tetrad pair. For the reflected change of variables S4,S2 both change sign. Saturation with m S4, n S2 and k Q insertions requires 2m+n+k=2N; reflection requires m+n even, hence m=k modulo two.

The accepted consequence is G(j;0,g2)=0 and B(j;0,g2)=0 wherever full Z is nonzero, with B=partial_j G including transported-Q contacts. It applies to the existing normalized four-site example. The raw numerator identity also holds at sixteen sites; it does not establish the sixteen-site denominator. A and D need not vanish. A positive two-time scalar moment is not an evaluation of the full contact-inclusive D=W_jj.

A direct calibration consequence is now explicit. Let a proposed source-independent physical metric chart be g_phys=F(G), C1 near G=0, with finite derivative. Then

    partial_j g_phys = (dF)_G B = 0                     (1)

on this branch. For the previously contemplated constant linear calibration F(G)=c_Q G, the background itself is zero/degenerate. Adding a fixed nonzero F(0) supplies a body but still leaves (1) zero. It is consequently impossible, under this chart restriction, to identify j with a nonzero ordinary metric-strain tangent at this finite-branch point.

This is a rank obstruction to THIS identification, not a physical-state no-go. An explicitly j-dependent F, configuration body, source admixture, matter backreaction or source-selected thermodynamic phase changes the premises and must be derived separately. Singular F, divergent calibration or a nonuniform limit evades the C1 finite-derivative hypothesis and requires its own domain/error argument. A nondegenerate metric at zero response also need not be impossible: the conflict is specifically with identifying this j as its nonzero strain tangent.

## 2. A discriminating same-regulator mixed-coupling calculation

At fixed g2!=0 put x=g1/g2^2. The accepted finite-polynomial decomposition gives

    Z=g2^(2N) z(x,j),   N_Q=g2^(2N-1) q(x,j),
    G=g2^-1 q(x,j)/z(x,j),                              (2)

with z even and q odd in x. Where z(0,j)!=0, the normalized finite-volume functions are analytic in x. In a fixed independent composite basis, including cell weights in J, write

    G=g2^-1 [x u1(j)+O(x^3)],    u1=q_x(0,j)/z(0,j),
    B_a=g2^-1 [x b1,a+O(x^3)],   b1,a=partial_ja u1,
    A=g2^-2 [a0+O(x^2)],        D=d0+O(x^2).             (3)

The scaling of A follows by saturating the two-Q numerator and subtracting GG^T. D uses the full prescribed dimensionless coframe source, so the common g2^(2N) factor cancels in its log derivatives. Coefficients and remainders refer to the SAME finite regulator and complete denominator. They are not uniform thermodynamic/continuum estimates.

If, additionally, a0 is nonsingular on a derived physical-coordinate quotient, local inversion gives the conditional identity

    B^T A^-1 B = x^2 b1^T a0^-1 b1 + O(x^4),
    Gamma_jj = -d0 + O(x^2),                            (4)

with Gamma=JG-W as in the accepted decomposition. The inverse and coordinates cannot be chosen by discarding an inconvenient direction. No positivity of a0 is assumed. Equation (4) is analytic matrix algebra, not a calculation of a0,b1,d0 or proof that this quotient exists.

For an explicit finite-domain error diagnostic, suppose on |x|<=r the derived quotient satisfies sigma_min(g2^2 A)>=alpha>0 and ||g2 B||<=beta |x|. Then

    ||B^T A^-1 B|| <= beta^2 x^2 / alpha.                (5)

Use the Euclidean operator norm for these real symmetric response blocks. This follows from submultiplicativity and ||(g2^2 A)^-1||<=1/alpha. It does not provide alpha,beta or r. If a pole/singularity enters the domain, the bound is unavailable.

A specific extra hypothesis sometimes implicit in calling the dressed response “the metric response” would be Gamma_jj=0: no independent quadratic j response at fixed G. The accepted Hessian formula then requires

    D = B^T A^-1 B.                                     (6)

At x=0 it requires D=0; if an actual full D there is nonzero, that is a contradiction to this extra hypothesis. Even if D=0, it does not restore the missing tangent in (1). No nonzero d0 is asserted here. Conversely, if Gamma has independent j dependence, (6) is not required: D can remain nonzero without reconstructing a collective metric response.

The actionable next inputs are the full tensor q_x(0,j), its j derivatives, z and its nonzero neighborhood, and a0 on the actual quotient. Selected words and a scalar path sign cannot determine them. This specifies a diagnostic for the existing owner; it neither launches a coefficient campaign nor chooses g1 to meet a target interval.

## 3. Exact physical transfer/source equation still owed

For the original source family s, the physical reconstruction must satisfy the accepted Eq.30

    I_out(s) L(s) = T_phys(s) I_in(s).                   (7)

No coefficient norm, auxiliary adjoint, annihilator ideal, global Ward identity or conditional CPTP channel supplies I or T_phys. The physical domain, null relations, positive pairing, reality/product, observable representation, opposite cut and periodic sewing must be justified. A Hilbert transfer realization alone must also reproduce the original periodic supertrace/source functional; replacing that sewing with an ordinary positive thermal trace is an extra assertion.

On a C2 common domain, differentiation of (7) requires

    I_out,a L + I_out L_a = T_a I_in + T I_in,a,

    I_out,ab L + I_out,a L_b + I_out,b L_a + I_out L_ab
      = T_ab I_in + T_a I_in,b + T_b I_in,a + T I_in,ab. (8)

These are necessary compatibility equations, not an existence theorem. L_a,L_ab are the actual original kernels: retain Bopp/coherent ordering contacts, time-mixing frame jets, action/measure/regulator variations and both interfaces. For L=L1 L0, L_ab has all four placements L1_ab L0+L1_a L0_b+L1_b L0_a+L1 L0_ab. The diagnostic source-restricted single-slice factorization cannot replace this full family.

For a concrete future candidate in which one cut has a fixed finite-dimensional derived quotient and I_s is a C2 isomorphism onto a fixed physical space, set C_a=I_s^-1 partial_a I_s. Then T=I L I^-1 implies

    I^-1 T_a I = L_a + [C_a,L],
    I^-1 T_ab I =
      L_ab+[C_b,L_a]+[C_a,L_b]+[partial_b C_a,L]
                                +[C_b,[C_a,L]].         (9)

Direct differentiation proves these formulas. Equality of mixed derivatives uses
partial_b C_a-partial_a C_b=[C_a,C_b]. Thus dropping reconstruction-map jets amounts to an additional choice, not a consequence of (7). Equations (9) apply only to that isomorphic fixed-quotient special case; general rectangular maps require (8). No such quotient, I_s or physical metric operator has been constructed here.

## 4. Absolute calibration and the precise B3 ambiguity

At fixed finite calibration, J=c_Q K gives W_KK=c_Q^2 A for a constant linear physical source conversion. More generally, with all action/measure/regulator dependence included in microscopic coordinates theta(K),

    W_KaKb = theta_i,a W_{theta_i theta_j} theta_j,b
                                  + W_{theta_i} theta_i,ab. (10)

This is the chain rule. Additional prescribed source-only normalization contributes its own derivatives. The second term cannot be inferred from connected covariance alone; volume, tensor projection and units remain necessary. Along the accepted normalization ray, c_Q rescales to compensate W_JJ suppression; it is not determined by it.

To specify B3 one must select from the intended physics which kernel is meant: collective connected A, its inverse Gamma_GG, dressed contact-inclusive D, the fixed-G remainder Gamma_jj, or a projected momentum coefficient of an actual physical effective/retarded kernel. These are distinct; (4)–(6) expose a finite-branch test of conflating them. A dimensionless-strain static Hessian per four-volume has mass dimension four; its p^2 coefficient, if a controlled expansion exists, has dimension two. This already accepted dimensional distinction rules out inferring the original Lambda^2/(16 pi^2) normalization from a zero-momentum scalar number alone.

No absolute c_Q, lattice/time/hbar scale, matter kinetic residue, physical subtraction, derivative expansion or approximation error is derived here. The required [0.1,10] interval remains a result to derive or obtain a specific evidence-backed disposition for. Source/coupling selection to force it is excluded.

## 5. Primary-source check and conclusion scope

- [Vladimirov–Diakonov 1208.1254v2, VIII, Eqs.77–79](https://arxiv.org/html/1208.1254v2#S8) explicitly introduces a source for the composite metric and its expectation/Legendre transform. Its Gamma=W-GJ has the opposite sign from this repository's Gamma. This supports the collective-source target; it supplies no original-benchmark physical reconstruction or absolute calibration.
- [Volovik 2312.09435v2, III, Eqs.18–22](https://arxiv.org/html/2312.09435v2#S3) proposes the quartet metric even with zero tetrad mean and distinguishes it from the tetradic contribution. It motivates the candidate, but does not calculate our regulated G,A,B,D or prove a positive transfer/state for it.
- [Moore–Sohrabi 1007.5333v3, II–III, Eqs.9–15](https://arxiv.org/html/1007.5333v3#S2) defines metric-derived retarded functions with contact terms and momentum derivatives. Its equilibrium conformal-fluid setting is a methodological comparison; no hydrodynamic or Lorentzian correspondence is imported to this benchmark.

Primary HTML bodies were read in the cloud. Repository acceptance records were consumed as scoped accepted inputs; underlying archives and scientific contractions were not reproduced. Equations (1), (3)–(6), (8)–(10) are elementary conditional deductions/interface expansions offered for independent review. Equation (2), the parity vanishing and the G,A,B,D Hessian decomposition are reused accepted work, not claimed discoveries.

The present conclusion is a precise obstruction to a source-independent smooth collective-metric calibration of j on the specified finite pure-g2 branch, plus a mixed-coupling discriminant and explicit reconstruction/source jets. It does not exclude source-selected phases, quantum-link reconstructions, nonperturbative branches or other physical products. No realized positive state, B3 value, tensor pole, photon cone, speed relation or arrival-time prediction follows. Those physical obligations and all applicable scientific/project gates remain open. This research handback changes no formula API, parameter registry, theorem, manuscript claim, ownership ledger or gate state.
