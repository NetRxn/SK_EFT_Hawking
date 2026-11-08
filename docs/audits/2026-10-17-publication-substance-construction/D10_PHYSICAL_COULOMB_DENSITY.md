# One-electron Coulomb density constrained search and attained variational principle

17 October 2026. **Independently reviewed manual construction; [complete nonauthor mathematical/source review](reviews/D10_PHYSICAL_COULOMB_DENSITY.md). Native representation and the full general many-electron objective remain OPEN BUILD.** This advances the original D10/B1 physical DFT construction in a declared continuum Coulomb special case. It is not a new Lean inhabitant, native proof, general many-electron Hohenberg–Kohn theorem or completed publication gate. No model, numerical/symbolic software, tests or prover were run.

## 1. Actual source boundary and physical carrier

The current molecular source defines nuclear attraction minus the charge-over-distance sum and pairwise electron repulsion. Its unconditional apex in `lean/SKEFTHawking/CoulombRelativeBound.lean` constructs relative-bound constants and proves self-adjointness of the closed kinetic operator plus molecular multiplication potential. Kinetic closure and Coulomb relative boundedness are actual results, not open `hkin`/`hrel` inputs. This does not automatically construct a ground state or density functional for arbitrary electron/nuclear data.

Here take one spinless electron and one fixed nucleus at the origin, charge Z>0, in three-dimensional Euclidean space. Use atomic units hbar=m_e=e²/(4pi epsilon_0)=1. The nuclear position is fixed; there is no electron–electron or nuclear–nuclear term. The physical Hilbert space is L²(R³;C), its form domain H¹(R³;C), and normalized states form

    S={psi in H¹(R³;C): integral |psi|² dx=1}.
    T[psi]=(1/2) integral |grad psi|² dx,
    q_Z[psi]=T[psi]−Z integral |psi|²/|x| dx.              (1)

All functions/densities are identified almost everywhere. Values at x=0 are immaterial. This choice is not the antisymmetric N-electron carrier for N>1. The matching of atomic-unit continuum objects to the current Lean `SpaceDQuantumSystem` constants/domains remains an explicit native bridge, not a consequence of using the same operator name.

## 2. Domain, origin and infinity controls

The punctured smooth core C_c^infty(R³\{0};C) is dense in H¹(R³;C). First approximate an H¹ function by outer cutoffs and convolution: cutoff-gradient errors are bounded by C/R times the L² tail, while ordinary translations of a function and each weak derivative are L²-continuous, giving convergence of mollification in H¹. For a resulting smooth compact f, remove the origin with a radial cutoff chi_epsilon that is zero inside epsilon, one outside 2epsilon, and has gradient bounded by C/epsilon. Boundedness of f and grad f on its compact support gives removed L² error O(epsilon^(3/2)), the removed original-gradient error O(epsilon^(3/2)), and the extra f grad chi error O(epsilon^(1/2)). All vanish. A diagonal approximation supplies the stated punctured core; no boundary condition is imposed on general H¹ states at a point.

On that core, divergence(x/|x|²)=1/|x|². Integration by parts in the nonnegative square yields

    0 <= integral |grad u+(x/(2|x|²))u|²
       = integral |grad u|²−(1/4) integral |u|²/|x|².
    ||u/|x|||_2 <= 2 ||grad u||_2.                        (2)

For complex u the cross term uses Re(conj(u) grad u)=grad|u|²/2. Approximation extends (2) to every H¹ function: the weighted approximants are L²-Cauchy by (2), and an a.e.-convergent subsequence identifies their limit with u/|x|. Consequently

    integral |u|²/|x| <= ||u/|x|||_2 ||u||_2
                         <=2 ||grad u||_2 ||u||_2.       (3)

Thus every potential integral in (1) is finite. It is continuous on H¹, since its diagonal difference is bounded by ||u−v||_2 times ||(|u|+|v|)/|x|||_2, which is at most 2||u−v||_2(||grad u||_2+||grad v||_2). This also proves the needed weighted-form convergence; singular integral continuity is not assumed from unweighted L² convergence alone.

For any eta>0, Z times (3) is bounded by eta||grad u||²+(Z²/eta)||u||². Choosing eta<1/2 shows that a sufficiently positively shifted q_Z norm is equivalent to the H¹ norm. The densely defined form is therefore closed and semibounded. This identifies the usual closed Coulomb form; its associated self-adjoint Schrödinger realization is used below. The general closed-form representation theorem is an analysis theorem, not an assumption that a ground state exists.

## 3. Completed square and exact ground state

Let rhat=x/|x| off zero and assign any bounded value at zero. Its distributional divergence is 2/|x|, without a delta term: for a smooth test function the inner-sphere flux is O(epsilon²) and tends to zero. On the punctured core the inner and outer boundary terms vanish directly. Expanding and integrating the cross term gives

    (1/2) integral |grad psi+Z rhat psi|²
      = (1/2)||grad psi||²+(Z²/2)||psi||²
          +(Z/2) integral rhat . grad|psi|²
      = q_Z[psi]+(Z²/2)||psi||².                         (4)

Extend (4) to all H¹ by the preceding core density and weighted continuity. Multiplication by bounded rhat is L²-continuous, so the right-hand square converges as well. No pointwise boundary trace of a rough H¹ function, unspecified infinity flux or formal integration by parts across a Coulomb singularity is used. It follows for normalized states that q_Z[psi]>=−Z²/2.

Define the actual wavefunction

    phi_Z(x)=(Z³/pi)^(1/2) exp(−Z|x|).                   (5)

It is in H¹, with weak gradient −Z rhat phi_Z; the possible nonsmooth point at zero creates no distributional surface mass. Radial integration, using the elementary integrations by parts integral_0^infty r² exp(−a r)dr=2/a³ and integral_0^infty r exp(−a r)dr=1/a² for a>0, gives

    ||phi_Z||²=4Z³ * 2/(2Z)³=1,
    T[phi_Z]=Z²/2,
    integral |phi_Z|²/|x|=4Z³/(2Z)²=Z,
    q_Z[phi_Z]=−Z²/2=:E0(Z).                             (6)

These are manual exact integrals, not numerical tests. The lower bound (4) is attained, so the ground energy is produced rather than specified as a carrier field. Polarization of (4) and (grad+Z rhat)phi_Z=0 give q_Z(phi_Z,eta)=E0<phi_Z,eta> for every eta in H¹. Hence phi_Z belongs to the operator associated with the closed form and is its eigenvector. Equivalently the distributional identity Delta phi_Z=(Z²−2Z/r)phi_Z has an L² right-hand side; Fourier characterization implies phi_Z in H², and (−Delta/2−Z/r)phi_Z=E0 phi_Z. The form lower bound rules out any lower spectrum. This uses the declared Coulomb realization, not a newly verified PhysLib identification.

Equality in (4) requires grad psi+Z rhat psi=0 almost everywhere. On every bounded ball, exp(Zr) is a bounded Lipschitz multiplier with bounded gradient, so f=exp(Zr)psi is H¹_loc and has zero weak gradient. Poincare's inequality on overlapping balls makes f a single complex constant on connected R³. Thus every normalized minimizer is exp(i theta)phi_Z, and every ground-state eigenvector is in that one-dimensional eigenspace. Conversely all these phases attain E0. No assertion is made for Z=0: the displayed normalized exponential then does not exist and the free operator has no normalized zero-energy minimizer.

## 4. Actual density representability and the modulus inequality

Use the physical admissible density set

    D={rho measurable: rho>=0 a.e., integral rho=1,
                       sqrt(rho) in H¹(R³;R)}.            (7)

For psi in H¹ complex, set u_epsilon=sqrt(|psi|²+epsilon²)−epsilon. This subtraction is essential on infinite volume: u_epsilon(0)=0 as a function of the two real components, 0<=u_epsilon<=|psi|, and it is in L². For fixed epsilon>0 the composition is smooth with derivative bounded by one. The Sobolev chain rule follows here by smooth H¹ approximation: bounded first derivatives control the derivative difference, and dominated convergence on a subsequence identifies the limiting composed gradient. It gives

    grad u_epsilon=Re(conj(psi) grad psi)/sqrt(|psi|²+epsilon²),
    |grad u_epsilon|<=|grad psi| a.e.                      (8)

Dominated convergence gives u_epsilon→|psi| strongly in L². The gradients are L²-bounded; weak compactness and the test-function definition of weak derivative identify a weak limit with grad|psi|. Lower semicontinuity then proves the integrated diamagnetic/modulus inequality

    |psi| in H¹,    integral |grad|psi||²
                          <=integral |grad psi|².        (9)

This proof needs no unjustified phase derivative at zeros. It applies to the ordinary zero-magnetic-field scalar kinetic energy used here; no magnetic/vector-potential claim is imported.

For normalized psi, rho=|psi|² lies in D by (9). Conversely for every rho in D, the real nonnegative state psi_rho=sqrt(rho) is an actual normalized H¹ witness with density rho. Thus D is exactly the density image of S in this one-electron pure-state model. Every constrained-search fiber is nonempty, not merely declared bounded below.

## 5. Exact attained constrained search and density variational principle

For rho in D define the nonempty real energy set

    A_rho={T[psi]: psi in S, |psi|²=rho a.e.},
    F_LL[rho]=inf A_rho.                                  (10)

It is bounded below by zero and contains the finite value T[sqrt(rho)]. Inequality (9) bounds every member below by this same value, and the square-root witness attains it. Therefore

    F_LL[rho]=(1/2) integral |grad sqrt(rho)|²,             (11)

with an actual minimizer for every admissible density. The square-root form (11) is used throughout; no undefined quotient by rho at its zeros is required. There is no electron–electron energy for N=1.

The nuclear contribution depends only on density and is finite by (3) applied to sqrt(rho). For every state in its fiber,

    q_Z[psi]=T[psi]−Z integral rho/r,
    E_Z[rho]:=F_LL[rho]−Z integral rho/r=q_Z[sqrt(rho)].    (12)

Combining (4), (6) and (11) proves the physical density statements

    E_Z[rho]>=E0(Z)=−Z²/2,
    rho0,Z(x)=(Z³/pi)exp(−2Zr) in D,
    E_Z[rho0,Z]=E0(Z),
    E_Z[rho]=E0(Z) iff rho=rho0,Z a.e.                    (13)

For the last implication, sqrt(rho) is a nonnegative state attaining (4), hence a constant-phase phi_Z; its nonnegativity fixes that phase and normalization fixes the magnitude. The reverse follows from the explicit density. Thus lower bound, attainment and unique minimizing density are derived from an actual continuum form and state, not restated from nondegen/ground fields. At rho0 the fiber's attained universal kinetic value is Z²/2, and the physical energy decomposition is exactly E0=Z²/2−Z*Z. This also explicitly relates the constrained search to the chosen ground state's universal energy in this case.

## 6. Strict cross inequalities: actual family versus missing general proof

Nondegeneracy of a ground state alone does not show that a ground state of another potential is a different state modulo phase. A common state can make Rayleigh–Ritz equality hold. Even constant shifts already show why potentials must be compared modulo constants; exclusion of common states for more general distinct potentials requires additional argument, such as suitable unique-continuation/nonvanishing hypotheses plus the eigen-equations. Neither current scalar-order reductio nor nondegeneracy by itself supplies it.

In the present charge family this issue can be resolved directly. For Z,W>0,

    q_Z[phi_W]=W²/2−ZW,
    q_Z[phi_W]−E0(Z)=(Z−W)²/2.                            (14)

Hence the cross inequality is strict when Z!=W, and analogously on exchanging them. Their explicit positive radial densities are different (equality a.e., then continuity off zero, forces equality of their exponential radial slopes). This proves a nonvacuous potential-to-ground-density injectivity result within the fixed-centre Coulomb-charge family; it is not the general HK theorem for arbitrary external potentials or antisymmetric interacting many-electron states. No general uniqueness conclusion is inferred by merely assigning strict inequalities to a structure.

## 7. Explicit coefficient rescaling to the source convention

Atomic units are not a substitution of the actual Lean constant hbar by one. For an arbitrary kinetic coefficient alpha>0 and the source potential coefficient Z>0, set

    q_alpha,Z[psi]=alpha integral |grad psi|²−Z integral |psi|²/r,
    k=Z/(2alpha),
    q_alpha,Z[psi]+[Z²/(4alpha)]||psi||²
        =alpha integral |grad psi+k rhat psi|².            (15)

Equation (15) follows by the same proved H1 integration identity: the cross coefficient is −2alpha*k=−Z and the constant is alpha*k²=Z²/(4alpha). All origin/infinity/density arguments above apply unchanged; no numerical rescaling program is needed. The actual normalized state and its exact energies are

    phi_alpha,Z=(k³/pi)^(1/2) exp(−k r),
    T_alpha=alpha*k²=Z²/(4alpha),
    V=−Z*k=−Z²/(2alpha),
    E0=−Z²/(4alpha),
    F_LL,alpha[rho]=alpha integral |grad sqrt(rho)|².       (16)

Normalization is the same radial integral with k in place of Z. The same square-root fiber witness proves (16), and (15)'s equality equation proves uniqueness and the corresponding unique ground density. Taking alpha=hbar²/(2m), m>0 and hbar>0, gives k=mZ/hbar² and E0=−mZ²/(2hbar²). Here Z denotes the actual coefficient of −Z/r, not automatically a dimensionless atomic number after units are restored. With fixed alpha, cross-charge energies differ from the ground bound by (Z−W)²/(4alpha), preserving the strict-family comparison.

For N=1 and a singleton nucleus at the origin, the source molecular potential has no electron–electron pair term and agrees with −Z/r almost everywhere; its assigned value at the singular point is irrelevant to the continuum form. The kinetic source is the mass-scaled momentum-square operator, not a literal hbar=1 operator. These coefficient identities specify the required normalization for a future bridge. They do not identify actual Lean Hilbert spaces, measures, weak-derivative/form/operator domains or construct a native state/groundness proof. That representation and unit/domain correspondence remains to be supplied explicitly.

## 8. Exact relationship to the current Lean interfaces

All three DFT module bodies were read. `GroundStateData` contains n,E,F and a decomposition field, not an actual normalized state/operator/groundness proof. Our explicit values provide manual physical candidates for those fields, but they have not been represented or proved in Lean. `hohenberg_kohn_uniqueness` and its injective companion additionally take BOTH strict cross inequalities. Their real cancellation proof remains genuine; the module header's explanation that nondegeneracy alone supplies them is insufficient in the possible-common-state case.

`DensityVariational` quantifies its real-valued Ev over every function X→R, with ground and unique-infimum attainment already fields. Our theorem (13) is instead over the proved admissible density set D. A native bridge must use an admissible subtype/indexed functional, or a well-defined extended-energy functional assigning +infinity to invalid densities, and actually prove its semiboundedness/attainment/uniqueness. Arbitrarily assigning real energies to invalid densities just to inhabit an all-functions carrier would not construct the physical functional.

`LevyLiebData` likewise asks only a real bounded-below fiber field for every real-valued function; it does not require each fiber nonempty. Empty fibers satisfy bounded-below vacuously, but their conditionally-complete Real infimum is not physical +infinity. We avoid that trap by (7)–(10), with an explicit sqrt witness and a nonempty finite energy set. The existing equality theorem assumes a minimizing witness and equates the infimum to its TW value; it does not mention a separately defined HK functional. Equation (13)'s conclusion and (11)'s witness are proved here before any prospective packaging. None of this edits the interfaces, constructs a native inhabitant or clears the historical carrier/naming/infrastructure findings.

## 9. Scope, ownership and next construction

This is the independently accepted physical Coulomb special case. The separately accepted [general finite-N construction](D10_MANY_ELECTRON_CONSTRAINED_SEARCH.md) and [full independent review](reviews/D10_MANY_ELECTRON_CONSTRAINED_SEARCH.md) now supply antisymmetric finite-spin total-density representability, repulsive-Coulomb form bounds, EVERY-admissible-fiber attained constrained search and molecular infimum reduction. These manual results are completed, not missing extensions. The separately accepted [finite-Coulomb HK construction](D10_COULOMB_HOHENBERG_KOHN.md) and [full original independent review](reviews/D10_COULOMB_HOHENBERG_KOHN.md) now establish density-to-potential uniqueness modulo constants and genuine strict cross inequalities for finite-N finite-spin molecular Coulomb inputs with existing ground states, including degeneracy and without wavefunction UCP. Native state/density/operator/units/spin integration, appropriate binding/existence and unique-density specializations remain the original D10/B1 BUILD. Arbitrary-potential UCP is a separate optional extension, not an added Coulomb B1 gate. Self-adjointness alone does not imply binding. Genuine hkin/hrel and finite-dimensional hreal progress remain credited.

The Physics Publication Remediation lead retains the full original objective. Independent manual verification of the domain/equality arguments is complete in the linked nonauthor review. The separate general-N extension and its full independent mathematical verification are now complete in the linked note/review. Independent manual review of the separate finite-Coulomb HK continuation is also complete in its linked full original report. Next: deliberate admissible-a.e.-density/native form/state/operator/unit/spin integration and native common-state/strictness lemmas for admitted bound inputs, with appropriate binding/existence and any unique-density specialization supported by fresh independent native evidence. The two owning roadmaps record those obligations and actual historical source progress. Dependency upgrades retain their original user-authorization/clean-branch/blast-radius gates; this manual note neither requires nor authorizes one. No 500-line budget, documented wall, disclosure, renamed theorem or source-only pass closes the scientific objective. Ordinary coherent accepted increments may integrate without waiting for the complete programme, through the existing workflow.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The June roadmaps' planned hkin/hrel/hreal labels and global COMPLETE framing are stale relative to the actual source and dated reviews. Their achievements are preserved; the physical DFT bridge remains open. Current uniqueness assumes both strict cross inequalities, and its header's nondegeneracy-only explanation does not exclude a common state. The one-electron construction derives its actual variational facts but does not create a Lean inhabitant or general many-electron closure. Original historical results and failures retain their actual scopes.
