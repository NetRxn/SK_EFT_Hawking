# Independent B8 Brownian Novikov construction review

Reviewer: publication_b6_fdt_review, fresh nonauthor for this B8 branch. I did not author the candidate or repair its mathematics. Candidate: complete CONSTRUCTION.md SHA256 `a32c8cf660814e55f8aafc9c26caa0663cf5d78b33b5018a931bbd30a3209fc1`; author REPORT `1881350edb7397c3533e8c903c9ed03df82d51b87a2f46cbd65e79614e612637`.

**Verdict: SCOPED_FULL_MANUAL_BROWNIAN_NOVIKOV_CONSTRUCTION_ACCEPT. No mandatory mathematical correction found.** This accepts the declared finite-horizon Brownian predictable-integrand construction: L² integral and isometry, continuous adapted martingale and predictable bracket, elementary stochastic exponentials and genuine local-martingale limit, exact E exp(V_T/2)<infinity criterion, unit terminal mass, closed/class-D exponential martingale, and equivalent probability on F_T. The proof does not assume the final martingale conclusion, a project Itô formula, a stronger epsilon moment, or a fixed unscaled Lp estimate.

This is manual mathematical acceptance of the stated Brownian construction. It is not native Lean/API/kernel/source/consumer acceptance, a general continuous-semimartingale integration or Itô formula, a Girsanov Brownian drift theorem, the separate Cramér/LDP branch, full B8/I3/G4/G5/G11 completion, source installation, canonical closure, protected/main integration, upstream submission, publication or human approval. Those original objectives and the external communication/submission gate remain in force.

## 1. Actual objects, finite energy and measurability

The candidate fixes a probability space with a complete right-continuous filtration, an adapted continuous real Brownian motion relative to that filtration and independent Gaussian future increments, finite deterministic T, and a real predictable random process theta. The predictable sigma algebra is specified by genuine (s,t] times A generators, A in F_s; it is not defined as whatever the desired approximation happens to approximate. Time-zero sets are dt-null. Brownian motion is assumed as an actual stochastic object, which is appropriate for a theorem about Brownian integrals; its existence is not claimed to be newly built from the project predicates.

V_t is the pathwise nonnegative time integral of theta². Since y<=2exp(y/2), the Novikov hypothesis gives E V_T<=2C<infinity and V_T<infinity almost surely. Predictable measurability implies product measurability; restricted to [0,t], each generating rectangle is measurable for B([0,t]) times F_t. Thus V_t is F_t-measurable by measurable integration. On the common probability-one event where V_T is finite, every V_t is finite, nondecreasing and continuous by absolute continuity of an integrable time primitive. Completeness permits fixing exceptional paths on one null event already in F_0. These are the adaptations/versions needed for the later stopping times. An adapted continuous version is predictable under the stated usual conditions.

The same comments apply to V^k, which is everywhere a continuous finite primitive of a bounded elementary process. No jump-energy overshoot is possible. T=0 is a separate exact case: all integrals are zero, Z=1 and Q=P on F_0, without division by T or an unnecessary stopping argument.

## 2. Elementary construction and L² density independently reconstructed

For bounded elementary h on a deterministic partition, the actual integral J_t(h) is the finite sum of weighted Brownian increments (3). It is continuous pathwise because each increment is stopped at deterministic endpoints, and adapted because active coefficients are already measurable at their left endpoints. For an interval containing deterministic s, its active coefficient is F_s-measurable and the remaining increment has conditional mean zero. Subsequent interval contributions have zero conditional expectation by iterating at their left endpoints. This proves the martingale property for arbitrary deterministic s<=t, including s/t inside cells.

For terminal isometry, take a common refinement for h,k. If i<j, the i-th weighted increment and the j-th coefficient are both F_(t_j)-measurable. The j-th Brownian increment has conditional mean zero, so the cross expectation is zero. The diagonal conditional second moment is h_i²(t_(i+1)-t_i). Summing gives E J_t(h)²=E integral_0^t h² and the difference isometry by linearity. For the compensated square, write J_t=J_s+(J_t-J_s). The conditional cross term vanishes, and the conditional expectation of the squared remaining increments equals that of the remaining integral of h² by the same tower/refinement argument. Hence J(h)²-integral h² is a martingale, not just an equality of unconditional terminal variances.

The density argument is valid on the finite measure space with measure P times dt, restricted to the predictable sigma algebra. The rectangle generators form a pi-system: intersection uses the larger left endpoint, where both events are measurable, and the intersected time interval. Complements relative to (0,T] times Omega are finite unions of elementary rectangles. Indicators of the resulting algebra lie in the closed L² span. Monotone-class closure follows since bounded increasing/decreasing indicator limits converge in L² on finite measure. Simple predictable functions then approximate arbitrary L² predictable functions by truncation and measurable simple approximation. A finite collection of rectangle endpoints gives one common deterministic partition with bounded left-measurable coefficients. Thus bounded elementary h^k can approximate this actual theta; density is proved from its sigma algebra, not assumed as the definition of theta.

For completeness of the process limit, the Banach space C[0,T] with the uniform norm is complete and separable. Continuous processes with measurable time coordinates define measurable C[0,T]-valued random variables (rational-time coordinates suffice). Doob's L² inequality together with the difference isometry gives

    E ||J(h^k)-J(h^l)||_infinity² <=4 ||h^k-h^l||_(L²(Pdt))².

The finite-grid maximal inequality used here follows from the stopping-level estimate for |N| and Cauchy–Schwarz; continuity permits refining rational/dyadic grids. There is no invocation of a stochastic integral theorem to establish this estimate. Completion yields M as an L²(C[0,T]) limit. A summably fast subsequence converges uniformly almost surely, which supplies a continuous version and adapted coordinates by completeness. The fixed-time L² limit preserves conditional expectation, giving a true square-integrable martingale. Differences of approximations tend to zero by the displayed bound, so the result is approximation-independent. The fixed-time isometry and Doob bound extend to theta as in (6). These steps construct an integral, not a witness to a continuity predicate.

## 3. Actual predictable bracket, including uniqueness

The energy estimate (7) follows directly from

    integral |(h^k)²-theta²|
       <= ||h^k-theta||_(L²(Pdt)) ||h^k+theta||_(L²(Pdt))

after expectation and Cauchy–Schwarz on the product space. The right side tends to zero because the second norm is bounded. This controls the supremum of the energy-primitive error in L¹. Likewise

    ||(J^k)²-M²||_infinity
       <= ||J^k-M||_infinity (||J^k||_infinity+||M||_infinity)

has expectation tending to zero by the uniform L² bounds. Conditional expectation is an L¹ contraction, so the compensated-square martingale identity passes to M²-V at deterministic s,t. V is continuous predictable increasing, starts at zero and has finite expected terminal value. It is therefore the actual predictable square compensator, or bracket, of this continuous square-integrable martingale.

I checked the stated uniqueness argument without assuming an Itô change-of-variables formula. If two continuous predictable compensators produce local martingales, their difference is a continuous finite-variation local martingale A starting at zero. Localize both its size and its total variation; continuity makes the stopped size/variation bounded without overshoot, and the bounded local martingale is a true square-integrable martingale by localization/dominated convergence. On deterministic refining grids, orthogonality gives

    E sum (Delta A)²=E (A_T-A_0)².

Pathwise, the sum is at most max|Delta A| times total variation. Continuity sends the maximum to zero and bounded size/variation supplies domination. Thus the squared terminal displacement has expectation zero. Repeat at rational terminal times, use continuity, then remove localization: A=0 indistinguishably. This validates uniqueness. The accepted bracket meaning is the continuous predictable compensator of M²; no separate native pathwise quadratic-variation API or all-partition theorem is claimed from reading a predicate.

## 4. Elementary Gaussian exponentials and bounded optional sampling

For bounded elementary h and real q, the conditional Gaussian law on each partition interval gives

    E[exp(q h_i Delta W-(q h_i)² Delta t/2) | F_(t_i)]=1.

This identity also holds for random F_(t_i)-measurable h_i: first verify simple coefficients, then use conditional Gaussian integration/measurable kernels; boundedness gives all necessary finite Gaussian exponential moments on a fixed interval. Intermediate deterministic s inside a cell is treated with the same known coefficient. Iterating the tower proves that (8) is a positive true martingale and is closed by its terminal value. Gaussian normalization is used before any local-martingale mass conclusion.

The identity E_t(h)^p=E_t(ph)exp((p²-p)V_t(h)/2), for p>1, gives the printed bound exp((p²-p)B²T/2) on the pth moment, since V_t(h)<=B²T and E E_t(ph)=1. An arbitrary fixed q is covered by replacing h with qh. This bound is per approximation and is not uniform in a sequence B_k->infinity.

The finite-horizon closed-martingale optional-stopping input is legitimate and does not require Itô calculus. At a finite-grid stopping time rho, tower conditioning gives E_T(qh)'s conditional expectation as E_rho(qh). Families of conditional expectations of one integrable terminal variable are uniformly integrable. For bounded general rho, round from above on finite grids, use continuity for convergence in probability, and uniform integrability for L¹ convergence. Testing on F_rho gives the bounded optional-sampling identity. In particular E E_rho(qh)=1 and the stopped process is a true martingale. All stopping times used for elementary exponentials are bounded by T.

## 5. Deterministic good energy levels and the stopped limit

Choose a subsequence with J^k->M uniformly almost surely and V^k->V uniformly almost surely. The existing L²/L¹ supremum bounds permit summably fast expectations; Markov's inequality and Borel–Cantelli give such a COMMON subsequence. Continuity of exp on each path's finite compact range gives uniform path convergence Z^k->Z. That observation alone would not justify a martingale limit; the candidate supplies the additional estimates below.

For K>0, first hitting of [K,infinity) by adapted continuous V or V^k, capped at T, is a stopping time. The usual conditions suffice; monotonicity also allows a direct rational-time test. At every stop, V^k_(sigma_K^k)<=K because V^k is continuous and V^k_0=0<K. If no hit occurs the terminal energy is below K.

For a fixed continuous nondecreasing path, a plateau level with a nontrivial constant interval has a rational pair r<s in that interval. Distinct plateau interiors are disjoint, so the plateau-value set is countable. Adding the terminal value keeps it Lebesgue-null. At any other positive K that is crossed, values a fixed epsilon before the first hit are strictly below K and values a fixed epsilon after it are strictly above K; otherwise there would be a plateau. Uniform V^k convergence therefore sandwiches sigma_K^k near tau_K. If V_T<K, uniform convergence makes every sufficiently late approximant stay below K and both capped times equal T. The excluded terminal equality handles a potentially tangential/terminal crossing. These cases prove the asserted hitting-time convergence without assuming it at every level.

The random good-level selection is deterministic and measurable as claimed. For each rational r<s, the joint set {V_r=V_s=K} is measurable in (omega,K) (graphs of measurable real variables, intersected with equality); restrict to r,s in [0,T]. The union over pairs describes nontrivial plateau values, and {V_T=K} is another measurable graph. Null exceptional path sets can be removed once by completeness. Each path section has Lebesgue measure zero. Tonelli on P times Lebesgue measure therefore gives P(bad at K)=0 for Lebesgue-almost every deterministic K. A full-measure subset of (0,infinity) intersects each interval (j,j+1); choosing K_j there gives an increasing divergent deterministic sequence. Intersecting its countably many full-probability events and the common approximation event is legitimate. No path-dependent localization level was silently chosen.

At a selected K, the stopped integrals obey the pathwise bound

    sup_t |J^k_(t capped sigma_K^k)-M_(t capped tau_K)|
       <= ||J^k-M||_infinity
          + modulus_M(|sigma_K^k-tau_K|).

The min map is 1-Lipschitz in its stopping-time argument. Uniform continuity of the limiting M on [0,T] makes this vanish; the same reasoning applies to V and then exp. This proves (10) uniformly in t.

At the SAME sigma_K^k, not at an unrelated localizer, the elementary power identity and bounded optional stopping give

    E (Z^k_(T capped sigma_K^k))^p
      <= exp((p²-p)K/2) E E_(T capped sigma_K^k)(p h^k)
       = exp((p²-p)K/2).

The p-maximal inequality applies to the stopped true martingale and bounds the expected supremum pth power uniformly in k. This supplies uniform integrability of fixed-time stopped values (indeed of their suprema). Combined with (10), it gives L¹ convergence. At deterministic s<=t, testing the stopped elementary martingale identity with any bounded F_s-measurable variable and passing the L¹ limit proves that Z stopped at tau_K is a true martingale with initial value one. No Itô formula or unproved general closure of uniform martingale limits has entered.

For K_j increasing to infinity, tau_(K_j) increases to T. Since V_T is finite almost surely, it actually equals T eventually on each path. This is sufficient localization on the finite horizon, including convergence of stopped terminal values. Conditional Fatou applied to the true stopped martingales yields the supermartingale inequality. Bounded optional stopping followed by ordinary Fatou gives E Z_rho<=1 for each rho<=T. These are inequality/mass conclusions only, not yet the desired unit expectation.

Linearity of the L² construction identifies the integral of a theta as aM. The same local construction works for every finite real a because E integral(a theta)²<infinity; it does not need a Novikov moment for a theta at this stage. Thus Z(a)=exp(aM-a²V/2) is genuinely constructed as a positive local martingale for every fixed a. The later proof uses this at a=1 and at 0<a<1. No simultaneous uncountable intersection of path versions or stronger exponential moment is needed; one can use countable sequences for the limiting a argument.

## 6. Exact half-energy Novikov: exponent choice and critical endpoint

For fixed 0<a<1, a(2-a)=1-(1-a)² is in (0,1), so there is a p with 1<p<=1/[a(2-a)]. In fact

    pa<=1/(2-a)<1,
    pa(1-a)/(1-pa)<=1
          iff pa(2-a)<=1.

This proves both valid Hölder conjugate exponents and the exact coefficient bound(14). Equality at the upper choice uses coefficient exactly1/2, never (1+epsilon)/2.

I recomputed the pathwise identity(15):

    Z(1)^(pa) exp(pa(1-a)V/2)
       = exp(pa M-pa V/2+pa(1-a)V/2)
       = exp(pa M-pa²V/2)=Z(a)^p.

For any bounded stopping time rho, Hölder with exponents 1/(pa),1/(1-pa) gives

    E Z_rho(a)^p
      <= (E Z_rho(1))^(pa)
         [E exp(pa(1-a)V_rho/[2(1-pa)])]^(1-pa)
      <= C^(1-pa).

The unscaled factor uses only its ALREADY PROVED supermartingale mass inequality, not unit mass. V_rho<=V_T uses monotonicity; the second factor uses only E exp(V_T/2)=C. The bound is uniform over all rho<=T. Applying it to a genuine localizing sequence for Z(a) supplies a uniform p-moment bound for stopped terminal densities whose means are one. Almost-sure convergence and uniform integrability then give L¹ convergence and E Z_T(a)=1. Conditional testing (or the same supermartingale unit-mass argument as below) yields a closed true martingale for each a<1.

The critical endpoint is separately justified. Recomputing(17) gives Z_T(a)=Z_T(1)^a exp(a(1-a)V_T/2). Hölder with 1/a and1/(1-a), and the just-proved E Z_T(a)=1, yields

    1 <= (E Z_T(1))^a [E exp(a V_T/2)]^(1-a)
      <= (E Z_T(1))^a C^(1-a).

Thus E Z_T(1)>=C^(-(1-a)/a). C is finite and >=1. Sending a upward to one makes this lower bound tend to one, while the positive-local-martingale bound is <=1. Therefore E Z_T=1. This argument does not exchange an unproved L¹ limit in a with expectation. It also does not infer endpoint mass from mere pointwise convergence of unit-mean densities. The lower-bound estimate supplies the missing mass control explicitly.

The allowable p may shrink to one as a tends to one. The proof never claims a uniform fixed p>1 or unscaled Lp bound at a=1. No stronger epsilon exponential moment, assumed terminal expectation or assumed UI is used. The nonlinear Hölder exponents and both signs in the energy correction are correct.

## 7. Closed/UI martingale and equivalent probability: no drift theorem inferred

From superconditioning and unit terminal mass,

    1=E Z_T<=E Z_t<=1.

For s<=t, the nonnegative gap Z_s-E[Z_t|F_s] has expectation zero; hence it vanishes almost surely. This proves the true martingale property, and using t=T gives Z_s=E[Z_T|F_s]. Integrability follows from the earlier supermass bound. This step needs neither a new moment nor an Itô change-of-variables identity.

For any stopping-time sigma algebra F_rho, let Y_rho=E[Z_T|F_rho]. It is nonnegative with mean one. Splitting Z_T at A and using {Y_rho>K} in F_rho gives exactly

    E[Y_rho 1_(Y_rho>K)]
       <= E[Z_T 1_(Z_T>A)] + A P(Y_rho>K)
       <= E[Z_T 1_(Z_T>A)] + A/K.

Choosing A=sqrt(K) sends both terms to zero uniformly in rho. To identify this UI family with actual Z_rho without circular optional sampling, round rho upward to dyadic stopping times rho_n<=T. At finite-grid stops the identity with the terminal conditional expectation is already known. Continuity gives Z_(rho_n)->Z_rho almost surely; the family of those conditional expectations is uniformly integrable by the same estimate, so convergence is L¹. For A in F_rho, A is in each F_(rho_n), and testing passes the identity to the limit. Continuity/adaptation gives F_rho-measurability of Z_rho. Thus Z_rho=Y_rho. This supplies class D on the finite horizon, including bounded stopping times, rather than only deterministic-time integrability.

Q(A)=E[1_A Z_T] on F_T is countably additive by monotone convergence and normalized by E Z_T=1. M_T and V_T are finite almost surely, so Z_T is finite and STRICTLY positive; therefore Q and P have the same null sets on F_T. The definition is an actual probability change, not an unnormalized weight. It does not prove the Brownian law or independent increments of W-integral theta dt under Q. The candidate correctly leaves the Girsanov drift identification and general Itô formula unclaimed.

## 8. Nonzero/random controls and actual source distinction

I independently checked all displayed controls. Theta=0 gives M=V=0, Z=1. For nonzero constant c, M=cW and V=c²t; conditional Gaussian normalization and E M_t²=c²t verify the integral and exponential at a genuine nonzero stochastic example. For 0<s<T and A={W_s>0}, theta=c1_A1_(s,T] is a bounded predictable random step. Up to s the integral/energy vanish; afterwards they are c1_A(W_t-W_s) and c²1_A(t-s). Since the future increment is independent of F_s, its conditional normalized exponential has mean one both on A and its complement. C=(1-P(A))+P(A)exp(c²(T-s)/2) is finite (for standard Brownian motion here P(A)=1/2). The random integrand need not be continuous in time. This is a genuine random predictable control, not a deterministic zero witness.

The good-level/energy-stop control handles growing B_k without inventing uniform un-stopped exponential moments. The critical p choice handles the exact half-energy coefficient and does not promise an endpoint Lp estimate. The proof maintains both distinctions at their actual carrying steps.

I personally read the COMPLETE four original source files, including every predicate and theorem body:

- Novikov.lean (`5daee23d...`) defines IsNovikovCondition(theta,T), theta:R->R, as 0<=T AND Continuous theta. Its explicit witness is the zero deterministic function. It has neither a probability space nor V/Z/expectation in the condition or theorem.
- StochasticIntegral.lean (`fddad25b...`) defines a conjunction Continuous I, I0=0, Continuous H and Continuous W. For example H=W=0 and I(t)=t satisfy that conjunction, although the actual zero-integrand integral must be zero. This is a structural countercontrol to identifying the predicate with the stochastic-integral relation, not a falsehood in the conjunction theorem.
- ItoIsometry.lean (`ce411f57...`) requires I0=0, nonnegativity of I(t) for t>=0 and Continuous H. H=0 with I(t)=t² satisfies it; it does not force the zero integral's actual second moment or equate two expectations.
- ItoLemma.lean (`34150283...`) requires continuity and a boundary-zero expression. With f=X=0 it allows result(t)=t, so it does not state the change-of-variables identity at positive time.

Those source conjunctions and zero witnesses are true at their stated structural level. The manual construction does not erase them, invent an already native stochastic API or claim a fresh kernel/axiom/library-absence verification. A deterministic continuous theta on a finite interval can indeed be embedded as a bounded deterministic Brownian integrand and satisfy a genuine Novikov moment, but the native predicate has not constructed that embedding, exponential or martingale theorem. The random step example additionally lies outside its deterministic-function carrier. These distinctions preserve real mathematics without mistaking names for substance.

## 9. Original scope, governing process and exact evidence

The original remediation B8 row requires the actual Novikov condition and genuine probability theorem; its separate Cramér upper/lower obligation is not discharged by this branch. Phase6o Wave3b explicitly names the Brownian elementary L² construction, isometry, bracket/semimartingale and Itô/Novikov followthrough. Phase6s Track2 continues the substantive lift and keeps external submission/community communication gated while permitting in-repo substantive work. This manual Brownian result is a coherent increment toward those objectives. It does not narrow the full original I3 stochastic/semimartingale/Itô/LDP/consumer/native charter or establish upstream acceptance. Historical “shipped” labels and predicate closure summaries are not current proof of those missing APIs.

The FIRST action was the actual original assigned check from N: return0/fresh/changed[], tool0cf7b8, duration0.071077125seconds. The initial tool exposed no separate UTC start/end pair; first-check.json records that limitation and its later capture time without reconstructing the missing pair. The author’s original first0 and final1/owned-files-only receipts were read, parsed and left unchanged. PLAN, construction and source snapshots remain unchanged. No packet refresh occurred.

Personal reading: complete candidate/REPORT/PLAN, complete original four source bodies, complete original B8 remediation row/plan, and the full original Phase6o Wave3b (displayed lines340–432), plus Phase6s introduction/catalog/in-repo versus external boundary (lines1–85) and full Track2 definitions/continuation/external-gate contexts displayed in the original combined read. The combined whole-roadmap read was oversized and clipped unrelated material; I do not claim a mathematical audit of every unrelated roadmap wave. Complete raw roadmap streams are nevertheless retained. The current r55 shared notebook and workspace/project AGENTS/CLAUDE/wave/ADR-008/ADR-017/continuity/PRE_DECISIONS were already personally read in the immediately preceding review work; current hashes are exact, and complete raw rereads are retained here. No Claude-only runtime procedure was inferred to be loaded or applicable. Author evidence/process were parsed for exact source/check metadata; their process was not re-executed.

Evidence binds all23 packet-reference occurrences,64 selected source-file pins and5 extra packet/workspace/worktree governing inputs. Each records exact SHA256, bytes, mode and device/inode/mode/size/nsmtime/nsctime before/after reading. Unrelated selected source files are hash-only observations, not independently reviewed probability code. Sequential observations are not atomic filesystem or process-memory attestation. Complete actual read/check subprocess records retain argv, cwd, actual UTC pairs, return codes and separate decoded/base64 stdout/stderr. Initial direct displays retain tool chunks; no missing times or old outcomes are invented.

Only the five allocated ignored reviewer outputs were written. No primary/source, other writer, shared notebook, author historical artifact, holding/registry/closure, controller/cache/pin/epoch, Git/index/ref or runtime state was changed. No project import, test/Verify/model, mathematical software, Lean/MCP/native/build/compiler/render/network, source application, external message or submission ran. The explicitly assigned continuity adapter is the only project script executed and provides freshness evidence only. No new native/probability dependency/library availability claim follows from static source reads.

Next substantive work remains ordinary ROOT native admission and actual probability/filtration/Brownian/predictable-L²/conditional integral/bracket/exponential/UI/measure interfaces, independent kernel/source/consumer checks, remaining full Itô/LDP/I3 work, supported canonical closure and coherent development/main/publication milestones. Missing infrastructure, effort or upstream delay is not a scientific impossibility or approved deferral. No shared notebook or ROOT message was sent by this reviewer.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory mathematical contradiction remains in this scoped author construction. The original native Novikov/integral/isometry/Itô predicates do not state the probability identities named in their prose. The actual constructed Brownian theorem uses genuine Gaussian conditional integration, completion, controlled energy localization, exact critical Hölder mass and class-D/measure arguments. Accepting that manual proof neither supplies absent native definitions nor closes full B8/I3 or the separate Cramér, Itô and Girsanov obligations.

## Actual terminal original-check receipt

The final ORIGINAL assigned reviewer check actually returned1/fresh=false, changed exactly [owned-files], stderr empty, at 2026-10-18T01:44:23.472544+00:00. All92 reference/source/extra input occurrences retained exact initial bytes, modes and recorded stat identity/nsmtime/nsctime. No packet was refreshed; author original first0/final1 receipts and all original sources remain unchanged. The report is frozen with scoped manual acceptance only; this freshness result grants no native, consumer, closure or publication authority.
