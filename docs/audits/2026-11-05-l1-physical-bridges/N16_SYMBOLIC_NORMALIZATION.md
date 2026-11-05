# Original conventions and whole-N16 symbolic normalization

Manual source-level construction for independent math and physics/source review.
Parent physical-image checkpoint8440c44fe, whose ROOT intake remains separate.
No residue, partition coefficient/value, evaluated matrix or state is computed.
No evaluation/slot admission or operator choice is inferred.

## 1. Reconcile the documented conventions before asking for a choice

Read the actual source bodies: original program strategy section4/6a.2,
Phase6a current scientific charter and Wave2, paper25 sectionII.A, current
publication manuscript snapshot ab097b381aec6658217bb7237c2dc1ba82bbc174,
the actual RPA/KMS declarations, and the primary sources below. The snapshot
is read-only context, not an Executor manuscript repair or acceptance receipt.

The charter retains original B3 normalization/range and physical mode/transport
BUILD requirements. The paper/Lean speed law and RPA response have effective
inputs; chi0>0 and gamma_star*chi0<1 are hypotheses of the actual sign theorem.
It adds neither gamma_star>=0 nor an identification of gamma_star/chi0 with
the bare Diakonov g1,g2. The adopted illustrative chi range is not a derived
microscopic phase domain. The inspected carriers do not establish that map;
this is a bounded source readback, not an absence claim about all literature.

[CGL1511.03646v3](https://arxiv.org/html/1511.03646v3), sectionI.F,(1.60),
EXPLICITLY starts its thermal specialization with a Gibbs density matrix
exp[-beta0(H-mu0 Q)]/Z0 before imposing KMS. Its general closed-time functional
uses a supplied density matrix. These are documented conventions, not blank
state choices. The actual SK declarations retain beta/KMS and positivity
premises; they do not construct a microscopic N16 Hamiltonian or density map.
The chemical potential mu0 is not a bare gravity coupling or metric unit scale.
CGL H is a Hamiltonian; Volovik H below is a Hubble rate, not that operator.

[Volovik2601.00639v1](https://arxiv.org/html/2601.00639v1), sectionsI-III,
uses T=H/pi in his deSitter two-fluid model, with specified vacuum/normal
components and a luminal second-sound result. That temperature is not already
the periodic two-slice lattice inverse extent, nor a construction of its tensor
or matter operators. No identity beta0=2a_t=pi/H is supplied merely by giving
the regulator two time slices; its trace and boundary correspondence must be
derived. The cited [2410.04392v11](https://arxiv.org/html/2410.04392v11)
supplies the associated cosmological thermodynamic/decay context. Do not replace
these source conventions with a temperature chosen to fit a response.

[Diakonov1109.0091v1](https://arxiv.org/abs/1109.0091v1),(23)-(28), fixes
the actual composite action, dimensionless couplings and finite Haar/Berezin
functional. Its discussion of loop regimes depends on couplings but is not
our phase/state certificate. The accepted closed ordering and original periodic
regulator are retained. Vergeles' composite extension and its Minkowski/gauge/
spectral hypotheses remain as reconciled in the parent, not an inherited N16
ordinary Gibbs trace.

Thus no operator fork is needed for the symbolic normalization below. What is
still to DERIVE is the correspondence of the documented Hamiltonian/adjoint,
phase, trace/temperature and source data to this finite microscopic functional.
Do not select new conventions merely because the map is not yet supplied.
If a later construction genuinely needs a physical specialization, first state
whether it derives the original correspondence or changes a premise, with
specific evidence and alternatives; only then raise an operator question.

## 2. Full zero-source partition polynomial and exact coefficient ring

Use the SAME original closed action,128 Grassmann generators,64 Spin(4) links,
normalized product Haar and oriented top coefficient. Write

    Z(g1,g2)=sum_(m=0..16) c_m g1^m g2^(32-2m),
    c_m=I[S4^m S2^(32-2m)]/[m! (32-2m)!].                       (Z)

This follows from degree8 for S4 and degree4 for S2. The already accepted
internal Pin/degree argument gives c_m=0 for odd m. This is NOT a claim of
time-reflection invariance theta(S2). No N4 cubic/quartic cancellation is
transferred to N16. At g2=0 the unknown c16 term can remain; no normalized
extension or zero partition there is inferred from the N4 example.

In canonical unit-quaternion coordinates, entries of U,Udagger,gamma,gamma5
have Gaussian-integer coefficients. The actual coframe has denominator4.
S4 has four frames and integer epsilon coefficients; S2 has two frames and
the action quarter. Therefore an unsourced m,n action word has denominator

    4^(4m+3n),      2m+n=32,

which divides4^96. The exponential denominator m!n! divides32!, since
m+n<=32 and the multinomial quotient is integral. Grassmann reordering adds
only signs. These claims use the actual cosmological determinant normalization
after its ordered-world sum, not an extra unrecorded factorial.

For one normalized SU(2) unit quaternion, odd moments vanish and an even
moment of total degree2k is

    integral q0^(2r0)...q3^(2r3)
         = product_j(2r_j-1)!! / [2^k (k+1)!],   sum r_j=k.       (H)

For k=0 the numerator/denominator are1. S4 contributes at most4 link
coordinates and S2 at most6. For the full saturated word their total degree
is at most4m+6n=192-8m<=192, without selecting an anchor or chirality.
Thus each of the128 independent SU(2) factors has k<=96. Each moment
denominator divides H96=2^96*97!. A safe COMMON denominator for EVERY c_m is

    D_Z=32! * 4^96 * (2^96*97!)^128,
    D_Z c_m in Z[i].                                          (D)

This is an intentionally conservative integer divisibility bound, not a
numerator value, support count, resource estimate or positivity argument.
All prime factors of D_Z are at most97. Hence every prime p>97 is a good
characteristic for the unsourced coefficient denominators, after fixing an
embedding of i (or a quadratic extension). A COMPLETE nonzero reduction of
c0=Z32 proves c0!=0; a zero residue does not. No such reduction has been run.
For rational couplings with denominators v1,v2, D_Z*v1^16*v2^32 is a safe
full-value denominator; primes must also avoid those coupling denominators.

## 3. Full physical-image matrix: a common denominator and height

This section applies to the EXACT full gauge-averaged monomial test list F_i
of the accepted physical-image reduction, not arbitrary fitted observables.
Initial monomials have Grassmann degree d<=64 and spatial quaternion degree
a<=160. A compact slice gauge transformation contributes at most d+2a<=384
gauge quaternion coordinates: one per spinor, two per transformed link
coordinate. Quaternion multiplication/inversion has integer coefficients,
with Gaussian-integer spinor matrix entries. The slice gauge group has16
SU(2) factors. Thus a safe coefficient denominator of each F_i is

    D_G=(2^192*193!)^16.                                      (DG)

Gauge averaging preserves spatial-link and Grassmann degree. The parent's
theta uses signed-permutation gamma0 and quaternion conjugation/chiral
exchange, introducing no extra denominators. Two inserted observables add at
most320 spatial link degrees. Including the full action gives total link
degree<=512 and hence k<=256 per physical SU(2) factor. Consequently EVERY
coupling-polynomial coefficient of the ORIGINAL unnormalized matrix

    N_ij=I[exp(S_g) theta(F_i) F_j]

has a safe common Gaussian-rational denominator

    D_N=32! * 4^96 * D_G^2 * (2^256*257!)^128.                  (DN)

The insertion degrees can lower the required action saturation; they never
increase m+n beyond32, the frame quarter bound96 or action link bound192.
No independence of the two chiral expectations is assumed. All primes p>257
avoid these coefficient denominators. Normalized N/Z has the ADDITIONAL unknown
partition denominator: a good coefficient prime does not establish Z invertible
at the chosen couplings, real ordering or positivity over a finite field.

There is also a safe height bound, derived from the original compact integral.
Use exterior coefficient l1 norm, submultiplicative under wedge. Every matrix
entry of gamma U or U gamma has modulus<=1. Four coframe endpoint blocks,
each with at most16 bilinear entries and its quarter, give ||T_mu^A||<=16.
Unitarity bounds |Tr(H gamma_A gamma_B gamma5)|<=4, where H is the original
closed plaquette. Thus over all16 bases,

    ||S4|| <=16*24*16^4 =24*16^5 <2^25,
    ||S2|| <=16*24*16*16^2 =24*16^4 <2^25.                     (B)

Set C=2^25 and B=C^32=2^800. Top extraction and normalized compact Haar then
give |c_m|<=B, with all original factorials retained (discarding them only
weakens this absolute bound).

For an F_i, the compact gauge action is unitary on degree-d exterior
coefficients. Its initial coefficient vector has l2 norm1; the scalar link
monomial evaluated on ANY transformed unit links has modulus<=1. Averaging
cannot increase that l2 norm. Cauchy-Schwarz in dimension binom(64,d)<=2^64
therefore gives ||F_i||_l1<=2^32 pointwise in the links. Theta preserves this
unitary coefficient bound. Hence every coupling coefficient n_ij,m,n obeys

    |n_ij,m,n| <=2^64 * C^32 =2^864.                           (height)

It follows that real and imaginary parts of D_N*n_ij,m,n are integers of
absolute value at most D_N*2^864. A COMPLETE dual-embedding CRT coefficient
certificate with modulus greater than twice this bound could uniquely recover
them, with exact original-action correspondence and denominator bindings.
This is a rigorous prospective height, not a reconstruction, positive-matrix
certificate, feasible prime count or instruction to enumerate the test list.
Reuse existing reviewed arithmetic conventions if an evaluator is later admitted;
no new runner, harness, test mechanism or resource envelope is proposed.

## 4. Conditional explicit nonzero neighborhood: no physical domain selected

For fixed real g2!=0 put x=g1/g2^2. Then

    Z=g2^32 z(x),    z(x)=c0+c2 x^2+...+c16 x^16.

If a FUTURE COMPLETE certificate establishes c0!=0, (D) implies |c0|>=1/D_Z:
a nonzero Gaussian integer has modulus>=1. Define the positive rational

    R=1/(16 B D_Z),       B=2^800.

For |x|<=R<=1, the eight possible higher even terms satisfy

    |z(x)-c0| <=8 B |x|^2 <=8 B R <=1/(2D_Z),
    |Z(g1,g2)| >= |g2|^32/(2D_Z) >0.                           (N)

This proves a conditional, nonempty finite-regulator normalization domain
without computing c0's full rational value or choosing its favorable sign.
The antecedent is NOT supplied here: actual nonvanishing still needs a complete
certificate. The bound can be tiny; it is an enabling algebraic neighborhood,
NOT a derived stable/ordered physical phase, thermal domain, chi interval or
an operator-approved replacement for the original B3 requirement. On pureg2
the accepted G=B=0 statement remains true wherever normalized. State positivity
is an independent full physical-image/representation problem, not a consequence
of (N). No continuum, matter, tensor or real-time conclusion follows.

## 5. Next substantive work and unchanged authority

This source-level result sharpens the full-normalization certificate target and
continues independent symbolic work without a new physical input. Next, have
producer-separated math and physics/source reviewers verify all normalization,
degree/divisibility/height bounds and the convention readback. Return exact
source pins and their verdicts through the existing notebook/PR115/queue.

Keep couplings and state correspondence symbolic unless the original input
or a derived model bridge supplies their specialization. The later genuine
fork would be whether a proposed construction derives the intended density/
adjoint/phase/thermal correspondence or changes action/source/boundary/state
premises. An operator question then must name that change, evidence and
alternatives. No choice is necessary to prove the identities above, and none
is requested now. Ordinary manuscript/source-consistency/Visser repairs and
all L1 readiness remain Publication ROOT's responsibility.

No evaluation, modulus data, whole partition, Gram matrix, positivity/state,
actual negative witness, native proof or feasibility has been established.
No Lean slot, codejob, resource, controller or test/harness change is admitted.
The N4 full tensor remains separately OPEN and owned; all original physical
L1 and final human acceptance requirements remain full strength.
