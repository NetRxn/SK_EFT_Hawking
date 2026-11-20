# Original-state premise correspondence and robustness of the N16 obstruction

Project-original manual source and mathematical construction for independent
review. This candidate neither constructs a physical state nor changes the
action, boundary, physical algebra or adjoint adopted by the publication work.
Its comparison theorems below do not select a replacement. No scientific
evaluator, CAS, numerical/matrix/Haar test, native proof, contraction or Lean
job has been run. The original full normalization and N4 tensor are OPEN.

## 1. Original theory and construction premises

The owning requirements are Phase6a's current overlay and Wave2, and the
successor [L1 Physical Bridges roadmap](https://github.com/NetRxn/SK_EFT_Hawking/blob/c0a775c942fc62528fec2d0b645e4dfe858ae61c/docs/roadmaps/L1_Physical_Bridges_Roadmap.md), W1-W4.
The latter is the independently reviewed PR115 roadmap at source commit
c0a775c942fc62528fec2d0b645e4dfe858ae61c, not a replacement acceptance contract. In particular W1 requires an
actual action/source/operator/gauge/constraint/boundary/reality/state map,
positive physical correlators and controlled regulator dependence, OR a
precisely scoped nonvacuous impossibility/counterexample. W2-W4 still require
the same-state response, derived B3 normalization/range, tensor and matter
reference, and causal transport. No source/unit/coupling tuning to force the
original [0.1,10] result is licensed by this report.

| Premise | Direct original-body evidence | Status in the N16 bridge |
| --- | --- | --- |
| Composite coframe and local gauge-invariant gravity action | [Diakonov1109.0091v1](https://arxiv.org/abs/1109.0091v1), V(20)-(25), defines the site coframe and cosmological/EHC terms, with local Spin(4) covariance | Original motivation for the fixed S4/S2 benchmark. Covariance does not by itself identify a positive operator state |
| Symmetric forward/backward coframe | Diakonov V(23) presents a family with arbitrary alpha and motivates alpha=1/2 by world/internal P,T vector transformations | The fixed benchmark uses this choice. Its motivation does not derive a unique Hilbert adjoint or reflection reconstruction |
| Euclidean functional and integration measure | Diakonov I chooses Euclidean gravity first; V(26)-(28) gives eight Berezin variables/site and normalized SU(2)L/R Haar, and a finite finite-volume integral | Directly supports the regulated algebraic functional. Finiteness is distinct from nonzero partition, positive physical state and justified Wick continuation |
| Closed two-coupling truncation | Diakonov V(28) contains an ellipsis and explicitly permits additional higher-derivative terms; VI analyzes the pure multifermion vertices with no bilinear propagator | The zero-source closed g1 S4+g2 S2 action is the fixed enabling benchmark, not a theorem that every term allowed by the original program vanishes |
| All-extended periodic 2^4 torus and a chosen time half | The inspected Diakonov I/V/VI specify the lattice regulator and finite-volume integral, rather than deriving this unique small torus/spin structure as the physical thermal regulator | Candidate finite enabling geometry. Its exact two-interface algebra is retained, without inferring a continuum or physical-temperature identification |
| Physical metric and matter | [Volovik2312.09435v2](https://arxiv.org/html/2312.09435v2), III(18)-(22), gives tetrad expectation and g_mu_nu=eta_ab <E_mu^a E_nu^b>, including vestigial <E>=0 and bosonic matter coupling | The physical target is an expectation-valued ordinary metric. The bare nilpotent configuration Q, and a fixed-body source family, are not automatically that target. Euclidean-to-Lorentzian signature correspondence remains owed |
| Physical observable products, adjoint and state | [CGL1511.03646v3](https://arxiv.org/html/1511.03646v3), I(1.7) starts with an operator density matrix; I.F(1.60), HTML(60), specifies the thermal Gibbs trace before KMS | Supplies the actual operator/state target and its positivity requirement, not an identification of Euclidean Grassmann multiplication or our theta with physical operator multiplication/adjoint |
| Full even gauge-invariant half polynomial algebra A+ and geometric theta | The accepted temporal-boundary/physical-image constructions specify this exact finite pairing and image | A candidate reconstruction premise. The inspected primary sections and owning W1 do not supply the required physical operator/source/adjoint correspondence. This is a bounded correspondence gap, not a literature-wide absence claim |
| Gauge/constraint treatment | Diakonov V(20)-(25) establishes local gauge covariance, with diffeomorphism invariance in the continuum limit | F and G below already obey the entire local Spin(4) gauge invariance. Removing them needs an additional derived physical constraint/correspondence, not gauge averaging alone |
| Alternative unitarity evidence | [Vergeles2506.00036v2](https://arxiv.org/abs/2506.00036v2), II-IV constructs a simplicial Minkowski/contour/gauge argument; VI(6.1) explicitly extends it to composite tetrads | Relevant original physical research, not an inherited positive-reflection theorem for our periodic Euclidean hypercubic symbol algebra. Its hypotheses and source/state/limit correspondence must be transported explicitly |

The last row must not be dismissed as exclusively independent-tetrad physics:
Vergeles explicitly states the composite substitution. Equally, II.B changes
contours and signature, III uses a chosen gauge and conserved degrees of
freedom, IV(4.3)-(4.8) uses an ONB, normalizable states, finite matrix elements
and an assumed complete real-eigenvalue basis. V(5.7) leaves the changing-
degree-of-freedom normalization issue open; VI retains Minkowski gauge and
noncompact gauge-volume issues after (6.1). These are material premises, not
a demonstrated map to the present Euclidean state.

No thermal identification beta=2*a_time or Hubble-to-Hamiltonian identification
is made. CGL's H is an operator; neither a temperature symbol nor geometric
symmetry supplies the missing microscopic density/transfer construction.
The physical-matching decomposition and common-source/contact requirements
already accepted in this audit folder remain in force.

## 2. Accepted complete raw obstruction used as input

Use N16_SATURATION_STATE_OBSTRUCTION.md, exact SHA256
832f231124cc46e41296caf13c50f46d9f4cd3dcb8508860a8b8d83709a5ca9b,
with its independent math and physics R1 reviews. This is a manual accepted
input, not a kernel proof. All original64 Spin(4) links and128 Grassmann
generators are retained, with64 generators in each time half. At J=j=0:

    S2 half-degrees: (4,0), (3,1), (1,3), (0,4), never (2,2);
    S4 half-degrees: (7,1), (1,7), never (6,2).

At y=(1,r), x=(0,r), let B_z=sum_a barpsi_z,a psi_z,a. The fixed oriented
site top is Theta_z. Let q_y be the degree6 dual with

    I_y[q_y barpsi_y,a psi_y,b]=delta_ab,
    Fhat=(product_(time1 z!=y) Theta_z) q_y.

The accepted full partial integral, retaining all internal/world channels, is

    W6=I_1 integral_(temporal and time1 spatial Haar) Fhat S2^2/2
      = B_x/8 * sum_A L_A^2,
    L_A=sum_(i=1..3,B) R^i_AB T_i^B(x).

W6 is a nonzero gauge-invariant degree6 polynomial, spatial-link degree<=10.
Its WHOLE conjugate Berezin dual G has degree58, link degree<=10, and

    a=integral_(time0 spatial Haar) sum_I |w_I|^2 >0,
    I exp(g1 S4+g2 S2) Fhat G=g2^2 a.

The accepted strict inequality follows from an explicit legitimate link
configuration and coefficient noncancellation, continuity and Haar full
support. It is auxiliary compact-Haar/coefficient positivity, not gravity
measure positivity. No new selected-sector argument or evaluator is used.

## 3. Reflection robustness on the same full even half algebras

This section proves a new comparison theorem, rather than adopting a new
reflection. Let A0,A1 be the SAME full complex even gauge-invariant polynomial
half algebras, with actual polynomial FUNCTIONS of compact spatial links as
coefficients. Let vartheta be any unital antilinear algebra anti-involution
between A0 and A1 (in both directions). In particular vartheta maps products
in reverse order and vartheta^2=id. No linear-on-spinors or Grassmann-degree-
preserving hypothesis is imposed. This is a specified algebraic comparison
class, not a claim about every possible physical quantization or adjoint.

In the original oriented eight-generator site algebra,

    B_z^5=0,       B_z^4=24 Theta_z,       q_y=B_y^3/6.

Indeed the four distinct mesons commute, their product equals the original
top since moving the four psis past the bars gives (-1)^6=+1, and in B^3
there are3! copies of each three-meson product. Multiplying by a diagonal
fourth meson gives6 times the top. Off-diagonal or same-type bilinears cannot
complete a top. Thus

    Fhat= [1/(24^7 *6)] (product_(time1 z!=y) B_z^4) B_y^3.

This is a product of31 nilpotent degree2 even gauge invariants. Each
vartheta(B_z) is nilpotent because vartheta(B_z)^5=0. The Grassmann-body map
from an even half algebra to its coefficient-function ring is an algebra
homomorphism. That ring is reduced: a polynomial function whose fifth power
vanishes is zero at every actual compact-group point and is the zero
function. Hence each vartheta(B_z) has zero body and minimum Grassmann
degree at least2. This argument uses actual functions, not an unreduced
coordinate presentation with spurious nilpotents.

Set F_vartheta=vartheta(Fhat) in A0. The product factorization implies
minimum degree62. There are only64 generators in this half and the algebra
is even, so it has only degree62 and possibly degree64 components. Also
vartheta(F_vartheta)=Fhat, independently of the couplings. Define

    P_vartheta(F,G)=I exp(g1 S4+g2 S2) vartheta(F) G.

For the degree62 component in F_vartheta, the diagonal leaves (2,2), which
no original degree4 action term can fill. The degree64 component leaves
(0,2), requiring a nonexistent degree2 action term. S4 and every higher
exponential term have too much total degree. Therefore, EXACTLY,

    P_vartheta(F_vartheta,F_vartheta)=0,
    P_vartheta(F_vartheta,G)=g2^2 a !=0        for real g2!=0.

The second equality is the SAME accepted full mixed integral: its integrand
is Fhat G and contains no vartheta dependence. For arbitrary finite real g1
and real g2!=0, no nonzero complex scalar can make P_vartheta Hermitian PSD,
by the zero-norm/zero-overlap condition. No action-reflection invariance
assumption is used as a substitute for these actual complete moments.

Ordinary constant gamma/phase reflection-convention changes in this class
cannot rescue the same full polynomial pairing. For a general nonlinear
vartheta, F_vartheta need not retain the old link-degree0 or V160 membership;
the theorem requires only its membership in the SAME FULL A0. This does not
enlarge the earlier fixed-theta finite-image claim retroactively. Nor does
the theorem assume that physical operator quantization preserves Euclidean
symbol multiplication; deriving such a map is a separate obligation.

## 4. Unitary temporal fermion twists: another comparison theorem

Keep the same all-extended 2^4 geometry, spatial links, closed two-coupling
action formula and full half algebras. Compare the family

    psi(t+2)=eta psi(t),    barpsi(t+2)=eta^(-1) barpsi(t),
    |eta|=1.

This includes periodic eta=1 and antiperiodic eta=-1. It does NOT select one
as physical, alter the adopted benchmark, or claim larger time extent.
At x=(0,r), both independent anchored temporal links V0,V1 remain. The
original symmetric coframe now has

    D_eta=V0^dagger-eta^(-1)V1,
    E_eta=eta V1^dagger-V0=-D_eta^dagger,
    T0^A(x)=1/4[barpsi_x gamma_A D_eta psi_y
                              +barpsi_y E_eta gamma_A psi_x].

The two same-link products in D_eta E_eta are -I4 each. The two independent
cross products have zero Haar mean. Consequently

    integral dV0 dV1 D_eta E_eta=-2 I4

for every unit eta, with no new Haar evaluation. The same two exterior
reordering signs and Clifford anticommutator give delta_AC B_x/4 in the
projected T0^A T0^C. The half-degree support is unchanged. Fhat still forces
the two surviving S2 vertices to the single base x; their curvature planes
are spatial. Thus the complete W6, its G and the strictly positive number a
are IDENTICAL to the accepted periodic case. All other action terms remain
excluded by complete saturation, not dropped as a model approximation.

For each compared eta and every vartheta in the class of section3,

    P_(eta,vartheta)(F_vartheta,F_vartheta)=0,
    P_(eta,vartheta)(F_vartheta,G)=g2^2 a !=0.

Hence no nonzero scalar normalization makes that full pairing Hermitian PSD.
Changing only periodic to antiperiodic temporal fermions, or combining a
unitary twist with an algebraic half-reflection convention, cannot repair
this N_t=2 full-symbol route. This is not a theorem for larger N_t, general
boundaries, added terms, constrained operator algebras or a continuum state.

## 5. Gauge invariance and pairing-preserving quotients

Fhat, F_vartheta and G are in the required gauge-invariant half algebras.
Gauge averaging fixes them; a Gauss projection alone cannot remove them.
For any scalar lambda!=0, suppose a linear map q and sesquilinear form H
were to preserve the ENTIRE compared pairing:

    lambda P_(eta,vartheta)(F,G)=H(qF,qG),   for all F,G in A0.

Then ker(q) must annihilate the original pairing in both slots. The explicit
nonzero mixed entry shows neither F_vartheta nor G can lie in that kernel.
If H were positive semidefinite its pullback would be positive semidefinite,
contradicting section4. Thus a pairing-preserving quotient cannot repair it.
No assumption that q is an algebra homomorphism is needed for this statement.

A physically derived constraint could instead restrict the physical domain
or replace the symbol-to-operator product/functional correspondence. Such a
construction must prove the original-goal source, observable, adjoint, state
and dynamics map. It cannot be described as preserving this full pairing
while silently removing its nonzero moments. No such constraint or replacement
is chosen or certified here.

## 6. Demonstrated breakdown, genuine fork and acceptance boundary

The accepted N16 full-symbol reflection route fails at nonzero g2; sections3-5
show that it cannot be rescued merely by the specified algebraic reflection
conventions, a unitary temporal fermion twist or a full-pairing-preserving
quotient. Additional normalization arithmetic cannot make this same pairing
positive. If its full Z is zero normalization is undefined; if nonzero the
same normalized pairing fails positivity. No particular normalized point or
full nonzero coefficient c0 is certified. Independent normalization remains
OPEN; g2=0 is neither analyzed here nor selected as an escape.

This does NOT establish that the original physical theory or L1's physical
objectives fail. To reach that conclusion one would need a demonstrated
correspondence making this full finite symbol pairing and adjoint necessary
for the intended physical state. Conversely a proposed successful original-
theory construction must supply an actual operator/constraint/state/source
and regulator/continuation map rather than assume positivity. The sources
and charter identify that scientific obligation, not a missing convention
for the operator to invent. No operator question is required for this bounded
symbolic breakdown, and no replacement branch is adopted by it.

The witness uses high-degree, half-volume-saturating observables. Its support
and degree are tied to this small lattice. The proof supplies no uniform
continuum/local-observable limit obstruction or proof that negative sectors
decouple in such a limit. Either extrapolation requires new controlled
estimates and original physical correspondence. Neither a selected positive
metric/dressed span nor this negative full span substitutes for those controls.

Any genuine proposal to change the original action/source/physical acceptance
scope must go through Publication ROOT for operator disposition before
replacement. All ordinary L1 source/manuscript/citation/Visser/review/gate/
integration work stays with Publication. The full N4 leading tensor remains
OPEN and owned; this is no cancellation, deferral or reduced-scope approval.
There is no positive state, derived B3 interval, tensor pole/light reference,
transport spectrum, kernel certification or publication readiness claim here.

Independent mathematics review must check the meson-power/orientation/body
argument, arbitrary anti-involution scope, exact saturation, twist factors,
quotient statement and reliance on the complete accepted mixed integral.
Independent physics/source review must check the body-to-premise table and
all physical/finite/continuum boundaries. No evaluation, Lean/slot/controller,
harness or test-infrastructure change is admitted by this construction.
