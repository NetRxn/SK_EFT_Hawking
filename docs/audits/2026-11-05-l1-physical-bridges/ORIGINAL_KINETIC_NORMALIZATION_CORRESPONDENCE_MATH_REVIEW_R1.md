# Independent ACTUAL mathematical review — kinetic/current normalization R1

Verdict: REVISE for one necessary normal-map normalization definition in section4. The other checked scaling/current/kernel/source formulas pass at the stated manual support scope. Preserve this frozen R1 and report; final acceptance should await an exact corrected revision. This is not a physical metric construction or a no-go.

Candidate /private/tmp/l1-original-kinetic-normalization-result-r1.md: 34796 bytes; SHA256 e2b59c5c63dde68515f68acabdb800b481030cc624c63dfc750f7fc46b38f03f.

## Necessary repair: specify the normal map at nonunit contraction

Candidate line103 states that 'the normal/Weyl conversion is exp(-kappa Delta/2)' without defining a kappa-dependent normal map. The inherited normal map from accepted coherent R2 is the UNIT-CAR map N_1(barpsi_I psi_J)=a_I† a_J. With that fixed map, the assertion is false already on a linear field:

 N_1^-1 W_kappa(psi_i)=sqrt(kappa) psi_i,
 exp(-kappa Delta/2)psi_i=psi_i.

It is also distinguishable on the number symbol: the fixed-map result is kappa*barpsi_i psi_i-kappa/2, not barpsi_i psi_i-kappa/2.

The intended narrow repair is to define explicitly on EVERY normal monomial

 N_kappa(barpsi_I psi_J)=kappa^((|I|+|J|)/2) a_I† a_J,
 N_kappa(1)=I,

with the same inherited index ordering and linear extension. Then

 N_kappa^-1 W_kappa=exp(-kappa Delta/2)

is correct. Required controls include linear psi/barpsi mapping to sqrt(kappa)a/a†, and W_kappa(barpsi_i psi_i)=kappa(n_i-I/2)=N_kappa(barpsi_i psi_i-kappa/2).

Alternatively retain N_1 and include the degree dilation D_a f(q)=f(aq):

 N_1^-1 W_kappa=exp(-Delta/2) D_sqrt(kappa)
                  =D_sqrt(kappa) exp(-kappa Delta/2).

This distinction is material to the claimed WHOLE normalization-covariant coherent/contact diagram, not a change to the proposed physical theory. Defining the transported N_kappa is sufficient; it selects no measured hbar, physical CAR or favorable ordering. No change to Eqs8–10, the current formulas or the physical limits is otherwise indicated by this review.

## Continuity, authority and actual review work

FIRST action from /Users/johnroehm/.codex/worktrees/l1-coupled-fixed-controls/.publication-l1-checkpoint-20261103:

`python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-original-kinetic-math-result-r1.json`

First and final SAME checks returned fresh:true, changed:[], exit0. Final check immediately preceded report writing; no snapshot refresh or discrepancy. Packet checkpointd95370a95128599ef9dbecb4bd3105b55f0019d4. Read FULL frozen candidate/packet and newest relevant primary notebook. Both exacted19 prospective approvals/read/fresh checks precede construction; this is ACTUAL proof review, not prospective endorsement. Reused the previously reviewed original coframe/force, graph/IBP/source, continuum alpha, coherent, normalization and conditional-process inputs at their accepted scopes. Governing pinned authorities/roadmap and inspected primary qualifications remain unchanged.

Commands: continuity adapter twice; cat FULL candidate/packet; tail -n8 of primary notebook; nl/sed of candidate lines100–140; stdlib pathlib/hashlib byte-count/SHA read. All factor/sign checks below were MANUAL. No scientific import/evaluator/CAS/matrix/exterior/Haar/Gram script, tests/build/Lean/native/slot/controller/harness/runtime action or process/suite probe. ROOT ordinary operations were untouched. Only this report was written; no candidate or other artifact changed.

## Checked covariance, kernel and cotangent factors

The r_lambda direction and Berezin Jacobian are correct. For q'=lambda^-1 q, each odd differential gives lambda, so the full128-variable factor is lambda^128. T/Y, Q and action homogeneities give the displayed transformed couplings and J_lambda=lambda^4 J with frame paths unchanged. At fixed scaled source argument the inverse right argument is lambda^-4 J'. Connected first/mixed quotient responses inherit the literal lambda^-4 factors; frame-only derivatives retain the full supplied path contacts. The degree12 temporal test and quartic insertion give lambda^-16. No accepted normalization or nontriviality is withdrawn.

Each step removes exactly64 old odd coordinates. Scaling copied shared/output coordinates and substituting only the old integral therefore gives Eq5's lambda^64. The matched intermediate pullbacks in the two-step composition yield lambda^128, preserving periodic sewing and the accepted parity/gauge identities. There is no additional integral over the copied variables.

Conjugating multiplication and LEFT differentiation gives lambda^-1 and lambda respectively. Independent cotangent momentum therefore scales contragrediently as p'=lambda p; it is distinct from the independent barred coordinate. The odd forces have weightlambda and link forces weight1, so the full graph/free shared momentum and pre/post pullbacks transport as claimed. Transport of a projected ideal is not proof of regularity or a formerly unknown source lift.

The zero-source continuum alpha comparison is correctly delimited. E,P,C,K and Lambda have the stated weights, making both terms invariant and the spinor momentum coefficient weightlambda. The candidate expressly does not apply this first-order velocity form to a temporal J00 deformation, which may be quadratic in continuum velocities, nor claim a controlled continuum limit.

For kappa'=lambda^-2 kappa, W_kappa'=W_kappa r_lambda follows monomialwise, and the star/adjoint covariance follows by transport. The kappa Bopp formula has the correct sqrt(kappa) generator and needs no inverse factor: it retains an absent Majorana and cancels a repeated one. The normalized trace-dual density equality Eq10 follows from equality of pairings against the complete W_kappa' basis, independently of positivity. Fixed-unit-product moment suppression and transported-product covariance are correctly distinguished. The only missing convention here is N_kappa, as specified above.

## Checked full current, gamma placement and kinetic charge

V_chi acts with opposite phases on barred/unbarred generators and is an even derivation. Its Berezin divergence cancels sitewise. For a forward anchor the negative reversed hopping term gains the opposite phase, leaving the plus B sum. For the backward negative term the phase difference reverses, leaving the SECOND plus in Eq13. C has gamma on the opposite side of U from B; neither is commuted through the link. This verifies the four endpoint terms and both anchored contributions.

Eq14 is the derivative of the COMPLETE determinant/EHC/J polynomial with respect to Y, followed by A's transpose. The determinant slot product, both EHC slots and diagonal-source factor2/off-diagonal-once convention are correct. Curvature is phase-fixed but remains in the force. Collecting the same directed anchor yields the two endpoint-force terms in Eq15 with factor i/4. No periodic link has been collapsed or canceled merely because its neighbor vertex coincides.

Evaluating the existing graph on the SAME shared phase field cancels the free shared kappa terms in the charge difference. Link momentum evaluation is zero because this transformation fixes links, but its dependence in forces remains. The continuum alpha contraction has two equal half-spinor contributions giving i chi Lambda_A barpsi gamma_A psi, with degree4/8 rather than a bare occupation bilinear. It is correctly kept at zero source and only structurally compared to the finite current.

## Checked kernel and explicit metric contacts

For Eq18, shared differentiation supplies its weight vertex plus the copied-test derivative; the new endpoint supplies its weight vertex; old divergence-zero IBP gives L V_a=-vertex(V_a s). Subtracting the old input term produces the stated positive full-current vertex. This proves the displayed commutator orientation. Constant GLOBAL chi gives finite intertwining; local chi is a current variation, not an added gauge symmetry or a charge-zero constraint.

Literal J_(r,00) differentiates the full coframe force to2T_r0 at j=0. Applying Eq13 to Q=T^2 gives Eq19's i/2 and both temporal anchors. The corresponding derivative of the bond current in Eq20 has the same i/2 factor and the correct tail/head Kronecker terms. At nonzero frame its2 A_0mu Y_0 replacement is correct. Local VQ is explicitly retained; global neutrality is not used to delete it.

The current-vertex derivative is w(s_alpha C+C_alpha), and its mixed derivative has the original weight contact, both crossed current derivatives and C_alphabeta. Fixed V commutes with source derivatives. Equations21–23 retain frame acceleration, time-mixed carriers before reduction, and all four sewn placements. They are actual microscopic source operations, not substituted Jordan scores.

## Checked normalized Ward and calibration boundary

Zero divergence gives the arbitrary-test periodic Ward law with V f+f C. The quotient formula Eq25 includes both first-normalization subtractions and(2m_alpha m_beta-m_alphabeta)omega X, where m_alphabeta is the RAW second-normalization ratio, not the connected Hessian. The displayed A_f derivatives include source-dependent tests. Only after the zeroth/first identities at the same source family may the quotient terms be removed. Eqs26–27 therefore have the correct literal/frame product, VQ and VQ_beta contacts. The f=1 specialization is not substituted for the arbitrary-test result.

The complete force has weightlambda^2 and the hopping sums weightlambda^-2, giving invariant current, cotangent charge and phase generator. Literal-current derivatives have weightlambda^-4; frame derivatives have no external literal-source factor. Including the old integral gives the same lambda^64 current-vertex kernel covariance. Thus the normalization/current/source diagram commutes at the explicitly stated algebraic scope, subject to repairing the normal-map definition.

Equations30–31 are honestly unresolved PHYSICAL equations: a domain/product/adjoint and source-dependent physical map/transfer, with its derivative terms, have not been constructed. A Ward identity does not identify a microscopic physical metric or calibrate its response. Physical unitarity is only a compatibility requirement for the CONSTANT global phase, not local site phases. No physical Hilbert state/domain, CAR, matter interpretation or causal time evolution is selected.

For the explicitly CONDITIONAL simple calibration, T scaleslambda^-2 and Q scaleslambda^-4, so keeping the physical quantities invariant requires the statedlambda^2 coframe factor andlambda^4 metric calibration. J=c_Q K and a constant-calibration response c_Q^2 W_JJ then transform consistently. This does not fix c_Q, a, hbar, time or matter residue. Source-dependent calibration would need further contacts and the actual physical derivative map. The optional mean-normalized ratio only cancels weights when that mean exists and is nonzero; it is not L1 chi/B3 by nomenclature.

## Handback and remaining scope

REVISE solely for the explicit N_kappa or fixed-N degree-dilation repair at line103. Preserve R1; freeze the narrow correction and obtain renewed actual review. The other inspected formulas support a substantive first original phase-current/kinetic/kernel/source correspondence with covariance, not a physical normalization or metric reconstruction. No new optional cone/no-go or infrastructure action is required.

Actual original normalization, temporal response and prior scoped results remain accepted. Physical Hilbert/product/adjoint/CAR, quantum link/time dynamics, coincident metric/source map, mean/spatial order/signature, absolute/matter calibration, B3/N4, tensor/matter/light/transport and controlled limits retain their full requirements. ROOT retains ordinary L1 roadmap/repairs/manuscripts/consumers/findings/gates/reviews/main/integration/operator authority. No runtime or publication acceptance follows. Only this report was written.
