# Next positive construction design: source-exact one-slice sewing quotient

Task l1-positive-next-construction-design-r1; parent publication ROOT01a13f67; owner /root/positive_toehold_synthesis; notebook writer Executor01a1ac65. Candidate source 4aaebb7974e714dd49e052357b9677e9325ba141. This is ONE proposed constructive research attempt, not a positive theorem, physical prescription or scientific implementation. Sole output is this private report.

## Decision

Attempt a **positive factorization of the exact one-slice boundary density R_b(u), obtained from the actual open-cut coefficient contraction, and use that SAME contraction to construct a source-stable null quotient and both kernel maps.** Do not start with a Hilbert metric to fit the transfer. Do not take sqrt(R_b), its positive part, log-density, a supplied CAR vacuum, or the already rejected two-slice spatial-record cone. The positive form must be the original one-slice contraction itself and its positivity must be proved from its actual coefficients. This is a concrete factorization-and-descent problem, not another parity screen.

This is the strongest bounded constructive route I can specify from the inspected inputs. **I have not found an actual positive factorization or established that this attempt succeeds.** Thus this report is suitable for prospective assessment of an attempt, not a claim that an implementation-ready physical representation is already supplied. Its physical acceptance includes all the source/kinetic/kernel gates below; R_b positivity alone is explicitly insufficient.

## 1. Exact input, which pairing, and which algebra

Retain the original16-site/128odd/64independentSpin4-anchor functional, quarter-coframe, closed full determinant/EHC, exp(+S), periodic seams, literal J and prescribed C2 frame/overlap/denominator family. Let u denote the24 spatial anchors at boundary slice0; v the other40. With the accepted fixed two-slice coefficient reconstruction,

 R_b(u;q)=Tr_1 integral dv Omega(u,v;q),
 ell_(u,q)(f)=Tr[R_b(u;q) W_b(f)].

This fixes the entire boundary functional, including every spatial-link-weighted boundary test. It is not inferred from integratedrho0. Z(q)=integral du Tr R_b(u;q) remains the original GLOBAL denominator. R_b has a necessary positivity obligation if all spatial h>=0 are retained as commuting positive records on the candidate one-slice Weyl boundary. This is a test of a prospective boundary realization; W_b and its contraction scale are still bookkeeping, not proved physical CAR.

The proposed form is **sharp-sewn, one-slice operator-density pairing**, namely

 B_q(F,G)=Z(q)^(-1) integral du Tr[R_b(u;q) F(u)^dagger G(u)]

for polynomial boundary matrix functions F,G, with dagger the already fixed bookkeeping sharp transported by W_b. This formula is fixed by original coefficients and the declared candidate boundary product; no matrix G is optimized. It differs from geometric theta pairing ell(theta f wedge g): the latter uses a different map, exterior product, and time/link reflection. The known full metric theta witness must NOT be transported into this B by pretending these products agree. Conversely, if an attempted source/constraint descent identifies this B with the old theta pairing on that unchanged witness, the candidate has met the known obstruction and must be rejected at that identification. No fresh negative-Gram work is requested.

Positivity of B on ALL boundary matrix functions is equivalent to R_b(u;q)>=0 a.e. It is not guaranteed by Hermiticity, integratedrho0, integratedPPT or the source Ward identities. This equivalence states the target; it does not discharge it.

## 2. Explicit coefficient construction of the form — no existential sewing matrix

Use an inherited ordered exterior basis xi_I for each64-generator slice. At the zero-source base A=I the accepted one-slice decomposition is available:

 s_b=C_b+(B_s,b+B_t,b).Rplus_b+B_s,b.Rminus_b+H00,b(Rminus_b+Rplus_b)^2,
 D_b=B_t,b.Rminus_b+2H00,b Rminus_b.Rplus_b,
 s_b=s_b^-+s_b^++D_b.

At the actual base J=0, A=I, D_b=0. Define EXACTLY the accepted edge weight and its finite polynomial kernel

 E_01=s_0^+(X0,X1,v0)+s_1^-(X0,X1,v0),
 k_01(X1,X0)=integral dv0 exp(E_01),
 E_10=s_1^+(X1,X0,v1)+s_0^-(X1,X0,v1),
 k_10(X0,X1)=integral dv1 exp(E_10).

The eight temporal anchors on EACH edge are integrated independently; all24 spatial links of slice1 are integrated only at their actual sewing. For general q, use the original PAIR weights exp(C+B.R+H00R.R), equivalently the two actual edge weights WITH exp(D0)exp(D1) at their shared variables. A D=0 product must never stand for the unrestricted source germ.

Here is a deterministic extraction rule for EVERY entry of the prospective boundary matrix, avoiding any choice of amplitude signs or eigenbasis. On the full128-generator original pair, let theta_I range over ordered Majoranas supported on slice0, C_I their fixed32-mode matrices, sigma_I=(-1)^[|I|(|I|-1)/2], d=2^32. Form

 m_I(u;q)=integral dU1^sp dv0 dv1 I_(xi0,xi1)
       [ exp(s_0+s_1) theta_I ],
 R_b(u;q)_(ab)=d^(-1) sum_I sigma_I m_I(u;q) (C_I)_(ab).

All128 odd integrations occur in m_I, even though theta_I lives on one slice. This is the accepted full coefficient dictionary specialized to the partial trace, not an assumed wavefunction. The C/B/H/D formulas and their exact source derivatives determine every coefficient. No local conditional partition appears.

To expose the actual finite sewing circuit rather than call an unknown matrix J a proof, expand each kernel in inherited exterior coefficients and in a finite polynomial compact-link basis. Use the exact coefficient rule

 (T_01)_(K,I)(u1,u0)
   =sum_J epsilon(J,I) [xi1_K xi0_J] k_01,

where epsilon(J,I) is zero unless J is the complement of I and is otherwise the ORIGINAL coefficient of the slice top in xi_J xi_I. Use the analogous rule for T_10. This specifies every Grassmann sewing sign; Haar contractions are the actual integrals of the corresponding compact-link basis products. The supertrace uses Gamma_I=(-1)^|I| and the already derived invariant support only where justified. Do not use auxiliary orthonormality as a physical adjoint.

This finite circuit, followed by the displayed fixed Clifford trace-dual transform, is the amplitude source. A prospective construction must KEEP its explicit factors and prove a Gram refactorization of them. An arbitrary identity R_b=A†J A with A assembled afterward from R_b entries is not the requested result.

## 3. The constructive factorization target and first acceptance milestone

The positive construction sought is an explicit coefficient amplitude family A_r(u;q), with rows labelled by retained one-slice occupation indices and internal labels r drawn from the ACTUAL cut exterior/compact-link coefficient circuit, such that

 R_b(u;q)_(ab)=sum_r conjugate(A_r,a(u;q)) A_r,b(u;q).

An internal Haar variable may remain under a normalized integral instead of a finite r-sum. The amplitudes must be obtained by grouping the actual exp(C+B.R+H00R.R) coefficient factors and their sharp-conjugate partners, with EVERY complement/Haar/periodic sign accounted for. They cannot be supplied by sqrt(R_b), a spectral positive-part operation, a Cholesky algorithm conditioned on unproved PSD, or replacing either half of the original action by the other's conjugate. Such replacements would merely hide the missing positivity or change the model.

**First scientific milestone after prospective approval:** derive the explicit open-cut coefficient contraction for R_b and organize it into blocks under actual boundary gauge/charge and graded insertion actions; on those blocks identify and prove a common sum-of-squares grouping from the original halves, or give the precise unmatched coefficient/sign preventing THAT grouping. The target is the FULL retained one-slice density, including its behavior at the spatial-cancellation locus, not selected positive principal minors. No new sign certificate, parity search or sampled eigenvalue test is the deliverable. The actual grouping is currently unprovided; the source equations above specify what must be grouped and which sign identities must be proved.

A REQUIRED structural compatibility audit precedes accepting any positive grouping: the new spatial result establishes z_sp(u′)=Tr R_b(u′)=0 at the retained-spatial cancellation locus. A continuous positive R_b there would have to vanish as an ENTIRE matrix. Thus the proposed amplitude factorization must establish A_r,a(u′)=0 for every amplitude/index, equivalently that EVERY one-slice coefficient m_I(u′) vanishes, not merely the scalar partition m_empty. The accepted bidegree exclusion proves the scalar statement; insertions theta_I can change saturation, so it must not be reused as a proof of the all-coefficient assertion. Derive/check the complete inserted bidegree roster and its actual coefficient contractions as part of amplitude construction, with all40 other anchors retained. This is a necessary structural admission test for a POSITIVE factorization, not a request to construct another finite negative certificate. If it fails, this specific commuting-spatial/Weyl boundary construction is inadmissible and the failure must be reported without claiming a broader quantization no-go.

If an exact half-amplitude Gram grouping cannot be written, this design does not authorize inventing an indefinite factorization and declaring its range positive. A specific failed grouping is information about that attempt, not an all-route obstruction. Continue constructive source research under the existing commission; no operator must invent a norm to make it work.

A finite independent prospective review can assess this attempt before its proof exists: the coefficient circuit, product candidate, source carrier and success conditions are all fixed. Actual acceptance must read the resulting grouping coefficient by coefficient (or a proved all-index identity); a label such as “fermion-bag positivity,” “pseudoreality,” or “RP” is insufficient without its exact action/sign applicability.

## 4. Domain, quotient, product and adjoint that a successful factorization would build

From a PROVED factorization define the amplitude map directly,

 (V_q F)_r(u)=sum_b A_r,b(u;q) F_(b,* )(u)/sqrt(Z(q)),

with the remaining matrix-column index retained. Thus the amplitude target carries the ordinary coefficient/Haar square norm and ||V_q F||²=B_q(F,F). This norm is not an independently fitted physical norm: its equality to the original one-slice functional is the preceding theorem obligation. Define N_q=ker V_q and H_q as completion of range V_q. Keep the original polynomial domain modulo N_q as the dense domain. Do not divide by z_b(u), including at its zeros. Do not impose a singlet support to manufacture positivity; the actual Ward action must descend equivariantly.

Boundary matrix multiplication has an induced representation ONLY for operators preserving N_q and having an adjoint preserving it. Require this for the algebra generated by the ACTUAL source, current and constraint operations used below, rather than automatically declaring every original exterior variable a CAR annihilator. The physical candidate product is composition on the descended insertion algebra; its adjoint is uniquely induced by B_q whenever it exists. It must be calculated on generators from the proved amplitude pairing, not postulated as psi†=barpsi, derivative†=multiplication, or a kinetic CAR normalization.

For ordinary left boundary matrices the bookkeeping dagger supplies an initial algebraic candidate, but identifying those matrices with physical original fields still requires the kinetic/cotangent gate. In particular the original momenta are independent, the accepted forces have positive odd degree, and the degenerate degree-zero kinetic body does not make a regular Dirac inverse available. A representation of coefficient wedge/contraction is not a derivation of gravitational CAR. The candidate succeeds physically only if the source/constraint comparison identifies a nontrivial admissible descended algebra and its actual product/adjoint with the original boundary observables.

## 5. Exact insertions and both kernel maps: indispensable gates

Exterior source insertion is fixed, not adjustable. On the full carrier use

 L_r^wedge(X)=[c_r X+P(X)c_r]/2,
 V_h(X)=W_full[h wedge W_full^-1(X)],
 Omega_alpha=V_(s_alpha)^times(Omega),
 Omega_alphabeta=V_(s_beta)^times V_(s_alpha)^times(Omega)
                                  +V_(s_alphabeta)^times(Omega).

These are the accepted Bopp operations. Integrate/partial-trace AFTER constructing them. A nominal spatialQij with time in any frame row/jet uses the full64-mode/two-slice lift. Bare normal labels and rigid Jordan insertion are already rejected alternatives; neither may replace V_h. The source operation need not be multiplication by a single static metric matrix or a CP tangent. The physical time-ordered/composite interpretation is a result to derive.

Specify cut maps I_in,q and I_out,q by applying the same amplitude extraction to the ACTUAL input/output boundary coefficient circuits. Do this separately for the accepted reflected/opposite cuts, giving I'_in,q,I'_out,q with their actual reflected profiles. Their precise finite formulas must be output of the coefficient construction; **they are not supplied merely by V_q on an equal-time density**. No claim of physical transfer may precede them.

For each original forward step L_q, define T_q[I_in,q f]=[I_out,q L_q f] only AFTER proving the relation is single valued: ker I_in,q maps into ker I_out,q. For the reflected step Ltheta_q require the analogous primed statement. Establish a bounded/closable operator on the stated dense domain and its actual adjoint law by the same original sewing contraction. Do not impose Ttheta=T† by relabelling geometric reflection; compare the full EHC source-reflection defect and the four orientation-sensitive maps. Reproduce the original periodic trace/sewing and all normalized tests with these maps, including both temporal seams and source-dependent multipliers.

The differentiated gate is the actual kinetic/source equation

 I_out,alpha L+I_out L_alpha=T_alpha I_in+T I_in,alpha,

with the complete mixed derivative and BOTH cross-first terms. Require it for every J/frame/current direction, including frame acceleration, overlap and normalization contacts. Unknown physical cut maps have their own source derivatives; the constant P0↔N0 coordinate maps do NOT set these derivatives to zero. Full pair D/Bt/expD and all four mixed two-step placements remain.

Constraint admission must use the actual graded operators D+M_(D s), their ordered derivative contact in the accepted equation23, and the true pre/post ideal-sidedness. The tests to prove are preservation of the amplitude null space and compatibility with the induced adjoint, including source-lift equations. No classical stationary ideal is simply set to zero, no RAQ self-adjointness assumed, and no phase invariance is reinterpreted as singlet support. The constant global phase generator must descend with the actual current identity, not an imposed charge-zero condition.

If the cut-map extraction or null stability fails, positive R_b would still be only a positive boundary state. Report that exact limitation; do not rename it positive physical time. Conversely, a successful noncommuting ordered-kernel realization is NOT obliged to reproduce the rejected doubled-Weyl joint positive cone: it must reproduce every original multi-time test through its derived ordering/contact operations. Any identification of its positive multi-time products with the rejected R_sp/Pminus test cone would encounter the already accepted obstruction and cannot be silently made.

## 6. Positive acceptance sequence and physical datum

Milestone P1: exact all-index original R_b coefficient circuit and actual half-amplitude sum-of-squares identity, with a justified real-source domain or a precise restriction to a base state. A full source-positive neighborhood needs a proved gap/factorization; source continuity alone does not promote semidefinite positivity.

Milestone P2: the amplitude-null quotient, nontrivial source/constraint-stable descended insertion algebra, induced product/adjoint, and gauge/global-charge representation derived from that identity. This is the first positive boundary/domain construction, still without automatic causal time or calibrated metric.

Milestone P3: all four actual cut maps, forward/reflected kernel descent, adjoint/sewing law, full C2 source contacts and original normalized generating functional reproduced. This is the necessary physical correspondence milestone. Neither P1 nor a generic Stinespring dilation substitutes for P3.

Milestone P4: identify the descended coframe/composite/current operators with the original kinetic/constraint data and the required physical metric insertion, with normalization covariance and matter/time/absolute-scale reference. The accepted lambda ray with fixedW1 is not a physical limit: the kinetic correspondence shows the covariantly transported contraction scale leaves the state unchanged. Therefore it is not offered here as a controlled infrared construction or a way to choose a favorable phase. B3/N4/tensor/light/transport and controlled4D limits remain separate original obligations.

The precise source datum still missing for a PHYSICAL promotion is a boundary polarization/ordering convention DERIVED from the actual graded kinetic/cotangent relation that selects which descended insertion/derivation operators are physical adjoint pairs and fixes their scale. Possible evidence would be an explicit source-compatible quantization of the original pre/post boundary relation, with the amplitude pairing above giving its adjoint and the source identities fixing its composite contacts. The current action, independentbar/psi fields and Ward identities do not already supply that theorem. This is a research obligation, not a request that the operator choose a favorable norm or authorize ordinary investigation again. No particular polarization is adopted in this design.

## 7. New accepted negative history and uncertainty

Newest ORIGINAL_SPATIAL_RECORD_RECONSTRUCTION and its acceptance were read FULL. They prove, at their exact scoped manual boundary, failure of BOTH classical24-spatial-record/full-two-slice-Weyl hybrid and CP-instrument densities. All40 other anchors remain integrated. Their effect uses both slices and does NOT settle one-slice R_b. The full metric geometric RP and earlier all-history link failures remain bounded failed identifications, not global no-go theorems. The specified bare Lorentz Haar cycle fails absolute integrability after its stated gauge reduction; distributions, other cycles and controlled Euclidean reconstruction remain open. No Lorentz cycle is used to repair the present candidate.

No positive amplitude grouping, physical quotient, physical CAR, four cut intertwiners, source-ordering identification, metric mean/body/signature or calibrated kinetic/matter sector has been derived here. The proposal is not a guaranteed positive theorem disguised as an implementation plan. It is ONE constructive factorization-and-descent attempt with explicit inputs and falsifiable acceptance identities; a fresh independent prospective reviewer should assess whether its first amplitude-grouping task is sufficiently bounded and scientifically discriminating. If not, the honest outcome is an unprovided construction rule, not an arbitrary G or another negative-certificate commission.

## 8. Exact inputs and activity

Under docs/audits/2026-11-05-l1-physical-bridges/ in the assigned checkout:

- ORIGINAL_SPATIAL_RECORD_RECONSTRUCTION.md SHA2567bd54eedcc36fae5fd9340301f44189d6ee12bdce06572042125d0266ac52993; acceptance b6ab816190d761c2bbb47e41c400cd2095dce24d8f111ffc755706f0ccc46f24. Both actual reviews accepted; ROOT personal intake pending at the assigned checkpoint.
- ORIGINAL_ONE_SLICE_SOURCE_KERNEL.md SHA256769838b284108660b08fb8f2bde6675d00d6b8209520cdcafcd43a5c3773fd65: §§1–3 exact C/B/H/D; §§5–7 equations9–22 actual A/B cut reduction, k/T coefficient sewing, full-source pair defects; §9 physical map boundary.
- ORIGINAL_MICROSCOPIC_METRIC_COHERENT_BRIDGE.md SHA256563aeda483e743933580139c7edc8c8ca32f9522ddd74128f091bf736b1062b2: §§3–7 exact coefficient/coherent kernels, R_b and Bopp/ordering contacts; §§8–10 failed shortcuts and remaining maps.
- ORIGINAL_TRANSFER_POSITIVE_PROCESS_RECONSTRUCTION.md SHA256d4e59e8d68ab4b6babc4f3daf374372bb1dddfbd4840e763b16a8eaafef248fd: original full coefficient reconstruction, accepted integratedpositive/PPT/channel and fullsource identities; no physical step identification.
- ORIGINAL_GRADED_CONSTRAINT_RELATION.md SHA25607054c34ffa7edb9ee141bef0f45a5396047ca14b534563df400119c6f31ce6c: §§3,5–8 typed relation, actual pre/post ideals, ordered kernel contact23 and source lifts.
- ORIGINAL_KINETIC_NORMALIZATION_CORRESPONDENCE.md SHA25650bb6c95b3c135c0956fb8b56a14c4ee443894d0abfe7455dbd08f4a59bbe019: §§3–4 kinetic/contraction covariance; §§6,10 current, actual physical equations30–31 and calibration boundary.
- ORIGINAL_LORENTZ_COMPOSITE_CYCLE.md SHA256aa32c7c983a2aa994a26d6336ffc2a7d925c9b1e1c495ff7c9de6a43b76612f1: restricted continuation/barecycle result, previously read in the scout scope; no new contour theorem invoked.
- P0_NUMERICAL_FULL_CUT_TRANSPORT.md SHA256b9bc1e82ab2f1eef802fa07738b93babe79dcf2d820759d09c040142f7153a1f: §§6–7 exact four coordinate cut maps/fullC2 transport, not positive physical maps.
- POSITIVE_RECONSTRUCTION_TOEHOLD_RESEARCH.md 664c3a6f755299f25a8c42432251a14ffa6a5d5184cc6a836ac18b7a660455bd and synthesis3afbe8fa62f0c2912e1eb62a6e38dcaf089cf4843357691833724d3d6a12a5c5: prior scoped scouting, no new imported theorem.

Topical primary L1FixedControls notebook entries and Phase6a OPEN BUILD/physical reconstruction assignments were consulted through current packet/context; no whole-portfolio absence claim. Earlier full process/coherent/scout readings remain context; this turn directly read the newest spatial result+acceptance, one-slice actual kernel/reduction, kinetic normalization/physical-map sections, graded relation/ordered-contact/physical gate and cut/source transport, plus the latest notebook update. No new external theorem or uninspected paper is a load-bearing premise.

FIRST action: SAME l1-positive-next-construction-design-r1.json check returned fresh=true, changed=[]. Only read-only cat/sed/rg and ordinary private artifact/continuity/hash bookkeeping. No actual proof construction, scientific evaluator/CAS/exterior/Gram/Haar/MC/numerical program, Lean/MCP/build/test, controller/slot/process/backend/GPU/dependency/harness action, repository/notebook/other-agent edit or commit. No other agent consulted before freezing this report. Direct assignment restricts ownership to this private report despite packet future repository path. ROOT ordinary Eq4–11/numerical/cut implementation/runtime/main/reset work remains unchanged. FINAL SAME fresh outcome and frozen hash are returned to the lead.
