# Independent D10 physical Coulomb-density and source-proposal review

**SCOPED MANUAL MATHEMATICS AND THREE-PATH SOURCE-PROPOSAL ACCEPT. No mandatory correction found in the reviewed candidate.** I accept the nonauthor review scope and independently rederived equations1–16, their domains/equality cases, density-fiber construction and coefficient normalization. Acceptance is for this spinless continuum N=1 fixed-centre positive-charge family and the exact unapplied three-path roadmap/note proposal. It is not a Lean inhabitant, native/kernel/build result, general interacting many-electron HK theorem, full D10/G4/G5/G11/Stage9, finding closure, source application, publication/main or human acceptance.

Reviewed complete original CONSTRUCTION.md SHA33aa181e79b77e9b84bc857887ba2b1a0ec0ab4870979b67cf372230ea6f9e13, author REPORT/PLAN/evidence/process, composition plan, complete three-path patch and pre/postimages. The first original reviewer packet check passed0/fresh/changed=[] from assigned N. Bound notebook is r52/848be5f1ef25f2c641aed27edc43986522d6c2bb3c4b58c8434f186c62bf690b. Earlier E1 reservoir authorship is a different candidate and creates no authorship conflict for this D10 note.

## 1. Actual carrier and endpoint hypotheses

The construction works on L2(R3;C), normalized H1 states, Z>0 and a fixed point nucleus, initially in atomic units. It treats a.e. classes, not pointwise values at the Coulomb singularity. N=1 has no electron–electron interaction and spinless means no suppressed spin degeneracy claim. No arbitrary molecular configuration, antisymmetric N>1 state or binding condition is smuggled into this special case.

The origin and infinity arguments are adequate at manual-analysis level. An outer cutoff eta_R with bounded gradient O(1/R) gives H1 convergence: the cutoff gradient term is bounded by O(1/R)||u||2 and the removed u/gradient tails vanish. Convolution then gives smooth compact approximants using translation continuity for u and every weak derivative. For such a smooth compact f, the inner cutoff changes the L2 function by O(epsilon^(3/2)); the old-gradient term has the same volume scaling, while ||f grad chi_epsilon||2 is O(epsilon^(1/2)) in dimension3. Thus the punctured smooth functions are indeed dense in the FORM domain H1. This is not an assertion that a punctured-domain Laplacian is essentially self-adjoint or is an OPERATOR core; the construction does not make that false substitution.

On that core, expanding grad u+x*u/(2r²), and using div(x/r²)=1/r² away from zero, gives exactly
||grad u||2²-(1/4)||u/r||2². Complex cross terms use the real part, so the coefficient is correct. The resulting Hardy estimate ||u/r||2<=2||grad u||2 extends by weighted Cauchy convergence and an a.e. subsequence. It proves the actual weighted limit rather than assuming singular weights preserve unweighted L2 convergence.

Cauchy–Schwarz now gives integral |u|²/r<=2||grad u||2||u||2. For two H1 functions the difference of these integrals is bounded by
2||u-v||2(||grad u||2+||grad v||2). The pointwise estimate ||u|-|v||<=|u-v| is enough here; this step does not circularly assume the later modulus-gradient theorem. Consequently the Coulomb form is continuous in H1. Young's inequality gives Z*integral|u|²/r<=eta||grad u||2²+(Z²/eta)||u||2². With eta<1/2 and a sufficiently positive L2 shift, the q_Z norm is equivalent to H1; the lower and upper estimates prove closedness and semiboundedness. The closed-form representation theorem is an explicitly used standard analysis theorem, not an assumed ground state or a fresh native proof.

## 2. Completed square, actual eigenstate and every equality case

With rhat=x/r, div rhat=2/r distributionally and there is no delta mass at zero: the small-sphere flux is O(epsilon²). Expansion gives
(1/2)||grad psi+Z rhat psi||2²
=q_Z[psi]+(Z²/2)||psi||2².
The sign and factor2 match nuclear ATTRACTION. Extension from the punctured core is legitimate because the potential form has just been controlled and multiplication by bounded rhat is continuous on L2. No arbitrary rough-H1 pointwise trace or boundary flux is assumed.

For phi_Z=(Z³/pi)^(1/2)e^-Zr, the independent radial integrations give:
4Z³ integral r²e^-2Zr dr=1,
||grad phi_Z||2²=Z²,
integral |phi_Z|²/r=Z.
Thus T=Z²/2, attraction=-Z² and E0=-Z²/2. phi_Z is an actual normalized H1 state with zero completed square. This constructs the infimum and its attainment; neither is supplied as a carrier field.

The form polarization/eigen-equation argument is sound. The zero-square state satisfies q_Z(phi_Z,eta)=E0<phi_Z,eta> for all H1 test eta, placing it in the associated operator domain. Independently its distributional Laplacian is (Z²-2Z/r)phi_Z in L2; the absence of an origin delta and the Fourier characterization yield H2 membership. The lower form bound excludes lower spectrum. This identifies the declared usual Coulomb form realization, not an automatically proved identification with the Lean operator.

Equality requires grad psi=-Z rhat psi a.e. On any bounded ball exp(Zr) is a bounded Lipschitz multiplier, so f=exp(Zr)psi belongs to H1_loc with zero weak gradient. Poincare on overlapping balls makes f a single complex constant on connected R3. Normalization then leaves exactly a global phase times phi_Z. This proves the one-dimensional ground eigenspace and no other normalized minimizing states. Z>0 is essential: Z=0 has no displayed normalized exponential/minimizer and is explicitly excluded. No assertion of nondegeneracy for a spinful or general molecular ground state follows.

## 3. Modulus inequality, representability and finite attained infima

The regularization u_epsilon=sqrt(|psi|²+epsilon²)-epsilon is the right infinite-volume choice: it is L2 because 0<=u_epsilon<=|psi| and its scalar composition vanishes at zero. The un-subtracted sqrt(|psi|²+epsilon²) would not be L2 on R3 and is not used.

For fixed epsilon, the derivative of the smooth map R2→R has norm<=1. In smooth H1 approximation, bounded derivatives control the term multiplying grad(psi_j-psi); continuity of the derivative plus a.e. subsequence/dominated convergence handles the term multiplying grad psi. Thus the asserted Sobolev chain rule and
grad u_epsilon=Re(conj psi grad psi)/sqrt(|psi|²+epsilon²),
|grad u_epsilon|<=|grad psi|
are justified. Strong L2 convergence of u_epsilon to |psi| and weak L2 compactness of its gradients identify the weak derivative of |psi|; weak lower semicontinuity proves the integrated modulus inequality. No phase derivative at zeros or magnetic extension is assumed.

Therefore the density image of normalized complex H1 states is exactly
D={rho>=0 a.e., integral rho=1, sqrt rho in real H1}.
One direction uses the modulus theorem. The other is constructive: sqrt rho itself is a normalized real nonnegative H1 state with precisely that density. Every admitted density fiber is NONEMPTY and contains a finite-energy witness.

For a fixed admitted rho, every fiber state has kinetic energy at least T[sqrt rho] by the modulus inequality. That finite value is in the actual energy set. The real infimum is therefore attained and equals (1/2) integral|grad sqrt rho|², not a merely asserted semibounded number. At zeros no division by rho is used. For N=1 there is no hidden interaction term.

The external energy depends only on rho and is finite by the proven Hardy/Cauchy–Schwarz bound. Thus E_Z[rho]=q_Z[sqrt rho]>=-Z²/2. The explicit rho0=|phi_Z|² belongs to D and attains equality. If any other admitted density attains equality, its nonnegative square root must be a constant-phase phi_Z by the independently proved equality equation; nonnegativity and normalization force rho=rho0 a.e. This establishes unique minimizing density from actual states, not by returning a pre-assumed DensityVariational.nondegen field. The statement is on D, not every raw real function.

## 4. Strict cross-family comparison and source-unit rescaling

I independently recomputed the charge-family comparison:
q_Z[phi_W]=W²/2-ZW and
q_Z[phi_W]-E0(Z)=(Z-W)²/2.
For Z!=W both cross inequalities are strictly positive, so these are actual Rayleigh–Ritz strict comparisons. Their densities cannot be equal a.e.: continuity away from zero upgrades a.e. equality there, and their radial logarithmic slopes -2Z/-2W then agree only if Z=W. This is a nonvacuous injectivity result within the specified family. It does not establish the general HK theorem.

The note correctly refuses the nondegeneracy-only shortcut. Nondegeneracy excludes two distinct rays at one ground energy for ONE operator; it does not itself prove that another potential's ground ray is different. A common ray, including constant-shift examples, makes the cross inequality an equality. A general external-potential proof needs actual eigen-equations/common-state exclusion and applicable UCP/nonvanishing/domain hypotheses. No such general theorem is invented here.

The rescaling is exact. For alpha>0, k=Z/(2alpha),
alpha||grad psi+k rhat psi||²
=q_alpha,Z[psi]+Z²||psi||²/(4alpha).
This follows because -2alpha*k=-Z and alpha*k²=Z²/(4alpha). The normalized (k³/pi)^(1/2)e^-kr has kinetic Z²/(4alpha), attraction -Z²/(2alpha), energy -Z²/(4alpha); its constrained-search value is alpha integral|grad sqrt rho|². For alpha=hbar²/(2m), m,hbar>0, k=mZ/hbar² and E0=-mZ²/(2hbar²). The same cross-family excess becomes (Z-W)²/(4alpha).

This coefficient is grounded in actual canonical source: KineticEssentialSelfAdjoint lines130–134 and166–218 retain momentum=-i*Constants.hbar*derivative and momentum-square Fourier symbol (2pi*hbar)²|xi|²; lines462–470 use kineticOperator_eq with scalar(2m)^-1. The 2pi here is the Mathlib Fourier convention, not an extra factor in the physical differential coefficient alpha. I additionally read/pinned the presently available Physlib SpaceDQuantumSystem source's kineticOperator definition, which has precisely the(2m)^-1 momentum-square scaling. This is a source observation, not proof of installed dependency/import/build compatibility. The molecular potential definition at MolecularHamiltonian461–475 reduces for N=1 and a singleton origin nucleus to -Z/r a.e., with the pair sum empty; its value at r=0 is immaterial.

Restoring units does not identify a dimensionless atomic number with the source's coefficient Z. Nor does it map a Hilbert space, measure, H1/form domain or operator domain into Lean merely by using the same name. The explicit native representation/normalization bridge remains OPEN.

## 5. Actual Lean progress and interface traps

I read all three actual DFT module bodies, not only theorem names. GroundStateData has n,E,F and decomp; it does not contain a normalized state/operator/groundness proof. The uniqueness and injective signatures separately require BOTH strict cross inequalities. Their cancellation/order proof is valid conditional content; the header's general nondegeneracy-only explanation does not supply the missing common-state argument.

DensityVariational.Ev takes EVERY raw X→Real and its ground/nondegen fields already assert attainment and unique minimization. Its theorem really derives the lower-infimum bound and returns those equality fields. The new physical result instead proves those facts for an admissible density carrier. A native bridge needs a suitable subtype/indexed carrier or meaningful extended-energy semantics; simply assigning arbitrary finite real energies to invalid functions would not construct physical DFT.

LevyLiebData's bddBelow requirement does not imply nonempty fibers. For an empty fiber, the Real conditionally-complete infimum does not mean physical +infinity. The existing equality theorem supplies a minimizing witness and concludes F_LL n=TW psi0; no separate HK object occurs in the statement. The candidate avoids both traps with the explicit D/square-root witness and actual attainment; it does not claim a fake inhabitant of the present all-functions interfaces. The theorem-name/inhabitance machinery and source-comment defects are not silently closed.

I also read the actual load-bearing molecular, kinetic, relative-bound and CP-semigroup declarations. MolecularHamiltonian511–516 supplies the real measurable potential symmetry; KineticEssentialSelfAdjoint462–470 constructs self-adjoint kinetic closure. CoulombRelativeBound2462–2492 PRODUCES a,b with0<=a<1,b>=0 and consumes them in the apex taking only N,m,m>0,nuclei. Its graph-limit proof has actual Cauchy/image/closedness steps; it is not a wrapper over an hrel premise. LindbladCPSemigroup574–599 obtains a Kraus family from proven complete positivity and trace preservation, with no supplied hreal. These are real source achievements and must not be reopened as planned work. I did not re-prove/native-check every lemma in the large existing analytic/CP corpus; this is exact source-scope verification, not a new kernel census.

The complete August17 review and full current793-line D10 manuscript were read. Their negative physical-density case and original findings1.3–1.6 are consistent with this bounded progression: a manual special-case result is not yet a native inhabitant, and it does not erase broader theorem-name, proof-substance, global inhabitance/gate or prompt/index debt. The manuscript is unchanged by this proposal.

## 6. All twenty roadmap units, histories and current dependencies

The independent literal reconstruction applies every declared replacement to its uniquely matching original roadmap occurrence. Reversing all twenty in reverse order reproduces BOTH full original roadmap byte strings. I read both complete proposed roadmaps, all original/new replacement texts and the actual patch contexts. The units correctly:
1. replace current global COMPLETE with full physical B1 BUILD while preserving the June29 build/pin receipt as history;
2. retain the original many-electron Coulomb/HK/variational/constrained-search objective;
3. label old substrate observations historically;
4. correct the HK strictness premise;
5–8. credit actual W1–W4 source progress and distinguish the physical gaps;
9. replace obsolete hkin/hrel routes and the automatic500LOC/wall exit with actual discharges plus OPEN physical bridge;
10–11. reconcile sequencing and historical DoD;
12–13. give D10 current status and remove cost/disclosure as scientific completion;
14–16. correct hkin/hrel/hreal inventory ownership/source;
17. describe the actual W2/W3/W4 routes;
18. retain full W5 physical/native work, actual normalization and dependency/historical-pointer limits;
19. retain transport/open-system synthesis as OPEN;
20. preserve actual review/native/integration/closure duties and permit coherent partial checkpoints.

The old first-lift/substrate/planning receipts remain dated context under explicit current/historical framing; they are not observations that D10 still lacks a manuscript. The genuinely historical missing prompt/notebook pointer is disclosed as not repaired by these three paths. No current global absence census or lifecycle closure is inferred. The proposal preserves actual mathematical achievements and original breadth instead of reducing B1 to this solvable example.

Author-captured history was inspected as evidence, not rerun. The complete decoded/raw pairs match for all ten captured command records. The June30 f285f4bf66d1a2fa40574a9da9aac0874de21f48 receipt and its actual saved source apex have no analytic-hypothesis arguments. The distinct July29 db37f9b4b6a5caa65aa749287bd92faaa2001ad0 receipt records API/measure repairs, not new physical DFT. The original ambiguous db37 lookup remains rc128; the exact subsequent query is separate. These source/history observations do not recertify the old build/kernel claims. Some static/final author captures expose differing timestamp field spellings; I preserve their actual schema rather than manufacturing missing timing data.

Additional read-only observations requested by lead, separate from the immutable packet: current P lean-toolchain is leanprover/lean4:v4.32.0 (SHA2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e). The configured lakefile SHA7008b3d79ac294f4e822e8c867a326c316e94ff9047c4fd110e66b9cab84e5fe pins Mathlib81a5d257c8e410db227a6665ed08f64fea08e997, Physlibc48433678e8fb6306ebcd48453300c8e16058a62 and matching REPL. Its existing OPEN ITEM explicitly notes that the July29 bump already brought unbounded spectral source into the configured substrate; swapping the in-tree implementation remains a separate bridge/axiom-review decision. The proposal does not claim the old4.30 bump is still the manual-work blocker, perform/authorize a new bump, or certify a live compiled environment. Actual dependency changes retain the original authority/clean-branch/blast-radius requirements; ordinary manual construction is not made to wait for an obsolete trigger.

## 7. Exact patch integration, preservation and scope

Independent parser replayed the actual plain unified patch (not presumed Git-header syntax), all3 paths/10 hunks forward against the complete saved preimages and backward against complete postimages. Every context/old/new line count and positional context matched. The resulting bytes equal each advertised full postimage; reverse bytes equal each original, with a new file represented as an empty saved artifact but an ABSENT actual target. The new public note equals complete CONSTRUCTION33aa181e, and the two actual P roadmap bytes/modes equal their exact prerequisites. All proposed file modes are0644. No tracked application was performed. Generic lead ownership is public provenance; declared private/ignored path patterns were absent from all public postimages.

This is a coherent three-path source-proposal acceptance, not a license to apply it over changed targets or transplant whole N/P branches. P selected source observations and N packet state are different scopes. Exact current prerequisites and the existing protected workflow govern later application. Coherent accepted partial mathematical/source work can checkpoint before full B1 completion; no recurring per-commit human approval or all-portfolio scientific prerequisite is invented.

Only the five assigned ignored reviewer outputs and fresh read-only metadata scratch are written. No mathematical/symbolic/numerical software evaluation, project import, test/Verify/model execution, Lean/native/MCP/build/compiler, network/holding, actual source/PDF/book/registry or Git/index/ref mutation was performed. The canonical continuity adapter performs its own read-only state queries with explicit bytecode/cache/temp/offline/optional-locks settings; that is not a proof lease.

Reviewer preparation defects are retained honestly: an assumed diff--git header caused ValueError on the actual plain unified patch; initial author-capture iteration assumed a list instead of a dict, and a later corrected-history loop assumed the opposite shape for one singleton record. These source-reading wrappers failed and were corrected by explicit schema handling, not by changing source or weakening a preservation predicate. One overbroad capture display included base64 and was truncated; complete raw captured records remain intact and were subsequently compared through bounded per-command channel digests/equality, not inferred from the truncated display. An initial guessed old Physlib DDimensions path lookup failed; current source normalization and an actually existing dependency path were then read. Some other large source displays were truncated; the full construction, both proposed roadmaps, complete20 replacement data, all three DFT modules, manuscript and carrying critical declarations were read in bounded follow-ups. These are reviewer-only metadata/capture limitations, not canonical test/native failures, new source defects or permission to repeat runtime.

The original historical N raw-index FAIL/cause UNKNOWN is retained as documented in the r52 book/base reconciliation. This review does not cure that history, infer an actor/cache cause, or claim blanket raw-index preservation from semantic stage equality. Current acceptance concerns the packet/bounded selected inputs and exact proposed unit.

## Original final check and terminal preservation

The final original supported reviewer check returned1 with changed=["owned-files"]. This is exactly the expected five-owned-output drift; no authority/source discrepancy was reported. All103 original reference/changed-source hash comparisons, all21 author-selected byte/mode/size/ns-mtime controls, and all3 additional dependency observations matched on direct terminal recheck. Packet bytes were unchanged and never refreshed. The first/final literal commands, assigned N cwd, new per-child temp/cache/offline/bytecode/optional-lock settings, UTC/rc and full separate decoded/base64 channels are retained. This measures bounded selected state, not a global P freeze or a cure of the historical raw-index exception.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory contradiction remains in the candidate. The old planned hkin/hrel/hreal and whole-DFT COMPLETE story conflicts with actual source; the proposal corrects it without erasing achievements. Nondegeneracy alone does not establish strict cross comparisons; the charge family now proves its own strict inequalities. Raw real-function infima do not automatically mean physical admissible densities or nonempty fibers; the new one-electron result constructs those witnesses and attainment. Atomic units do not set the actual Lean hbar to one; the explicit alpha bridge correctly preserves it. The full general antisymmetric many-electron/UCP/native construction, original synthesis and scientific/publication/main obligations remain OPEN.
