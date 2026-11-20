# Actual Grassmann-valued Eq7: original construction C, prospective design r2

Status: PROPOSED FOR DIFFERENT INDEPENDENT PROSPECTIVE REVIEW. No implementation, Lean elaboration, kernel result, build result or C acceptance is claimed.

Task publication-grassmann-valued-eq7-design-r2; parent publication-remediation; owner eq7-design-author; notebook writer and integration owner ROOT. Own only this R2 report and its JSON companion; R1 artifacts remain immutable. First shell action executed the SAME assigned R2 packet check: exit0, fresh=true, changed=[]. Then read its packet/ROOT notebook and the complete different independent review R1 Markdown/JSON (ACCEPT_FOR_IMPLEMENTATION with two required author clarifications). This R2 changes only product typing/order and the zero-coframe weighted control, plus revision/provenance metadata; all other R1 text below is retained byte-for-byte, including the record of source/discovery work performed in R1. Packet source is PRIMARY84cb3f5911bcffc4d071662af2311908f89de279. Its owned_files entry names the accepted B1 input, not permission to edit it; dispatch limits writes to the two new R2 /tmp files. No source/Git/build/cache/controller/slot/MCP operation was performed. The JSON records the exact exhaustive R1→R2 diff and unchanged-block hashes; different independent review of these exact corrected bytes remains required.

## Original scope and authority

Read original complete ADW_EXACT_AUXILIARY_IDENTITY.md Eq1–11 and original AUXILIARY_COMPENSATION_GRASSMANN_DESIGN_R1.md at the cumulative checkpoint, complete accepted 702-line GaussianAuxiliaryCompensation.lean (A), complete accepted 527-line FiniteGrassmannCoframe.lean (B1), their independent full-source/kernel reviews, B1 scope r2, packet/notebook, CLAUDE and governing pipeline/continuity, and owning Phase6a roadmap. The accepted reviews supply scoped A/B1 evidence, not this author's independent kernel verification. Read installed lean4 skill for statement/type discovery; project restrictions supersede its build suggestions. Static searches included actual Mathlib declarations and the project lean_deps.json types; the graph does not yet return A/B1 entries and is not an absence oracle. No live LSP is available under this design-only assignment, so declaration discovery and syntax validation remain incomplete.

Directly read held Diakonov2011.pdf, arXiv1109.0091v1, PDF pages11–15 as extracted text, especially p11 Eq14/16, p12 Eq17, p13 Eq21/23, p14 Eq24–27, p15 Eq28. Held path is workspace Lit-Search/Phase-5d/primary-sources/Diakonov2011.pdf, outside the nested PRIMARY checkout. Earlier attempted nested path did not exist; workspace copy was then read. This is text-source reading, not a new visual PDF review. The B1 independent review supplies its prior rendered-page review and SHA132d63150a678ef17bfbbc04978a8cab9c9801f03556982a6aa67c11d3fbc4da. No source quotation is needed for the mathematical construction.

Original C includes actual coframes, actual source polynomials, actual Gaussian G-valued integrability/equality, local Eq7 and its product over sites. A universal conditional evaluation theorem alone cannot complete it. The original design's suggested standard forward plaquette cannot silently override its later discovered ordering boundary. C will explicitly define both literal and closed source polynomials and instantiate the same theorem separately. Equivalence, gauge invariance and physical action correspondence remain B2 obligations; C cannot certify the original manual's unqualified word “precisely” for either action.

## Actual carrier and a genuine norm

Reuse B1 exactly: Torus L has positive extents; Site L is the product of four ZMod coordinates; V=volume L; Gen L=Site L × (Fin4 ⊕ Fin4), card=8V; Coordinate L=Gen L→ℂ; G=Grassmann L=ExteriorAlgebra ℂ (Coordinate L). C=bilinearAlgebra L is its actual algebra-adjoin of coordinate pairs. Open scoped IsMulCommutative only where C's CommRing is needed. The inclusion j:C→ₐ[ℂ]G is injective. G remains noncommutative. Named barred generators remain independent complex coordinates, with no Hilbert adjoint or physical state.

Let n=4V*2 and b=(coordinateBasis L).ExteriorAlgebra, an actual Basis (Finset (Fin n)) ℂ G. This uses B1's ordered Fin coordinate basis, avoiding any fresh arbitrary order on sites/generators. Let E=b.equivFun:G≃ₗ[ℂ](Finset(Fin n)→ℂ). Choose the induced sup norm, explicitly ‖g‖=max_s ‖E(g)(s)‖. This is a real norm on the genuine G, not a diagonal scalar image. The target finite Pi space already has its sup norm, complex NormedSpace and completeness. Candidate local constructions to live-elaborate are NormedAddCommGroup.induced G _ E E.injective and NormedSpace.induced ℂ G _ E; check that their inherited additive/module instances agree definitionally. Establish FiniteDimensional ℂ G from b.finiteDimensional_of_finite, then CompleteSpace G by FiniteDimensional.complete ℂ G. Also restrict scalars to ℝ for Bochner infrastructure. Prefer named scoped instances so imports do not accidentally install competing norms on ExteriorAlgebra globally.

Proof-bearing exports: grassmannBasis, grassmannCoordinates (linear equivalence), grassmann_norm_eq_coordinates, coordinates_injective, grassmann_finiteDimensional, grassmann_complete. Prove equality of the norm to the finite-coordinate norm and norm=0 iff element=0; do not export only an existential assertion without constructing the norm used by the integral. Cardinal dimension can be proved finrank ℂ G=2^(8V) from this basis/card-finset, but is not needed computationally. No enumeration of 2^(8V) elements is executed. No NormedRing, NormedAlgebra, multiplicative bound or analytic exp is required anywhere. Every function to be integrated is a finite sum of complex integrable scalar functions times fixed vectors.

## Exact finite exponential and degree budget

Use nilExp M z=Σ k∈range(M+1), ((k.factorial:ℂ)⁻¹) • z^k, defined for any complex algebra. It is independent of the desired integral. The source exp means this finite nilpotent exponential, justified by the following proofs, not by defining exp as the RHS of Eq7.

For a finite index ι, t:ι→C, write t^β=β.prod(fun i e→t i^e). The reusable bridge has the explicit single algebraic premise jointZero M t: ∀β, M<β.degree → t^β=0. A/B1 do not provide this as an assumption at the actual theorem: it is discharged below. Prove:

1. eval_trunc_poly: aeval t (truncTotal(M+1)(U:series))=aeval t U for every ordinary polynomial U, by its finite monomial expansion and jointZero. Never claim ordinary truncation is an algebra hom.
2. low-degree coefficient agreement implies equal evaluations of ordinary polynomials, by killing all higher monomials.
3. J(F)=aeval t(truncTotal(M+1) F) defines an AlgHom ℂ from formal series to C. Prove multiplication by finite truncation convolution locality, then evaluation of all discarded terms is zero. Unit/add/scalars follow their actual maps. No unrestricted evaluation of infinite series is invoked.
4. J(coe U)=aeval t U; if U.constantCoeff=0, J(auxiliaryFormalExp(coe U))=nilExp M (aeval t U). Call A.auxiliaryFormalExp_coeff_finite then (1); map the finite sum/powers through aeval.
5. Any zero-constant polynomial U in t has (aeval t U)^k=0 for k>M: every monomial in U^k has degree≥k. Prove the support lower bound by induction/convolution, not totalDegree (which is an upper bound). Same for any positive-constant-zero source sum. Thus nilExp K z=nilExp M z for K≥M on these arguments. The Gaussian exponent L(h)=Σ(h_i:ℂ)•t_i obeys this too.
6. For positive-ideal a,b with commuting products, nilExp M(a+b)=nilExp M a*nilExp M b. The double finite sum uses the binomial coefficient identity; terms with total original coframe degree>M vanish. Individual nilpotence of a and b alone is insufficient for this common cutoff. Formulate the lemma for a,b given as evaluations of zero-constant polynomials in one jointZero family, or explicitly prove the mixed a^k*b^l vanishing for k+l>M.

At actual global coframe index I=Site L × Fin4 × Fin4, t=coframeEven L U, M=4V. B1.coframe_monomial_zero proves aeval t(monomial β 1)=0 for degree>M. Rewrite aeval_monomial to obtain jointZero. No new nilpotence premise remains. At local i=Fin4×Fin4, t_x(i)=coframeEven L U (x,i.1,i.2), derive the same GLOBAL bound by renaming/local monomial embedding into I, or B1.weighted_product_grade with coframe_grade. The latter avoids proving rename injectivity just to establish the bound. It does not replace M with 4 or 8: each local coframe contains neighboring-site generators and the regulator has 8V global generators. Use the same M=4V in every local compensation polynomial and site product. Generic grade-two t into the actual G is useful for controls and is an additional theorem; the actual coframe theorem is mandatory.

## Analytic bridge: actual integral, no assumed evaluation commutation

Set μ(ι,v)=Measure.pi(fun _:ι→gaussianReal 0 v), σ>0, v:ℝ≥0 and hv:(v:ℝ)=σ². Let B_M=(Finsupp.finite_of_degree_lt(M+1)).toFinset, as used inside Mathlib truncTotal. Let L_t(h)=Σi(h_i:ℂ)•j(t_i). Prove the finite multinomial identity in C and map into G:

nilExp M L_t(h)=Σβ∈B_M, ((auxiliaryMonomial β h:ℂ)/(auxiliaryFactorial β:ℂ)) • j(t^β).

It holds without nilpotence because both sides are exactly the degree≤M exponential of a linear form. Proof route: ordinary polynomial L_X(h)=Σi(h_i:ℂ)•X_i; use coeff_linearCombination_X_pow_of_fintype, the multinomial factorial identity and coefficient extensionality for auxiliaryFiniteExp M L_X(h). Then aeval/map powers and sums. Prove each product factorial is nonzero before cancellation. In particular β!=(∏i β_i!), never |β|!. Empty ι and M0 are included.

For arbitrary P, prove integrable_weight_nilExp (not compensation only):

`Integrable (fun h : ι → ℝ ↦ auxiliaryWeight σ P h • nilExp M (L_t h)) μ`.

Expand the finite sum. Call integrable_auxiliaryWeight_mul_monomial σ hσ v hv P β; divide by the fixed nonzero factorial; use Integrable.smul_const with fixed j(t^β), then integrable_finsetSum. This proves measurability and finite norm integral independently of the desired value; no integral-by-default-zero shortcut.

Then prove integral_weight_nilExp equals Σβ∈B_M [(∫h W(h)h^β dμ)/β!] • j(t^β), using integral_finsetSum and integral_smul_const. This is a PROVED evaluation/integral bridge. Equivalently it equals j(J(auxiliarySeries σ v P)); prove the coefficient/truncation sum identity, not assume aeval commutes with integrals. No finite-dimensional norm on the infinite-dimensional ordinary polynomial ring is needed. An alternative finite coefficient space `(β:{β // degree≤M})→ℂ` is legitimate: its explicit evaluation linear map is continuous by finite dimension and `ContinuousLinearMap.integral_comp_comm`; but only after proving coefficient-vector integrability. The direct finite-sum route has fewer structures and is preferred.

Take P=compensationPolynomial M σ S, hS:S.constantCoeff=0. Each normalized coefficient is exactly A.integral_compensation_normalized (or raw plus nonzero factorial). A.compensation_series_truncTotal and the J exp theorem then give the final generic actual-G identity:

nilExp M (j(aeval t S)) = ∫h:ι→ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h • nilExp M (Σi(h_i:ℂ)•j(t_i)) ∂μ(ι,v).

Generic theorem binders may expose jointZero. The actual local/global coframe exports below must not expose it, commutation, integrability, compensation or integral equality as a premise.

## Source-specialized local Eq7 and explicit scales

Local variable type D=Fin4×Fin4, X_(μ,A). Define epsilon4 on four Fin4 labels as the sign of the corresponding permutation, zero if repeated, normalized epsilon4(0,1,2,3)=1. Prove both the orientation control and repeated-index zeros; do not use a floating epsilon table or replace it by +1. A sum over permutations is an equivalent finite implementation.

Pin A=dirac(U x κ), B=dirac(U(forward x κ) λ), C=dirac(U(forward x λ) κ), D=dirac(U x λ). Define two literal matrix words:

plaquettePrinted x κ λ = A*B*Cᴴ*Dᴴ (p12 Eq17 in the given endpoint notation);
plaquetteClosed x κ λ = Dᴴ*Cᴴ*B*A (the distinct convention compatible with carrying around the loop under Eq21).

Use these exact names/words, no equality theorem, cyclic-trace replacement, action correspondence or gauge claim. For either specified plaquette F define

S_x^F(X)=g1 Σ_(A,B,C,D) epsilon4(A,B,C,D) X_(0,A)X_(1,B)X_(2,C)X_(3,D)
 +(g2/4) Σ_(κ,λ,μ,ν,C,D) epsilon4(κ,λ,μ,ν) trace(F(x,κ,λ)*gamma C*gamma D*gamma5) X_(μ,C)X_(ν,D).

The gamma maps are B1's source-ordered blocks; all products are ordered as displayed. g1,g2 may be arbitrary ℂ; real finite source couplings specialize by inclusion. Constant coefficient is proved zero for each construction. Prove coefficient normalization and homogeneous degree4/degree2 controls, including zero couplings; these are source polynomial construction checks, not proof that the two F define the same physical action.

The p14 Eq24 last expression has no additional 1/4! in the fixed direction cosmological sum: the earlier antisymmetrized spacetime expression contains 1/4!, which has already canceled. EHC retains exactly g2/4. p15 Eq28 uses exp(+Σx S_x). Pin positive sign. For a>0 define ehat_i=(a:ℂ)⁻¹ • T_i. Prove a⁴ times each four-ehat product equals the four-T product, and a² times each two-ehat product equals the two-T product, using a≠0. No Hermite σ rescaling enters T=a*ehat. Weight uses h/σ, σ^(-|α|), v=σ² as already defined by A. Auxiliary h multiplies dimensionless T directly.

Required actual exports (proposed signatures; names/syntax to validate live):

`coframe_local_integrable (L) (U:Links L) (x:Site L) (S:MvPolynomial D ℂ) (σ) (hσ:0<σ) (v) (hv) : Integrable (fun h:D→ℝ ↦ auxiliaryWeight σ (compensationPolynomial (4*volume L) σ S) h • nilExp (4*volume L) (∑i,(h i:ℂ)•coframe L U x i.1 i.2)) μ(D,v)`.

`coframe_local_eq7 ... (hS:S.constantCoeff=0) : nilExp (4V) (j(aeval t_x S)) = ∫h, ...`.

`printed_source_local_eq7 (L U x g1 g2 σ hσ v hv)` and `closed_source_local_eq7 ...` instantiate these at the explicitly constructed S_x^F, with no hS or degree/nilpotence assumptions. Provide actual integrability counterparts. Such separate instantiations complete C's full source-specialized identity surface without certifying B2. A theorem only for arbitrary S with no constructed source instances is insufficient for original C.

## Original global product, fixed links only

For supplied family S_x (zero constant), define P_x=compensationPolynomial(4V) σ S_x and independent h:Site L→(D→ℝ). Define μsite=Measure.pi(fun _:Site L→μ(D,v)). First define c_x=nilExp(4V)(aeval t_x S_x) in the actual commutative subalgebra C, and let I_x be the actual G-valued local integral ∫h_x W_x(h_x) • nilExp(4V)(L_x h_x) ∂μ(D,v). Prove I_x=j(c_x) by the actual local Eq7 and the proved compatibility of nilExp with inclusion. Thus every actual local integral lies in the image of C before any product is formed. State both:

nilExp(4V)(Σx j(aeval t_x S_x)) = j(∏x c_x);

The displayed Finset.prod is formed ONLY in C, then included into G. To state the product of actual G-valued integrals, for every list xs enumerating Site L exactly once prove (xs.map (fun x ↦ I_x)).prod = j(∏x c_x). Substitute I_x=j(c_x), use that j preserves binary multiplication, and use commutativity in C to prove this equality for every enumeration. Consequently all such ordered List.prod values agree; equivalently prove pairwise Commute(I_x,I_y) from the same included-C values and derive order independence. This is the original product of actual local integrals with its typing/order evidence, not a formal surrogate. Never install CommMonoid or CommRing on full G or use Finset.prod of G values.

and the actual single Bochner integral

nilExp(4V)(Σx j(aeval t_x S_x)) = ∫h, (∏x W_x(h x)) • nilExp(4V)(Σx L_x(h x)) ∂μsite,

with independent integrability of the global integrand. State its reindexed version on I=Site×D with μ(I,v), proving measure transport for the currying equivalence rather than identifying nested and uncurried Pi measures by notation. All coframes are the SAME global B1 coframes and all cutoffs are the SAME4V. This is original product Eq7 at fixed compact links; it is not a new single global compensation weight substituted for ∏xW_x.

Proof: rename each source to I and use actual common jointZero. NilExp addition/product comes from the common ideal's mixed bound. Expand each local finite exponential; the global integrand becomes a finite sum indexed by sitewise multiindices. Each scalar term is a product of integrable one-site `W_x*h_x^β_x` divided by factorials, times one fixed G vector. Prove product-measure integrability and factorization by finite induction/Fubini from those actual scalar integrabilities (Mathlib finite-Pi product lemmas to locate live; fallback induction is mathematical proof, not a new assumption). High-total-degree vector terms vanish by B1. Thus derive the single integral by finite sums and scalar product factorization, independently of nonlinear multiplication under an integral. Instantiate for both printed/closed source families, preserving their distinction. Empty finite site interface may be generic, but actual positive torus has V≥1; do not advertise M0 as an actual zero-volume torus.

## Pinned existing declaration evidence and discovery limits

PRIMARY lean/SKEFTHawking/ADW/GaussianAuxiliaryCompensation.lean: auxiliaryFiniteExp lines27–29, compensationPolynomial31–37, auxiliaryFormalExp_coeff_finite103, compensationPolynomial_eq_finite142, compensation_series_truncTotal214, integrable_compensation_monomial226, integral_compensation_normalized234, raw245, compensation_source_truncation498. Their actual source statements were inspected; no reproof or edit is proposed. GaussianAuxiliaryComplex.lean: auxiliaryDegree/Factorial/Monomial/Weight26–36, integrable_auxiliaryWeight_mul_monomial58–65, auxiliarySeries383. FiniteGrassmannCoframe.lean: coframeEven, coframe_grade, coframe_mem, weighted_product_grade, coframe_monomial_zero, coordinateBasis, inclusion_injective and actual controls are the called input API. The source hash is4d9ae0f635b648a88dbd7cdf07ccd2248553057aa12f3633c92ea7657dc35261; A hash99a40ad1f4304547b2701845e14f168fd3cfcaf2a7526b07eed4eaa7aaead2b6.

Under pinned lean/.lake/packages/mathlib/Mathlib:

- LinearAlgebra/ExteriorAlgebra/Basis.lean:30 `Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M)` requires LinearOrder I; B1's Fin index meets it. Basis.equivFun is an actual linear equivalence, not a multiplicative map.
- Analysis/Normed/Group/Basic.lean:736–748 generated additive forms `NormedAddGroup.induced`, `NormedAddCommGroup.induced` transport along injective additive maps; Analysis/Normed/Module/Basic.lean:185 `NormedSpace.induced` supplies compatible complex scalar norm inequality.
- Topology/Algebra/Module/FiniteDimension.lean:512 `FiniteDimensional.complete`; :277 `LinearMap.continuous_of_finiteDimensional`; :300 `LinearMap.toContinuousLinearMap`. Completeness must be explicitly installed; this theorem is not assumed to be an automatic instance.
- Algebra/MvPolynomial/Coeff.lean:86 `coeff_linearCombination_X_pow_of_fintype a s n` gives `if s.sum id=n then s.multinomial*s.prod(a_i^e_i) else0`.
- Data/Nat/Choose/Multinomial.lean:77 `Nat.multinomial_spec` states product factorial times multinomial equals factorial sum; :406 `Finsupp.multinomial_of_support_subset` connects support/fintype versions. Complex factorial cancellation still needs nonzero proofs.
- RingTheory/MvPowerSeries/Trunc.lean:326 `truncTotal` uses `(finite_of_degree_lt n).toFinset`; :330–338 exact retained/zero coefficient lemmas. Exclusivity requires M+1.
- MeasureTheory/Function/L1Space/Integrable.lean:1011 `Integrable.smul_const`; Integral/Bochner/Basic.lean:246 `integral_finsetSum` requires integrability of every summand. The old integral_finset_sum spelling is deprecated.
- Integral/Bochner/ContinuousLinearMap.lean:218 `integral_smul_const` for complete complex normed targets; :69 `ContinuousLinearMap.integral_comp_comm` requires integrability of the domain function and complete domain. These are genuine proved integral tools, not a shortcut to infer integrability.

Static search initially used a nonexistent FiniteDimension/*.lean glob and nonexistent Data/Finsupp/Multinomial.lean path; corrected actual source paths above. No Lean/tool/backend failure occurred. Runtime metadata idle slots was not treated as permission. Matching live LSP hover/type searches, candidate statement elaboration and Pi-product factorization API discovery are required on ROOT-admitted proof execution. Do not install new tools or infer proof absence from these searches.

## Discriminating actual controls

Controls must compare actual G values or actual integrals after evaluation, with nonzero witnesses where needed. Scalar A controls can be reused but cannot replace these.

1. Normalization/sign: in a genuine G choose t=b1+b2 from two disjoint coordinate pairs, so B1 proves t²=2 b1b2≠0 and t³=0. For S=gX², prove Eq7 equals1+g t²; for i-real coupling the uncompensated Gaussian generates the minus quadratic while real coupling gives plus. Check the variance coefficient σ²/2, not σ² or1/(2σ²). Use positive σ2 and1/2, v4 and1/4, and prove the resulting G values agree while P coefficients change.
2. Complex linear source: S=iX with this t, prove target1+i t−t²/2≠1+i t, retaining factorial2 and no coefficient conjugation. RHS must be genuine integral.
3. Mixed factorial: choose t=sum two disjoint pairs, u=sum two other disjoint pairs in the actual eight-generator algebra, so t²u²≠0. For S=(1+i)XY, nilExp target is1+(1+i)tu+i t²u². The scalar raw(2,2) moment4i is divided by2!*2!, yielding i, not1/4!; detect incorrect coefficient by the actual nonzero t²u². Prove constants via B1 basis/top-word controls.
4. Global mixed cutoff: two-site pair witnesses give nonzero cross-site products below M. For arbitrary actual coframe multiindices of total degree>M call B1.coframe_monomial_zero, including mixed sites/repeated coordinates, not just each t_i^(M+1). Global site product uses this same bound. Generic bilinear topPairs reaches degreeM nonzero; do not assert every physical coframe saturates it.
5. Arbitrary-degree source: on a genuine torus with V≥2 choose t a sum of seven disjoint pairs, prove t^7=7! times a nonzero fourteen-generator word and t^8=0. S=iX7 then has target1+i t^7. A raw seventh moment5040i must cancel7!, and the term must survive. Degree>M source additions evaluate to0 and leave P and Eq7 unchanged; prove source locality at actual evaluation. Do not reduce universal S to degree4.
6. M0 and empty coordinates: separate the true constant-integrand cases from zero coframes at positive cutoff. M0 jointZero forces every t_i=0; A proves P=1, and nilExp0=1, giving1=∫1 dμ. Empty coordinates with hS force S=0 and P=1 for every M, again giving1=∫1. There is no nonempty-coordinate premise. For a generic zero family t at arbitrary M>0, every zero-constant S evaluates0 and nilExp M(L_t(h))=1, so the actual integrand is auxiliaryWeight σ (compensationPolynomial M σ S) h • (1:G), which need not be pointwise constant. Prove its scalar weighted mean ∫W dμ=1 by A.integral_compensation_normalized at β=0 (with auxiliaryFactorial0=1 and the zero-constant source exponential coefficient1), then use integral_smul_const to obtain the G-valued1. Discriminating example: for one variable S=iX and M1, P=1+iX and W(h)=1+i h/σ²; prove this formula and the actual mean1 rather than replacing W by1. Actual torus has positive volume; use B1.one_site_identity_coframe with actual identity links at M4. All these actual coframes vanish, every hS source evaluates0, but the genuine RHS is the integral of its possibly nonconstant W times1 and must be proved equal1 by the weighted-mean argument. Keep the one-site M4 actual weighted integral as a separate mandatory control; do not replace it by the easier M0/empty constant-integrand test.
7. Source construction: epsilon(0,1,2,3)=+1, odd permutation−1 and repeated indices0; cosmological fixed-direction coefficient has g1 with no extra factorial; EHC coefficient g2/4, source gamma5 order and quarter hopping remain B1's actual values. Check g1=0/g2=0 and both0. Do not replace literal/closed words by each other. Their separate kernel statements must retain the correct names.
8. Scale: prove a⁴/a² cancellation at a=2 and1/2 as consequences of the general a>0 theorem. Keep a, σ and actual real h distinct. For global product compare two-site source terms using the same global coframe family and independent Gaussian site fields; do not test a diagonal h_x=h_y surrogate.

## Proof-ready package ownership and acceptance

ROOT should obtain a different independent prospective source/math reviewer before dispatch. Recommended dependency graph, to fit runtime capacity without shared edits:

C1 owns NEW lean/SKEFTHawking/ADW/FiniteGrassmannEvaluation.lean only: imports accepted A/B1, constructs the scoped norm and actual basis/completeness, nilExp and ideal/truncation/J lemmas, finite multinomial expansion, actual local/global premise discharge and cutoff/addition controls. This is the next coherent proof-ready package. It must expose actual G basis/norm and generic+actual coframe APIs, not leave them as typeclass assumptions at acceptance.

C2 after C1 owns NEW GaussianGrassmannAuxiliary.lean only: actual integrability/finite integral bridge, generic Eq7, actual local coframe Eq7, local controls including nonzero G coefficients. No source A/B1 edits. Reusable generic lemmas should live in C1/C2, not a new infrastructure mechanism.

C3 after C2 owns NEW FiniteGrassmannSourceAuxiliary.lean only: explicitly labeled printed/closed source polynomial construction, epsilon/sign/coupling/scaling controls, source-specialized Eq7, sitewise product and actual global integral/integrability with reindexing. It can prepare a source-only package independently of C1, but cannot claim C acceptance before integration. ROOT can combine C2+C3 in one admitted worker if that reduces API churn; no new fourth slot or parallel conflicting source ownership.

Each assigned worker is not alone, edits only its module, never reverts peers, reads ROOT's notebook/roadmap/packet, uses only its admitted matching slot LSP, and records actual full requests/responses. No builds, cache repair, controller, reset, aggregate, registry or integration edits by workers. ROOT owns dispatch, lease/reset, absorption, authoritative builds/extraction/generated updates and the existing remediation planner. No new axiom, sorry, native_decide or heartbeat override.

Per package require actual file diagnostics, every public theorem closing goal and all-export #print axioms from the exact full source, only propext/Classical.choice/Quot.sound, source scans and targeted lean_verify. A different independent implemented-source reviewer must assess the actual integral semantics and nonvacuous controls and repeat kernel evidence, not accept compiled statements alone. ROOT then runs appropriate whole-project Wave gates; neither prospective acceptance nor scoped kernel checks are full-tree/publication acceptance. C acceptance requires the entire C1–C3 surface above, source-specialized actual G-valued Eq7 and independent Gaussian global product, with no hidden hypotheses. Partial packages remain named partials.

Original Eq9 matrix construction/signs, Berezin orientation/determinant Eq10, compact-link continuity/Haar/Fubini over link fields, inserted observables/derivative-of-W Eq11, nonzero normalized Z, phase/positive sampling and all original physical source/state/adjoint/response/B3, mode/matter/transport, continuum/thermodynamic/simulation and publication gates remain OPEN. Fixed-link Gaussian product factorization here does not close compact-link Haar/Fubini. This design does not disposition, replace or lower any of these goals.

Memory used only for project discovery discipline and separation of local evidence from publication; present scientific assertions are based on the sources inspected in this task. Final freshness is recorded in the JSON companion after the final SAME-packet check.
