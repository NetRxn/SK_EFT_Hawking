# Original Eq4 compensation and actual Eq7 Grassmann evaluation: prospective design r1

Status: MATHEMATICAL PROPOSAL FOR INDEPENDENT PROSPECTIVE REVIEW. No Lean implementation, proof, LSP result, kernel acceptance, native build, publication acceptance or scientific closure is asserted by this report.

Task `publication-auxiliary-compensation-design-r1`, parent `publication-remediation`, scientific owner leadL1, notebook writer ROOT. First continuity check of the assigned SAME packet returned exit 0, `fresh=true`, `changed=[]`. Packet: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-auxiliary-compensation-design-r1.json`. Selected primary HEAD in that matching packet is `7fc0d2c0b720989cf3f9003ce87a6654895a11bc`. Only this report and its JSON companion are authored. I have no slot lease and make no controller/build/MCP/source/Git/notebook changes.

## 1. Scope and source authority

I directly read the COMPLETE original 98-line `ADW_EXACT_AUXILIARY_IDENTITY.md` at the packet's frozen checkpoint path, including all original equations 1–11 and the residual physical obligations. Its Eq4 is an ordinary complex polynomial construction before any evaluation; its Eq7 must subsequently hold in the actual Grassmann algebra for its actual lattice coframes. Neither a generic nilpotent carrier nor a degree-four demonstration completes this task.

The assigned frozen unit notebook, governing CLAUDE/pipeline/continuity documents, current Phase6a scientific-successor section, installed lean4 skill, actual accepted `GaussianAuxiliaryComplex.lean`, independent kernel review r2 and native-result receipt were consulted. Existing Eq5–6 acceptance is inherited from those specified receipts, not independently reverified here. The report uses static source/type inspection only. Live Lean search, hover, diagnostics and kernel verification remain REQUIRED once ROOT admits an implementing worker. A static search miss is not an absence result. Older `GoltermanShamir.lean` private lemmas are proof-pattern references, not new public callable APIs.

All repo-relative paths below are relative to PRIMARY `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`. `ML/` denotes its actual pinned `lean/.lake/packages/mathlib/Mathlib/`. No dependency bump is proposed.

## 2. Deterministic Eq4 construction for every finite complex polynomial

Let `ι` be any finite type, possibly empty; `S : MvPolynomial ι ℂ`; assume ONLY `S.constantCoeff = 0`. Let `M : ℕ`, with no positivity restriction. Let `σ : ℝ`. Write `d(α)=α.degree`, prove its equality with the existing `auxiliaryDegree α`, and put

- `Qσ = Σ i, C((σ^2/2 : ℝ) : ℂ) * X i ^ 2` as an ordinary polynomial;
- `e(U) = PowerSeries.subst (U : MvPowerSeries ι ℂ) (PowerSeries.exp ℂ)` when U has constant coefficient zero;
- `E_M(U) = Σ k ∈ Finset.range (M+1), ((k.factorial : ℂ)⁻¹) • U^k` as an ordinary polynomial;
- `τ_M(F) = MvPowerSeries.truncTotal (M+1) F`;
- **`P_M(S,σ) = τ_M(e(S) * e(-Qσ))`**.

This definition matches original Eq4 literally; the crucial implementation theorem identifies it with the completely finite executable formula

`P_M(S,σ) = τ_M(((E_M(S) * E_M(-Qσ)) : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ)`.

Thus no infinite-series evaluation is needed to compute P. Expand finitely many polynomial powers, multiply, then discard monomials of total degree greater than M. For memory efficiency each multiplication may be truncated immediately, using the same lower-set truncation lemmas; this changes no retained coefficient. Noncomputability of the existing complex/finite-type presentation is not an unknown fitting function: the finite formula is deterministic on a supplied finite coefficient table.

An explicit coefficient algorithm, for d=|β|≤M, is

`pβ = Σ (k,l) with k+2*l≤d, (-1)^l / (k! l!) * coeff β (S^k * Qσ^l)`.

Each polynomial coefficient on the right is the finite convolution over the known supports of S and Q; no real-coefficient assumption, conjugation, inferred degree-four cutoff or choice of pβ by the desired output is used. Both factors have zero constant term, and Q has minimum degree two; a simpler rectangle `0≤k,l≤M` with the same polynomial coefficients is equally correct. For original Eq2, S has only degrees two and four, allowing the stronger safe pruning `2*k+2*l≤d`. Keep the general theorem independent of that optimization. Coefficients above M are ZERO in P by construction, but the transformed formal series usually has a nonzero tail; do not assert global equality of formal exponentials after compensation.

### Proposed exact result surface

The following are proposed strong statements, not checked Lean declaration syntax. Generic binders: `[Fintype ι]`, `S : MvPolynomial ι ℂ`, `hS : S.constantCoeff = 0`, `M : ℕ`, `σ : ℝ`. No `Nonempty ι`, degree limit, assumed moment law or conclusion-valued premise.

1. `auxiliaryQuadraticPolynomial_coe`: `(Qσ : MvPowerSeries ι ℂ) = auxiliaryQuadraticSeries σ`.
2. `compensationPolynomial_eq_finite`: P equals the finite formula above.
3. `compensationPolynomial_totalDegree`: `P_M(S,σ).totalDegree ≤ M`.
4. `compensationPolynomial_coeff`: for EVERY β,
   `P_M(S,σ).coeff β = if auxiliaryDegree β ≤ M then coeff β (e(S)*e(-Qσ)) else 0`.
5. `compensation_series_coeff`: for EVERY β with `auxiliaryDegree β ≤ M`,
   `coeff β (auxiliaryGaussianSeries σ * (P_M(S,σ) : MvPowerSeries ι ℂ)) = coeff β (e(S))`.
6. Strong aggregate version: `τ_M(auxiliaryGaussianSeries σ * P_M(S,σ)) = τ_M(e(S))`.
7. Actual auxiliary integral consequence, now adding `hσ : 0<σ`, `v : ℝ≥0`, `hv : (v:ℝ)=σ^2`: for EVERY β with |β|≤M,
   `(∫ h, auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ) ∂μσ) / (auxiliaryFactorial β : ℂ) = coeff β (e(S))`.
   Here `μσ = Measure.pi (fun _ : ι ↦ gaussianReal 0 v)` and P is the deterministic P_M. State the raw version multiplying by `auxiliaryFactorial β` as well. Integrability is a separate proved result obtained by CALLING the existing accepted integrability theorem.
8. `compensation_M_zero`: `P_0(S,σ)=1`; `compensation_empty`: for `ι=Fin 0` and hS, S=0 and P=1. Empty Gaussian integrals are handled by the existing probability measure, not an excluded case.

### Proof architecture for all retained coefficients

For any zero-constant U, use `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hU` and `coeff_of_lt_order` to prove `coeff β (U^k)=0` when |β|<k. Use `PowerSeries.coeff_subst` and `coeff_exp` to reduce each coefficient of e(U) to the finite sum `k≤|β|`. This establishes finiteExp and formalExp agreement at every retained coefficient independently of compensation.

Total truncation is exclusive: `truncTotal n` retains degree `< n`, so **always use M+1**. `coeff_truncTotal_eq_ite` gives the exact retained/zero coefficient statement; `totalDegree_truncTotal_lt` gives totalDegree≤M, including zero polynomials and M=0. `coeff_truncTotal_mul_truncTotal_eq_coeff_mul`, or its lower-set general form, proves that multiplication below the cutoff depends only on coefficients below the cutoff. For multiplication by one untruncated factor, first truncate both and then use equality of the relevant retained coefficients; do not silently treat truncation as an algebra hom on the ordinary polynomial ring.

Prove full formal inverse cancellation `e(Qσ) * e(-Qσ) = 1` by applying the existing `PowerSeries.substAlgHom` at Qσ to `PowerSeries.exp_mul_exp_neg_eq_one`. Identify substitution of `evalNegHom(exp ℂ)` with e(-Qσ), either by existing substitution composition/rescale lemmas found in live search, or directly with `coeff_subst`, `(-Q)^k=(-1)^k Q^k`, and `coeff_exp`. This identification is a small explicit lemma, not an assumed cancellation law. Associativity and commutativity of the complex series ring then give `e(Qσ)*(e(S)*e(-Qσ))=e(S)`. Low-degree truncation locality gives result 5; existing `auxiliarySeries_eq_exp_quadratic_mul` gives result 7. No multivariate analytic exponential, infinite integral exchange or general exp-add theorem is required. A single `τ_M(E_M(S-Qσ))` implementation is an optional binomially proved optimization, not a new premise or necessary dependency.

## 3. Actual complex Grassmann algebra and the original coframes

Use an actual finite four-torus Λ with fixed boundary conditions. For example Λ is the product of four `ZMod Lμ` with each Lμ>0; V=`Fintype.card Λ`. Nearest-neighbor permutations `x↦x±μ` come from that torus, rather than unconstrained symbols. Distinguish the two boundary hops and incorporate the fixed fermion boundary signs into their actual coefficient matrices. A general finite Λ interface may precede this, but the torus specialization is part of the original-regulator construction.

Define

`Gen = Λ × (Fin 4 ⊕ Fin 4)`;
`H = Gen → ℂ`;
`G = ExteriorAlgebra ℂ H`.

Then `Fintype.card Gen = 8*V`. The generators are `ψ(x,I)=ιℂ(e_(x,inl I))` and `barψ(x,I)=ιℂ(e_(x,inr I))`, using the coordinate basis of H. These are independent COMPLEX generators, with no conjugacy identification and no unproved eight-real-Majorana/Pfaffian interpretation. An equivalence to `Fin (8*V)` may aid basis APIs but must retain the named ψ/barψ correspondence.

Use actual `Matrix.specialUnitaryGroup (Fin 2) ℂ` for each SU(2) factor, and link fields

`U : (Λ × Fin 4) → SU2 × SU2`,
`Ω(x,μ)=Matrix.fromBlocks U_L 0 0 U_R`,

reindexed from `Fin 2 ⊕ Fin 2` to `Fin 4`. This is the Dirac `(2,1) ⊕ (1,2)` representation; a Kronecker `(2,2)` is the wrong representation here. Dagger is complex conjugate transpose. Fix the original Euclidean Dirac gamma convention. A concrete compatible chiral realization can be assembled from existing `σ_x, σ_y, σ_z` as `γ_k=[[0,-iσ_k],[iσ_k,0]]`, `γ_4=[[0,1],[1,0]]`, `γ5=diag(1,-1)`; source convention/reindexing/chirality must be checked before pinning these definitions. The algebraic homogeneity proof works for all coefficient matrices, so it must then be explicitly specialized to the genuine block links and fixed gamma matrices, with no gamma or source identity smuggled in as a hypothesis.

For any complex 4×4 matrix A define the genuine bilinear

`B(y,z,A) = Σ I,J, A I J • (barψ(y,I) * ψ(z,J))` in G.

Define the ACTUAL coframe, retaining every coefficient/sign/orientation:

`T(x,μ,A) = (1/4 : ℂ) • [ B(x,x+μ, γ_A * Ω(x,μ)†)`
`                         - B(x+μ,x, Ω(x,μ) * γ_A)`
`                         - B(x,x-μ, γ_A * Ω(x-μ,μ))`
`                         + B(x-μ,x, Ω(x-μ,μ)† * γ_A) ]`.

Boundary signs multiply the corresponding coefficient blocks as specified by the fixed regulator; they do not change generator count or parity. This is dimensionless `T=a*ehat`, exactly original Eq1. There is no inverse tetrad and no independent bare term.

### Actual even subalgebra and commutation

Prove the elementary four-swap identity

`(θa*θb)*(θc*θd) = (θc*θd)*(θa*θb)`

using `ExteriorAlgebra.ι_add_mul_swap` and associativity. It remains true for coincident indices because the exterior relations themselves handle zero factors. Extend it by finite sums and scalar multiplication to every coframe pair. Do not use `ring` on G and do not give G a false CommRing instance.

For a commutative target of existing `MvPolynomial.aeval`, use the actual subalgebra

`EvenG = Algebra.adjoin ℂ (Set.range (fun p : Gen×Gen ↦ θ(p.1)*θ(p.2)))` inside G.

The four-swap identity plus `Algebra.isMulCommutative_adjoin` proves commutativity; existing inherited ring structure then supplies a CommRing presentation (exact instance construction to be live-checked). Each actual T belongs to EvenG by its displayed finite bilinear expansion. This is an actual subalgebra of the original exterior algebra, with injective inclusion into G. It is not a freely postulated nilpotent carrier. If exported under the name `evenGrassmann`, also prove its equality with `CliffordAlgebra.even (0 : QuadraticForm ℂ H)`: generator pairs belong to the existing even sector, and `CliffordAlgebra.even_induction` plus expansion in the coordinate basis proves the converse. That equality is useful API hygiene; Eq7 already holds via the injective concrete inclusion once the explicit membership and nilpotence results below are proved.

### Degree two and GLOBAL nilpotence are construction obligations

Proposed actual statements, with no nilpotence/commutation hypotheses:

- `coframe_mem_exteriorPower_two`: for all x,μ,A and all actual links, `T(x,μ,A) ∈ ExteriorAlgebra.exteriorPower ℂ 2 H`.
- `coframe_commute`: for all coframe indices a,b across ALL sites, `Commute (T a) (T b)`.
- `coframe_product_mem`: for every list `l : List (Λ×Fin4×Fin4)`, `(l.map T).prod ∈ ⋀[ℂ]^(2*l.length) H`.
- `coframe_product_eq_zero`: for every such l with `4*V < l.length`, `(l.map T).prod = 0`.
- `coframe_monomial_eq_zero`: for every multiindex α on the GLOBAL coframe index type with `4*V < auxiliaryDegree α`, `aeval T α-monomial = 0` (state concretely as evaluation of `monomial α 1`, then derive all complex coefficients).

Membership in degree two follows directly from `exteriorPower = range(ι)^2`, finite sums and scalar closure; products follow `SetLike.mul_mem_graded` and the existing N-grading. To kill grade n>8V, use `exteriorPower.finrank_eq`, `Module.finrank ℂ H = 8V`, `Nat.choose_eq_zero_of_lt` and `Submodule.finrank_eq_zero`. This argument is already present as a PRIVATE proof pattern in `GoltermanShamir.lean:199`; do not attempt to import its private name. Alternatively use the actual finite-set exterior basis and pigeonhole: a word in more than 8V coordinate generators repeats an index, and `ιMulti_eq_zero_of_not_inj` kills it. The graded/finrank route avoids expanding a huge coframe product. These proofs establish global joint nilpotence even when sites overlap or coframes share generators. Individual `T_i^(M+1)=0` alone is NOT sufficient.

## 4. Universal evaluation bridge AND its actual coframe discharge

A reusable conditional bridge is appropriate, with actual-premise discharge above mandatory. For a commutative complex algebra A, family t:ι→A and M, assume joint nilpotence: every monomial t^α with |α|>M is zero. Define

`J_(M,t)(F) = MvPolynomial.aeval t (τ_M F)`.

Prove this map is a unital complex algebra hom: add/scalar/unit are immediate from truncation and aeval; product uses coefficient locality and kills every discarded product monomial. Prove `J(coe polynomial)=aeval t polynomial` and, for U.constantCoeff=0,

`J(e(U)) = Σ k≤M, (k! : ℂ)⁻¹ • (aeval t U)^k`.

The nilpotence premise must be explicitly uniform in all multiindices, not a dependent package containing the desired Eq7 identity. Derive this bridge's premise for `A=EvenG`, `t=T_x`, `M=4V` from `coframe_monomial_eq_zero` and injectivity of EvenG's inclusion. Here `ι=Fin4×Fin4`, the ORIGINAL sixteen local coframe coordinates. The same global theorem also permits a single global set of coordinates if later needed; do not change original Eq4 to sixteen independent Grassmann generators at each site.

Put `S=S_x(·,Ω)` from original Eq2, and `P=P_(4V)(S_x,σ)`. Build S_x explicitly as the degree-four epsilon cosmological term plus degree-two EHC term, with the literal `g2/4`, spacetime epsilon, `Tr(Ω_(x,κλ) γ_C γ_D γ5)` and ordered plaquette product. For a standard forward plaquette this product is `Ω(x,κ) Ω(x+κ,λ) Ω(x+λ,κ)† Ω(x,λ)†`; pin its orientation to the source before claiming the original-action bridge. Show `S_x.constantCoeff=0` by actual polynomial construction, even when couplings vanish. Couplings can be arbitrary complex numbers; original real finite g1,g2 specialize by embedding. Verify that scaling `T=a*ehat` cancels the original a^4/a^2 factors, rather than introducing another normalization.

The central polynomial identity now follows:

`J_(4V,T_x)(auxiliarySeries σ v P) = finiteExp_(4V)(aeval T_x S_x)`.

Prove it by the retained-coefficient compensation theorem and J's definition; then prove the integral version below. This is an algebra identity BEFORE any Berezin operation.

### Actual Eq7 integral, with independent integrability

Choose the actual exterior basis `(coordinateBasis Gen ℂ).ExteriorAlgebra`, indexed by `Finset Gen`. It gives a finite-dimensional complex vector space and an explicit norm via `Basis.equivFun` into `(Finset Gen → ℂ)`. Transport the norm/NormedSpace structure using existing induced APIs and prove completeness via the finite-dimensional normed-space instance. No multiplicative norm bound is needed: every exponential here is a finite algebraic polynomial. Work in G for the Bochner integral and use EvenG only for polynomial aeval.

Set `L_x(h)=Σ i, (h i : ℂ) • T(x,i)` in G, and define `nilExp_M(z)=Σ k≤M, (k! : ℂ)⁻¹ • z^k`. The original coframe theorem to implement is:

For EVERY finite torus, fixed boundary conditions, actual compact Spin(4) links, finite couplings g1,g2, site x, σ>0 and v with coe v=σ², with M=4V and P the deterministic Eq4 polynomial,

`Integrable (fun h ↦ auxiliaryWeight σ P h • nilExp_M(L_x(h))) μσ`,

and

`nilExp_M(S_x(T,Ω)) = ∫ h, auxiliaryWeight σ P h • nilExp_M(L_x(h)) ∂μσ` in G.

There are NO premises assuming coframe commutation, global nilpotence, auxiliary moments, compensation, positivity or Eq7. Those facts are proved and called. `S_x(T,Ω)` means the inclusion of the aeval value, not a scalar substitute.

To prove: the multinomial theorem for the proved commuting coframes gives

`nilExp_M(L_x(h)) = Σ |β|≤M, ((auxiliaryMonomial β h : ℂ)/(auxiliaryFactorial β : ℂ)) • T_x^β`.

This is where product coordinate factorials, not |β|!, enter. Use existing `MvPolynomial.coeff_linearCombination_X_pow_of_fintype` followed by actual aeval, or the corresponding commuting-element multinomial theorem located by live search. It is a finite sum over `finite_of_degree_lt (M+1)`. Multiply by W. Each scalar coefficient is genuinely integrable by `integrable_auxiliaryWeight_mul_monomial`; scalar division and multiplication by a fixed G vector preserve integrability. Finite summation gives the displayed independent integrability statement. `integral_finsetSum` and `integral_smul_const` identify the integral with `J(auxiliarySeries σ v P)`. Compensation and the exponential-evaluation bridge identify that with the left side. Thus Eq7 is a genuine finite-dimensional Bochner integral, with no exchange of an infinite exponential and integral and no unevaluated Grassmann carrier.

Prove `nilExp_M` is independent of increasing the cutoff on these positive-degree nilpotent arguments. That connects the notation unambiguously to the source's finite nilpotent exponential. Optionally prove the product-over-sites identity using joint commutation; a full Haar/Berezin partition-function result is downstream, not silently part of Eq7.

## 5. Located pinned APIs (source-verified signatures; live types still required)

- `lean/SKEFTHawking/ADW/GaussianAuxiliaryComplex.lean:30–40`: `auxiliaryDegree`, `auxiliaryFactorial`, `auxiliaryWeight`; finite support, inverse σ^degree and original COMPLEX coefficients.
- Same module: `integrable_auxiliaryWeight_mul_monomial (σ) (hσ:0<σ) (v:ℝ≥0) (hv:(v:ℝ)=σ^2) (P:MvPolynomial ι ℂ) (β:ι→₀ℕ)`; actual complex scalar insertion integrability.
- Same module: `auxiliaryGaussianSeries` is `PowerSeries.subst (auxiliaryQuadraticSeries σ) (PowerSeries.exp ℂ)`; `auxiliarySeries_eq_exp_quadratic_mul` states the full actual-integral-series equality for arbitrary P and all coefficients. Reuse these exact accepted objects.
- `ML/RingTheory/MvPowerSeries/Trunc.lean:327–384`: `truncTotal (n:ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R`; `coeff_truncTotal (h:degree x<n)`; `coeff_truncTotal_eq_zero (h:n≤degree x)`; `coeff_truncTotal_eq_ite`; `coeff_truncTotal_mul_truncTotal_eq_coeff_mul`; `coeff_truncTotal_pow`; `truncTotal_pow_eq_truncTotal_truncTotal_pow`; `totalDegree_truncTotal_lt (h:n≠0)`; `truncTotal_coe_eq_self_iff`. Finite σ suffices.
- `ML/RingTheory/MvPowerSeries/Order.lean:416,496`: `coeff_of_lt_order (h:degree d<f.order) : coeff d f=0`; `le_order_pow_of_constantCoeff_eq_zero (n:ℕ) (hf:f.constantCoeff=0) : n≤(f^n).order`.
- `ML/RingTheory/PowerSeries/Exp.lean:48–58,149`: actual `exp`, `coeff_exp : coeff n (exp A)=algebraMap ℚ A (1/n!)`; `exp_mul_exp_neg_eq_one : exp A * evalNegHom(exp A)=1`.
- `ML/RingTheory/PowerSeries/Substitution.lean:61,171,212,236`: `HasSubst.of_constantCoeff_zero`; `substAlgHom (ha:HasSubst a) : PowerSeries R →ₐ[R] MvPowerSeries τ S`; `subst_mul`; `coeff_subst` with a finite-support `finsum` of `coeff d f • coeff e (a^d)`. Search actual composition/negative-substitution APIs LIVE before making a helper.
- `ML/LinearAlgebra/ExteriorAlgebra/Basic.lean:60–90,244,299–345`: actual ExteriorAlgebra, ι, exteriorPower; `ι_add_mul_swap`; `ιMulti_eq_zero_of_not_inj`; `ιMulti_mul_ιMulti`; `ιMulti_range`; `ιMulti_span_fixedDegree`.
- `ML/LinearAlgebra/ExteriorAlgebra/Grading.lean:45,72`: `SetLike.GradedMonoid (fun n ↦ ⋀[R]^n M)` and actual `gradedAlgebra`.
- `ML/LinearAlgebra/ExteriorPower/Basis.lean:104–110,159`: `Module.Basis.exteriorPower` and `exteriorPower.finrank_eq : Module.finrank R (⋀[R]^n M)=Nat.choose (Module.finrank R M) n` under stated finite/free/nontrivial ring assumptions.
- `ML/LinearAlgebra/ExteriorAlgebra/Basis.lean:30–61`: `Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M)`; actual `basis_mul_of_not_disjoint` and signed `basis_mul_of_disjoint`. These are genuine exterior basis APIs, not abstract carrier axioms.
- `ML/Algebra/Algebra/Subalgebra/Lattice.lean:754`: `Algebra.isMulCommutative_adjoin (hcomm : ∀ x∈s, ∀ y∈s, x*y=y*x) : IsMulCommutative (Algebra.adjoin R s)`.
- `ML/LinearAlgebra/CliffordAlgebra/Even.lean:54`: `CliffordAlgebra.even (Q) : Subalgebra R (CliffordAlgebra Q)`; `Grading.lean:188` actual `even_induction`. No commutativity for arbitrary nonzero Q is asserted.
- `ML/Algebra/MvPolynomial/Eval.lean:591,703`: ordinary `aeval` and `aeval_monomial` require the commutative target; target EvenG, never G. `ML/Algebra/MvPolynomial/Coeff.lean:86`: `coeff_linearCombination_X_pow_of_fintype` is the actual existing multinomial coefficient theorem already used by the accepted complex module.
- `ML/LinearAlgebra/UnitaryGroup.lean:255–262`: actual `Matrix.specialUnitaryGroup` and its unitary/determinant-one characterization.
- `lean/SKEFTHawking/PauliMatrices.lean:33–100`: actual σ matrices, Hermiticity/involutivity/commutators. Construct the four gamma blocks from these and check source conventions; do not duplicate an unrelated Clifford representation.
- `ML/LinearAlgebra/Basis/Defs.lean:247`: `Basis.equivFun_apply`; `ML/Analysis/Normed/Module/Basic.lean:185`: `NormedSpace.induced`; standard `NormedAddCommGroup.induced`; `ML/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:218`: `integral_smul_const` for a complete normed target. These suffice for finite G-valued integration after the explicit basis norm is installed.

## 6. Construction DAG and sensible ownership

A. Ordinary compensation module: polynomial Q, e(U), finiteExp agreement, total truncation, inverse cancellation, retained coefficient theorem and actual normalized/raw integral corollaries. It imports the accepted Eq5–6 module and leaves it unchanged.

B. Actual finite Grassmann/coframe module: named 8V generators, genuine exterior basis and grading, even subalgebra commutativity, actual torus/Spin(4)/gamma/quarter-coframe construction, grade-two membership and global nilpotence. Keep basis/norm integration utility here or in a small directly used companion, not a new generic framework.

C. Evaluation module: conditional joint-nilpotent J hom and finiteExp compatibility, actual coframe specialization, finite-sum integrability and original Eq7 in G. Dependencies A+B → C. Source-action polynomial S_x and source convention bridge must have ONE owner, naturally B with C importing it. If B is too large for one slot, ROOT may sequence basis/parity and source coframes under a refreshed assignment rather than give two workers overlapping files.

D. Independent prospective mathematical review BEFORE proof dispatch; independent implemented-source/kernel review AFTER actual proofs, then ROOT authoritative slot absorption/build/extraction/native gates. File names such as `GaussianAuxiliaryCompensation.lean`, `FiniteGrassmannCoframe.lean`, `GaussianAuxiliaryGrassmann.lean` are proposals only. ROOT chooses exact scopes and leases through ADR-008. At most the currently admitted public wt1–wt3 capacity; this proposal grants none. Workers read but never write ROOT's notebook. Existing planner remains the sole routing ledger.

A and B are mathematically independent once shared index/notation interfaces are pinned; C follows both. No separate worker should repair the already accepted complex module merely to rename an API. Actual slot workers must first inspect live outlines/goals, perform semantic/type search and hover the candidate APIs, then prove and independently kernel-verify their exports; this design's static searches do not satisfy that obligation.

## 7. Discriminating controls (proposed, not executed)

1. Nonreal linear source: S=iX, M=3, q=σ²/2. P has coefficients `1, i, -1/2-q, -i/6-iq`; exp(+qX²)P has retained coefficients `1,i,-1/2,-i/6`. This simultaneously detects Gaussian compensation sign, missing factorial and phase conjugation.
2. Mixed complex source: S=cX0X1 with c=1+i, M=4. P contains `-q(X0²+X1²)`, `cX0X1`, `q²/2(X0⁴+X1⁴)`, `-cq(X0³X1+X0X1³)`, and `(q²+c²/2)X0²X1²`. Compensated coeff(2,2)=c²/2=i; actual RAW insertion β=(2,2) is `2c²=4i`, using coordinate factorial 2!*2!=4, not total factorial 4!=24.
3. High degree: S=iX^7, M=7. P includes iX7 and the degree 0,2,4,6 terms of exp(-qX²); compensated degrees 1–6 vanish and degree7=i; raw seventh insertion=5040i. No theorem restricted to degree≤4 can pass this. Add source monomials of degree>M to verify they do not affect any retained coefficient.
4. Cutoff fence: include a genuine nonzero source monomial of degree exactly M; it must survive. Degree M+1 must be discarded in P. Do NOT assert the transformed series has zero tail or agrees above M.
5. M=0, arbitrary σ, and empty ι: P=1 and the normalized degree-zero auxiliary integral=1. Also test S=0, g1=0, g2=0 and σ=2 versus σ=1/2. The representation cancels σ, including raw source coefficients.
6. Exterior sign and parity: θaθb=-θbθa for distinct generators; θa²=0; disjoint bilinears commute; overlapping products vanish where appropriate. A sum of bilinears need not square to zero: `(θ1θ2+θ3θ4)^2=2θ1θ2θ3θ4≠0`. This rejects an erroneous assumption that each original coframe is a single square-zero variable.
7. Global bound: for N=8V, the product of 4V disjoint coordinate pairs is the nonzero top basis vector (sign pinned by fixed ordering), whereas every product of 4V+1 degree-two forms vanishes. This establishes why 4V, not V or a local cap, is the universal threshold. Demonstrate a two-site mixed product before the global bound to reject per-site independent truncations. This sharpness test concerns generic bilinears; do not promise sharpness for every special link/coframe configuration.
8. Original quarter-coframe: inspect coefficients of all four hopping blocks with distinct x,x+μ,x-μ (torus extents≥3 for this diagnostic), actual `+,-,-,+` pattern and literal 1/4; complex conjugation occurs only in link dagger, never on pα. Verify block-diagonal `(2,1)⊕(1,2)` links and source plaquette orientation. A one-site torus can cause legitimate cancellations and is not a good nonzero coframe witness.
9. Actual source degree: show cosmological S_x has four T factors and eight fermion factors; EHC has two T factors and four fermion factors. Include a nonzero cosmological top-grade control where available; never drop the degree-four-in-T vertex to make Gaussian decoupling easy.
10. Eq7 retained dependence: compare both sides as actual exterior-basis coefficients at nonreal couplings and mixed site/direction coframes. Verify the G-valued integral's integrability independently, not just a scalar coefficient identity packaged as Eq7.

## 8. Explicit acceptance boundary and remaining original obligations

The proposed milestone is Eq4 for all finite complex coefficients with zero constant source, plus actual original Eq7 in the 8V-generator exterior algebra with displayed coframes and finite Gaussian integral. A generic conditional evaluation theorem alone, an abstract nilpotent test ring, scalar tests alone, or a real-only degree-four construction fails that boundary.

Still downstream OPEN: exact original Eq9 4V×4V matrix element/sign assembly; Berezin orientation and determinant identity; compact-link continuity/boundedness and Haar integration; all coefficientwise finite Fubini exchanges; source insertions and original Eq11 derivative-of-W term; Z≠0 for normalized correlations; any positive sampling/RHMC/phase treatment; actual physical source normalization and Legendre response; selected state/domain/stability, B3 and spin/polarization/transport; thermodynamic/continuum control; actual numerical simulation and publication gates. No assumption of W positivity, determinant positivity, Majorana Pfaffian identification or auxiliary h=tetrad expectation is introduced. This finite representation preserves the original microscopic and later physical objectives without claiming they are solved.

Memory was used only to confirm the required discovery discipline (statement/type/import/dependency search and separation of local acceptance from publication). Current mathematical/API claims above come from the assigned source and pinned files, not memory-derived status.
