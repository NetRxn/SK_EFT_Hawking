# Independent B4 balanced-induction and change-of-rings review

**Verdict: SCOPED COMPLETE MANUAL MATHEMATICAL ACCEPTANCE. No mandatory correction found in the complete declared construction.** I did not author this proof. I independently checked all thirteen sections of CONSTRUCTION.md03f6a3e026f499e2e1e68c9c71ad98dfeb500f6b5e3a65004e8f4ffe18ff6d1c, including the actual source coefficient convention, nonflat Ext counterexample, infinite splice and non-involutive anti-automorphism conversion.

Accepted scope: an actual noncommutative balanced quotient and induction/restriction adjunction; free-module and natural cochain comparison; projective preservation and correctly sided conditional exactness/derived Ext; full resolution comparison; the source finite-prefix interpretation and a genuine infinite extension; and an explicit conditional conversion to the original left-module form. This is complete manual algebra at those stated hypotheses. It does not construct the full Steenrod A/inclusion/global basis, instantiate flatness or antipodes for that A, complete native H2, establish grading/Adams/topological identifications or close B4/D2.

## Balanced quotient, action and universal property (§§1–3)

The free abelian group on M×A supplies formal finite integral sums independently of any desired Hom isomorphism. Killing the two additivity relations and [mb,a]-[m,i(b)a] makes the pure-tensor map biadditive and genuinely B-balanced. Zero, negatives and integer multiples follow from those relations; no commutativity of B is used.

For fixed c, [m,a]->[m,ac] preserves each relation. In particular the balance image uses (i(b)a)c=i(b)(ac), with the same coefficient order. It descends to an additive quotient map. Associativity, the unit and distributivity in c can be checked on pure generators and therefore on every quotient element. This constructs the right A-module structure rather than presupposing it.

A balanced biadditive map kills the generated subgroup and factors uniquely; the converse follows by restriction to generators. Its additional right-A covariance makes the descended map A-linear. This proves the module universal property. For a B-map f, the induced map f(m)⊗a respects the same relations; identities/composition are generator equalities. The unit m->m⊗1 is B-linear because mb⊗1=m⊗i(b).

Evaluation Phi(g)(m)=g(m⊗1) is B-linear. The inverse Psi(f)(m⊗a)=f(m)a is balanced precisely because f(mb)a=f(m)i(b)a. Its covariance in a proves A-linearity. Evaluating the composites on m and m⊗a proves both inverses, additivity and naturality. The unit/counit triangles reduce to (m⊗1)a=m⊗a and n1=n. These are actual maps, not matching dimensions or a supplied equivalence field. The construction is induction LEFT adjoint to restriction; coinduction has not been substituted. Compatible central k-linearity is properly conditional, and no unwarranted A-module structure on general Hom groups is claimed.

## Free modules, differentials and noncommuting order (§4)

The maps Theta(x⊗a)_j=i(x_j)a and Lambda(y)=sum e_j⊗y_j have finite sums where needed. Balance follows from i(x_jb)a=i(x_j)i(b)a. The first composite is coordinatewise identity; the other uses x=sum e_j x_j and the actual balance relation. This remains valid for infinite index sets because module elements have finite support. Hom out of the direct sum may have arbitrary values on its basis; the proof does not incorrectly require finite support for that family.

For right-free columns, d(e_j)=sum e_i b_ij gives d(x)_i=sum b_ij x_j. Induction replaces each coefficient by i(b_ij) on the LEFT of y_j. Composition multiplies b_ij c_jk in that order. A right-linear functional has f(y)=sum n_i y_i, so precomposition is n->(sum n_i i(b_ij))_j. This is the actual differential formula on both Hom sides.

The matrix-unit control is correct: E12 E21=E11 while E21 E12=E22. Left multiplication maps are right-module linear, their ordered composites distinguish the products, and the corresponding right multiplication on Hom values yields nbc rather than ncb. This also demonstrates why the maps need not be left B-linear. I checked these manually; no matrix computation program ran.

## Right exactness, projectives and the precise flatness side (§§5–6)

The cokernel isomorphism T(coker u)=T(M)/im T(u) is well-defined in both directions: changing a representative by u(l) adds precisely an element of im T(u). Balance and A-linearity descend. Surjections lift finite sums of pure tensors termwise; direct sums are preserved by component/inclusion maps. This proves right exactness without asserting injection preservation.

Projective preservation does not require flatness. Restriction takes a surjection of right A-modules to a surjection of right B-modules. Lift the adjoint map from a B-projective P, then use the inverse Hom map and naturality to obtain the required A-lift. Exactness of the full induced resolution remains separate.

The supplied basis condition a=sum i(b_lambda(a))u_lambda is LEFT-B freeness of A. Uniqueness gives additive finite-support coordinates and b_lambda(i(b)a)=b b_lambda(a). Thus chi(m⊗a)_lambda=m b_lambda(a) is balanced. Its inverse sum x_lambda⊗u_lambda is well-defined, and basis delta-coordinates and balance prove the two composites. Naturality identifies T(f) with the coordinatewise direct-sum f as additive maps; no coordinatewise A-action on that direct sum is invented.

A finitely supported kernel vector has finitely many coordinate preimages, chosen zero elsewhere, proving exactness of the direct-sum sequence. The additive identification therefore proves equality of actual kernels/images for the induced A-module maps. This constructs sufficient exactness from an actual basis; it does not construct that basis for the full Steenrod A. The alternative hypothesis “A flat as LEFT B” is the correct side for M_RIGHT tensor_B A. Right exactness plus injection preservation yields short exactness and, by the kernel/image short sequences, exactness of complexes. A separately proved exactness witness for a particular induced augmented resolution is also sufficient. These are genuine alternatives, not new unnecessary gates.

## Full resolutions, homotopies and derived cohomology (§§7–8)

The free cover with one symbol per underlying module element surjects by evaluation e_k->k. Iterating on each actual kernel constructs an infinite free resolution, with exactness at every degree. This is not zero-padding a prefix.

For arbitrary full projective resolutions, the chain comparison lifts through each surjection onto the next kernel by projectivity. In the homotopy construction, applying d_Q to
r_n=f_n-g_n-h_(n-1)d_P,n
gives zero by the previous homotopy identity and d_P²=0. Exactness and projectivity supply h_n. The degree0 augmentation case is explicitly included. Hence f-g=d_Q h+h d_P; identity/composite lifts agree up to homotopy, giving resolution independence and the ordinary contravariant first-variable/covariant second-variable Ext functor.

Applying induction preserves projective terms by §5 and preserves exactness only under the hypothesis of §6. The degreewise natural Hom isomorphisms commute with precomposition by each induced differential. Both directions carry kernels onto kernels and images onto images, so they induce actual ker/im isomorphisms. The resulting Ext isomorphism is canonical under comparison lifts and natural in both variables. No equality of dimensions is used in place of this argument. The central-k and graded variants retain their additional hypotheses; the ungraded theorem alone supplies no Adams stem or bidegree.

## Genuine injective-extension Ext² counterexample (§9)

The ring Z⊕F2 with square-zero second summand has the stated associative multiplication and unit. Z embeds injectively. Multiplication by2 on A has nonzero kernel {0,epsilon}, so induction loses the original injection even though the degree0 Hom adjunction still holds.

The displayed free resolution really is exact through P2: ker(A->A/2A)=2A, ker(2)=epsilon A, and ker(epsilon) consists of (2k,t)=2A+epsilon A, the image of d3:A²->A. Appending free covers of subsequent kernels gives a full resolution. For N=F2 via the integer residue, both2 and epsilon act by0, so the three Hom coboundaries adjacent to C2 vanish. Therefore H2=N=F2. Over Z the ordinary length-one resolution of Z/2 gives Ext²=0. This is an actual failure of the unconditional Ext claim for an injective unital extension, not merely a demonstration that one proof method fails. No mathematical software or generated result was used.

## Actual A1 coordinates, prefix and splice (§§10–11)

I personally read complete ChangeOfRings, A1ModuleCat, A1Exactness, A1ExtSubstantive and ExtBordismBridge bodies. I additionally read complete A1Algebra, A1Resolution definitions through its initial matrix section and its full right-action section438–500, and the actual Lmat/Rmat/unit-column definitions in A1Ring.

A1op is structurally LEFT A1sub-op, hence RIGHT B. coordEquiv reads each unop matrix's column0 and encodes block i/basis a as8i+a. Lmat_col0 and e0=1 make the free unit vector e_j exactly coordinate8j. For the source D, its column8j therefore recovers b_ij=sum_a D(8i+a,8j)e_a. Augmentation selects its a=0 coefficient. The right-trivial Hom inverse f(sum e_i x_i)=sum n_i epsilon(x_i), together with right linearity, gives delta(k,j)=D(8j,8k), matching every source delta0…delta4 definition. The transpose/order is correct.

Actual convention boundary: L1 column2 has e3+e4, whereas L2 column1 has e3. Thus the PINNED source gives e1e2=e3+e4 and e2e1=e3. The local Phase5s research report labels those two products oppositely. I checked the actual source, not remembered Milnor labels. The construction correctly uses D/coordEquiv/augmentation and does not import that report's products or asserted global free basis. This discrepancy does not affect the conditional algebra or source-coordinate comparison; an actual full-A inclusion/basis proof must reconcile its conventions explicitly. This review is not a new identification of the matrix algebra with an externally specified Steenrod presentation.

A1Exactness proves augmentation surjectivity and exactness through homological P4 using an F2-linear contraction. Equality of underlying kernels/images transfers to the already B-linear maps, but the contraction itself is not B-linear and cannot simply be tensored. The source's finite-prefix/projectivity and dual zero-map certificates remain genuine read inputs, not freshly executed native proofs.

The splice indexes are correct: homological P5 has free rank4, K=ker d5 is its submodule, and d6:Q0->K->P5 uses a full projective resolution of K. Exactness at P5 follows from surjectivity onto K; exactness at Q0 uses injectivity of K->P5; higher exactness is that of Q and lower exactness is the pinned prefix. The notation P 4 in source denotes rank4, not homological P4.

The completed resolution therefore computes ordinary right-module Ext0…Ext4 from delta0…delta4, with ungraded dimensions1,2,2,2,3 under those pinned source facts. In degree5, the outgoing Hom map uses d6. A1ExtSubstantive's coker(delta4) dimension4 is not alone H5 or categorical Ext5; the note explicitly retains that boundary. The general balanced route and the finite-free/direct-sum implementation route both remain valid. Neither a general tensor library nor the full-A basis is made a prerequisite for the independent B-only T3 splice; H2 induction still needs its actual exactness/side data.

## Left-module H2, opposites, anti-automorphisms and topology (§12)

The separate left quotient has the proper relation [a i(b),l]=[a,bl] and action c[a,l]=[ca,l]. Its induction theorem needs RIGHT-B flatness of A. Applying the right theorem to opposites gives the right result as left-A-op Ext, which alone is not the original left-A H2. The swap a-op⊗m->m⊗a respects the reversed product in A-op.

I checked formula(14) without assuming an involutive antipode. Under b·m=m chi_B(b), twisting a right module yields a left module because chi reverses products; chi^-1 gives the inverse equivalence. For the tensor map, F(m⊗a)=chi_A^-1(a)⊗m:
F(mb⊗a)=chi_A^-1(a)i(chi_B^-1(b))⊗m
equals F(m⊗i(b)a) by compatibility. Left A-linearity uses chi_A^-1(a chi_A(c))=c chi_A^-1(a). The inverse G(x⊗m)=m⊗chi_A(x) is balanced because chi_A(xi(b))=i(chi_B(b))chi_A(x), and the two formulas compose exactly. Compatible augmentations preserve trivial coefficients. This supplies a valid conditional conversion, not an actual compatible Steenrod antipode construction.

The full A/inclusion, all-degree one-sided basis or direct exactness, side conversion, actual grading and native Ext interface remain owed. Finite low-degree counts are not a global spanning/uniqueness witness. The proposed next basis unit is concrete; it does not revoke the valid particular-complex exactness alternative or require a huge arbitrary-generalization library before T3.

No F2-vector-space Ext calculation is identified with Z/16. H1 ko cohomology, H3 Adams/spectral/topological comparison and genuine H4-dependent bordism input remain separate. ExtBordismBridge actually has H1/H2/H3=True markers; H4=Nonempty SpinBordismData is real and consumed by rokhlin_from_H4. Its generation_constraint_chain clears decorative binders and proves the independent divisibility arithmetic. The construction preserves that genuine content without pretending the generic algebra derives topology or a physical generation count.

## Authorities, reading extent and preservation

I read the complete proof/PLAN/REPORT, full current T3/T4 owning roadmap, full Phase5r roadmap, complete279-line local Phase5s research note, original B4 remediation and relevant map scope. The current r55 and unchanged governing authorities were personally read in preceding assigned work at the same hashes and checked again here. The stale coinduction recommendation in older roadmap passages is explicitly superseded by its settled-route correction. Research-report API, freeness/axiom advice and topology claims are contextual text, not mathematical premises or current Mathlib availability claims. No native MCP/API/library-absence check ran.

A combined full proof/report display truncated §9/10; an explicit subsequent read recovered those sections. Complete carrying sources and targeted additional coordinate definitions were subsequently displayed without that truncation. Unrelated transitive dependencies and every closed finite decide certificate were not re-executed. I read their actual statements/bodies and independently checked the argument interpreting them; this is not a fresh build/axiom audit.

The FIRST original check actually returned0/fresh/changed[] before inspection, tool38f712. Its argv/cwd/exposed stdout/stderr/rc are retained; unavailable separate subprocess UTC endpoints remain null. A captured stdlib text/hash/stat/JSON operation actually returned0 at2026-10-18T01:47:19.724001+00:00 through01:47:19.766772+00:00. It checked27 current reference occurrences,64 selected N source pins, three additional coordinate sources and ten immutable author artifacts. All85 original author input observations also match their recorded final hashes/modes/sizes/ns-mtimes, including the two additional original sources. These are repeated observations, not unique-input counts or proofs of mathematical truth.

Original first/final/interim outcomes, initial SyntaxError preparation failure and other history remain unchanged. The original author's helper was read, not imported or rerun. Actual captures retain argv/cwd/UTC/rc and raw/base64 channels; direct native reads retain chunks without fabricated missing per-read timing. No original snapshot is refreshed. The historical N raw-index FAIL/cause UNKNOWN remains unwaived.

Only five assigned ignored review outputs are written. No mathematical software, project import/model/test/Verify, Lean/native/MCP/controller/build/compiler/render/export/network, Git/index/ref/source/holding/registry/notebook/closure mutation or external communication occurred. This findings review does not repair the author source.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory defect was found in the declared construction. Source right-module orientation, correct LEFT-B exactness requirement and the finite-prefix/Ext5 limitation agree with the active brief. Actual matrix products differ from local report labels, so the latter cannot supply an unexamined full-A embedding. Historical “H2 discharged” language conflicts with the actual True marker/open contract, while the current Hom finrank/finite exactness/dual-complex results are real progress and must not be called the retired arithmetic proxies. Generic conditional algebra is now manually substantiated; actual full-A/native H2, topology, closure, protected/main/publication and genuine human gates remain open.

Terminal ORIGINAL check actually returned1 with changed=["owned-files"] only and empty stderr. All189 current/source/additional/author observations retain exact hash/mode/size/ns-mtime at terminal capture; repeated paths are observations, not unique-input counts. Original first0/final1 outcomes are sealed without refresh. Scoped complete manual acceptance does not discharge the actual full-A/nativeH2/topological or publication boundaries.
