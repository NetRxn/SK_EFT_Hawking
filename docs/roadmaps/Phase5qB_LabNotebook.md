# Phase 5q.B Lab Notebook — zero-axiom van der Blij `8 ∣ σ` (FULL classification route)

**Authoritative living tracker for the extended research-grade attempt.** Re-read on every bootstrap
/ after every compact (the memory note `next_session_phase5qB_resume` points here). Update CONTINUOUSLY.

## North star + standing decision (USER, 2026-06-04)

**GO FULL: prove van der Blij `IsEvenUnimodular M → 8 ∣ latticeSig M` ZERO-AXIOM, ZERO-CITATION**, via
the classification of even unimodular lattices. This discharges `charSq` in `SmoothSpinManifold4`,
making `16 ∣ σ` unconditional + wired into `RokhlinBridge.sixteen_convergence_full`. The cited
geometric inputs `even_unimod` (Wu) and `topo` (Â-parity) legitimately remain — they are irreducible
manifold topology; only the *algebraic* `8 ∣ σ` is in scope here.

**Operating rules (do not violate):** (1) NO revisiting scope/estimates — we don't know how long, we
just work it. (2) NO axiom, NO `native_decide`, NO `maxHeartbeats`; kernel-pure
(propext/Classical.choice/Quot.sound). (3) Decompose hard → tractable sub-steps. (4) Raid unrelated
codebase corners for reusable substrate. (5) Log tried-and-FAILED so we never repeat post-compact. (6)
Have fun. We turn "multi-year" into tractable here regularly.

## DONE (proven, kernel-pure, file:name)

- `LatticeSignature.lean`: `latticeSig` (= sigPos−sigNeg of ℝ-cast form), `latticeSig_neg`,
  `latticeSig_le/ge`, `abs_latticeSig_le`, `latticeSig_of_posDef` (=rank), `latticeSig_of_negDef` (=−rank),
  `sigPos_eq_finrank_of_posDef`, `sigNeg_eq_zero_of_posDef`.
- `E8Literal.lean`: `E8lit` (literal E₈), `E8inv` (its integer inverse), `e8lit_mul_inv` (E8lit·E8inv=1
  by decide — inverse-exhibition, dodges 8×8 det), `e8lit_symm`, `e8lit_even`, `e8lit_unimodular`,
  `e8lit_even_unimodular`. **Kernel-pure, no native_decide.**
- `SignatureAdditivity.lean` (the engine): `prodSubEquiv`, `finrank_prodSub`, `le_sigPos_prod`,
  `le_sigNeg_prod`, `neg_prod`, `radical_prod_eq_bot`, `sigPos_prod_of_nondeg`, `sigNeg_prod_of_nondeg`,
  `posDef_radical_eq_bot`, `negDef_radical_eq_bot`. Full signature additivity over ⊕ for nondegenerate forms.
- `LatticeTheta.lean` (23 thms): definite-case theta modular machinery (convergence, T/T²/S-transform for
  standard lattice via jacobiTheta, congruence-invariance, cusp normalization, Fubini/product-tsum,
  jacobiTheta₂ slice). [Built for the analytic route; may feed the DEFINITE case of van der Blij.]
- `ArfInvariant.lean`, `EvenLatticeForm.lean`: the 8→16 layer (σ/8 mod 2 = Arf), NOT van der Blij itself.
- **`E8Signature.lean` (NEW, [A1] DONE, kernel-pure, root-imported, file-gate green): `C8` (integer
  `2×roots`), `c8_eq` (`C8ᵀ·C8 = 4•E8lit` by `decide` over ℤ), `E8r`/`C8r` (ℝ casts), `c8r_eq`
  (`C8rᴴ·C8r = 4•E8r`), `e8r_posDef` (E₈ posdef over ℝ), `e8lit_latticeSig` (`σ(E₈)=8`),
  `neg_e8lit_latticeSig` (`σ(−E₈)=−8`).** Verified axioms = {propext, Classical.choice, Quot.sound}.
- **`LatticeSignatureCongr.lean` (NEW, kernel-pure, root-imported, file-gate green) — the Sylvester engine:**
  `toQuadraticMap'_congr` (`(Bᵀ·A·B).toQuadraticMap' = A.tQM'.comp (mulVecLin B)`), **`latticeSig_congr`**
  (`IsUnit P.det → latticeSig (Pᵀ·M·P) = latticeSig M` — congruence invariance, the tool that reads σ off the
  classification normal form), `Hyp`/`hyp_symm`/`hyp_even`/`hyp_unimodular`, **`hyp_latticeSig` (`σ(H)=0`)**
  via `H ≅ −H` (`Pflip=diag(1,−1)`). Axioms clean. ⚠️ **Mathlib ALREADY HAS the isometry-invariance**
  `QuadraticMap.Equivalent.sigPos_eq`/`sigNeg_eq` (Signature.lean) — used directly (first cut hand-rolled
  `sigPos_isom` etc., then deleted as redundant). `QuadraticMap.Equivalent Q Q' = Nonempty (IsometryEquiv)`.
- **`BlockSignature.lean` (NEW, kernel-pure, root-imported, file-gate + project-gate green): the block-diagonal
  signature calculus.** `fromBlocks_tQM_elim` (`Q_{A⊕B}(x⊕y)=Q_A x+Q_B y`), `fromBlocksEquivProd`
  (`(fromBlocks A 0 0 B).tQM' ≃ A.tQM'.prod B.tQM'` via `sumArrowLequivProdArrow`), **`sigPos_fromBlocks`/
  `sigNeg_fromBlocks`** (`σ(A⊕B)=σA+σB` for nondegenerate A,B — radical=⊥), **`nondeg_radical_eq_bot`** (general
  symmetric `Nondegenerate ⟹ radical=⊥` via `radical_eq_ker_polarBilin` + polar formula). Axioms clean.
- **`GeneratorNondeg.lean` (NEW, kernel-pure, root-imported, project-gate green): generators are nondegenerate.**
  `cast_nondegenerate` (int det≠0 ⟹ real-cast nondeg), `e8r_radical` (E₈ via posDef), `negE8_radical`,
  `hyp_radical`. Axioms = [] (fully axiom-free).
- **`LatticeSigBlock.lean` (NEW, kernel-pure, root-imported, project-gate green): signature on arbitrary index +
  block additivity + reindex-invariance.** `latticeSigOf {ι}[Fintype][DecidableEq]`, `latticeSigOf_fin`
  (=latticeSig on Fin n, rfl), **`latticeSigOf_fromBlocks`** (integer-matrix block additivity), `reindexFormEquiv`,
  **`latticeSigOf_reindex`**. ⟹ signature calculus closed end-to-end: normal form `E₈^a⊕(−E₈)^b⊕H^c ↦ 8(a−b)`.
- **`LatticePrimitive.lean` (NEW, kernel-pure, root-imported, project-gate green) — [E1] + most of [E2].**
  `IsPrimitiveVec`, `isPrimitiveVec_iff_exists_dot` (Bezout-for-tuples), `exists_vecMul_dot_eq_one` (primitive
  covector through unimodular ⟹ pairs to 1), **`exists_hyperbolic_pair`** (primitive isotropic `v` ⟹ `{v,w'}`
  Gram = H). Axioms clean. (Imports `EvenLatticeForm` for `even_form_dvd`.)
- **`EvenLatticeForm.lean` += `even_form_dvd`** (`2∣wᵀMw` for even symmetric integer M, via the mod-2 bridge to
  `redBilin_self_eq_zero`). Kernel-pure.
- **`SplitHyperbolic.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9092) — [E2] COMPLETE.**
  `gramB_eq` (Gram of M in `hypFullBasis` = `fromBlocks Hyp 0 0 residGram`); **`latticeSig_split`** (even
  unimodular M rank≥2 + hyperbolic pair ⟹ **`latticeSig M = latticeSigOf residGram`**, the split-off-H inductive
  step — unimodular change-of-basis P from the combined basis + `latticeSig_congr` + block additivity);
  **`residGram_det`** (`det residGram = −det M`) + **`residGram_evenUnimodular`** (residGram is EVEN UNIMODULAR
  — the recursion induction invariant). Axioms clean. ⟹ split-off-H FULLY characterized: peel H ⟹ residGram even
  unimodular rank n−2 with `latticeSig M = latticeSigOf residGram`.
- **`VanDerBlijReduction.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9093) — 🎯 CAPSTONE.**
  **`eight_dvd_latticeSig_of_HM_of_Theta`**: for ALL even unimodular `M`, `8 ∣ latticeSig M`, GIVEN only the
  two precisely-isolated classical inputs [HM] (indefinite ⟹ primitive isotropic vector) and [Θ] (definite ⟹
  `8∣σ`). Strong induction on rank: definite → [Θ]; indefinite → [HM] + `exists_hyperbolic_pair` →
  `latticeSig_split` (peel H) → `residGram_evenUnimodular` (rank n−2) → IH. **Everything between [HM]/[Θ] and
  van der Blij is now machine-checked kernel-pure.** The residual van der Blij content is EXACTLY two named
  classical theorems (neither in Mathlib): local-global Hasse–Minkowski + theta-modularity.
  Also **`sixteen_dvd_latticeSig_of_HM_of_Theta_of_topo`**: `16 ∣ latticeSig M` from even-unimodular + `2∣σ/8`
  + [HM] + [Θ] (composes the capstone with the Rokhlin bridge) — the Rokhlin conclusion with NO opaque
  algebraic hypothesis; inputs are exactly geometric (Wu even-unimod, Â-even `2∣σ/8`) + the 2 classical theorems.
- **`ThetaModularity.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9094) — [Θ] build + de-risked plan.**
  `posDef_unimodular_det_one` (posdef unimodular ⟹ det=1), `latticeSig_posDef_eq_rank` (posdef ⟹ latticeSig=n).
  Docstring = the executable [Θ1]–[Θ4] decomposition with VERIFIED Mathlib toeholds (`UnitAddTorus`,
  `fourier_gaussian_innerProductSpace`, `LevelOne`). [Θ1] n-dim Poisson + [Θ2] anisotropic Gaussian FT remain.
- **`MultivarPoisson.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9097) — [Θ1] engine + first brick.**
  ⚠️ NAME CORRECTION: the d-torus Fourier engine is `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` (the
  FILE is `AddCircleMulti.lean`, the NAMESPACE is `UnitAddTorus`) — the prior `AddCircleMulti.*` name was wrong.
  Shipped: `mFourier_eval_zero` (`mFourier i 0 = ∏ fourier _ 0 = 1`), **`hasSum_mFourierCoeff_at_zero`** (Σ of
  Fourier coeffs of a summable-coeff torus fn = its value at origin — the Poisson RHS-collapse), `tsum_…`. Verified
  API in docstring: `UnitAddTorus d := d→UnitAddCircle`, `mFourier n x = ∏ fourier(nᵢ)(xᵢ)`, `mFourierCoeff f n =
  ∫ mFourier(-n)•f`, `mFourierCoeff_eq_integral`/`integral_preimage` (fundamental-domain integral). REMAINING [Θ1]
  crux = periodisation Fourier coeff = ℝᵈ Fourier integral (d-dim analog of `Real.fourierCoeff_tsum_comp_add`) +
  summability side conditions — the substantial analytic build. ✅ **RECIPE STEP 3 SHIPPED:
  `integral_eq_tsum_zspan`** (`∫_ℝᵈ f = ∑'_{g:Λ} ∫_{[0,1)ᵈ} f(↑g+x)`, integrable f) via
  `IsAddFundamentalDomain.integral_eq_tsum` + `ZSpan.isAddFundamentalDomain` + `setIntegral_image_emb`; resolved a
  `VAdd` TC diamond by passing `MeasurableConstVAdd`/`VAddInvariantMeasure` positionally.
- **`MultivarPoissonDescent.lean` (kernel-pure, root-imported) — ✅✅ [Θ1] MULTIVARIATE POISSON COMPLETE
  (2026-06-04).** The LHS steps 1+2 + final assembly landed: **`mFourierCoeff_torusDescent`**
  (`mFourierCoeff (torusDescent F hc) n = latFourier F n`) and **`multivar_poisson`**
  (`∑_{γ∈ℤᵈ} F(↑γ) = ∑_{n∈ℤᵈ} latFourier F n`), both `[propext, Classical.choice, Quot.sound]`.
  🔑 The fiddly remaining piece — the `Ioc`-cube (from `mFourierCoeff_eq_integral`, `{x|∀i,xᵢ∈Ioc 0 1}`) vs
  `Ico`-cube (`ZSpan.fundamentalDomain (Pi.basisFun) = ∏[0,1)`) reconciliation — cracked cleanly:
  `{x|∀i,xᵢ∈Ioc 0 1} = Set.pi univ Ioc` (ext + `Set.mem_univ_pi`), `rw [volume_pi]`,
  `Measure.ae_eq_set_pi (fun i _ => Ico_ae_eq_Ioc.symm)` (1-D `MeasureTheory.Ico_ae_eq_Ioc` lifted to the
  product — the boundary diff is a finite union of null coordinate hyperplanes), then `setIntegral_congr_set`.
  Integrand bridge `fun i => ↑(xᵢ)` ↔ `Pi.map (fun _ => ↑) x` handled by a `show` (defeq); then
  `mFourier_q_eq_char` + `torusDescent_comp` + `periodisationCM_apply` + `smul_eq_mul` + `periodisation`.
  Side conditions (`hFint`/`hmeas`/`hLsum`/`hsum`) are the honest analytic hypotheses, discharged from
  Schwartz/Gaussian decay at application time. **[Θ1] DONE → next analytic brick is [Θ2] anisotropic
  Gaussian FT** (`𝓕(exp(−π vᵀAv)) = (det A)^{−1/2} exp(−π wᵀA⁻¹w)` from isotropic
  `fourier_gaussian_innerProductSpace` via change-of-vars `x ↦ A^{1/2}x`), then [Θ3] S-transform (Poisson on
  the Gaussian) + [Θ4] level-1 weight-n/2 ⟹ `8∣rank`.
- **`HasseMinkowskiLocal.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9095) — [HM] build + de-risked
  plan.** **`finite_field_form_isotropic`** (symmetric form over a finite field in ≥3 vars is isotropic, via
  Mathlib Chevalley–Warning `char_dvd_card_solutions`) — the residue-field core of [HM-p] at odd primes.
  Docstring = the [HM-ℝ]/[HM-p]/[HM-LG]/[HM-ℤ] decomposition; [HM-LG] local-global is the remaining frontier.
- **`LatticeContent.lean` (NEW, kernel-pure, root-imported, ExtractDeps green 9096) — [HM-ℤ] content extraction +
  weakened capstone.** `exists_primitive_isotropic_of_isotropic` (a NONZERO integer isotropic vector yields a
  PRIMITIVE one, dividing by the content = generator of `span ℤ (range v)`; isotropy is homogeneous degree 2 so
  `v⬝Mv = g²·(w⬝Mw)`). `eight_dvd_latticeSig_of_HMweak_of_Theta` = van der Blij from [HM-weak] (merely a NONZERO
  isotropic vector — the form local-global delivers) + [Θ]; primitivity recovered internally. 🔑 Mathlib bricks:
  `Submodule.IsPrincipal.generator`/`generator_mem`/`span_singleton_generator`, `Submodule.mem_span_singleton`,
  `Submodule.mem_span_range_iff_exists_fun ℤ`, `smul_dotProduct`/`dotProduct_smul` (ROOT ns, not `Matrix.`),
  `Matrix.mulVec_smul`, `Int.mul_ediv_cancel'`. So [HM] is now reduced to just [HM-LG] producing ANY nonzero
  ℚ/ℤ isotropic vector (the [HM-ℝ]+[HM-p]+[HM-LG] local-global core).
- **`RokhlinClassification.lean` (NEW, kernel-pure, root-imported, project-gate green) — [E3] assembly +
  Rokhlin bridge.** `eight_dvd_latticeSig_e8lit`/`_neg_e8lit`/`_hyp`, `eight_dvd_latticeSigOf_fromBlocks` (step),
  `eight_dvd_latticeSig_congr`, `eight_dvd_latticeSigOf_reindex`, **`sixteen_dvd_latticeSig_of_eight_dvd_of_topo`**
  (`8∣latticeSig M` + `2∣latticeSig M/8` ⟹ `16∣latticeSig M`, kernel-pure — the bridge to the Rokhlin
  conclusion in latticeSig terms). Remaining for unconditional `8∣σ` = classification EXISTENCE only.
- **DELIVERABLE DOCS SYNCED (2026-06-04, per goal mandate "as gating sub-results land, D2/L2 + HYPOTHESIS_REGISTRY
  updated to match"):** `src/core/constants.py` `HYPOTHESIS_REGISTRY['rokhlin_sigma_mod_16']` rewritten to the
  CLASSIFICATION route + rewired interface + complete signature calculus (dependent_theorems += `eight_dvd_sig`,
  `sixteen_dvd_latticeSig_of_eight_dvd_of_topo`; module list updated; imports clean); `['characteristic_square_mod_8']`
  marked `superseded_on_wiring_path`. D2 `papers/D2/paper_draft.tex` "spectra-free route" paragraphs rewritten
  (interface now `sig:=latticeSig form` + precise `eight_dvd`; discharge via classification with the signature
  calculus complete + remaining = classification existence) — **compiles clean (10pp, pdflatex exit 0)**. L2
  confirmed accurate as-is (high-level Rokhlin mentions, no charSq/discharge claims).
- **`SpinRokhlinInterface.lean` REWIRED (kernel-pure, project-gate green): `SmoothSpinManifold4` now connects
  `sig := latticeSig form` (closes the "sig was a free unconnected ℤ" gap), carries the PRECISE residual
  `eight_dvd : 8 ∣ latticeSig form` (= the isolated van der Blij wall, replacing the opaque `charSq`/
  `CharacteristicSquareModEight`), and `topo : 2 ∣ latticeSig form / 8`; `.rokhlin : 16 ∣ latticeSig form`
  kernel-pure via `sixteen_dvd_latticeSig_of_eight_dvd_of_topo`; `sixteen_convergence_unconditional` updated.**
  The 16∣σ derivation is now wired through the new signature machinery; the SINGLE remaining input is the
  classification existence (`even_unimod ⟹ 8 ∣ latticeSig form`).

## DECOMPOSITION TREE (van der Blij `8 ∣ σ`, FULL)

The signature is analytic (eigenvalue signs); `8∣σ` is arithmetic. Bridge = classification OR theta OR
Hasse–Minkowski (all equivalent depth). FULL route splits by definiteness:

- **[A] DEFINITE case** (`σ = ±rank`, need `8 ∣ rank`): θ_L is a level-1 modular form of weight rank/2
  ⟹ `8 ∣ rank`. Substrate: `LatticeTheta.lean`. GAP: general (non-separable) S-transform = multivariate
  Poisson; the modular-forms weight argument.
  - [A1] generators σ values: σ(E₈)=8 ⟸ E₈ posdef (LDL `E8lit = L·D·Lᵀ`, D>0 — computed, see SCRATCH). σ(H)=0.
  - [A2] multivariate Poisson (ℤᵈ) — `AddCircleMulti` engine + torus↔ℝᵈ unfold bridge.
- **[B] INDEFINITE case** (`σ = 8(a−b)` via classification `≅ E₈^a⊕(−E₈)^b⊕H^c`):
  - [B1] indefinite even unimodular represents 0 (isotropic vector) — Meyer / Hasse–Minkowski.
  - [B2] isotropic vector ⟹ splits off H; induct on rank.
  - [B3] signature additivity over ⊕ — **DONE** (`SignatureAdditivity.lean`).
- **[C] WIRE**: discharge `charSq` (`SpinRokhlinInterface`), rewire `RokhlinBridge.sixteen_convergence_full`,
  update D2/L2 + registry.

Alternative unified spine to keep in mind: characteristic vectors (`c² ≡ c'² mod 8` ELEMENTARY — provable;
`c² ≡ σ mod 8` needs the odd indefinite classification ⟨1⟩^p⊕⟨−1⟩^q = HM-level).

## TRIED & FAILED (do not repeat)

- `decide` / `simp [det_succ_row_zero]` on 8×8 `det(E₈)` → recursion/step blowup. (Use inverse-exhibition instead — works.)
- `#eval`/`logInfo` of Mathlib `CartanMatrix.E₈` entries → deep recursion (E₈ is recursively built from E₆/E₇);
  need `--tstack` for `lake env lean #eval`, and work with a LITERAL copy `E8lit`, not Mathlib's E₈.
- Anisotropic Gaussian INTEGRAL/FT for the theta S-transform → NOT needed if using geometric/isotropic
  formulation; but the even-unimodular case is non-separable ⟹ genuine multivariate Poisson required.
- Mathlib has NO: Hilbert symbol, Witt group of quadratic forms, Hasse–Minkowski, p-adic quadratic forms,
  Siegel–Narain, multidim/lattice Poisson, lattice theta. (Confirmed by MCP semantic search + grep, 2026-06-03/04.)
- **`decide` on ℚ matrix identity (the LDLᵀ `E8lit.map ℚ = Lq·diag dq·Lqᵀ`) → STUCK** ("Decidable did
  not reduce", Rat.num kernel match). **`ext + fin_cases i<;>fin_cases j<;> simp+norm_num` over 64 ℚ
  entries → heartbeat TIMEOUT.** ⟹ rational LDL is a dead end in-kernel. **WINNER: integer route.**
  `2·E₈ ⊂ ℤ⁸` ⟹ integer `C8` with `C8ᵀ·C8 = 4•E8lit`, which `decide` reduces cleanly over ℤ; posdef via
  `conjTranspose_mul_self` + invertibility (det²=4⁸·(±1), no 8×8 det) + `PosDef.smul (1/4)`. [A1] DONE.

## REUSABLE SUBSTRATE (found across repo / Mathlib)

- Mathlib: `QuadraticForm/Signature` (`sigPos`/`sigNeg`, `sigPos_add_sigNeg_add_radical`,
  `exists_finrank_eq_sigPos_and_posDef`, `le_sigPos_of_posDef`), `QuadraticMap.prod`/`prod_apply`/`polar_prod`,
  `nondegenerate_iff_radical_eq_bot`, `Matrix.nondegenerate_iff_det_ne_zero`, `AddCircleMulti` (multivar torus
  Fourier `hasSum_mFourier_series_of_summable`), `jacobiTheta`/`jacobiTheta₂_functional_equation`, real spectral
  theorem `Matrix.IsHermitian.spectral_theorem`, `Module.finrank_prod`, `finrank_bot`.
- Project: `AlgebraicRokhlin` (`serre_even_unimodular_mod8` conditional on charSq; `rokhlin_from_serre_plus_topology`).
- **Mathlib gems found this session (REUSE, don't reinvent):** `QuadraticMap.Equivalent.sigPos_eq`/`sigNeg_eq`
  (Sylvester invariance — `Equivalent Q Q' = Nonempty (Q.IsometryEquiv Q')`); `isometryEquivOfCompLinearEquiv
  Q e : Q.IsometryEquiv (Q.comp ↑e)`; `Matrix.toLinearEquiv' P (Invertible P)` with `toLinearEquiv'_apply :
  ↑(toLinearEquiv') = toLin' P`; `Matrix.invertibleOfIsUnitDet`; `Int.cast_det : ↑M.det = (M.map cast).det`;
  `Matrix.det_smul`, `Matrix.det_conjTranspose`; `RingHom.isUnit_map`; `Matrix.posDef_iff_eq_conjTranspose_
  mul_self` (DEPRECATED → use `Matrix.PosDef.conjTranspose_mul_self A (Function.Injective A.mulVec)`);
  `Matrix.mulVecLin_injective_of_isUnit`/`mulVec_injective_of_isUnit`; `Matrix.PosDef.smul (hx) (0<a)`;
  `Matrix.conjTranspose_eq_transpose_of_trivial` (ℝ); `Matrix.map_mul`/`transpose_map` (need `⇑ringHom`);
  `LinearEquiv.finrank_map_eq`; `Matrix.nondegenerate_toBilin'_iff`/`nondegenerate_iff_det_ne_zero`.

## E₈ LDL (computed, for σ(E₈)=8 = [A1])

`E8lit = L · D · Lᵀ` (L lower-unitriangular, D positive-diagonal, over ℚ; verified `L D Lᵀ = E₈`, all D>0):
- `D = diag(2, 2, 3/2, 5/6, 4/5, 3/4, 2/3, 1/2)` (all > 0 ⟹ positive definite).
- `L` (lower-unitri) nonzero off-diagonal entries: L[2,0]=−1/2, L[3,1]=−1/2, L[3,2]=−2/3, L[4,3]=−6/5,
  L[5,4]=−5/4, L[6,5]=−4/3, L[7,6]=−3/2.
- ⟹ σ(E₈)=8 via congruence to D (sigPos invariant under `Equivalent`) OR `Matrix.PosDef` congruence + `latticeSig_of_posDef`.

## NEXT ACTIONS

1. ✅ **[A1] σ(E₈)=8, σ(−E₈)=−8 — DONE** (`E8Signature.lean`, kernel-pure, file-gate green, axioms clean).
   Integer-Cholesky route (not LDL): `C8ᵀ·C8 = 4•E8lit` decide-over-ℤ → posdef → `latticeSig_of_posDef`.
2. ✅ **σ(H)=0 — DONE** (`LatticeSignatureCongr.lean`, `hyp_latticeSig`), via `H ≅ −H` + congruence-invariance.
3. ✅ **Congruence-invariance `latticeSig_congr` — DONE** (Sylvester; the σ-readoff tool). Plus the reusable
   `sigPos_isom`/`sigNeg_isom`.
4. ✅✅ **[B3] SIGNATURE CALCULUS — FULLY DONE end-to-end** (all kernel-pure, project-gate green):
   - `BlockSignature.lean`: `sigPos_fromBlocks`/`sigNeg_fromBlocks` (`σ(A⊕B)=σA+σB`, Sum-indexed real form) +
     `nondeg_radical_eq_bot` (general symmetric-`Nondegenerate ⟹ radical=⊥` via `radical_eq_ker_polarBilin`).
   - `GeneratorNondeg.lean`: `cast_nondegenerate`, `e8r_radical`, `negE8_radical`, `hyp_radical` (all 3 generators
     nondeg; E₈ via posDef, −E₈/H via det≠0). Axioms clean (E₈/−E₈/H = []).
   - `LatticeSigBlock.lean`: **`latticeSigOf {ι}`** (index-general signature) + `latticeSigOf_fin` (=latticeSig
     on Fin n, rfl) + **`latticeSigOf_fromBlocks`** (`σ(A⊕B)=σA+σB` on integer matrices) + `reindexFormEquiv` +
     **`latticeSigOf_reindex`** (relabel-invariance, via `funCongrLeft`).
   ⟹ **For ANY normal form `E₈^a⊕(−E₈)^b⊕H^c` (nested `fromBlocks`, reindexed to Fin n): `latticeSig = 8a−8b+0
   = 8(a−b)`, manifestly `8∣σ`.** The signature side is COMPLETE; only the classification theorem (#5) remains.
5. **van der Blij `8∣σ` — REORIENTED 2026-06-04 (user pushback: "multi-year" was slipping/parroting stale DR).
   FRESH Mathlib scout CORRECTS the stale "zero substrate" claim — the analytic substrate EXISTS:**
   `Analysis/Fourier/PoissonSummation.lean` (`Real.tsum_eq_tsum_fourier`, **`SchwartzMap.tsum_eq_tsum_fourier`**
   = general Poisson), `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` (**`fourier_gaussian_
   innerProductSpace`** = MULTIVARIATE Gaussian FT on an inner-product space), `Gaussian/PoissonSummation.lean`
   (1-D Gaussian Poisson `Complex.tsum_exp_neg_quadratic`/`tsum_exp_neg_mul_int_sq`), `ModularForms/Basic`+
   `LevelOne` (`levelOne_neg_weight_eq_zero`, `levelOne_weight_zero_const`, `levelOne_weight_zero_rank_one`),
   `jacobiTheta_S_smul` (PROVEN via Poisson). So the two legs are NOT walls — they DECOMPOSE:
   - **[Θ] definite even unimodular ⟹ `8∣σ` — ✅✅✅ FULLY DONE & DISCHARGED (2026-06-04).** The full chain
     [Θ1]→[Θ2]→[Θ3]→[Θ4] is complete and the [Θ] hypothesis of `eight_dvd_latticeSig_of_HM_of_Theta` is now a
     THEOREM, not an assumption:
     * **[Θ3] S-transform DONE** (`ThetaSTransform.latticeTheta_S`, `ThetaModularWeight.latticeTheta_S_self`:
       `Θ_M(-1/τ)=(τ/i)^{d/2}Θ_M(τ)` for even unimodular, via `multivar_poisson` + `integral_cexp_neg_quadratic_form`
       + det=1 + `latticeTheta_inv_eq`).
     * **[Θ4] weight ⟹ `8∣d` DONE** (`ThetaModularWeight.eight_dvd_rank`): the `(ST)³`-orbit assembly at τ=I —
       three `theta_ST` steps around `(ST)³·I=I`, `Θ_M(I)≠0` (`latticeTheta_I_ne_zero`) divides out the
       automorphy factors, `mul_cpow_of_re_pos` collapses them to `(-I)^{d/2}=1 ⟺ 8∣d`
       (`neg_I_cpow_eq_one_iff_eight_dvd`). Helpers: `mul_cpow_of_arg_mem`, `neg_inv_im_pos`.
     * **[Θ-discharge] DONE** (`ThetaDefiniteDischarge.eight_dvd_latticeSig_of_definite`): `(sigPos=0 ∨ sigNeg=0)`
       even unimodular ⟹ `8∣latticeSig`. Bridge `sigNeg=0 ⟹ PosDef` via `posDef_of_sigPos_eq_finrank`
       (max positive subspace=⊤) + `nondeg_radical_eq_bot` (unimodular⟹nondegenerate) + Sylvester
       `sigPos_add_sigNeg_add_radical`; then `eight_dvd_rank` (PosDef σ=rank; sigPos=0 = neg-def mirror via `-A`).
     ALL kernel-pure [propext, Classical.choice, Quot.sound], no new axioms. **The definite case of `8∣σ` is
     UNCONDITIONAL.** Historical build trail below.
     ✅✅ **[Θ1] n-dim Poisson summation DONE** (`MultivarPoissonDescent.multivar_poisson`, kernel-pure, 2026-06-04): `∑_{γ∈ℤᵈ} F(↑γ) =
     ∑_{n∈ℤᵈ} latFourier F n`, under integrability/measurability/L¹-summability/coeff-summability side
     conditions (Schwartz-dischargeable). Built the whole RHS+continuity+Tonelli torus-free, then the torus
     descent + the `Ioc`↔`Ico` cube reconciliation. **✅✅ [Θ2] COMPLETE** (`AnisotropicGaussianFT.lean`,
     kernel-pure, commits `2d6539d2`/`4d033402`/`796b3d3c`/`c80495ba`/`6d3f8664`): the anisotropic multivariate
     Gaussian integral **`integral_cexp_neg_quadratic_form`** — for PosDef G, `0<b.re`, complex c,
     `∫_{ℝᵈ} exp(-b·xᵀGx+∑cᵢxᵢ) = (det G)^{-1/2}(π/b)^{d/2}exp((∑(c ᵥ* (√G)⁻¹_ℂ)ᵢ²)/(4b))`. Bricks: brick1
     `integral_comp_linearMap_volume`, brick2 `dotProduct_mulVec_eq_sqrt`, brick3 `integral_comp_sqrtInv`
     (Jacobian √det G), `isUnit_det_sqrt`, `sqrtInv_quadratic`, `sqrtInv_linear`; isotropic core =
     **Mathlib `GaussianFourier.integral_cexp_neg_mul_sum_add`** (separable, over the product space — NO
     EuclideanSpace bridge). 🔑 `Real.pi` not `π`; `Complex.real_smul`+`inv_mul_cancel₀` to solve-for-∫.
     **NEXT = [Θ3] S-transform** `Θ_A(−1/τ)=(τ/i)^{n/2}Θ_A(τ)` for even unimodular A: apply `multivar_poisson`
     to `F(x)=exp(iπτ xᵀGx)` (b=-iπτ, `b.re=π Im τ>0`; c=-2πI·n), recognize `latFourier F n` via
     `integral_cexp_neg_quadratic_form`, with `∑(c ᵥ* (√G)⁻¹_ℂ)ᵢ²=cᵀG⁻¹c=-4π²nᵀG⁻¹n`; det A=1
     [✅`posDef_unimodular_det_one`], A⁻¹≅A ⟹ `Θ_{A⁻¹}=Θ_A` [`latticeTheta_congr`]. (Original target form:)
     `𝓕(exp(−π vᵀAv))=(det A)^{−1/2}exp(−π wᵀA⁻¹w)`. [Θ3]
     S-transform `Θ_A(−1/τ)=(τ/i)^{n/2}Θ_A(τ)` (det A=1 [✅`posDef_unimodular_det_one`]; A⁻¹≅A ⟹ `Θ_{A⁻¹}=Θ_A`
     [`latticeTheta_congr`]). [Θ4] Θ_A nonzero level-1 weight-n/2 modular form (T=`latticeTheta_T_int`,
     S=[Θ3], nonzero=`latticeTheta_eq_one_add`) ⟹ `8∣n` (`LevelOne`). ✅ shipped `posDef_unimodular_det_one`,
     `latticeSig_posDef_eq_rank`. [Θ1]/[Θ2] = the substantial analytic builds remaining. NOT multi-year.
   - **[HM] indefinite even unimodular has a primitive isotropic vector** — DE-RISKED + first brick shipped
     (`HasseMinkowskiLocal.lean`, 2026-06-04). Decomposition: [HM-ℝ] indefinite⟹represents 0 over ℝ (elementary);
     [HM-p] unimodular rank≥3 represents 0 over ℚ_p ∀p — ✅ **`finite_field_form_isotropic`** (residue-field core:
     symmetric form over a FINITE FIELD in ≥3 vars is isotropic, via Mathlib `char_dvd_card_solutions`
     [Chevalley–Warning] — kernel-pure, axioms clean), then Hensel-lift to ℤ_p (Mathlib `Hensel`); p=2 via even
     unimodular ℤ_2 ⊃ U; [HM-LG] local-global Hasse–Minkowski (THE frontier — needs Hilbert symbol + product
     formula + Dirichlet/AP for rank 3,4, not in Mathlib); [HM-ℤ] ℚ-isotropic + unimodular ⟹ primitive ℤ-isotropic
     (elementary). NOT a monolith — [HM-ℝ]/[HM-p, odd]/[HM-ℤ] are reachable; [HM-LG] is the genuine remaining frontier.
   **Elementary scaffolding that ISOLATES [HM] and [Θ] (attackable now, pure algebra — but Mathlib has NO
   primitive-vector substrate, so build from scratch):**
   - ✅ **[E1] DONE** (`LatticePrimitive.lean`, kernel-pure, project-gate green): `IsPrimitiveVec v :=
     1∈span_ℤ(range v)`; `isPrimitiveVec_iff_exists_dot` (`IsPrimitiveVec v ↔ ∃w, v⬝ᵥw=1`, Bezout via
     `Finsupp.mem_span_range_iff_exists_finsupp`); **`exists_vecMul_dot_eq_one`** (unimodular `M` + primitive
     `v` ⟹ `∃w, (v ᵥ* M)⬝ᵥw=1` via `M⁻¹`, `mul_nonsing_inv`) — the isotropic vector's hyperbolic partner.
   - [E2] **split-off-H**: even unimodular `M` + primitive isotropic `v` ⟹ `∃ P∈GL(ℤ), PᵀMP = H ⊕ M'`
     (M' even unimodular rank −2). PARTIAL: ✅ partner `w` with `vᵀMw=1` (`exists_vecMul_dot_eq_one`, [E1]);
     ✅ **`even_form_dvd`** (`EvenLatticeForm.lean`: `2∣wᵀMw` for even symmetric M, via `redBilin_self_eq_zero`);
     ✅ **`exists_hyperbolic_pair`** (`LatticePrimitive.lean`: primitive isotropic `v` ⟹ `∃w'`, `{v,w'}` Gram = H,
     i.e. `vᵀMv=0 ∧ vᵀMw'=1 ∧ w'ᵀMw'=0`, via the `w':=w−(wᵀMw/2)v` adjustment). 🎯 **[E2] now reduces PURELY to
     the basis-completion** (last hard *elementary* piece). SUBSTRATE SCOUTED (2026-06-04): over ℤ (PID),
     `Module.Basis.extend`/`Submodule.exists_isCompl` are DIVISION-RING-ONLY; the ℤ tool is **Smith Normal Form**
     (`Submodule.smithNormalForm`, `Module.Basis.SmithNormalForm`, `Mathlib.LinearAlgebra.FreeModule.PID`).
     CLEANER CONCRETE ROUTE: H-duality splitting `π:ℤⁿ→ℤ², π(x)=(w'ᵀMx, vᵀMx)`, section `s(a,b)=a•v+b•w'`
     (`π(v)=(1,0)`, `π(w')=(0,1)` from H Gram) ⟹ `π∘s=id` ⟹ `ℤⁿ = K ⊕ ker π`, `K^⊥=ker π`. ✅ **projection
     `q(x)=x−(w'ᵀMx)•v−(vᵀMx)•w'` SHIPPED** (`LatticePrimitive.hyperbolic_proj_ortho`: `q(x)∈K^⊥`) + ✅
     **`hyperbolic_proj_idem`** (onto-`K` projector idempotent). ✅ **`hypPerp` + `hyperbolic_isCompl` SHIPPED**:
     the direct-sum splitting **`IsCompl (span ℤ {v,w'}) (hypPerp M v w')`** = `ℤⁿ = K ⊕ K^⊥` (disjoint via the
     H-Gram pairing forcing `a=b=0`; codisjoint via `p(x)+q(x)` with `hyperbolic_proj_ortho`). All kernel-pure.
     ✅ **`hyperbolic_linearIndependent`** ({v,w'} lin. indep. ⟹ basis of K, finrank K=2) + ✅ **`hypPerp_finrank`**
     (`finrank K^⊥ = n−2` via `prodEquivOfIsCompl`+`finrank_prod`; note `finrank_sup_add_finrank_inf_eq` is
     DIVISION-RING-ONLY, use the prod-equiv over ℤ). All kernel-pure. RESIDUAL = a concrete ℤ-basis of
     `K^⊥=hypPerp` (free rank n−2, established) ⟹ assemble `P = [v | w' | basis]`, prove `P` unimodular +
     `PᵀMP=H⊕M'` ⟹ consume `latticeSigOf_fromBlocks`/`_reindex`/`latticeSig_congr`. NEXT BRICK: obtain
     `Module.Free.chooseBasis`/SNF basis `b` of `hypPerp`, form `P` (cols v,w',b), show `P.det = ±1` and the
     congruence. (Alternative: recurse at the real-form level via `sigPos`/`sigNeg` orthogonal-additivity over
     the `IsCompl` real decomposition, `latticeSig M = σ(H)+σ(M|K^⊥)`.) ✅ **`hypPerpBasis`** (concrete `Fin (n−2)`
     ℤ-basis of `K^⊥`, via `Module.finBasis`+`finCongr hfr`; `Module.Free ℤ hypPerp` is automatic) + ✅
     **`hypPerpBasis_ortho`** (each basis vector ⊥ `v,w'` through `M`, from `hypPerp` membership). REMAINING [E2]:
     combine `![v,w']` ⊕ `hypPerpBasis` into a `Basis (Fin n) ℤ (Fin n→ℤ)` (via `Basis.prod`/`prodEquivOfIsCompl`
     + `finSumFinEquiv`, n=2+(n−2)), form change-of-basis `P` (unimodular: basis ⟹ `IsUnit P.det`), Gram in this
     basis = `fromBlocks H 0 0 M'` (off-diag 0 by `hypPerpBasis_ortho` + symmetry) ⟹ `latticeSig M = σ(H)+
     latticeSigOf M' = latticeSigOf M'` via `latticeSig_congr`+`latticeSigOf_fromBlocks`+`_reindex`.
     ✅ **`hypFullBasis` SHIPPED**: the combined `Basis (Fin 2 ⊕ Fin (n−2)) ℤ (Fin n→ℤ)` adapted to `K ⊕ K^⊥`
     (`bK.prod hypPerpBasis` mapped through `prodEquivOfIsCompl`; `bK` = `Basis.span hindep` transported across
     the `span{v,w'}=span(range![v,w'])` equality via `LinearEquiv.ofEq`). NEXT BRICK: the change-of-basis matrix
     `P := hypFullBasis.toMatrix (Pi.basisFun)` (or its inverse) is unimodular (`Basis.toMatrix` ∈ GL ⟹
     `IsUnit P.det`); Gram-in-basis `B i j = (hypFullBasis i)⬝ᵥM*ᵥ(hypFullBasis j) = (Pᵀ·M·P) reindexed`; show
     it `= fromBlocks H 0 0 M'` (diagonal blocks H/M', off-diag 0 via ortho); then `latticeSig_congr`+
     `latticeSigOf_fromBlocks`+`_reindex` ⟹ `latticeSig M = latticeSigOf M'` (the inductive split-off-H step).
     ✅ **`residGram` (M' = Gram of M on hypPerpBasis) + `residGram_symm` + `residGram_even` SHIPPED**: M' is even
     symmetric (induction invariant maintained; M' unimodular follows from the unimodular change of basis = the
     remaining assembly). NEXT BRICK: P := change-of-basis matrix of `hypFullBasis.reindex (finSumFinEquiv∘
     finCongr)`; `IsUnit P.det` (it is a basis); `Pᵀ·M·P = reindex (fromBlocks H 0 0 (residGram))` (entries:
     inl/inl=H via hypFullBasis(inl)=v,w'; inl/inr=0 via hypPerpBasis_ortho; inr/inr=residGram) ⟹ chain to
     `latticeSig M = latticeSigOf residGram`. ✅ **`hypFullBasis_inl`** (`B(inl k)=![v,w'] k`) + **`hypFullBasis_inr`**
     (`B(inr i)=hypPerpBasis i`) SHIPPED (via `Basis.map_apply`/`prod_apply`/`span_apply` + `prodEquivOfIsCompl`
     pair-eval `(a,b)↦↑a+↑b`; key: `Module.Basis.*` qualified in-file). NEXT BRICK: `GramB s t := (hypFullBasis s)
     ⬝ᵥ M *ᵥ (hypFullBasis t) = fromBlocks Hyp 0 0 residGram` (case-split s,t on inl/inr using the two
     evaluations + `hypPerpBasis_ortho`; inl/inl gives Hyp by `decide`/`Fin.cases` on the 2×2 `![v,w'] k ⬝ᵥ M *ᵥ
     ![v,w'] l` = hv0/hvw/hwv/hw0), then the change-of-basis matrix P + `Pᵀ M P = reindex GramB` + `latticeSig_congr`.
     ✅ **`gramB_eq` SHIPPED** (`SplitHyperbolic.lean`): Gram in combined basis = `fromBlocks Hyp 0 0 residGram`.
     ✅✅ **[E2] COMPLETE — `latticeSig_split` SHIPPED** (`SplitHyperbolic.lean`, kernel-pure, project-gate +
     ExtractDeps green 9092): for even unimodular `M` (rank ≥ 2) with a hyperbolic pair `{v,w'}`,
     **`latticeSig M = latticeSigOf (residGram M v w' hfr)`** — the split-off-H inductive step. Proof: `P :=
     (Pi.basisFun).toMatrix hypFullBasis` (unimodular: `Basis.toMatrix_mul_toMatrix_flip` ⟹ `IsUnit P.det`);
     `Pᵀ M P = reindex e e (of GramB)` (central identity via `Basis.toMatrix_apply`+`Pi.basisFun_repr`+
     `Finset.sum_comm`); `= reindex (fromBlocks Hyp 0 0 residGram)` (`gramB_eq`); `residGram` nondeg from
     `det residGram = ±det M = ±1` (via `det_reindex_self`+`det_fromBlocks_zero₂₁`); chain `latticeSig_congr` +
     `latticeSigOf_fromBlocks`(`hyp_radical`,`hRG`) + `_reindex` + `hyp_latticeSig`(σ(H)=0). 🔑 reusable:
     `Basis.toMatrix_mul_toMatrix_flip`, `det_fromBlocks_zero₂₁`, `det_reindex_self`, `Pi.basisFun_repr`.
   - ✅ **[E3] INDUCTIVE CONTENT DONE** (`RokhlinClassification.lean`, kernel-pure, project-gate green):
     `eight_dvd_latticeSig_e8lit`/`_neg_e8lit`/`_hyp` (generators `8∣σ`), `eight_dvd_latticeSigOf_fromBlocks`
     (block-sum step), `eight_dvd_latticeSig_congr` + `eight_dvd_latticeSigOf_reindex` (`8∣σ` invariant under
     congruence/reindex). ⟹ `8∣latticeSig(any block sum of generators)` follows by structural induction at the
     point of use — NO packaged recursive `normalForm` def needed. The assembly is COMPLETE; the only content
     left is the classification EXISTENCE.
   NEXT BRICK = [E1] (primitive vectors + dual lemma). Alternatively start [Θ]'s multidim-Poisson if the
   analytic route looks more tractable. Either way: long multi-session; ship kernel-pure bricks continuously.

---

## 2026-06-04 — ROUTE PIVOT to Hasse–Minkowski + [Θ] FULLY DISCHARGED; [HM-LG] local-solvability layer underway

**Strategic update.** The full classification route (above) decomposes `8∣σ` for even unimodular into two
classical inputs (van der Blij): **[Θ]** definite ⟹ `8∣σ`, and **[HM]** indefinite ⟹ primitive isotropic
vector. The classification-existence `≅ E₈^a⊕(−E₈)^b⊕H^c` itself reduces to exactly these two
(Hasse–Minkowski for indefinite; theta-modularity for definite) — there is **no elementary dodge** (re-confirmed
2026-06-04 by Explore fan-out across the whole corpus: no `H^a⊕E8^b` shortcut, no Eichler/strong-approx escape).
So the work is: discharge [Θ] (DONE) + grind [HM] = Hasse–Minkowski from scratch (Mathlib has zero substrate).

### ✅ [Θ] DEFINITE CASE — FULLY DISCHARGED (unconditional theorem)
- `ThetaModularWeight.eight_dvd_rank`: PosDef even unimodular ⟹ `8∣d`, via the `(ST)³`-orbit of the lattice
  theta at `τ=I` (`latticeTheta_I_ne_zero` divides out automorphy factors; `(-I)^{d/2}=1 ⟺ 8∣d`).
- `ThetaDefiniteDischarge.eight_dvd_latticeSig_of_definite`: `(sigPos=0 ∨ sigNeg=0)` even unimodular ⟹ `8∣σ`
  — the EXACT [Θ] hypothesis of `eight_dvd_latticeSig_of_HM_of_Theta`, now a theorem.

### ✅ GOAL WIRING (structure complete modulo [HM])
- `RokhlinFromHM.{eight_dvd_latticeSig_of_HM, sixteen_dvd_latticeSig_of_HM_of_topo}` feed the discharged [Θ]
  in, so even-unimodular `8∣σ`/`16∣σ` now need ONLY [HM] (+topo for the 16).
- `RokhlinManifoldFromHM.sixteen_convergence_of_HM` derives `16∣σ(M)` from the manifold's genuine
  `even_unimod`+`topo`+[HM]. ⟹ once [HM] is a theorem, drop the `eight_dvd`/`charSq` field ⟹ fully
  unconditional bridge. **Target shape of [HM]** (`HasWeakIsotropicVectorHyp`): for a symmetric integer Gram
  matrix `A`, `IsEvenUnimodular A` + `0<sigPos` + `0<sigNeg` ⟹ `∃ v:Fin m→ℤ, v≠0 ∧ v ⬝ᵥ A *ᵥ v = 0`. The
  weak (nonzero) output upgrades to primitive via `hasIsotropic_of_weak` (content extraction). Downstream
  consumers of a primitive isotropic vector already exist: `LatticePrimitive.exists_hyperbolic_pair`,
  `SplitHyperbolic.latticeSig_split`.

### [HM] decomposition (anti-circular — no ABP/Rokhlin input)
[HM-ℝ] ✓ (`HasseMinkowskiLocal.indefinite_repr_zero`/`indefinite_matrix_repr_zero`, discriminant root) ·
[HM-ℤ primitivization] ✓ (`LatticeContent.exists_primitive_isotropic_of_isotropic`) ·
weak⟹strong ✓ (`RokhlinFromHM.hasIsotropic_of_weak`) ·
**[HM-LG] = the frontier** (local solvability everywhere + Hasse–Minkowski local–global rank-induction).

### ✅ Hilbert-symbol arithmetic FOUNDATION (all kernel-pure, root-imported)
- `HilbertSymbolReal` (∞), `HilbertSymbolPadic` (odd p, signed ℤ), `HilbertSymbolTwo` (p=2, signed ℤ),
  `PadicUnitResidue` — all four local symbols bimultiplicative.
- **`HilbertProductFormula.hilbertGlobalProd_eq_one` ✓ MAJOR MILESTONE**: `∏_v (a,b)_v = 1` for all nonzero
  integers `a,b` (≡ quadratic reciprocity + supplementary laws). Built via unified `hilbertPrime` place symbol,
  finiteness-of-support, all generators (`(−1,−1)`, `(−1,q)`, `(2,q)`, QR-core `(p,q)`), multiplicative
  reduction by nested `Nat.recOnMul`, sign extension. Mathlib had none of this.

### ✅ p-adic LOCAL-SOLVABILITY layer — odd-p complete (2026-06-04, all in `PadicSquare.lean`)
- **p-adic square classes at every prime:** odd p `isSquare_iff_isSquare_toZMod` (square ⟺ residue mod p
  square, via Hensel on `X²-u`); p=2 `isSquare_iff_toZModPow_three_eq_one` (square ⟺ `≡1 mod 8`); bridge
  `toZModPow_eq_zero_iff_norm_le`.
- **`exists_ternary_isotropic_odd`** (units a,b, odd p ⟹ `aX²+bY²=Z²`, Z unit) via
  `FiniteField.exists_root_sum_quadratic` (binary form universal over 𝔽_p, represents `1=1²`) + Hensel lift.
- **`exists_diag_ternary_zero_odd`** (symmetric `ax²+by²+cz²=0`) + **`exists_diag_nary_zero_odd`**
  (rank n≥3 unit diagonal form isotropic). ⟹ ALL odd-p local conditions discharged for unit-coeff diagonal
  forms. ⚠️ **p=2 ternary isotropy is NOT unconditional** (depends on `(a,b)_2`; `x²+y²+z²=0` anisotropic over
  ℚ₂) — p=2 forces the symbol↔solvability bridge, not a free lemma.

### ✅ Diagonalization scaffold (`HasseMinkowskiLocal.lean`, 2026-06-04)
- **`toQuadraticMap'_apply`** (`M.toQuadraticMap' x = x ⬝ᵥ M *ᵥ x`) + **`exists_ne_zero_isotropic_congr`**
  (isotropy transfers across `QuadraticMap.Equivalent`, via `IsometryEquiv.map_app`). These connect the
  Gram-matrix isotropy shape to Mathlib's diagonalization `equivalent_weightedSumSquares` (any field,
  `Invertible 2`) so the diagonal local lemmas above can be applied at each completion and transported back.

### NEXT bricks (critical path; THE BULK remains — multi-session)
(i) p=2 square-class → symbol↔solvability bridge `(a,b)_p=1 ⟺ z²=ax²+by² solvable over ℚ_p` (general a,b via
bimult reduction to unit / p·unit cases); (ii) full diagonalization-over-ℚ_p bridge: scale `weightedSumSquares`
weights to `unit×pᵏ`, group by valuation parity (= local classification / Hasse invariant); (iii) "rank≥5 ⟹
isotropic over ℚ_p (any p)" workhorse [rank 2 ELEMENTARY via binary discriminant; rank 4 = quaternary HM crux];
(iv) Hasse–Minkowski local-global rank-induction (3/4 via the completed product formula + Mathlib's Dirichlet;
n≥5 by reduction); (v) apply to indefinite even unimodular ⟹ `HasWeakIsotropicVectorHyp` ⟹ drop the field ⟹
unconditional bridge + update D2/L2 + HYPOTHESIS_REGISTRY + dispatch closure reviewer.

**Standing rules unchanged:** kernel-pure (standard axioms only), no `native_decide`/`maxHeartbeats`/axiom;
file-gate per brick, project-gate (`ExtractDeps`) at wave close; commit brick-by-brick to `main`, NEVER push;
PadicSquare/HasseMinkowskiLocal are root-imported but appending theorems needs no root edit (no bordism dance).

---

## 2026-06-08 — FLEXIBLE-SELECTION LAYER SHIPPED (the Serre Thm 4 construction engine)

**Resume session after multi-day pause. 3 substantive bricks, all kernel-pure `{propext, Classical.choice,
Quot.sound}`, file-gate green, committed to `main` (NOT pushed); all in `PadicSquare.lean`.** These break the
rigidity (`exists_prime_gt_isSquare_pair` forced `q ≡ 1 mod p`, over-constraining the residue-matching freedom)
that was the identified obstacle to the keystone construction.

- `3e0e5980` **`isSquare_odd_prime_zmod_flex`** — flexible QR: odd primes `p,q`, `q ≡ 1 mod 4`,
  `IsSquare ((q:ℤ):ZMod p)` ⟹ `IsSquare ((p:ZMod q))`. Relaxes `isSquare_odd_prime_zmod`'s rigid `q ≡ 1 mod p`
  to the genuine reciprocity input `(q|p)=1`. Proof = `legendreSym.quadratic_reciprocity` + `eq_one_iff`,
  sign `+1` from `q ≡ 1 mod 4`.
- `c47ffa26` **`isSquare_{natCast,intCast}_zmod_of_isSquare_residues`** — flexible multiplicative criterion:
  `q ≡ 1 mod 8` + every prime factor `p` of `m` has `IsSquare ((q:ℤ):ZMod p)` ⟹ `IsSquare ((m:ZMod q))`.
  Generalises `isSquare_*_zmod_of_modEq`. `Nat.recOnMul` over the factorisation; `p=q` trivial (`m≡0`),
  odd `p` via the flex QR lemma, `p=2` via `q≡1 mod 8`, sign via `−1` square.
- `d279f953` **`exists_prime_gt_eq_mod_isSquare`** — THE construction engine: `8∣D`, unit `r:ZMod D` with
  `r.val ≡ 1 mod 8` and `r` a QR mod every prime factor of `|m|` (all dividing `D`) ⟹ ∃ prime `q>N` with
  `q ≡ r (mod D)` AND `IsSquare ((m:ZMod q))`. Realizes the prescribed square class `r` *exactly* (ZMod-unit
  Dirichlet `Nat.forall_exists_prime_gt_and_eq_mod`) while keeping `m` square (flex criterion). Generalises
  `exists_prime_gt_isSquare_pair` (rigid `r=1`, `D=8|m||n|`). **This is Serre Ch III §2.2 Thm 4's auxiliary-prime
  step: ONE prime simultaneously matches a prescribed class and keeps a target square. The consistency that
  such a unit `r` EXISTS is the product-formula content — a separate, still-to-build input.**

🔑 reusable API confirmed: `Nat.forall_exists_prime_gt_and_eq_mod {q}[NeZero q]{a:ZMod q}(IsUnit a)(n) :
∃ p>n, p.Prime ∧ ↑p=a` (ZMod-unit Dirichlet, cleaner than the ℕ-ModEq form); `ZMod.natCast_rightInverse r :
↑r.val = r`; `Nat.ModEq` is defeq to `% = %` (omega-usable directly); `Nat.ModEq.of_dvd`.

**➕ MATCHING PRIMITIVES (same 2026-06-08 session, kernel-pure, file-gate green, `main` NOT pushed) — the
square-class matching layer the construction feeds to `binary_represents_of_isSquare_ratio`:**
- `318745e4` **`exists_int_coprime_residues`** — refines `exists_int_residues`: nonzero target residues
  (`¬p∣r p`) ⟹ the CRT integer `k` hits `(k:ZMod p)=r p` AND is coprime to every `p∈ps`. The *unit factor* `u`
  of `t = ε·q·(∏T)·u` (a `p`-adic unit at each bad prime, perturbs no valuation while setting the unit part).
- `3b24138c` **`padicValInt_prod_primes`** — for a Nodup prime list `T`, `padicValInt p (∏T) = if p∈T then 1
  else 0`. The *valuation-fixing factor*: `T` = bad primes where `v_p(c_p)` is odd ⟹ `t` gets matching
  valuation parity (so `v_p(t/c_p)` is even). Proof = list induction + `padicValNat.mul/self/eq_zero_of_not_dvd`
  + `padicValInt.of_nat`; `List.prod_eq_zero_iff` for nonzero-product; ⚠️ `List.mem_cons_self` takes NO explicit
  args in this Mathlib.
- `d2de4449` **`isSquare_padic_div_of_decomp`** — odd `p`, `x=p^{vx}·ux`, `y=p^{vy}·uy` (`ux,uy` ℤ_p units),
  `Even(vx−vy)` + `toZMod ux=toZMod uy` ⟹ `IsSquare(x/y)`. `p^{vx−vy}=(p^k)²` square × `ux/uy` square
  (`isSquare_padic_div_units`). 🔑 `mul_div_mul_comm`+`←zpow_sub₀`; `IsSquare(p^{2r})` via `⟨p^r, by rw[hr,
  zpow_add₀]⟩` (NOT `congr 1;omega` — that over-closes). **⟹ constructed `t` and local `c_p` share a ℚ_p-square
  class iff valuation parities + unit residues agree — the exact consumer of `binary_represents_of_isSquare_ratio`.**

**STATE: all multiplicative ingredients (ε via `exists_sign_for_real_common`, q via `exists_prime_gt_eq_mod_isSquare`,
∏T via `padicValInt_prod_primes`, u via `exists_int_coprime_residues`) + the square-class matcher are in hand.**

**➕ VERIFICATION + PRODUCT-FORMULA-CLOSURE LAYER (same 2026-06-08 session, kernel-pure, file-gate green, NOT pushed):**
- `f542e912` **`binary_represents_padic_even_val_int`** (PadicSquare) — odd `p`, `p∤a`, `p∤b`, `t≠0`,
  `Even((t:ℚ_p).valuation)` ⟹ `⟨a,b⟩` represents `t` over `ℚ_p`. The good-place verification: at every odd
  prime outside `2abcd` and `≠ q`, the constructed `t = ε·q·∏T` is a unit (valuation 0 even) ⟹ both binaries
  represent it. (`padic_norm_intCast_eq_one` + `binary_represents_padic_even_val`.)
- `129175e3` **`hilbertReal_eq_of_hilbertPrime_eq`** (HasseMinkowskiGlobal, **axiom-free []**) — if
  `(t,−ab)_p=(a,b)_p` at EVERY finite place `p`, then it holds at `∞` too. Both global products `=1`
  (`hilbertGlobalProd_eq_one`); equal finite factors (±1, nonzero) cancel ⟹ equal real factors. **The
  distinguished-place mechanism of Serre Thm 4: using `∞` as the free place removes one degree of constraint
  exactly as the product formula dictates — the construction need only match symbols at the bad FINITE places.**

🔑 **KEY STRUCTURAL SIMPLIFICATION discovered this session (de-risks the assembly):** with `−ab,−cd` square mod
the Dirichlet prime `q` (handled by the engine via `q`'s residue being a QR mod each bad prime), `q` is a square
in `ℚ_p` at each bad prime `p` ⟹ the `(q,·)_p` factor of the symbol is `1` ⟹ **the symbol at `p` does NOT depend
on `q`'s residue**, only on `ε` and `T` (the valuation/sign data). And at `q` itself, `−ab,−cd` square ⟹ both
symbols are `1=1` automatically (`binary_universal_padic_of_residue`/`good_prime_symbol_auto`). So the only
genuinely-constrained data is `ε` (real sign) + `T` (which bad primes carry the odd-valuation factor), matched
at the bad finite places, with `∞` free by `hilbertReal_eq_of_hilbertPrime_eq`.

**NEXT = the big assembly proof `quaternary_solvable_of_local` (n=4): build the global integer `t = ε·q·∏T`,
prove its symbol at each bad finite place matches `(a,b)_p`/`(c,d)_p` by the `ε`/`T` choice (q-factor trivial),
feed `hilbertReal_eq_of_hilbertPrime_eq` for `∞`, then `represents_everywhere_iff_symbols` +
`quaternary_isotropic_of_keystone`. Then n≥5 Meyer, p=2 even-unimod local isotropy, `HasWeakIsotropicVectorHyp`,
wire RokhlinBridge + D2/L2 + registry + closure reviewer. No new walls — all leaves shipped.**

**➕ INTEGER↔ℤ_p-UNIT BRIDGES (same 2026-06-08 session, kernel-pure, file-gate green, NOT pushed):**
- `c19a881d` **`binary_represents_padic_val_zero_int`** (PadicSquare) — odd `p`, `p∤a`, `p∤b`, `t≠0`,
  `padicValInt p t = 0` ⟹ `⟨a,b⟩` represents `t` over `ℚ_p`. The exact good-place form for the constructed `t`
  (its valuation is read via `padicValInt_prod_primes`); bridges to the ℚ_p-valuation hyp via `Padic.valuation_intCast`.
- `2e772372` **`padicInt_intCast_isUnit`** (PadicSquare) — `¬p∣C ⟹ IsUnit (C:ℤ_[p])`. With `map_intCast
  PadicInt.toZMod C`, packages an integer cofactor as the `ℤ_[p]`-unit-with-known-residue that
  `isSquare_padic_div_of_decomp` consumes (the unit part of `t=ε·q·∏T` at a bad prime is the integer `t/p`).

### THE REMAINING CORE: the 𝔽₂ consistency (Serre Thm 4 heart) — precise plan
All leaves are shipped; the bottleneck is the single hard proof that the construction data `(ε, T)` exists.
Concretely (square-class matching via `binary_represents_of_isSquare_ratio` + `isSquare_padic_div_of_decomp`):
at each bad odd prime `p∈S`, with `q` a QR mod `p` (so `q` is a `ℚ_p`-square, its symbol factor drops out),
`t/c_p` is a square ⟺ `ε·∏_{p'∈T,p'≠p} p' ≡ c_p`'s unit class (mod squares mod `p`) AND `[p∈T] ≡ v_p(c_p) (mod 2)`.
The first conditions, across all `p∈S` (plus `p=2` via mod 8) and for BOTH forms `⟨a,b⟩,⟨c,d⟩`, form a **linear
system over 𝔽₂** in the unknowns `ε` (1 bit) + `{[p∈T] : p∈S_odd}`. **Solvability ⟸ the product formula**
(`hilbertGlobalProd_eq_one`): the equations are consistent because the global product of each form's symbols is 1.
`hilbertReal_eq_of_hilbertPrime_eq` already discharges the `∞` equation for free (one fewer constraint). NEXT
increments: (i) formalize the per-bad-prime symbol/square-class of `t` as an 𝔽₂-linear functional of `(ε,T)`
(cross-terms = Legendre symbols `legendre(p'/p)`); (ii) prove the system is solvable from the product formula
(the genuine crux — a rank/consistency argument over 𝔽₂); (iii) assemble. This is the "hardest single piece,
never formalized via this route." No axiom, no absent Mathlib machinery (Dirichlet present) — pure construction.

### 🔎 SCOPE OBSERVATION (worth exploiting / flag for review): rank-4 indefinite even unimodular ⟹ SQUARE disc.
An indefinite even unimodular form of rank 4 has `8∣σ ∧ |σ|≤4 ⟹ σ=0` ⟹ real form has 2 pos + 2 neg eigenvalues
⟹ `det = (+)(+)(−)(−) = +1` (and `|det|=1` by unimodularity) ⟹ **discriminant is a square** ⟹ handled by the
already-proven **Dirichlet-free** `quaternary_sqdisc_solvable_of_local`. So the non-square-disc n=4 construction is
NOT needed at rank 4. Generally `det = (−1)^{(n−σ)/2}`, a square iff `4∣n`; ranks `≡2 mod 4` (6,10,…) still give
non-square disc, so the general n=4 construction is still required for those via the n≥5 reduction. (Rank 2 even
unimodular indefinite = `H`: `b²−4ac=1` square disc ⟹ elementary binary isotropy.) Net: the 𝔽₂ construction is
unavoidable for rank ≥ 6, but rank-2 and rank-4 cases are already discharged by elementary/square-disc routes.

**➕ BAD-PRIME VERIFICATION TOOLKIT NOW COMPLETE (2026-06-08, kernel-pure, file-gate green, NOT pushed):**
- `a52579c9` **`hilbertPrime_eq_of_others`** (HasseMinkowskiGlobal) — companion of the ∞-free lemma: match at ∞
  and every finite place except a chosen prime `q` ⟹ match at `q`. Single-point finprod factoring
  (`mul_finprod_cond_ne`). **Both free-place directions now available — the construction may free ANY place.**
- `deb3d35d` **`isSquare_padic_div_int`** (PadicSquare) — integer face of `isSquare_padic_div_of_decomp`: integers
  `x=p^vx·Cx`, `m=p^vm·Cm` (Cx,Cm coprime to p), equal valuation parity + `Cx≡Cm mod p` ⟹ `IsSquare(x/m)` /ℚ_p.
- `ecdd77c7` **`isSquare_2adic_div_of_decomp` + `isSquare_2adic_div_int`** (PadicSquare) — the `p=2` analogues
  (valuation parity + residue mod 8 via `toZModPow 3`/`ZMod 8`). `2∈S` always, so the p=2 matcher is mandatory.
🔑 reusable: `padicInt_intCast_isUnit hC` lifts an integer cofactor `¬p∣C` to a `ℤ_[p]` unit; `map_intCast
PadicInt.toZMod`/`toZModPow 3` gives its residue; `push_cast [zpow_natCast]; ring` bridges `ℕ`-pow `p^v` to the
`zpow` the decomp matcher wants.

### ASSEMBLY ENTRY POINT (next increment): `quaternary_solvable_of_local`
EVERY verification leaf is now shipped (good odd p: `binary_represents_padic_val_zero_int`; q-place:
`binary_universal_padic_of_residue`; bad odd p: `binary_represents_of_isSquare_ratio` ∘ `isSquare_padic_div_int`
∘ `exists_int_sq_ratio_odd`; p=2: `…_2adic_div_int`; ∞: `real_binary_represents_iff` + product-formula closure).
The ONLY remaining mathematical content is the **𝔽₂-consistency / construction of the data `(ε, T, q-residues)`**:
prove that `hilbertGlobalProd_eq_one` makes the per-bad-prime square-class conditions jointly solvable. This is
the genuine large core; everything it feeds is a theorem. Build order next: (1) extract local common values `c_v`
+ their integer square-class reps at each `v∈S` (`common_value_of_quaternary_isotropic` + `exists_int_sq_ratio_*`);
(2) the 𝔽₂ solvability from the product formula (the crux); (3) assemble `t = ε·q·∏T`, verify place-by-place,
feed `quaternary_isotropic_of_keystone`; (4) downstream chain + wire.

**➕ WEAK-APPROXIMATION BRIDGE LAYER (2026-06-08, kernel-pure, file-gate green, NOT pushed) — CRT ⇒ square-class:**
- `0b73a2fa` **`exists_int_prime_pow_residues`** — prime-power CRT: distinct primes, prescribed residues mod
  `p^{e p}` ⟹ ∃ integer `k` hitting them all (`Nat.chineseRemainderOfList` + `Nat.Coprime.pow`). Prescribing mod
  `p^{v_p(t_p)+1}` fixes the full ℚ_p-square class. The weak-approx core — matches all bad primes at once.
- `44f3cf47` **`exists_int_factor_padicValInt`** — `m≠0 ⟹ m = p^{padicValInt p m}·m'` with `p∤m'`
  (`padicValInt_dvd_iff`). Lets the integer matchers apply to ANY integer.
- `a86c77e1` **`isSquare_padic_div_of_modEq`** — odd p, `k ≡ m (mod p^{v_p(m)+1})` ⟹ `IsSquare(k/m)` /ℚ_p
  (congruence ⟹ equal valuation [ultrametric] + cofactors ≡ mod p ⟹ `isSquare_padic_div_int`). **The bridge:
  the prime-power-CRT integer automatically shares `t_p`'s square class at each bad odd prime — connecting the
  CRT step to bad-prime verification with NO manual decomposition.**
🔑 reusable: `padicValInt_dvd_iff n a : p^n∣a ↔ a=0 ∨ n≤padicValInt p a`; `Nat.Coprime.pow` takes exponents
positionally; `exists_int_factor_padicValInt (p := p)` — pin `p` (else `Fact` metavar stuck).

**STATUS: the CRT→square-class→representability pipeline is now end-to-end** for BOTH bad odd primes
(`isSquare_padic_div_of_modEq` `a86c77e1`) AND p=2 (`isSquare_2adic_div_of_modEq` `e423d7ac`, mod 2^{v+3}).
**The ONLY remaining mathematical content is the 𝔽₂ solvability** (existence of `(ε,T)` / the Dirichlet prime
residue making every bad-prime square-class condition hold, via `hilbertGlobalProd_eq_one`), then assemble.

### 🔎 ROUTE-CONFIRMATION investigation (2026-06-08, Explore breadth scan — NO shortcut, summit required)
Before committing ~1000 lines to Serre Thm 4, scanned Mathlib + repo + Lit-Search for a Dirichlet-free shortcut
(motivated by the rank-4 = square-disc observation). FINDINGS:
- **Mathlib has NO Minkowski convex-body theorem / geometry-of-numbers isotropy** (only `ZLattice`/`covolume`
  infra + number-field `minkowski_bound`). So a geometry-of-numbers Meyer would require building the convex-body
  theorem from scratch (Blichfeldt + ...) — itself substantial. Mathlib has NO Meyer, NO genus classification.
- **Repo rank-≥5 LOCAL isotropy IS Dirichlet-free and shipped:** `exists_diag_nary_zero_odd_padic`
  (`PadicSquare.lean:317`) — any rank-≥5 diagonal form over ℚ_p (odd p) is isotropic, via parity-pigeonhole
  (`exists_three_same_parity` → same-parity ternary block). Plus `indefinite_repr_zero` (ℝ). So rank-≥5 forms are
  locally isotropic everywhere with NO Dirichlet — BUT the **global** local→global step for rank ≥5 still reduces
  (Serre's rank reduction) to the **n=4 common-value construction**, which needs Dirichlet. ⟹ Meyer does NOT
  dodge the summit.
- **Lit-Search Phase-5c** (`Rokhlin/Rokhlin's theorem, even unimodular lattices, and Lean 4 formalization.md`):
  confirms σ≡0 mod 8 for indefinite uses Hasse–Minkowski (odd indefinite classification); no algebraic dodge.
- **CONCLUSION (consistent with prior deep research): the n=4 / Serre Thm 4 construction is genuinely required.**
  The rank-4 = square-disc observation handles rank 4 (and rank 2 elementary), but rank ≥ 6 even unimodular needs
  the general construction. PROCEED to build the summit (the 𝔽₂ consistency).

**NEXT: design+build the 𝔽₂ consistency** (linear system over ZMod 2 with the reciprocity matrix; solvable from
`hilbertGlobalProd_eq_one`), then assemble `quaternary_solvable_of_local` from the shipped leaves → downstream
chain (n≥5 Meyer-via-HM → p=2 even-unimod local isotropy → `HasWeakIsotropicVectorHyp`) → wire.

### ⭐⭐ CLEAN CONSTRUCTION (2026-06-08) — the free-place mechanism DISSOLVES the 𝔽₂ matrix
**Key realization: the feared 𝔽₂ linear system / per-prime QR conflict is NOT needed.** The conflict only arose
when requiring `−ab,−cd` square mod the auxiliary prime `q` (to handle the q-place directly), which pinned `q`'s
residue mod each bad prime to the QR subgroup AND to the matching class simultaneously. **Instead, FREE the
q-place via the product formula** (`hilbertPrime_eq_of_others`, shipped): then `q`'s residue is only constrained
to set the unit residue of `t = (S-part)·q` at the bad places — a *coprime* class, always realizable by plain
Dirichlet (`exists_prime_gt_eq_mod`, shipped `b31ad43f`), with NO QR requirement and NO consistency obstruction.

**The clean construction of the global `t`:**
1. At each `p∈S = {2}∪{odd p∣abcd}`, the certificates `binary_pair_represents_of_congr_{odd,2}` give an integer
   common value `m_p` such that any `t ≡ m_p (mod p^{N_p})` is represented by BOTH binaries over ℚ_p.
2. Choose sign `ε` (via `local_realizable_symbol_real`/`exists_sign_for_real_common`) so both binaries represent
   `t` over ℝ (matches both families at ∞).
3. Let `t = (S-part)·q` where the S-part `= ε·∏_{p∈S-odd}p^{v_p(m_p)}` carries the valuations, and `q` is a
   single Dirichlet prime (`exists_prime_gt_eq_mod`) with `q ≡ (m_p·(S-part)⁻¹) (mod p^{N_p})` at each `p∈S`
   and `q ≡ 1 mod 8` — a coprime residue class, CRT-combined, ALWAYS realizable (no product-formula needed here).
4. Verify both families match at every place EXCEPT q:
   - `p∈S`: `t ≡ m_p mod p^{N_p}` ⟹ certificates ⟹ both represent `t` ⟹ symbols match (`represents_padic_iff_hilbertPrime_linear`).
   - good odd `p∉S∪{q}`: `t` is a unit (supported on `S∪{q}`) ⟹ `good_prime_symbol_auto` (p∤a,b,c,d,t).
   - `∞`: sign `ε` ⟹ both represent ⟹ symbols match.
5. **q-place: FREE** — `hilbertPrime_eq_of_others` (per family) gives `(t,−ab)_q=(a,b)_q` and `(t,−cd)_q=(c,d)_q`
   from matching at ∞ + all finite ≠ q (the product formula does the work).
6. ⟹ both families match at ALL places ⟹ `quaternary_isotropic_of_symbol_keystone` (shipped `2b685c64`) ⟹
   `quaternary_solvable_of_local`.

**NO 𝔽₂ matrix, NO consistency obstruction — just CRT + plain Dirichlet + the shipped free-place lemmas.** The DR
(`Lit-Search/tasks/submitted/Phase5qB_SerreThm4_n4...`) will confirm/refine, but this path is now concrete. NEXT:
build the global-`t` construction (CRT residue target + Dirichlet `q` + `t=(S-part)·q` with its
supported-on-`S∪{q}` + `≡m_p` + sign properties), then `quaternary_solvable_of_local`, then the downstream chain.

## 🎯🎯🎯 2026-06-08 — RANK-4 HASSE–MINKOWSKI DISCHARGED (`quaternary_solvable_of_local`, `f0bc7048`)

**THE SUMMIT IS DONE.** `HasseMinkowskiGlobal.quaternary_solvable_of_local`: for nonzero integer `a,b,c,d`, if
`a x²+b y²=c z²+d w²` is isotropic over ℝ and every ℚ_p, then it is isotropic over ℚ. Kernel-pure
`{propext, Classical.choice, Quot.sound}`, NO new axioms. This is the previously-"never-formalized-via-this-route"
core of indefinite even-unimodular `8∣σ`.

**The clean construction (NO 𝔽₂ matrix) that did it:** `t = ε·(∏_{p∈S} p^{v_p(m_p)})·q`, `S = primes∣2abcd`,
`m_p` = local common values (`hilbertPrime_pair_match_of_congr`), `ε` = real sign (`exists_sign_for_real_common`),
`q` = ONE plain-Dirichlet prime (`exists_prime_prime_pow_residues`) whose residues set `t`'s unit part so
`t ≡ m_p (mod p^{N_p})` at each bad prime (`exists_residue_smul_congr` hides the modular inverse). Symbols match at
every place except `q` directly (bad: certificates; good: `hilbertPrime_pair_match_good` via support
`not_dvd_sign_mul_prod_pow`; `∞`: sign); **`q` recovered FREE from the product formula
(`quaternary_isotropic_of_symbol_except_q`)** — this is what dissolved the consistency obstruction.

🔑 build lessons (file-vs-run_code): `lake env lean` uses STALE dep `.olean` — must `lake build` after editing an
imported file; `rw [hmeq]` self-references `m` inside `padicValInt p m` → use `set e`/`linear_combination`/
`Ring.inverse` (non-dependent, avoids `IsUnit.unit` motive errors); `ZMod.coe_int_isUnit_iff_isCoprime` wants
`IsCoprime ↑D k` order (use `.pow_left`); double-cast `Int.cast∘Nat.cast` in a `List.map` blocks `ring` →
`simp only [List.map_map, Function.comp_def, Int.cast_natCast]`.

### REMAINING downstream chain (no more walls — standard HM machinery, n=4 base now in hand):
1. **n≥5 Meyer reduction** — indefinite rank-≥5 forms reduce to the n=4 base (`quaternary_solvable_of_local`)
   via the common-value step; rank-≥5 LOCAL isotropy is already Dirichlet-free (`exists_diag_nary_zero_odd_padic`).
2. **p=2 even-unimodular local isotropy** — even unimodular over ℤ_2 contains U ⟹ isotropic over ℚ_2 (the `hloc`
   input at p=2 for even unimodular forms).
3. **`HasWeakIsotropicVectorHyp`** — matrix → ℚ-diagonalize → locally isotropic everywhere (1+2) → globally
   isotropic (n=4/n≥5 HM) → `exists_int_isotropic_of_rat` (shipped) → integer vector. Feeds `RokhlinFromHM`.
4. **Wire**: drop `eight_dvd`/`h_rokhlin` from `RokhlinBridge.sixteen_convergence_full`; update D2/L2 +
   HYPOTHESIS_REGISTRY; dispatch closure reviewer.
(rank-2 even-unimod = `H` square-disc elementary; rank-4 indefinite even-unimod = square-disc → `quaternary_sqdisc`
DONE; general n=4 now also DONE.)

### REMAINING toward the keystone (`quaternary_isotropic_of_keystone` consumes a global `t`):
With the engine in hand, the keystone existence (Serre Thm 4 for the two families `a₁=−ab, a₂=−cd`) now needs:
(a) **the consistency brick** — construct the unit target `r:ZMod D` whose images encode the matching square
classes at the bad primes AND the QR conditions, with joint realizability = `hilbertGlobalProd_eq_one` (the
genuine crux); (b) **valuation builder** — assemble `t = ε·q·∏_{p∈S} p^{δ_p}` (sign `ε` via
`exists_sign_for_real_common`, prime `q` via the new engine, valuations via squarefree products + `exists_int_residues`
CRT); (c) **place-by-place verification** — ℝ (`real_binary_represents_iff`), good odd `p`
(`binary_represents_good_odd` / `_padic_even_val`), bad `p` (`binary_represents_of_isSquare_ratio` matching `c_p`),
`q` (`binary_universal_padic_of_residue`); (d) feed `represents_everywhere_iff_symbols`/`quaternary_isotropic_of_keystone`
⟹ `quaternary_solvable_of_local` (n=4); then n≥5 Meyer, p=2 even-unimod local isotropy, `HasWeakIsotropicVectorHyp`,
wire RokhlinBridge + D2/L2 + registry + closure reviewer. **EVEN-UNIMOD SIMPLIFICATION still to exploit:
bad set reduces toward {∞,2}, dissolving odd-prime residue conflicts in (a).**
