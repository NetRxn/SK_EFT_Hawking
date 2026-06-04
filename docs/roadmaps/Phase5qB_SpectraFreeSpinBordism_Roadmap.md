# Phase 5q.B: Spin-Bordism Formalization — an unconditional `16 ∣ σ` via quadratic-form methods

## Technical Roadmap — June 2026

*Goal: make the spin-bordism / Rokhlin leg of the generation-constraint program unconditional by
classical quadratic-form, lattice, and 4-manifold methods — the route that reuses the repo's existing
`E8Lattice` / `AlgebraicRokhlin` substrate and Mathlib's `QuadraticForm` library, rather than building the
stable-homotopy / Steenrod / Adams-spectral-sequence stack. PUBLIC repo. No new axioms; correctness over
expedience.*

---

## The target, precisely

The generation-constraint program has three distinct topological strands; this roadmap addresses the first.

1. **`16 ∣ σ(M)`** for closed smooth spin 4-manifolds (Rokhlin's theorem). This is the fact consumed — as a
   **hypothesis** — by [RokhlinBridge.lean](../../lean/SKEFTHawking/RokhlinBridge.lean)
   `sixteen_convergence_full` (the Rokhlin axiom was demoted to a hypothesis 2026-04-04). Discharging it is
   the objective here. The stronger statement `Ω^Spin_4 ≅ ℤ` (packaged in
   [SpinBordism.lean](../../lean/SKEFTHawking/SpinBordism.lean) `SpinBordismData`) is **not** required by the
   chain and is an optional further target.
2. **`Ω₅^{Spin×ℤ₄} ≅ ℤ₁₆`** (`Z16AnomalyComputation.dai_freed_spin_z4`, an honest placeholder): the 5D
   Dai-Freed anomaly classification. Out of scope here (see §"Out of scope").
3. **`24 ∣ c₋`** via the Niemeier / Schellekens c=24 holomorphic-VOA classification. Out of scope here.

Note the `3 ∣ N_f` **headline** (`GenerationConstraint.generation_mod3_constraint`) consumes only `24 ∣ 8N_f`
— the Dedekind-η modular-framing leg, conditional on Wang's Cardy–Casimir hypothesis (a physics premise, not
a topological one). This roadmap therefore strengthens the **16-convergence / chirality-wall** rigor of the
D2 deep paper, not the headline itself.

## Central algebraic identity (the spine of the whole route)

For an even unimodular lattice `(L, b)`, define the mod-2 quadratic refinement
`q̄ : L/2L → 𝔽₂`, `q̄(x) = b(x,x)/2 mod 2` (well-defined since `b` is even; the reduced bilinear form
`b̄(x,y) = b(x,y) mod 2` is alternating and nondegenerate by unimodularity). Then

> **σ(L) ≡ 8 · Arf(q̄) (mod 16)**     (van der Blij 1959 / Brown 1972 / Freedman–Kirby).

This single identity organizes the route:
- **`8 ∣ σ` (Wave B1) is an immediate corollary**: `8·Arf(q̄) ∈ {0, 8}`, so `σ ≡ 0 or 8 (mod 16)`, hence
  `8 ∣ σ`. (No separate van der Blij-mod-8 argument needed.)
- **`σ/8 mod 2 = Arf(q̄)`**, so the topological factor `2 ∣ σ/8` (Wave B3) is exactly **`Arf(q̄) = 0`** — which
  for an intersection form of a *smooth closed spin 4-manifold* is the Freedman–Kirby vanishing (equivalently
  Â even). That is the irreducible topological input, entered as a narrow tracked hypothesis.
- **`16 ∣ σ` (Wave B4)** = the identity + `Arf(q̄) = 0`.

Two proof routes for the identity itself: (a) additivity of `σ` and `Arf` over orthogonal sums + values on
the generators `E₈` (σ=8, Arf=1), `−E₈` (σ=−8, Arf=1), `H` (σ=0, Arf=0) + the classification of even
unimodular lattices as `E₈ᵃ ⊕ (−E₈)ᵇ ⊕ Hᶜ` (needs Hasse–Minkowski — heavy); or (b) the **direct Brown/van
der Blij Gauss sum** `∑_{x} i^{q(x)} = √|·| · e^{2πi σ/8}` (no classification — the unconditional route). The
Wave B2 Arf + Gauss-sum machinery targets route (b).

## Why the quadratic-form route

The homotopy-theoretic derivation of `Ω^Spin_4` (mod-2 cohomology of `ko` → change-of-rings → Adams
spectral-sequence collapse → Anderson–Brown–Peterson splitting) requires the stable homotopy category, the
Steenrod algebra, the Adams spectral sequence, and the Thom spectrum `MSpin` — none of which exist in
Mathlib, and all of which are infinite, non-decidable constructions. The classical proof of `16 ∣ σ` instead
goes through quadratic forms of 4-manifold intersection lattices and the Arf/Brown invariant of a
characteristic surface (Freedman–Kirby, Guillou–Marin). That route reuses Mathlib's `QuadraticForm` library
and the repo's existing lattice substrate, and its pieces are finite/linear-algebraic except for the
4-manifold geometry layer.

## Current state (the starting line)

**Proven, kernel-pure, in repo:**
- [AlgebraicRokhlin.lean](../../lean/SKEFTHawking/AlgebraicRokhlin.lean) `serre_even_unimodular_mod8` proves
  `8 ∣ σ` for even unimodular forms, conditional on the `CharacteristicSquareModEight` hypothesis (a
  `def : Prop` encoding the van der Blij / Milgram identity `c² ≡ σ mod 8`).
- `rokhlin_from_serre_plus_topology : 8 ∣ σ ∧ 2 ∣ (σ/8) → 16 ∣ σ` — so reaching `16 ∣ σ` reduces to the
  algebraic `8 ∣ σ` plus the single **extra factor of 2**, `2 ∣ σ/8`.
- [E8Lattice.lean](../../lean/SKEFTHawking/E8Lattice.lean) proves E8 is even unimodular with `σ = 8`
  (`e8_det_one`, `e8_diagonal_even`, minors); `e8_sigma_not_div_16` + `rokhlin_gap` record that the algebraic
  floor is 8, not 16 (Freedman's E8-manifold counterexample) — i.e. the `2 ∣ σ/8` step is genuinely
  topological, not algebraic.

**Available in Mathlib:**
- `LinearAlgebra/QuadraticForm/*` — general quadratic forms, isometries, tensor products; `Signature.lean`
  gives Sylvester's law of inertia (`sigPos`/`sigNeg`).
- `NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean` — Gauss sums of quadratic *characters of finite
  fields* (`∑ χ(x)ζ^x`). NB this is a different object from the lattice/quadratic-form Gauss sum
  `∑_{x ∈ L/2L} i^{q(x)}` the Milgram formula uses; the latter is built here on the char-2 refinement layer
  (Wave B2), not reused from this file.

**Not in Mathlib (must be built):** the Arf/Brown invariant and char-2 quadratic-refinement theory; the
Milgram/van der Blij signature-mod-8 formula; even-unimodular-lattice infrastructure; characteristic surfaces
and intersection forms of smooth closed 4-manifolds; smooth-manifold structure beyond the "beginnings of
unoriented bordism" in `Geometry/Manifold/Bordism.lean`.

---

## Waves

### Wave B1 — Unconditional algebraic `8 ∣ σ` for even unimodular forms

Discharge the `CharacteristicSquareModEight` hypothesis for the even case, where the clean statement is the
classical *signature of an even unimodular lattice is `≡ 0 mod 8`* (van der Blij). `serre_even_unimodular_mod8`
uses only the `c = 0` instance of the hypothesis, so the genuine target is: define the lattice signature of
`M` from Mathlib's `QuadraticForm/Signature` (`sigPos − sigNeg` over ℝ) and prove `IsEvenUnimodular M →
8 ∣ latticeSig M` unconditionally. **The signature definition itself is now DONE — see Wave B5** (`latticeSig`,
kernel-pure, built directly on Mathlib's freshly-landed `QuadraticForm/Signature`). What remains is the
divisibility, and that is the genuine wall.

**STRATEGIC CORRECTION (direct Mathlib + first-principles scout, 2026-06-03).** The earlier plan — "route B1
through the finite L/2L Gauss sum of Wave B2" — is WRONG, and this is the load-bearing reframe of the leg:
- The real-valued L/2L Gauss sum `∑_{x∈L/2L} (-1)^{q̄(x)}` that Wave B2 builds (`gaussSum_genus_g`) detects
  **only `Arf(q̄) = σ/8 mod 2`** — i.e. the *second* factor of two, the 8→16 layer. For an even lattice
  `q̄(x) = (x·x)/2 mod 2` and `i^{x·x} = (-1)^{(x·x)/2}` is real, carrying no `mod 8` phase.
- van der Blij's `σ mod 8` lives in the **discriminant Gauss sum over `L*/L`** (quarter-integer values),
  whose Milgram reciprocity `∑ e^{2πi q(x)} = √|L*/L| · e^{2πiσ/8}` is the deep step. For a *unimodular*
  lattice `L*/L` is trivial, the sum is `1`, and Milgram instantly gives `8 ∣ σ` — but the THEOREM (Milgram
  reciprocity) is exactly the content, and it is **not** the finite 𝔽₂ identity B2 supplies.
- Mathlib (scouted 2026-06-03) has **no** Witt group, **no** p-adic quadratic-form theory / Hasse–Minkowski,
  **no** lattice Gauss-sum reciprocity, **no** discriminant-form infrastructure. So both classical routes to
  `8 ∣ σ` — (a) Hasse–Minkowski classification of indefinite unimodular forms, (b) Milgram reciprocity — are
  genuine **frontier formalizations with no Mathlib toe-hold**, not mechanical builds.
- The *characteristic-vector* partial result is provable (existence of `c`; `c² ≡ c'² mod 8` for any two
  characteristic vectors — elementary, `c'=c+2x ⟹ Δ = 4(b(c,x)+b(x,x))` with the bracket even). But the final
  `c² ≡ σ mod 8` is again exactly van der Blij and again needs the arithmetic classification. No elementary
  shortcut exists.

Output target unchanged (`IsEvenUnimodular M → 8 ∣ latticeSig M`); the route is now understood to be a
research-grade arithmetic build, NOT a corollary of B2. **This is the one decision point flagged to the user**
(axiom sign-off vs. honest tracked hypothesis vs. commit to the frontier formalization — see the
"Decision required" box below).

**Risk: HIGH (frontier).** No Mathlib shortcut for either Milgram or Hasse–Minkowski; the finite Arf Gauss-sum
of B2 is for the 8→16 layer (B4), not this one.

### Wave B2 — Arf / Brown invariant of a char-2 quadratic refinement

Build the char-2 quadratic-form / quadratic-refinement layer and the Arf (Brown) invariant. Finite,
linear-algebraic, upstreamable; greenfield (no Mathlib reuse beyond `ZMod 2` basics). This is the algebraic
half of the `2 ∣ σ/8` step (the 8→16 layer, consumed by Wave B4). **Correction (2026-06-03): its finite
𝔽₂ Gauss-sum machinery is NOT the linchpin Wave B1 (van der Blij `mod 8`) consumes** — see the strategic
correction under Wave B1. B2 is foundational *for B4*, not for B1.

**Risk: medium.** Bounded and decidable in flavour, but a from-scratch theory.

**Progress (2026-06-03, `lean/SKEFTHawking/ArfInvariant.lean`, all kernel-pure):**
- *Genus-1 (F₂-plane):* `B`/`IsRefinement`/`arf`/`zeroCount`, `refinement_on_sum`, the **democratic
  characterisation** `arf_democratic` (three zeros iff `Arf=0`, one iff `Arf=1`), `arf_surjective`, and the
  genus-1 **Arf Gauss sum** `gaussSum_arf : ∑_x (-1)^{q x} = 2·(-1)^{Arf q}`.
- *Gauss-sum multiplicativity engine* (the genus-`g` lifter): `signZ` ±1-character with `signZ_add`,
  `signZ_zero`, `signZ_sum` (character extends to finite sums); generic `gaussSum` over a fintype;
  `gaussSum_orthogonal` (pairwise multiplicativity over `ι × κ`); `gaussSum_pi` (multi-factor:
  `gaussSum (x ↦ ∑ᵢ qᵢ(xᵢ)) = ∏ᵢ gaussSum qᵢ`). With the genus-1 value this gives `2^g·(-1)^{∑Arf}` for a
  block-diagonal genus-`g` form.
- *Genus-`g` (landed):* `sum_univ_V` (F₂-plane enumeration via `finTwoArrowEquiv`, no function-space decide),
  `gaussSum_eq_gaussSumZ`, `gaussSum_arf'` (unified `gaussSum q = 2·(-1)^{Arf}`), and the headline
  `gaussSum_genus_g : gaussSum (x ↦ ∑ᵢ qᵢ xᵢ) = 2^g·(-1)^{∑ᵢ Arf qᵢ}` — the **finite Milgram identity at the
  𝔽₂/Arf level**.
**Lattice→form bridge (started, `lean/SKEFTHawking/EvenLatticeForm.lean`, kernel-pure):** `redBilin` (mod-2
reduced bilinear form `b̄(x,y)=∑(Mᵢⱼ mod 2)xᵢyⱼ`), `entry_symm`, `redBilin_symm`, `sq_self` (`a²=a` in ZMod 2),
`even_diag_cast_zero`, and `redBilin_self_eq_zero` (**`b̄` alternating** for symmetric even `M`, via
`Finset.sum_ninvolution Prod.swap` + char-2 cancellation) — i.e. `b̄` is a symplectic form on `L/2L`.
**Lattice→form bridge structure (COMPLETE, kernel-pure):** `hdSum`/`upperSum`/`redQuad`
(`q̄(x)=∑ᵢ(Mᵢᵢ/2)xᵢ + ∑_{i<j}Mᵢⱼxᵢxⱼ`), `bUpper` (polar), `hdSum_add`, `upperSum_add`, `redQuad_add`,
`redQuad_zero`, the bridge `bUpper_eq_redBilin` (i<j↔full reindex via `sum_comm` + symm + zero-diagonal), and
the capstone **`redQuad_refines_redBilin`** (`q̄(x+y)=q̄ x+q̄ y+b̄(x,y)`, `b̄=redBilin`). So `q̄` is a genuine
quadratic refinement of the alternating symplectic form `b̄ = b mod 2` on `L/2L`.
Next: nondegeneracy of `b̄` from unimodularity (`det M̄ = det M mod 2 = 1`); the symplectic-basis / Arf
well-definedness (the hard classical Arf theory — connects `redQuad` to `gaussSum_genus_g`); then the Brown
`ZMod 4` ℂ Gauss sum `∑ i^{q(x)}=√|·|·e^{2πiσ/8}` (`σ mod 8` codomain) → B1's unconditional `8 ∣ σ` +
`σ/8 mod 2 = Arf(q̄)`.

### Wave B3 — Characteristic surfaces / intersection forms of smooth closed 4-manifolds

The Guillou–Marin / Freedman–Kirby bridge from a smooth spin 4-manifold to the Arf-invariant input. This is
the genuinely hard topological layer (smooth 4-manifold structure, characteristic surfaces, the intersection
form). **Recommended approach: interface-first.** Rather than build full smooth-4-manifold infrastructure up
front, define a *narrow, explicit interface* capturing exactly the manifold→quadratic-form data the
Guillou–Marin formula needs, and discharge `2 ∣ σ/8` relative to it. This replaces the current opaque
`SpinBordismData` hypothesis with a far narrower, more transparent one, and lets B4 proceed before (or
without) a complete manifold library. Build out the interface's internals incrementally as Mathlib's manifold
support matures.

**Risk: high.** The real lift; the interface-first tactic is the de-risking lever.

**Interface SHIPPED (`lean/SKEFTHawking/SpinRokhlinInterface.lean`, kernel-pure):** `SmoothSpinManifold4`
carries `form` + `even_unimod : IsEvenUnimodular form` (Wu, topological) + `sig` + `charSq :
CharacteristicSquareModEight form sig` (van der Blij, the **Wave-B1 algebraic input**, tracked here pending
discharge) + `topo : 2 ∣ sig/8` (Â-even / Arf=0, the **irreducible topological input**). A far narrower,
transparent interface than the opaque `SpinBordismData`. Dependency graph + anti-circularity documented in the
module header.

### Wave B4 — Assemble `16 ∣ σ`  [SHIPPED]

`SmoothSpinManifold4.eight_dvd` (= `serre_even_unimodular_mod8` on the interface) + `topo`, composed by
`AlgebraicRokhlin.rokhlin_from_serre_plus_topology`, give the kernel-pure theorem
**`SmoothSpinManifold4.rokhlin : 16 ∣ M.sig`** (no global Rokhlin hypothesis, no new axiom). The wired
`sixteen_convergence_unconditional` is the unconditional companion to `RokhlinBridge.sixteen_convergence_full`
— its `16 ∣ σ` conjunct is now a *theorem*, not an assumed input.

**Anti-circularity:** the derivation routes even-unimodular + van-der-Blij ⟹ `8∣σ`, plus `2∣σ/8` ⟹ `16∣σ`;
it does NOT use ABP or Rokhlin's theorem as input (Rokhlin's theorem *is* the conclusion). ✓

**Remaining to FULL unconditional:** discharge `charSq` (van der Blij) algebraically from `even_unimod` via the
Wave-B1 Arf/Gauss-sum/Brown machinery (then it drops as a field), and update D2/L2 + HYPOTHESIS_REGISTRY. The
`topo` field is irreducibly topological and remains the single narrow tracked hypothesis (= `Arf(q̄)=0`).

### Wave B5 — The genuine lattice signature `latticeSig`  [SHIPPED 2026-06-03]

`lean/SKEFTHawking/LatticeSignature.lean` (kernel-pure, root-imported, file-gate + axiom-check green):
closes the long-standing gap that the whole leg carried the signature only as a *free* parameter
(`AlgebraicRokhlin`'s `sigma`, `SpinRokhlinInterface`'s `sig`), never the actual signature of the form.
- `latticeSig M := sigPos − sigNeg` of `(M.map Int.cast).toQuadraticMap'` over ℝ, on Mathlib's freshly-landed
  `QuadraticForm/Signature` (`sigPos`/`sigNeg`, Sylvester's law of inertia). This obsoletes the April DR's
  "~500–1000 lines to define signature" — Mathlib now supplies it.
- Genuine structural laws, all kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only): `latticeSig_neg`
  (orientation reversal `σ(−M) = −σ(M)`), `latticeSig_le`/`latticeSig_ge`/`abs_latticeSig_le` (`|σ(M)| ≤ n`).
- This is the `latticeSig` that Wave B1's divisibility target is now phrased against, and the real signature to
  bind `SmoothSpinManifold4.sig := latticeSig form` to once the B1 landing is chosen.

### Disposition of the van der Blij `8 ∣ σ` gap (per standing mandate — pursue route C)

Full diligence is complete (DR read directly; Mathlib scouted 2026-06-03; B2 machinery confirmed to be the
8→16 layer not the mod-8 layer; signature now defined via B5). The remaining `IsEvenUnimodular M → 8 ∣
latticeSig M` is a frontier formalization (Milgram reciprocity or Hasse–Minkowski; no Mathlib toe-hold for the
mod-8 layer). Three landings exist:
- **(A) One documented classical axiom** `vanDerBlij : IsEvenUnimodular M → 8 ∣ latticeSig M`. Discharges
  `charSq`; `16 ∣ σ` becomes "wired unconditional modulo one flagged 1959 classical theorem" (parallels `topo`).
  **Policy-locked behind explicit user sign-off (invariant 15); also the expedient shortcut the project's
  axiom-elimination posture disfavors.** Reserved as a fallback ONLY if (C) is proven genuinely infeasible after
  real first-principles attempts.
- **(B) Keep van der Blij as a tracked Prop hypothesis** (status quo, sharpened by B5): zero axioms, honest, but
  conditional — not "full done."
- **(C) [CHOSEN BY USER 2026-06-03] Build the zero-axiom arithmetic proof from first principles.** Per the
  standing mandate (correctness over expedience; "approach from first principles before assuming infeasible";
  ignore DR LOEs; 30k LOC in scope; continuous execution). The only route to true full-DONE (zero-axiom
  unconditional `16 ∣ σ`). The leg pursues (C); increments ship continuously across compacts; (A) is invoked
  ONLY if a *specific* sub-lemma is demonstrated to need an unformalizable input, surfaced for sign-off — never
  preemptively.

**ROUTE CHOICE WITHIN (C): the analytic / theta route (most Mathlib toe-holds).** The two candidate spines:
- *Analytic bridge (CHOSEN spine):* σ enters via the **Fresnel/Gaussian-integral phase** `∫_{ℝⁿ} e^{iπτ·xᵀAx}
  = |det A|^{-1/2}(τ/i)^{-n/2} e^{iπσ/4}` → Poisson summation → theta transformation → even-unimodular forces
  `e^{2πiσ/8}=1`. Toe-holds: `integral_cexp_neg_sum_mul_add` (n-dim Gaussian), `Real.tsum_eq_tsum_fourier`
  (Poisson, 1-dim), `jacobiTheta_S_smul` (1-dim theta S-transform), real spectral theorem, `ZLattice/Summable`.
- *Arithmetic (rejected as spine):* Hasse–Minkowski classification — ZERO Mathlib toe-hold; only as last resort.
- **The genuine obstruction is the INDEFINITE case** (all smooth spin 4-manifold forms are indefinite by
  Donaldson): the lattice theta diverges, needing the **Siegel–Narain majorant**. Reduction "indefinite ⟹
  splits off H" (Meyer) itself needs Hasse–Minkowski. So the build sequences: **definite case first** (converges;
  yields a real theorem + builds the n-dim-Poisson/Fresnel-phase substrate the indefinite case reuses), then the
  Siegel–Narain construction for indefinite.

**Build sub-waves (frontier (C)):**
- **C1 — Fresnel phase lemma:** ~~`∫_{ℝⁿ} e^{iπt·xᵀAx}` phase~~ **SUPERSEDED / NOT NEEDED (2026-06-03).** Two
  scout findings collapsed C1: (i) Mathlib has NO Fresnel/oscillatory boundary integral (all `integral_cexp*`
  need `0 < b.re`), but (ii) we don't need it — mirror Mathlib's `jacobiTheta` proof at `Im τ > 0` (convergent
  Gaussians) + Poisson + analytic continuation, which never touches the pure-imaginary boundary. The σ-phase
  instead emerges from the S-transformation multiplier `(−iτ)^{n/2}` (definite: σ = rank). C1 dropped.
- **C2 — n-dim Poisson summation** over `ℤⁿ`. **Engine FOUND (2026-06-03):** `Analysis/Fourier/AddCircleMulti.lean`
  supplies the multivariate torus Fourier series + `hasSum_mFourier_series_of_summable`. Still needs a real
  "unfold torus-integral ↔ ℝⁿ-integral" bridge (the d-dim analog of `Integrable.hasSum_intervalIntegral_comp_add_int`)
  — a genuine multi-hundred-line brick, but now "build on engine" not "from scratch."
  **PROGRESS 2026-06-04 (`MultivarPoisson.lean`, kernel-pure, ExtractDeps green 9097):** ⚠️ NAME FIX — the engine
  namespace is `UnitAddTorus` (file is `AddCircleMulti.lean`); the theorem is
  `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`. Shipped: `hasSum_mFourierCoeff_at_zero` (Fourier-series
  origin collapse `∑ₙ mFourierCoeff f n = f 0` = Poisson RHS) + **`integral_eq_tsum_zspan`** (THE unfold bridge:
  `∫_ℝᵈ f = ∑'_{g:Λ} ∫_{[0,1)ᵈ} f(↑g+x)` for integrable f, via `IsAddFundamentalDomain.integral_eq_tsum` +
  `ZSpan.isAddFundamentalDomain` + `setIntegral_image_emb`; a `VAdd` TC diamond on the submodule action was
  resolved by passing `MeasurableConstVAdd`/`VAddInvariantMeasure` positionally). The full assembly recipe (4
  steps, every step a named Mathlib lemma) is in the module docstring; step 3 (this unfold) ✅ shipped. Remaining:
  steps 1+2 (periodisation `F♯` torus-descent + `mFourierCoeff F♯ n = ∫_{∏(0,1]} mFourier(-n)·F♯` via
  `mFourierCoeff_eq_integral` + Tonelli swap, Schwartz summability) + step 4 (`∫_ℝᵈ mFourier(-n)·F = 𝓕F n`,
  matching Mathlib's `Real.fourierIntegral` 2π convention — note `EuclideanSpace` vs `Fin d→ℝ` inner-product
  type bridge).
  **PROGRESS 2026-06-04 (steps 3+4 RHS reassembly shipped, kernel-pure):** dodged the `EuclideanSpace` bridge by
  defining the lattice Fourier integral `latFourier F n := ∫ exp(2πi·∑(-nᵢ)xᵢ)·F` directly on `Fin d→ℝ`;
  `latFourier_eq_tsum` (`= ∑'_{g:Λ} ∫_{[0,1)ᵈ} exp(2πi·∑(-nᵢ)xᵢ)·F(↑g+x)`) via `integral_eq_tsum_zspan` +
  `latChar_periodic` (exp-form char lattice-periodicity, `Complex.exp_int_mul_two_pi_mul_I`). REMAINING = LHS
  steps 1+2: torus descent `F♯` + `mFourierCoeff F♯ n = latFourier F n` (Tonelli), then `+
  hasSum_mFourierCoeff_at_zero` ⟹ Poisson `∑_γ F γ = ∑_n latFourier F n`.
  **LHS PROGRESS 2026-06-04 (kernel-pure):** `periodisation` + `periodisation_lattice_periodic` (ℤᵈ-periodicity
  via tsum reindex) + `periodisationCM`/`periodisationCM_apply` (the CONTINUOUS periodisation as a bundled
  `C(Fin d→ℝ,ℂ)` via `ContinuousMap.tsum` + `summable_of_locally_summable_norm`; the global-uniform
  `continuous_tsum` does NOT apply — locally-uniform/compact-open convergence does). **TONELLI CRUX SHIPPED
  (`cube_integral_char_periodisation`): `∫_{[0,1)ᵈ} char·(periodisation F) = latFourier F n` via `integral_tsum`
  + `tsum_mul_left` + `latFourier_eq_tsum` — the HARD analytic heart, torus-free.** **TORUS DESCENT SHIPPED
  (`MultivarPoissonDescent.lean`, kernel-pure): `torusDescent`/`torusDescent_apply`/`torusDescent_comp` —
  `F♯:C(UnitAddTorus (Fin d),ℂ)` via the concrete `Ioc`-section through the open quotient covering map; 3
  defeq-wall fixes (separate module → opaque `periodisationCM`; atomic continuity hyp; decl order).**
  **✅✅ C2 COMPLETE (2026-06-04, kernel-pure):** final assembly landed —
  **`mFourierCoeff_torusDescent`** (`mFourierCoeff F♯ n = latFourier F n`, via `mFourierCoeff_eq_integral` +
  the `Ioc`↔`Ico` cube reconciliation [`Measure.ae_eq_set_pi` lifting 1-D `Ico_ae_eq_Ioc` + `volume_pi` +
  `setIntegral_congr_set`] + `mFourier_q_eq_char` + `torusDescent_comp` + `cube_integral_char_periodisation`)
  and **`multivar_poisson`** (`∑_{γ∈ℤᵈ} F(↑γ) = ∑_{n∈ℤᵈ} latFourier F n`, via `hasSum_mFourierCoeff_at_zero` +
  `torusDescent_at_zero`). Both `[propext, Classical.choice, Quot.sound]`. **The multivariate Poisson
  summation formula is now a kernel-pure theorem** under the standard (Schwartz-dischargeable) summability
  side conditions. Next: C3 S-transformation (apply Poisson to the Gaussian) via [Θ2] anisotropic Gaussian FT.
- **C3 — n-dim lattice theta** `Θ_A(τ)=∑_{v∈ℤⁿ} e^{iπτ vᵀAv}` + convergence (definite) + S-transformation (via C2).
  *Convergence engine SHIPPED 2026-06-03 (`LatticeTheta.lean`, kernel-pure, default heartbeats, root-imported,
  project-gate green = 9069 jobs):* `summable_normprod_pi` (coordinatewise-product norm-summability over `ℤᵈ`
  by `Fin.consEquiv` induction + `Summable.mul_of_nonneg`) + `summable_prod_pi` (ℂ-valued form via
  `norm_prod`). This is the dominating-series summability every theta-convergence argument routes through:
  PD form `vᵀGv ≥ λ‖v‖²` ⟹ dominate by the diagonal Gaussian `∏ᵢ e^{−cλvᵢ²}`, whose summability is exactly
  `summable_prod_pi` (with `g i n = cexp(π·I·τ·n²)`, per-coord summable from `summable_jacobiTheta₂_term_iff`).
  *PD coercivity SHIPPED 2026-06-03* (`posDef_coercive`, kernel-pure): `∃ λ>0, ∀x, λ·∑xᵢ² ≤ xᵀGx` via
  compactness. *Convergence theorem SHIPPED 2026-06-03* (`summable_gram_gaussian`, kernel-pure, default
  heartbeats): **the general Gram-matrix lattice theta sum `∑_{v∈ℤᵈ} exp(iπτ·vᵀGv)` is summable for any PD `G`
  and `Im τ>0`** — the summand norm `exp(-π·Im τ·vᵀGv)` dominated by the diagonal Gaussian
  `∏ᵢexp(-π·λ·Im τ·vᵢ²)` via coercivity + `Summable.of_norm_bounded`. C3 CONVERGENCE LAYER (definite) COMPLETE.
  *T-TRANSFORM LAYER SHIPPED 2026-06-03* (kernel-pure): `latticeTheta` (def `Θ_G(τ)=∑'v, exp(iπτ·vᵀGv)`);
  `latticeTheta_T` (`Θ(τ+1)=Θ(τ)` under even condition — purely termwise); `even_lattice_heven` (even condition
  holds for any even symmetric integer matrix via `EvenLattice.redBilin_self_eq_zero` — no dangling hypothesis);
  `latticeTheta_T_int` (grounded T-transform for even symmetric integer lattices). LatticeTheta.lean = 10 decls.
  *Next:* the S-transformation (hard half) via C2 Poisson summation.
  **KEY ARCHITECTURAL FINDING:** the *isotropic* reformulation (even unimodular = self-dual lattice in
  Euclidean V with `‖·‖²∈2ℤ`) lets Mathlib's existing isotropic Gaussian integral + Fourier transform carry
  the anisotropy in the lattice — but the ℤᵈ-with-Gram-matrix formulation (above) is more tractable given the
  AddCircleMulti engine works over the standard ℤᵈ. **The definite case is buildable; the INDEFINITE case (=
  all smooth-spin-4-mfld forms, by Donaldson) still needs Siegel–Narain (C5) — but the definite substrate
  (C2/C3/C4) is exactly what Siegel–Narain extends, so it is necessary, not wasted, progress.**
- **C4 — definite even unimodular ⟹ `8 ∣ rank = σ`** (theta is level-1 modular ⟹ weight `n/2` even + S-multiplier).
  *Stepping stone SHIPPED 2026-06-03 (`LatticeSignature.lean`, kernel-pure):* `latticeSig_of_posDef`
  (`σ = rank`) / `latticeSig_of_negDef` (`σ = -rank`), with reusable general helpers `sigPos_eq_finrank_of_posDef`
  + `sigNeg_eq_zero_of_posDef`. So once C3 gives `8 ∣ rank` for definite even-unimodular, `8 ∣ σ` is immediate.
- **C5 — Siegel–Narain majorant** ⟹ indefinite case ⟹ general `IsEvenUnimodular M → 8 ∣ latticeSig M`.
- **C6 — discharge `charSq`, bind `sig := latticeSig form`, rewire `sixteen_convergence_full`, D2/L2 + registry.**

**Route-C sub-routes (to attack from first principles, easiest provable pieces first):**
1. *Characteristic-vector steps 1–2* (ELEMENTARY, no wall): char vectors exist for unimodular forms; any two
   satisfy `c² ≡ c'² mod 8` (`c'=c+2x ⟹ Δ = 4(b(c,x)+b(x,x))`, bracket even by the characteristic condition).
   Real, kernel-pure progress; ship first.
2. *Step 3* `c² ≡ σ mod 8` — the wall. Candidate first-principles attacks: (i) **analytic/Fresnel**: real
   Gaussian integral `∫ e^{πi xᵀAx} = |det A|^{-1/2} e^{πiσ/4}` + Poisson summation over the lattice (Mathlib
   has Gaussian integrals + a Poisson-summation formula — scout for toe-holds); (ii) **Brown ℂ Gauss sum** lift
   of `redQuad` to `ZMod 4` + finite reciprocity; (iii) **classification** route (heaviest). Scout each before
   committing.

### Recommended sequence (revised 2026-06-03)

**B5 is done.** The next move depends entirely on the Decision box above (A/B/C for van der Blij). Independently
of that choice, **B2** (the char-2 Arf/Gauss-sum layer) remains the linchpin for **B4**'s 8→16 layer and is
already largely shipped; **B3 interface-first** + **B4** assembly are shipped. The leg is complete *modulo the
single van der Blij input*, whose disposition is the user's call.

---

## Out of scope (separate tracks)

- **5D `Ω₅^{Spin×ℤ₄} ≅ ℤ₁₆`** (`dai_freed_spin_z4`) — the load-bearing *anomaly* placeholder. Reaching it
  needs either the Adams-spectral-sequence machinery for ℤ₄-twisted spin bordism or APS / η-invariant index
  theory; neither is in Mathlib, and the repo's `APSEta/*` content is η = 0 placeholder. The 4D `16 ∣ σ`
  target here does not discharge it. A separate roadmap if the D2 anomaly story's full rigor is pursued.
- **24-leg via Niemeier / Schellekens** — classification of 24-dimensional even unimodular lattices and c=24
  holomorphic VOAs; the repo's `Schellekens/*` is a predicate-level scaffold. A separate, larger ambition.

---

*Phase 5q.B roadmap. Created 2026-06-03. Companion to
[Phase5qT_ExtSubstantiation_Roadmap.md](Phase5qT_ExtSubstantiation_Roadmap.md). Follows
[Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
