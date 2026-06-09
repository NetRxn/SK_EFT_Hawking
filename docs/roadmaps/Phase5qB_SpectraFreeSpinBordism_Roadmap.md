# Phase 5q.B: Spin-Bordism Formalization — an unconditional `16 ∣ σ` via quadratic-form methods

## Technical Roadmap — June 2026

*Goal: make the spin-bordism / Rokhlin leg of the generation-constraint program unconditional by
classical quadratic-form, lattice, and 4-manifold methods — the route that reuses the repo's existing
`E8Lattice` / `AlgebraicRokhlin` substrate and Mathlib's `QuadraticForm` library, rather than building the
stable-homotopy / Steenrod / Adams-spectral-sequence stack. PUBLIC repo. No new axioms; correctness over
expedience.*

---

## ✅ STATUS: GOAL MET — `16 ∣ σ` is UNCONDITIONAL, kernel-pure, and wired (2026-06-08)

**The leg is COMPLETE. `16 ∣ σ(M)` for closed smooth spin 4-manifolds is now a kernel-pure theorem
(`{propext, Classical.choice, Quot.sound}` only) with NO project-local axiom and NO Rokhlin hypothesis.**
Everything below the "## Waves" header is the historical build narrative, retained for provenance; the
sections marked **[STALE — see this banner]** describe an intermediate state where `[HM]` was still open.
What actually shipped:

- **`[HM]` (Hasse–Minkowski: indefinite even unimodular ⟹ isotropic vector) is DISCHARGED unconditionally**,
  via the chosen *classification* spine (NOT the abandoned theta/Siegel–Narain route, NOT a tracked Prop).
  `RokhlinFromHM.HasWeakIsotropicVectorHyp` is now a **theorem** (`RokhlinHMRankFour.hasWeakIsotropicVector`),
  proven at every rank: rank 1/3 vacuous (odd rank can't be even unimodular), rank 2 explicit isotropic
  vector, **rank 4 via binary Hilbert-symbol reciprocity** (the project's documented "lone sub-frontier" —
  the feared 4-dim Hasse-invariant theory collapsed to `quaternary_sqdisc_iso_iff_ternary` +
  `hilbertGlobalProd_eq_one`), rank ≥ 5 by the earlier `weakIsotropic_of_five_le` reduction.
- **`8 ∣ σ` (van der Blij) is DISCHARGED** = `[HM]` (classification existence) + the already-complete
  signature calculus on the normal form `E₈^a ⊕ (−E₈)^b ⊕ H^c` (`RokhlinClassification`) +
  theta-modularity `[Θ]` for the definite case. `RokhlinHMRankFour.eight_dvd_latticeSig` is unconditional.
- **`16 ∣ σ` assembled** = `eight_dvd_latticeSig` + the irreducible topological factor `2 ∣ σ/8`
  (`RokhlinHMRankFour.sixteen_dvd_latticeSig`).
- **WIRED into the interface:** `SpinRokhlinInterface.SmoothSpinManifold4` **dropped the `eight_dvd` field**
  (now derived); `SmoothSpinManifold4.rokhlin : 16 ∣ M.sig` and `sixteen_convergence_unconditional` consume
  only the genuine `even_unimod` (Wu) + `topo` (Â-even, `2 ∣ σ/8`). The **single remaining tracked
  hypothesis is `topo`** — irreducibly topological (Atiyah–Singer / Freedman–Kirby), NOT algebraic.
- **Registry + papers synced:** `HYPOTHESIS_REGISTRY['rokhlin_sigma_mod_16'].status = 'discharged'`
  (`constants.py`); D2 / L2 / paper10 reframed onto the proven theorem and Stage-13 re-reviewed GREEN.
- **Anti-circularity preserved:** the derivation uses even-unimodularity (Wu) + classification +
  van-der-Blij + `2 ∣ σ/8`; it does NOT use ABP or Rokhlin's theorem as input (Rokhlin's theorem *is*
  the conclusion). Closure reviewer PASSED 5/5; `axiom_closure_allowlist` GREEN; ExtractDeps project-gate
  GREEN.

**Key files:** `RokhlinHMRankFour.lean` (rank-4 frontier + all-rank assembly + `eight/sixteen_dvd_latticeSig`),
`RokhlinHMDischarge.lean` (rank 2 + odd-rank vacuity), `HasseMinkowskiNary.lean` / `HasseMinkowskiGlobal.lean` /
`HasseMinkowskiLocal.lean` / `PadicSquare.lean` / `HilbertProductFormula.lean` (the from-scratch p-adic /
Hilbert-symbol / quaternary-HM substrate), `RokhlinFromHM.lean` / `RokhlinManifoldFromHM.lean` (compose
[HM]+[Θ]+topo), `SpinRokhlinInterface.lean` (wired manifold interface), `RokhlinClassification.lean` +
`LatticeSignature.lean` (signature calculus). Lab notebook: `Phase5qB_LabNotebook.md`.

**Out of scope (unchanged):** the 5D `Ω₅^{Spin×ℤ₄} ≅ ℤ₁₆` Dai–Freed leg and the `24 ∣ c₋` Niemeier/Schellekens
leg remain separate tracks (see "Out of scope" at the bottom). The `3 ∣ N_f` headline still consumes only the
Dedekind-η modular leg conditional on Wang's Cardy–Casimir physics premise — this leg strengthens the
16-convergence / chirality-wall rigor of D2, not the headline.

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

### Wave B4 — Assemble `16 ∣ σ`  [✅ COMPLETE & UNCONDITIONAL 2026-06-08]

> **[STATUS — read the top banner]** The `eight_dvd` field has been DROPPED from the interface; `[HM]` is
> DISCHARGED (rank-4 frontier closed via binary Hilbert reciprocity, all other ranks done);
> `SmoothSpinManifold4.rokhlin : 16 ∣ M.sig` is a kernel-pure theorem consuming only `even_unimod` + `topo`.
> The UPDATE blocks below this line are the historical build narrative from when `[HM]` was still open —
> all "sole remaining gap" / "keystone remains" / "Serre Thm 4 is the multi-session hard core" language in
> them is **superseded**; the actual route that landed was the classification + rank-4 quaternary HM, not
> the weak-approximation/Serre-Thm-4 path those blocks were scouting.


`SmoothSpinManifold4.eight_dvd` (= `serre_even_unimodular_mod8` on the interface) + `topo`, composed by
`AlgebraicRokhlin.rokhlin_from_serre_plus_topology`, give the kernel-pure theorem
**`SmoothSpinManifold4.rokhlin : 16 ∣ M.sig`** (no global Rokhlin hypothesis, no new axiom). The wired
`sixteen_convergence_unconditional` is the unconditional companion to `RokhlinBridge.sixteen_convergence_full`
— its `16 ∣ σ` conjunct is now a *theorem*, not an assumed input.

**Anti-circularity:** the derivation routes even-unimodular + van-der-Blij ⟹ `8∣σ`, plus `2∣σ/8` ⟹ `16∣σ`;
it does NOT use ABP or Rokhlin's theorem as input (Rokhlin's theorem *is* the conclusion). ✓

**Remaining to FULL unconditional:** discharge `eight_dvd` (van der Blij) algebraically from `even_unimod`,
then it drops as a field, and update D2/L2 + HYPOTHESIS_REGISTRY. The `topo` field is irreducibly topological
and remains the single narrow tracked hypothesis (= `Arf(q̄)=0`).

**UPDATE 2026-06-04 — `eight_dvd` discharge: [Θ] DONE, wiring DONE, [HM] is the sole remaining gap.**
- **[Θ] (definite `8∣σ`) DISCHARGED unconditionally** via theta-modularity: `ThetaModularWeight.eight_dvd_rank`
  (PosDef even unimodular ⟹ `8∣rank`, by the `(ST)³`-orbit `(-I)^{d/2}=1`) → `ThetaDefiniteDischarge.
  eight_dvd_latticeSig_of_definite` (`sigPos=0 ∨ sigNeg=0` ⟹ `8∣latticeSig`). Kernel-pure, no axioms.
- **Wiring DONE:** `RokhlinFromHM.{eight_dvd_latticeSig_of_HM, sixteen_dvd_latticeSig_of_HM_of_topo}` compose
  [Θ] into `eight_dvd_latticeSig_of_HM_of_Theta`, so even-unimodular `8∣σ`/`16∣σ` need ONLY [HM]+topo;
  `RokhlinManifoldFromHM.{SmoothSpinManifold4.rokhlin_of_HM, sixteen_convergence_of_HM}` derive `16∣σ(M)` from
  the manifold's GENUINE `even_unimod`+`topo`+[HM], NOT the assumed `eight_dvd` field. ⟹ **`16∣σ(M) = [HM]
  applied to (even_unimod+topo)`; once [HM] is a theorem the `eight_dvd` field + `hHM` param drop ⟹ fully
  unconditional.**
- **[HM] (indefinite even unimodular ⟹ primitive isotropic vector) = the SOLE remaining gap = Hasse–Minkowski.**
  Foundation bricks B1–B3 landed: `HilbertSymbolReal` (real place), `PadicUnitResidue`, `HilbertSymbolPadic`
  (odd-`p` symbol, bimultiplicative). Path: sign/ℚ extension → `p=2` → product formula (≡ quad recip) → local
  classification → HM rank-induction → apply (locally isotropic everywhere [B3 `_units`+[HM-p]+[HM-ℝ]] ⟹ global).
  Per decision A (grind, ≤50k LOC). Strategic note confirmed: NO Mathlib shortcut for Milgram OR Hasse–Minkowski;
  theta route is definite-only (indefinite theta diverges).

**UPDATE 2026-06-04 (cont.) — GLOBAL HM ROUTE DECISION: route A = Legendre descent, NOT Dirichlet (B).**
Two Explore toe-hold scans (Mathlib + repo) settled the global-reduction architecture:
- **Mathlib has only `Nat.exists_prime_gt_modEq_one` / `infinite_setOf_prime_modEq_one` (primes ≡ 1 mod k) —
  NOT full Dirichlet** (primes ≡ a mod n for coprime a,n). So Serre's HM ternary-via-Dirichlet route would force
  formalizing full Dirichlet (Dirichlet L-functions + non-vanishing at s=1) — a mountain atop the mountain. REJECTED.
- **Chosen: route A — Legendre's theorem via elementary infinite descent (no Dirichlet).** Serre Ch IV Thm 6
  (Legendre, the ternary case) is an elementary descent on `|a|+|b|` with squarefree coprime coefficients;
  Dirichlet only enters Serre's n≥4 reduction (Thm 8), which I will instead handle by rank-reduction off the
  ternary + n≥5 universal p-adic isotropy. Mathlib `Int.sq_of_isCoprime`, `Nat.sq_mul_squarefree`,
  `Int.squarefree_natAbs`, `legendreSym.eq_one_iff` (↔ `IsSquare (a:ZMod p)`), `ZMod.chineseRemainder`,
  `legendreSym.card_sqrts` are the descent toe-holds; the local↔QR bridge reuses the shipped Hilbert machinery.
- Also confirmed ABSENT (must stay built-from-scratch): Legendre three-square thm, Witt group, Hasse invariant,
  p-adic QF isotropy. PRESENT and reused: full QR (`legendreSym.quadratic_reciprocity`), χ₄/χ₈, `Nat.sum_four_squares`.
- **n=2 base SHIPPED (`PadicSquare.lean`, kernel-pure):** `isSquare_rat_of_isSquare_padic` (0≤q, square every ℚ_p
  ⟹ IsSquare q), `isSquare_rat_iff_local` (the rank-2 local-global iff), `exists_squarefree_sq_mul_int`/`_rat`
  (squarefree square-class representative — the diagonal-coefficient normalization).

**UPDATE 2026-06-04 (cont.) — ★ TERNARY HASSE–MINKOWSKI (Legendre's theorem) PROVEN, kernel-pure (`PadicSquare.lean`).**
`ternary_solvable_of_local` : for nonzero squarefree `a, b : ℤ`, `z² = a x² + b y²` solvable over ℝ and every
ℚ_p ⟹ solvable over ℚ. Proof by infinite descent (Serre Ch IV Thm 6, route A — NO Dirichlet, NO Hilbert
symbols, coprimality-free). Axioms `[propext, Classical.choice, Quot.sound]` only. The full ingredient stack
(all kernel-pure, ~28 commits): descent engine (`norm_form_comp_identity`, `solvable_transfer`/`_field`,
`solvable_scale`/`_field`, `solvable_descent_field`, `solvable_descent_or_isSquare_field`), size-reduction
(`descent_construct` via `Int.bmod`), normalization (`exists_squarefree_sq_mul_int`/`_rat`,
`exists_squarefree_diag_isotropic`), per-place + CRT bridges (`solvable_padic_odd_iff_residue`,
`solvable_real_canonical_iff`, `isSquare_zmod_of_forall_prime`, `isSquare_residue_of_solvable_padic`,
`exists_dvd_sq_sub_of_locally_solvable`), base case (`ratSol_of_isSquare`), helpers (`solvable_norm_value`,
`solvable_canonical_symm`, `exists_y_ne_zero_of_not_isSquare`). **Key insight:** the descent's local-solvability
invariant is *field-generic* (over each ℚ_v, "solvable ⟺ b is a norm of ℚ_v(√a)"; norms form a group containing
`t²−a`), so it preserves cleanly per place with no Hilbert-symbol bookkeeping. **REMAINING to `HasWeakIsotropicVectorHyp`:**
(i) **rank-reduction** general diagonal form (rank n) → ternary (n=3) + n=4 quaternary + n≥5 (split off a
hyperbolic/represented value), via the ℚ ternary HM; (ii) apply to the diagonalized even-unimodular Gram form
(locally isotropic everywhere: ℝ indefinite, odd-p unimodular rank≥3, p=2 even-unimod ⊃ U) ⟹ nonzero ℚ then ℤ
isotropic vector (`exists_int_isotropic_of_rat`) ⟹ `HasWeakIsotropicVectorHyp`; (iii) wire `RokhlinBridge` (drop
`h_rokhlin`), update D2/L2 + HYPOTHESIS_REGISTRY, dispatch closure reviewer.

**UPDATE 2026-06-04 (cont.) — [HM] RANK-REDUCTION STACK COMPLETE THROUGH n≤4-reduction; SOLE KEYSTONE = weak
approximation.** Beyond the ternary theorem, the following are now kernel-pure (project-gate green):
- **n=2 base** `binary_solvable_of_local` (binary form isotropic /ℚ ⟺ /ℝ and every ℚ_p; via
  `exists_binary_zero_iff` + `isSquare_rat_iff_local`, the square local–global).
- **n=3 base** `diag_ternary_solvable_of_local` (diagonal ternary `a x²+b y²+c z²=0` /ℚ ⟺ locally everywhere;
  via `isotropic_diag_ternary_iff_canonical` + `ternary_canonical_solvable_of_local_rat`, the latter extending
  the integer ternary theorem to rational canonical coefficients through `solvable_canonical_of_sq_mul`).
- **value representation** `binary_represents_of_local` (a binary form represents a value /ℚ ⟺ locally
  everywhere) + `represents_of_ternary_isotropic` + `binary_isotropic_universal`.
- **n=4 reduction (both directions)** `quaternary_isotropic_of_common_value` + `common_value_of_quaternary_isotropic`
  (rank-4 isotropy ⟺ the two binary parts share a common represented value).
- **matrix→diagonal** `exists_diag_weights_iff_matrix` (Gram form ⟺ diagonal via
  `equivalent_weightedSumSquares`); ℚ→ℤ clearing `exists_int_isotropic_of_rat` (already present).

**THE SOLE REMAINING MATHEMATICAL KEYSTONE = WEAK APPROXIMATION for ℚ (Dirichlet-free, CRT-based).** It produces
a *global* common value from local ones (find `t ∈ ℚˣ` in prescribed square classes at finitely many places —
realizable by `Nat.chineseRemainderOfList` + sign, NO Dirichlet). This finishes n=4; n≥5 follows by induction on
the complete n≤3 bases. After it: establish even-unimodular ℚ_p local isotropy (ℤ_p-diagonalization plumbing) ⟹
`HasWeakIsotropicVectorHyp` ⟹ wire `RokhlinBridge` (drop `h_rokhlin`) + D2/L2 + HYPOTHESIS_REGISTRY + closure
reviewer. (Alternative Dirichlet-free n=4 route reusing the completed `hilbertGlobalProd_eq_one`:
quaternion-algebra-split-everywhere ⟹ split via Hilbert reciprocity ⟹ norm form isotropic — needs Hasse-invariant
↔ isotropy machinery, not yet scoped.) **The crux (ternary HM) and the entire rank-reduction/value-representation/
plumbing stack are done; only the weak-approximation keystone and the even-unimodular local-isotropy plumbing
remain before wiring.**

**UPDATE 2026-06-04 (cont.) — [HM] foundation: HILBERT'S PRODUCT FORMULA COMPLETE (major gating sub-result).**
The full scalar Hilbert-symbol arithmetic layer for `[HM]`/Hasse–Minkowski is now a kernel-pure, axiom-clean
fact, built entirely from scratch (Mathlib has NONE of it):
- **All four signed local Hilbert symbols** (`HilbertSymbolReal` ∞, `HilbertSymbolPadic` odd-`p`/signed-ℤ,
  `HilbertSymbolTwo` `p=2`), each `{±1}`-valued and bimultiplicative, with the supplementary laws
  (`chi2_eps2_eq_legendre_neg_one`, `chi2_omega2_eq_legendre_two`, `chi2_eps2_mul`) tying the dyadic ε/ω
  characters to Mathlib's `legendreSym`/`χ₄`/`χ₈`.
- **`HilbertProductFormula.hilbertGlobalProd_eq_one : ∏_v (a,b)_v = 1`** for all nonzero `a,b : ℤ` — assembled
  from quadratic reciprocity (`legendreSym.quadratic_reciprocity`) + supplementary laws over all generators
  `{(1,b),(-1,±1/q),(2,q/2),(p,q),(p,p)}`, then the multiplicative reduction (nested `Nat.recOnMul` over prime
  factorizations + `Int.sign_mul_natAbs` sign extension). Kernel-pure `[propext,Classical.choice,Quot.sound]`.
- **REMAINING for [HM] = the form-level p-adic theory (the bulk; Mathlib lacks it entirely — only residue-field
  `IsSquare` + Hensel exist):** (i) connect the *combinatorial* `(a,b)_p` to actual local solvability of
  `z²=ax²+by²` over ℚ_p (p-adic square classes via Hensel on `X²-u`); (ii) Hasse invariant of forms over ℚ_p +
  Witt local classification; (iii) the Hasse–Minkowski local–global rank induction (ternary/quaternary via the
  product formula + Dirichlet, n≥5 by reduction); (iv) apply to indefinite even unimodular (locally split ⟹
  globally isotropic) ⟹ `HasWeakIsotropicVectorHyp` ⟹ drop `eight_dvd` + `hHM`. This is a multi-session
  from-scratch p-adic-quadratic-forms library; grind continues per decision A.

**UPDATE 2026-06-04 (cont.) — ★ ROUTE PIVOT: FULL DIRICHLET IS IN MATHLIB; the n=4 non-square-disc "wall" is
dissolved. Place-level + Dirichlet-selection layers SHIPPED.** The earlier "avoid Dirichlet (Route A descent)"
premise was STALE: `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` provides full Dirichlet —
`Nat.forall_exists_prime_gt_and_zmodEq`/`_modEq`, `infinite_setOf_prime_and_eq_mod` (verified usable under
`import Mathlib`, 2026-06-04). **User decision: PIVOT to the textbook Serre Ch IV §3.2 n=4 proof.** This makes
the n=4 non-square-disc case "pure assembly" (scout-confirmed) rather than the abandoned Scharlau/number-field
frontier. SHIPPED this session (all kernel-pure, build-clean, axioms `{propext,Classical.choice,Quot.sound}`):
- **Place-level representability layer** (the bad-set-is-finite facts for Serre's common-value search):
  `binary_represents_padic_of_units` (good odd p, unit value), `binary_represents_padic_even_val` (good odd p,
  even valuation), `binary_universal_padic_of_residue` (odd p, `−ab` square mod p ⟹ ⟨a,b⟩ universal — the
  Dirichlet-prime clause), `real_binary_represents_iff` (ℝ: represents t ⟺ `0≤a·t ∨ 0≤b·t`),
  `binary_represents_congr_sq` (representability is square-class invariant, field-generic, HasseMinkowskiLocal).
- **Dirichlet-prime selection** (the crux): `isSquare_odd_prime_zmod` (QR), `isSquare_natCast_zmod_of_modEq` +
  `isSquare_intCast_zmod_of_modEq` (multiplicative QR criterion via `Nat.recOnMul`), and the headline
  **`exists_prime_gt_isSquare_pair`** — ∀ N, nonzero `m,n:ℤ`, ∃ prime `q>N` with both `m,n` squares mod `q`
  (Dirichlet `q≡1 mod 8|m||n|` + the QR criterion). Take `m=−ab, n=−cd`.
- **KEYSTONE PLAN (single-prime construction, cleaner than general weak approximation):** the global common
  value is `t = ε·q` for ONE Dirichlet prime `q`: `ε∈{±1}` chosen for the real sign (`real_binary_represents_iff`);
  `q` chosen (one combined-modulus Dirichlet call) so that (a) `−ab,−cd` are squares mod `q` ⟹ both binaries
  universal at `q` (`binary_universal_padic_of_residue`, handles `q`'s odd valuation), (b) `±q` lies in the
  local square class matching the common value `c_p` at each bad odd `p∈S` and mod 8 at `p=2`. Good odd primes
  `p∉S` are automatic (`binary_represents_padic_even_val`, since `v_p(±q)=0`). The joint satisfiability of the
  bad-set residue conditions with the `−ab,−cd`-square conditions is guaranteed by the local isotropy everywhere
  (the parity is exactly `hilbertGlobalProd_eq_one`). **REMAINING = the weak-approximation/consistency step**
  (extract `c_p`; the combined Dirichlet with bad-set residue targets; product-formula consistency) → assemble
  keystone → `quaternary_solvable_of_local` (n=4) → n≥5 Meyer reduction (weak-approx + ternary, NO further
  Dirichlet; "rank≥5 over ℚ_p always isotropic" — odd-p have `exists_diag_nary_zero_odd_padic`, need p=2) →
  even-unimodular ℚ_p local isotropy (⊃U over ℤ₂ at p=2) → `HasWeakIsotropicVectorHyp` → wire `RokhlinBridge`
  (drop `h_rokhlin`/`eight_dvd`) + D2/L2 + HYPOTHESIS_REGISTRY + closure reviewer.

**UPDATE 2026-06-04 (cont.) — ★ PER-PLACE represents⟺symbol LINEAR TRIO COMPLETE + global packaging (kernel-pure).**
The full LOCAL input layer for Serre Thm 4 is now in repo:
- **`PadicSquare.lean`:** `represents_{padic_odd, 2adic, real}_iff_symbol` (the `(at,bt)=1` form at each place via
  the solvability bridges + ×t scaling); Steinberg `(a,−a)_v=1` (`hilbertPadicInt_self_neg_odd`,
  `hilbert2Int_self_neg`); diagonal `(a,a)_v=(a,−1)_v` and the bimultiplicative cross `(at,bt)_v=(a,b)_v(t,−ab)_v`
  at each place; and the headline **`represents_{padic_symbol_linear_odd, 2adic_iff_symbol_linear,
  real_iff_symbol_linear}`** — at EVERY place `v`, `⟨a,b⟩` represents `t` over ℚ_v ⟺ `(t,−ab)_v = (a,b)_v`
  (linear in `t`, the exact Serre-Thm-4 prescription shape; real factor matches `hilbertGlobalProd`'s
  `hilbertReal (·:ℝ)(·:ℝ)`).
- **NEW `HasseMinkowskiGlobal.lean`** (above `PadicSquare` + `HilbertProductFormula`; not root-imported yet):
  `represents_padic_iff_hilbertPrime_linear` (unified finite-place criterion over `hilbertPrime`) +
  **`represents_everywhere_iff_symbols`** (`⟨a,b⟩` represents integer `t` at every place ⟺ the prescription
  `(t,−ab)_v=(a,b)_v` at every place). This is the bridge between the two faces of the keystone: LHS = the
  everywhere-represented hypothesis `quaternary_isotropic_of_keystone` consumes; RHS = the prescribed-symbol
  output of Serre Thm 4. **⟹ `n=4` HM now reduces to: (i) Serre Ch III §2.2 Thm 4 (global `t∈ℚˣ` with
  prescribed symbols, given consistency = `hilbertGlobalProd_eq_one`); (ii) local realizability plumbing
  (`common_value_of_quaternary_isotropic` gives `t_v∈ℚ_v` → integer rep in same ℚ_v-square class → integer
  linear criterion). Then keystone → `quaternary_solvable_of_local` → n≥5 → p=2 even-unimod local isotropy →
  `HasWeakIsotropicVectorHyp` → wire.** Serre Thm 4 is the multi-session hard core; the entire local theory
  feeding it is now done.

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

### Disposition of the van der Blij `8 ∣ σ` gap  [✅ RESOLVED — route C delivered, zero axioms]

> **[STATUS — read the top banner]** This decision is CLOSED. Landing **(C) the zero-axiom arithmetic proof**
> was achieved — but via the **classification / rank-4 quaternary Hasse–Minkowski** route, NOT the
> analytic/theta spine the sub-waves C1–C6 below scoped. The theta route (C1–C5, Siegel–Narain) was built
> out partway (Poisson summation `multivar_poisson`, definite lattice-theta convergence) and is retained as
> reusable substrate, but the *indefinite* case — the actual obstruction — was instead closed arithmetically
> (`RokhlinHMRankFour`). Option (A) one-axiom and (B) tracked-Prop were NOT taken. `8 ∣ σ` and `16 ∣ σ` are
> unconditional. The C1–C6 sub-wave narrative below is historical.

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

### Recommended sequence  [✅ EXECUTED — leg complete 2026-06-08]

All waves shipped. Final landed dependency chain: **B5** (`latticeSig`) → **B2** (Arf/Gauss-sum, char-2 layer,
feeds the 8→16 factor) → **B1/[Θ]** (theta-modularity, definite `8∣rank`) → **[HM]** (classification existence
via rank-4 quaternary Hasse–Minkowski + binary Hilbert reciprocity — the route actually taken) → **B3**
interface-first (`SmoothSpinManifold4`) → **B4** assembly (`16 ∣ σ`, `eight_dvd` field dropped). The leg is
**complete unconditionally** — no van der Blij input remains open; the only tracked hypothesis is the
irreducibly-topological `topo` (`2 ∣ σ/8`). Registry + D2/L2/paper10 synced; closure reviewer PASSED.

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
