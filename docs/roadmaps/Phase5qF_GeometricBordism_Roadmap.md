# Phase 5q.F — Geometric Level 4: derive the ℤ₁₆ bordism invariants, discharge `SmithInflow`

**Status:** ACTIVE (opened 2026-06-14). Continuation of [Phase 5q.E](Phase5qE_SixteenConvergence_Roadmap.md) — the "16 convergence."
**Owner workstream:** public `SK_EFT_Hawking` Lean.
**Tracker = this file.** Lab notebook (gitignored working scratch): `temporary/working-docs/phase5qF/LabNotebook.md`.

---

## The directive (read first, every bootstrap/compaction — a future goal-mode agent MUST NOT re-defer this)

This phase exists because 5q.E built the four-16 convergence **conditionally** — to ℤ₁₆ level, with the
bordism identifications carried as a disclosed `SmithInflow` hypothesis and the manifold invariants
**posited** (the `signature : ℤ` field of `PinPlusManifold4`, the `daiFreed : ℤ` field of the Ω₅
substrate). Level 4 = make those invariants **derived from geometry**, so the convergence is
**unconditional**.

**The continue-vs-stop rule for this phase (locked, per user 2026-06-14):**
- The ONLY legitimate stops are (1) a *proved* mathematical no-go (decomposition-backed
  impossibility) or (2) a genuine product/strategy decision only the user can make.
- **NOT stops — build straight through them:** "absent from Mathlib," "no foothold," "needs new
  upstream infrastructure," "multi-week / multi-month," "this is a large program," "would require
  formalizing <hard theorem>." We **regularly build upstream Mathlib infra.** Absence is the *work*.
- A long roadmap is fine; stopping execution because the roadmap is long is the failure mode.
  Decompose the far horizon into waves and ship the next brick. Funded autonomous time left
  unexecuted is itself a failure (see memory `feedback-no-hypothesis-based-descope`).
- Kernel-purity is non-negotiable: `{propext, Classical.choice, Quot.sound}` only; **no new
  project-local `axiom` without explicit user sign-off**, no `sorry`, no `native_decide`, no
  `maxHeartbeats`/`synthInstance.maxHeartbeats` in proof bodies. A genuinely absent named-landmark
  theorem is carried as **ONE disclosed tracked `Prop`** (registry entry + discharge plan), exactly
  as `SmithInflow` was — never an axiom, and only after the surrounding infra is built, never as a
  shortcut to skip buildable work.

---

## The mathematics (what "Level 4" actually requires)

The convergence chain (4 facets as images of one ℤ₁₆):

```
SM 16 Weyl   ─(Spin(10) spinor)─┐
                                 ├─►  Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆  ──(Smith hom)──►  Ω₄^{Pin⁺} ≅ ℤ₁₆  ──┬─► σ mod 16 (Rokhlin)
SM anomaly  ─(Dai–Freed)────────┘    [W6–W7: derive this]   [W6 geometric]   [W1–W5: derive this]  └─► c₋ mod 16 (Kitaev)
```

5q.E built every box at the **ℤ₁₆-algebra** level (genuine `Quotient ≃+ ZMod 16`, the non-`rfl`
`rokhlin_reads_kitaev`), but the two `≅ ℤ₁₆` identifications and the Smith map's iso-content were
**posited / carried as `SmithInflow`**. Level 4 derives them.

**Chosen route — geometric/combinatorial (Guillou–Marin / Kirby–Taylor), NOT analytic (Dirac/APS).**
Why this is the clearly-best route (decision taken 2026-06-14, no user gate needed — technical-best):
1. The project's own no-go [[nogo-lattice-arf-not-sigma8]] **proved** the mod-16 is carried by the
   characteristic-**surface** Brown/Arf invariant (Guillou–Marin), not a lattice Arf and not something
   that forces the analytic η. That fixes the correct invariant.
2. The project already has genuine Gauss-sum machinery (`SKEFTHawking.ArfInvariant`, `Arf.gaussSum`)
   — the algebraic heart of the Brown/ABK invariant is seeded.
3. The analytic route (η-invariant of the Pin⁺ Dirac operator) would require building elliptic-operator
   theory + the Atiyah–Patodi–Singer index theorem — a far larger program with *no* current foothold
   (`DiracOperator` confirmed Mathlib-absent). Guillou–Marin reaches the same ℤ₁₆ by elementary
   4-manifold topology + finite quadratic forms, which Mathlib + the project substrate support.

So: build the invariant `β : (Pin⁺ 4-manifold data) → ℤ₁₆` combinatorially, prove its bordism-invariance
(handle calculus / Guillou–Marin congruence), prove it's an iso, then the Smith map, then Ω₅.

> ⚠️ **SCOPE CORRECTION 2026-06-14 (the "two finite bounds" framing was an over-claim) — but the FULL
> objective is HELD; we do NOT de-scope.** Honest scope: the full geometric `Ω₄^{Pin⁺}=ℤ₁₆` is a **large
> multi-layer infrastructure build** (Thom spectra + Steenrod algebra + Adams SS + APS / spinor-Dirac-η),
> none of it in any proof assistant. The dedicated DR estimates 15–25 *human* person-years — but per the
> user (2026-06-14), **authoritative person-year estimates do NOT gate this** (AI-dev pace has crushed such
> estimates; thousands of PY in months). The "finite A(1)-Ext" is a real but PARTIAL kernel embedded in
> that infra (not a shortcut to the bordism group). **Plan: hold the full discharge as the goal; START with
> the achievable de-risking pieces (the A(1)-Ext upper-bound algebraic kernel; the categorical 16-fold-way
> on existing fusion-category infra; Brown evidence ✅ W1+W2), THEN attack the foundational layers (Thom
> spectra → Steenrod → Adams SS; spinor bundles → Dirac → η/APS; Smith exact sequence) over an extended
> period.** No de-scope; see memory `[[feedback-no-hypothesis-based-descope]]` (person-year estimates
> eliminated from continue-vs-stop). W3–W5 below are re-cast as "build the layers," not "finite bounds."

### The `Ω₄^{Pin⁺} ≅ ℤ₁₆` discharge — a large infrastructure build (de-risk-first, full objective held)

The discharge needs both bounds of `Ω₄^{Pin⁺} ≅ ℤ₁₆`. Each requires genuinely-absent infrastructure that
we BUILD (not axiomatize); the "finite" pieces below are the **de-risking entry points**, not the whole:

`Lit-Search/Phase-5a/Formalizing the chirality wall- a Lean 4 feasibility assessment.md` (read directly)
is explicit that the iso splits into two **finite, machine-checkable** bounds — neither needs the absent
infrastructure (Adams SS / APS / Dirac):

1. **Lower bound `|Ω₄^{Pin⁺}| ≥ 16`** — the **Brown/ABK invariant** `β : Ω₄^{Pin⁺} → ℤ₁₆` (the geometric
   Guillou–Marin route) with `β([RP⁴])` a generator of order 16. **This is W1's Brown invariant** — its
   ℤ₈ phase + the signature defect give the ℤ₁₆; the order-16 element forces `|group| ≥ 16`.
2. **Upper bound `|Ω₄^{Pin⁺}| ≤ 16`** — the assessment (line 57): *"The Ext computation over A(1) in total
   degree 4 is actually finite and algorithmic — this specific computation could in principle be
   machine-checked even without general spectral sequence infrastructure, by encoding A(1) as an
   8-dimensional 𝔽₂-algebra and computing Ext directly via a free resolution. This would partially
   discharge the cobordism axiom."* I.e. `Ω₄^{Pin⁺} = π₄(MPin⁻)` (Pontryagin–Thom) and the A(1)-`Ext`
   in degree 4 is a **finite 𝔽₂-linear-algebra computation** (free resolution of the relevant A(1)-module),
   giving `|group| ≤ 16`.

Together ⇒ `≅ ℤ₁₆`. **Both bounds are finite/algebraic and avoid every Mathlib-absent landmark.** The
assessment *recommends axiomatizing* (`axiom cobordism_Z16`, `axiom RP4_generates`, …) — but per project
policy that is **advisory only**, and per the standing directive we **BUILD both finite bounds instead of
axiomatizing.** (This corrects the earlier "η/Adams-SS, no foothold, multi-week" mis-call, which conflated
the *general* spectral-sequence infrastructure — genuinely absent — with *this specific finite computation*
— buildable. The DR draws exactly that distinction.)

---

## Existing substrate to build ON (do not duplicate)

| File | What it has | Level-4 disposition |
|------|-------------|---------------------|
| `SKEFTHawking/ArfInvariant.lean` | `Arf.gaussSum`, `redQuad`, Arf of a ℤ-form mod 2 | **Extend** → Brown/ABK ℤ₈ (W1) |
| `SKEFTHawking/RokhlinArfNoGo.lean` | `arfOfForm`, the proved lattice-Arf no-go | Reference (fixes the correct invariant); Arf = ABK mod 2 bridge (W1) |
| `SKEFTHawking/SymTFT/PinPlusManifold4.lean` | `PinPlusManifold4` (carries `signature : ℤ`), `pinPlusRP4`, `pinPlusK3Lift` | **Re-base** carrier on derived β (W5) |
| `SKEFTHawking/SymTFT/PinPlusBordism4.lean` | `Omega4PinPlusBordism = Quotient … ≃+ ZMod 16`, generator order-16 facts | **Re-derive** from β (W5); keep the group skeleton |
| `SKEFTHawking/SymTFT/SpinZ4Bordism5.lean` (5q.E W6) | thin Ω₅ substrate (`daiFreed:ℤ`), constructed `smithHom` | **Re-base** on geometric Smith (W6–W7) |
| `SKEFTHawking/CommonOrigin.lean` (5q.E W5–W6) | `SmithInflow` hypothesis, conditional convergence | **Discharge** `SmithInflow` → unconditional (W8) |

Mathlib footholds (verified 2026-06-14): `spinGroup`/`pinGroup` PRESENT (`CliffordAlgebra/SpinGroup.lean`).
ABSENT (= build surface): `DiracOperator`, bordism groups, `QuadraticForm.signature`, η-invariant.

---

## Wave plan

> Dependency spine: **W1 → W2 → {W3 lower ‖ W4 upper} → W5 → W6 → W7 → W8 → W9.** Start = W1.
> W3 (lower bound) and W4 (upper bound) are independent and can be built in either order.

- **W1 — Arf–Brown–Kervaire (Brown) invariant ∈ ℤ₈.** ✅ **DONE.** ABK of a ℤ₄-quadratic refinement of a
  nondeg ℤ₂ space via the ℤ[i] Gauss sum (`gaussSum4 = √dim · ζ₈^{ABK}`): multiplicativity, the magnitude
  theorem `|gaussSum4|² = dim` (well-definedness), the ℤ₈ phase structure (order exactly 8). The algebraic
  heart of the Pin⁺ ℤ₁₆ **lower bound**.
- **W2 — general Brown extraction + characteristic-surface data.** (a) general `brown : Z4Quadratic → ZMod 8`
  phase-extraction (via the Gaussian-integer norm-`2^{2d}` structure ⇒ `gaussSum4·(1-i)^d = 2^d·i^k`, which
  gives additivity *without* the full form-classification) + `brown(stdForm g)=g` + Arf-mod-2 bridge;
  (b) the ℤ₄-valued quadratic enhancement on `H₁(F;ℤ₂)` of a characteristic surface (the Guillou–Marin form).
- **W3 — LOWER bound `|Ω₄^{Pin⁺}| ≥ 16`: the β invariant + order-16 generator.** Assemble
  `β = (signature defect) + 2·brown(char surface) ∈ ℤ₁₆` (Kirby–Taylor/Guillou–Marin); `β([RP⁴])` = generator
  of exact order 16 ⇒ the group has an order-16 element. (β's bordism-invariance: build the elementary
  handle-calculus/Guillou–Marin route; any irreducible named congruence carried as ONE disclosed tracked
  `Prop` + discharge plan, only after building everything above it.)
- **W4 — UPPER bound `|Ω₄^{Pin⁺}| ≤ 16`: the finite A(1)-`Ext` computation.** Pontryagin–Thom
  `Ω₄^{Pin⁺} = π₄(MPin⁻)`; encode `A(1) = ⟨Sq¹,Sq²⟩` as an **8-dimensional 𝔽₂-algebra**, build the relevant
  free resolution, compute `Ext_{A(1)}` in total degree 4 (a **finite 𝔽₂-linear-algebra** computation) ⇒
  `|group| ≤ 16`. No spectral-sequence infrastructure (per Phase-5a assessment line 57). Independent of W3.
- **W5 — `Ω₄^{Pin⁺} ≅ ℤ₁₆` derived + re-base substrate.** Combine W3 (≥16) + W4 (≤16) ⇒ `≅ ZMod 16`;
  re-base `PinPlusManifold4`'s carrier on derived β (retire the posited `signature = 1` for `[RP⁴]`);
  re-derive `Omega4PinPlusBordism ≃+ ZMod 16`.
- **W6 — Smith homomorphism (geometric).** `Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` as the cut along the Poincaré dual
  of the ℤ₄ class; replace the thin constructed `smithHom`.
- **W7 — `Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` via Smith iso.** Discharge the `daiFreed:ℤ` carrier.
- **W8 — Discharge `SmithInflow`; convergence unconditional.** Wire derived maps into `CommonOrigin`;
  `sixteen_convergence_common_origin` loses its hypothesis. Retire registry `smith_inflow_z16`
  (hypothesis → theorem). Reconcile all disclosure surfaces.
- **W9 — Closure.** lib+ExtractDeps clean, validate.py, counts, status/roadmap/Inventory sync,
  fresh-context adversarial review.

---

## Landed shards

| Wave | Module(s) | Key declarations | Commit | Status |
|------|-----------|------------------|--------|--------|
| W1a | `SKEFTHawking/BrownInvariant.lean` | `gaussSum4` (ℤ[i] Gauss sum) + `gaussSum4_orthogonal`/`gaussSum4_pi` multiplicativity; `qGen`/`stdForm` generators; `gaussSum4_stdForm = (1+I)^g`; `gaussSum4_stdForm_normSq = 2^g` (magnitude); `one_add_I_pow_{two,four,eight}` (phase order **exactly 8** → genuinely `ZMod 8`); `brownStd` + additivity + `brownStd_order_eight`. Kernel-pure. | (source-only) | ✅ landed |
| W1b | `BrownInvariant.lean` (cont.) | `Z4Quadratic` structure (nondeg `ZMod 4`-quadratic form: refines a symmetric biadditive nondeg `B`); `B_zero_left`/`q_zero`/`B_add_right`; `chi2_B_sum_eq_zero` (character orthogonality on `B`); **`gaussSum4_normSq` magnitude theorem** `gaussSum4 q · conj = \|V\|` — the well-definedness of the Brown phase. Kernel-pure. | (source-only) | ✅ landed |

**W1 status:** ✅ core complete (Gauss sum + multiplicativity + ℤ₈ structure + magnitude/well-definedness).

**W2 status:** ✅ COMPLETE (`509ba644` + `f95b2661` + `3c163033`) — the general Brown invariant + additivity + generator bridge, all kernel-pure:

| W2a | `BrownInvariant.lean` | Gaussian-integer norm-`2^N` classification `g = i^k·(1+i)^N` (elementary, NO prime theory — via `(1+i)`-division `⟨a,b⟩=(1+i)·⟨(a+b)/2,(b-a)/2⟩` induction); `zeta4` injectivity/uniqueness; `norm_gaussSum4 = 2^dim` bridge | `509ba644` | ✅ |
| W2b | `BrownInvariant.lean` | `brown : Z4Quadratic → ZMod 8` (ζ₈-phase via `Exists.choose`); `orthSum` (disjoint-union form, all 4 fields incl nondeg); **`brown_orthSum` additivity** | `f95b2661` | ✅ |
| W2c | `BrownInvariant.lean` | `stdQuadratic g` instance; **`brown(stdForm g) = g`** ⇒ `brown(RP²-form)=1`, the order-16 generator value W3 consumes | `3c163033` | ✅ |

Deferred (NOT a DONE-criterion — cross-check only): the `brown mod 2 = Arf` bridge to `SKEFTHawking.Arf`
needs the symplectic (spin) pairing, not the diagonal Pin⁻ form; off the two-bound critical path. Revisit only if W3/closure needs it.

**Session 2 (2026-06-14) — bounds + Smith mechanism + capstone, all kernel-pure (8 commits, NOT pushed):**

| W3b/c | `GuillouMarinBridge.lean` | `doubleBrown`/`GMrelation`/`GM_rp4`/`doubleBrown_eight_distinct` (even part ≥8); **odd-bit ≥16 via the finite η-surrogate**: `reduce16to8`, `order_exact_sixteen_of_surfaceABK` (kernel-pure: mod-8 reduction = surface ABK `β`; `β` a unit ⟹ odd ⟹ order 16 — NO APS), `pinPlus_RP4_order16_from_ABK` (∀g, **posit-free**), `pinPlusRP4_order16_backed_by_ABK` (concrete, uses posited `signature=1`) | `7b508fd3`+`8158eeef` | ✅ |
| W4a | `JokerModule.lean`, `KspModule.lean` | the joker `J=A(1)/A(1)Sq³` + ksp `K=A(1)/(A(1)Sq¹+A(1)Sq²Sq¹Sq²)` A(1)-modules (Adem-verified actions; CORRECTED joker action vs the erroneous DR §2.4d) | `7e469b39`+`5e0e7bda` | ✅ |
| W4b | `KspResolution.lean` | K's minimal free A(1)-resolution `d₁,d₂,d₃` (`eps`, `Rsq1/Rsq2/Re6/Rsq3`, block chain `ε∘d₁=0`, `d₁∘d₂=0`, `d₂∘d₃=0`, minimality), verified vs Campbell/Mills §3.2 generator-for-generator | `b9b55e99`+`8a62f2a3`+`e5a24c21` | ✅ |
| W4c | `PinPlusExtBound.lean` | upper `≤16` via disclosed Campbell **δ-truncation cap** (`DeltaTruncationCap`, inhabited; does NOT assert the FALSE `Ext(K)_4=0`) + **two-bounds pinch** `addOrderOf [RP⁴]=16` (lower ABK + upper δ-cap); H1–H4 disclosed-Prop pattern | `d33444a1` | ✅ |
| W6b | `SymTFT/SmithMechanism.lean` | the Smith map's SW-obstruction heart `w₂(N)=0⟹Pin⁺` (Whitney `w₂(N)=c+b²` + Spin-ℤ₄ `c=b²`; RP⁵→RP⁴ via Karoubi `C(6,2)=1`,`C(5,2)=0`) — geometric content under the content-free `smithHom` | `0aec7431` | ✅ |
| W7 | `SixteenConvergenceDerived.lean` | capstone: SmithInflow's opaque content **REFINED** into constructed `smithHom` + two-bounds-derived order + SW-mechanism (`sixteen_convergence_derived_substrate`, no SmithInflow binder). Explicitly **NOT** a geometric discharge | `966e4760` | ✅ |
| QA | (4 files) | fresh-context adversarial review = **DEFENSIBLE** (no vacuous/axiom/false-math; capstone framing "exemplary"); remediated CRITICAL-2 (concrete "derived" wording: uses posited `signature=1`) + CRITICAL-1 (cupSquare rank-transport note); dropped `shared_generator_order_derived` alias | `14e74d1e` | ✅ |

**Scout verdict (2026-06-14, `Explore`):** the algebraic Ext layer (resolution + `A1ExtSubstantive`-style `dim Ext = rank P_n` via `Module.finrank`) is **TRACTABLE** to deepen; the topological grounding (Pontryagin–Thom + ABP + Adams convergence + δ-truncation-as-spectrum) is **genuinely Mathlib-absent** (ADR-003; existing `ChangeOfRings.h2`/`ExtBordismBridge` H1/H3/H4 are themselves `True` placeholders — our disclosed Props are *more* substantive). The honest endpoint: bounds + order + Smith built; topological landmarks carried as disclosed cited Props with the discharge plan = future stable-homotopy Mathlib infra.

(rows appended as waves land)

---

## Honest-endpoint accounting (updated each wave)

The target is the **unconditional** discharge of `SmithInflow` and the posited carriers. The single
deepest brick is W4 (bordism-invariance of β) — classically Rokhlin's theorem / the Guillou–Marin
congruence, both of which have *elementary* (handle-calculus, non-APS) proofs. We build toward a fully
constructive discharge. Any residual that genuinely bottoms out in a named-landmark theorem with no
constructive Mathlib route will be carried as ONE disclosed tracked `Prop` with a discharge plan and
flagged here — never an axiom, never a reason to stop building the rest.
