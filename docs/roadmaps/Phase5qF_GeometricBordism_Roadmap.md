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

> Dependency spine: **W1 → W2 → W3 → W4 → W5 → W6 → W7 → W8 → W9.** Start = W1.

- **W1 — Arf–Brown–Kervaire (Brown) invariant ∈ ℤ₈.** Genuine ABK of a ℤ₄-quadratic refinement of a
  nondegenerate ℤ₂ inner-product space, via the normalized Gauss sum (`gaussSum = √dim · ζ₈^{ABK}`).
  Build on `Arf.gaussSum`. Deliver: Gauss-sum modulus `|gaussSum|² = dim`; the unit-phase ∈ μ₈;
  `brown : Form → ZMod 8` well-defined; additivity under ⊥; `brown(generator)=1`; `Arf = brown mod 2`
  (bridge to `arfOfForm`). *Self-contained algebra; the heart of the Pin⁺ ℤ₁₆.*
- **W2 — ℤ₄-quadratic classification + general Brown extraction + characteristic-surface data.**
  (a) Normal-form classification of finite nondeg `Z4Quadratic` forms (orthogonal sum of generators);
  (b) the general `brown : Z4Quadratic → ZMod 8` phase-extraction function with additivity and
  `brown(stdForm g) = g` + the Arf-mod-2 bridge to `SKEFTHawking.Arf` (carried over from W1, where it
  was correctly identified as classification-dependent); (c) the ℤ₄-valued quadratic enhancement on
  `H₁(F;ℤ₂)` of a characteristic surface — the Guillou–Marin form β consumes.
- **W3 — β : Pin⁺-4-manifold data → ℤ₁₆ (Kirby–Taylor / Guillou–Marin formula).** Assemble
  β = (signature-defect term) + 2·(Brown of characteristic surface) ∈ ℤ₁₆ from W1+W2; `β(RP⁴)=1`.
- **W4 — Bordism-invariance of β (descent).** β descends to the bordism quotient (handle calculus /
  Guillou–Marin congruence). Deepest geometric brick: build the elementary route; if an irreducible
  named congruence (Rokhlin / Guillou–Marin) remains, carry as ONE disclosed tracked `Prop` + discharge
  plan — only after building everything above it.
- **W5 — Ω₄^{Pin⁺} ≅ ℤ₁₆ derived.** Re-base `PinPlusManifold4` on derived β; re-derive
  `Omega4PinPlusBordism ≃+ ZMod 16` from β-injectivity + RP⁴ generation. Posited `signature` carrier retired.
- **W6 — Smith homomorphism (geometric).** Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺} as the cut along the Poincaré
  dual of the ℤ₄ class; replace the thin constructed `smithHom`.
- **W7 — Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆ via Smith iso.** Discharge the `daiFreed:ℤ` carrier.
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

**W1 status:** ✅ core complete (Gauss sum + multiplicativity + ℤ₈ structure + magnitude/well-definedness). The standalone `brown : Z4Quadratic → ZMod 8` *extraction function* + Arf-mod-2 bridge are **moved to W2**: they require the normal-form classification of finite ℤ₄-quadratic forms (to prove additivity / `brown(stdForm g)=g`), which W2 builds alongside the characteristic-surface forms. (Mathematical dependency, not effort-deferral — the general well-definedness, the hard part, is done.)

(rows appended as waves land)

---

## Honest-endpoint accounting (updated each wave)

The target is the **unconditional** discharge of `SmithInflow` and the posited carriers. The single
deepest brick is W4 (bordism-invariance of β) — classically Rokhlin's theorem / the Guillou–Marin
congruence, both of which have *elementary* (handle-calculus, non-APS) proofs. We build toward a fully
constructive discharge. Any residual that genuinely bottoms out in a named-landmark theorem with no
constructive Mathlib route will be carried as ONE disclosed tracked `Prop` with a discharge plan and
flagged here — never an axiom, never a reason to stop building the rest.
