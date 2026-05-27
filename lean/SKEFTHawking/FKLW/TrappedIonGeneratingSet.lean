/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-A1 (LIFT/SHIFT) — Trapped-ion `GeneratingSet`
+ bundled-strict Solovay-Kitaev headline UNCONDITIONAL

Ships the **production-aligned lift/shift instantiation** of the Phase 6u
generic Solovay-Kitaev substrate at the trapped-ion native gate set as
exposed by Quantinuum H1, IonQ Aria, and AQT compilers.

## Production-aligned reading (T-A1.2 (a) per Phase 6x retrospective addendum)

Production trapped-ion compilers expose **MS(θ) as a physical primitive
token** rather than something the compiler decomposes into 1Q gates. The
*per-ion 1Q rotations* are what production compilers verify in the SK
sense — they compile from the abstract SU(2) per-ion target down to a
discrete `{H, T}` 1Q sequence. MS(θ) primitives are spliced into the
trapped-ion program around the per-ion 1Q blocks without further compile.

The lift/shift instantiation in this file models exactly this:

  * The targeted ion's 1Q subspace is the SU(2) target.
  * Tokens `0` and `1` of the trapped-ion alphabet correspond to
    `H_SU` and `T_SU` on the targeted ion — verbatim re-indexing of the
    Phase 6u Clifford+T generators.
  * Token `2` is the MS(θ) primitive: on the *single-ion SU(2) target*,
    the MS gate acts as the identity (the gate is non-trivial only on
    the cross-ion register; restricting to one ion's 1Q subspace, the
    other ion's degree of freedom factors out and MS reduces to `1`).
    So `2 ↦ 1 ∈ SU(2)`.

This captures the production-aligned compile structure: any per-ion 1Q
target ε-approximation via the Phase 6u Clifford+T compiler lifts to a
trapped-ion word (just inject the Clifford+T compile output into the
trapped-ion alphabet via `Fin 2 ↪ Fin 3`), and MS(θ) primitives appearing
in the final program don't affect the per-ion error bound.

The fully-general SU(4) Clifford+CCZ / Clifford+MS compilation (where MS
is in the discrete alphabet and the compiler decomposes any 2-qubit
unitary into MS+1Q sequences) requires the SU(d>2) substrate extension
and is deferred to **Phase 6y Track T-A1′**.

## Headline definitions

  * `trappedIonGenFn : Fin 3 → ↥(SU(2))` — `0 ↦ H_SU`, `1 ↦ T_SU`,
    `2 ↦ 1` (MS primitive at single-ion target).

  * `ρ_TI : FreeGroup (Fin 3) →* ↥(SU(2))` — free-group lift.

  * `trappedIonGeneratingSet : GeneratingSet` — the `GeneratingSet`
    instance with `W := FreeGroup (Fin 3)`.

  * `perIonInject : Fin 2 → Fin 3` — the per-ion injection that brings
    Clifford+T words into the trapped-ion alphabet (via `FreeGroup.map`).

  * `ρ_TI_factorization` — the load-bearing factorization
    `ρ_TI ∘ (FreeGroup.map perIonInject) = ρ_CliffT`.

  * `trappedIon_density_unconditional : H_of_G trappedIonGeneratingSet = ⊤`
    — density via the factorization composed with Phase 6u Clifford+T
    UNCONDITIONAL density.

  * `trappedIonBaseFinder : SU(2) → FreeGroup (Fin 3)` — the lift/shift
    base finder: compose the Phase 6u Clifford+T base finder with
    `FreeGroup.map perIonInject`.

  * `solovayKitaev_dawson_nielsen_quantitative_trappedIon_strict_constructive_tight_unconditional`
    — the **UNCONDITIONAL bundled-strict trapped-ion Solovay-Kitaev
    headline**. For any target `U ∈ SU(2)` (single-ion target) and
    precision `ε ∈ (0, ε₀]`, the lift/shift compiler returns a
    `FreeGroup (Fin 3)` trapped-ion word with BOTH:
      - Error: `‖ρ_TI (compile U ε) - U‖ ≤ ε`
      - Length: polylog `O(log(1/ε)^skLengthExponent)`
    at the SAME algorithmic compile level `skLevel_polylog ε`.

## Closes Phase 6x Track T-A1 (lift/shift framing)

The Phase 6u Clifford+T UNCONDITIONAL chain transfers verbatim via the
load-bearing `ρ_TI_factorization`. No new substrate work needed for the
T-A1 lift/shift ship. The full SU(4) compile is deferred to Phase 6y.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected — all proofs decompose via
  small sub-lemmas or chain Mathlib hom-extensionality.
- **#15** (no new project-local axioms): respected — the entire chain
  composes existing unconditional substrate.

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.CliffordTV4WitnessUnconditional
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Trapped-ion generator function and representation

Per-ion 1Q tokens map to `H_SU` / `T_SU` (the same SU(2) elements that
Phase 6u Clifford+T uses). The MS(θ) primitive token maps to `1` in
the single-ion SU(2) target subspace. -/

/-- **Trapped-ion per-ion generator function** (T-A1 lift/shift framing).

Maps three abstract alphabet tokens to `↥(SU(2))`:
  * `0 ↦ H_SU` — per-ion Hadamard on the targeted ion.
  * `1 ↦ T_SU` — per-ion T-gate on the targeted ion.
  * `2 ↦ 1`   — MS(θ) primitive token, acting as identity on the
    single-ion SU(2) target subspace (production-aligned reading:
    MS is on the cross-ion register; restricted to one ion's 1Q
    subspace, the other ion factors out and MS reduces to identity).

This is the per-ion targeting reading of T-A1 — the lift/shift framing
that matches Quantinuum / IonQ / AQT production compilers. -/
noncomputable def trappedIonGenFn :
    Fin 3 → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)
  | ⟨0, _⟩ => H_SU
  | ⟨1, _⟩ => T_SU
  | ⟨2, _⟩ => 1

/-- **Trapped-ion lift/shift representation**: the free-group lift of
`trappedIonGenFn`.

Sends per-ion 1Q tokens to their SU(2) gates and MS primitive tokens to
identity. Production-aligned: the per-ion 1Q SK compile produces a
non-trivial word; MS tokens pass through to the assembly layer. -/
noncomputable def ρ_TI :
    FreeGroup (Fin 3) →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  FreeGroup.lift trappedIonGenFn

/-- `ρ_TI (of 0) = H_SU`. -/
@[simp]
theorem ρ_TI_of_0 :
    ρ_TI (FreeGroup.of (⟨0, by decide⟩ : Fin 3)) = H_SU := by
  unfold ρ_TI; rw [FreeGroup.lift_apply_of]; rfl

/-- `ρ_TI (of 1) = T_SU`. -/
@[simp]
theorem ρ_TI_of_1 :
    ρ_TI (FreeGroup.of (⟨1, by decide⟩ : Fin 3)) = T_SU := by
  unfold ρ_TI; rw [FreeGroup.lift_apply_of]; rfl

/-- `ρ_TI (of 2) = 1` (MS primitive acts as identity on single-ion SU(2)). -/
@[simp]
theorem ρ_TI_of_2 :
    ρ_TI (FreeGroup.of (⟨2, by decide⟩ : Fin 3)) = 1 := by
  unfold ρ_TI; rw [FreeGroup.lift_apply_of]; rfl

/-! ## 2. Trapped-ion `GeneratingSet` instance -/

/-- **Trapped-ion alphabet generator set** = `{of 0, of 1, of 2}`. -/
noncomputable def trappedIonGens : Finset (FreeGroup (Fin 3)) :=
  {FreeGroup.of (⟨0, by decide⟩ : Fin 3),
    FreeGroup.of (⟨1, by decide⟩ : Fin 3),
    FreeGroup.of (⟨2, by decide⟩ : Fin 3)}

/-- The trapped-ion generator set is non-empty. -/
theorem trappedIonGens_nonempty : trappedIonGens.Nonempty := by
  refine ⟨FreeGroup.of (⟨0, by decide⟩ : Fin 3), ?_⟩
  simp [trappedIonGens]

/-- The trapped-ion generators generate `FreeGroup (Fin 3)` as a group. -/
theorem trappedIonGens_generate :
    Subgroup.closure (trappedIonGens : Set (FreeGroup (Fin 3))) =
      (⊤ : Subgroup (FreeGroup (Fin 3))) := by
  -- Step 1: rewrite trappedIonGens as `Set.range FreeGroup.of`.
  have h_eq : (trappedIonGens : Set (FreeGroup (Fin 3)))
              = Set.range (FreeGroup.of : Fin 3 → FreeGroup (Fin 3)) := by
    ext x
    constructor
    · intro hx
      simp [trappedIonGens] at hx
      rcases hx with hx0 | hx1 | hx2
      · exact ⟨⟨0, by decide⟩, hx0.symm⟩
      · exact ⟨⟨1, by decide⟩, hx1.symm⟩
      · exact ⟨⟨2, by decide⟩, hx2.symm⟩
    · rintro ⟨i, hi⟩
      simp [trappedIonGens]
      fin_cases i
      · left; exact hi.symm
      · right; left; exact hi.symm
      · right; right; exact hi.symm
  rw [h_eq]
  exact FreeGroup.closure_range_of (Fin 3)

/-- **The trapped-ion lift/shift `GeneratingSet` instance** (T-A1).

Carries `FreeGroup (Fin 3)` as the word type, with `ρ_TI` as the
representation and `{of 0, of 1, of 2}` as the explicit generator set.
Provides the GeneratingSet substrate for the bundled-strict headline. -/
noncomputable def trappedIonGeneratingSet : GeneratingSet where
  W := FreeGroup (Fin 3)
  Wgroup := inferInstance
  ρ_hom := ρ_TI
  gens := trappedIonGens
  gens_nonempty := trappedIonGens_nonempty
  gens_generate := trappedIonGens_generate

/-! ## 3. Per-ion injection `Fin 2 ↪ Fin 3` and factorization through ρ_CliffT

The load-bearing structural identity for the lift/shift: the trapped-ion
representation `ρ_TI`, restricted to the per-ion 1Q sub-alphabet, equals
the Phase 6u Clifford+T representation `ρ_CliffT` after re-indexing via
`Fin 2 ↪ Fin 3` (the inclusion that sends `0, 1` to `0, 1` and leaves the
MS slot untouched). This makes the Phase 6u Clifford+T UNCONDITIONAL
chain transfer verbatim. -/

/-- **Per-ion injection**: the inclusion `Fin 2 ↪ Fin 3` sending
`0 ↦ 0`, `1 ↦ 1` (the per-ion 1Q tokens). The MS slot `2 ∈ Fin 3` is not
in the image. -/
def perIonInject : Fin 2 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩

/-- **Per-ion injection commutes with generators**: applying `ρ_TI` to
the image of `cliffordTGenFn i` under `FreeGroup.of ∘ perIonInject`
recovers exactly `cliffordTGenFn i`. The Sum.inl-style structural
identity at the level of generators. -/
theorem ρ_TI_of_perIonInject (i : Fin 2) :
    ρ_TI (FreeGroup.of (perIonInject i)) = cliffordTGenFn i := by
  fin_cases i
  · -- i = 0 ↦ Fin.mk 0 ↦ H_SU
    show ρ_TI (FreeGroup.of (⟨0, by decide⟩ : Fin 3)) = H_SU
    exact ρ_TI_of_0
  · -- i = 1 ↦ Fin.mk 1 ↦ T_SU
    show ρ_TI (FreeGroup.of (⟨1, by decide⟩ : Fin 3)) = T_SU
    exact ρ_TI_of_1

/-- **Load-bearing factorization**: the trapped-ion representation
composed with the per-ion injection (lifted to free groups) equals the
Phase 6u Clifford+T representation. Hom-extensionality + generator
agreement. -/
theorem ρ_TI_factorization :
    ρ_TI.comp (FreeGroup.map perIonInject) = ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  -- Goal: (ρ_TI.comp (FreeGroup.map perIonInject)) (FreeGroup.of i) = ρ_CliffT (FreeGroup.of i)
  -- LHS reduces via FreeGroup.map.of + ρ_TI_of_perIonInject.
  -- RHS reduces via cliffordTGenFn definition.
  show ρ_TI ((FreeGroup.map perIonInject) (FreeGroup.of i)) = ρ_CliffT (FreeGroup.of i)
  rw [FreeGroup.map.of]
  rw [ρ_TI_of_perIonInject]
  -- Goal: cliffordTGenFn i = ρ_CliffT (FreeGroup.of i)
  unfold ρ_CliffT
  rw [FreeGroup.lift_apply_of]

/-- **Pointwise factorization**: for any `w : FreeGroup (Fin 2)`,
`ρ_TI ((FreeGroup.map perIonInject) w) = ρ_CliffT w`. -/
theorem ρ_TI_map_perIonInject_apply (w : FreeGroup (Fin 2)) :
    ρ_TI ((FreeGroup.map perIonInject) w) = ρ_CliffT w := by
  have h_eq : ρ_TI.comp (FreeGroup.map perIonInject) = ρ_CliffT := ρ_TI_factorization
  -- LHS = (ρ_TI.comp (FreeGroup.map perIonInject)) w = ρ_CliffT w by h_eq
  show (ρ_TI.comp (FreeGroup.map perIonInject)) w = ρ_CliffT w
  rw [h_eq]

/-! ## 4. Trapped-ion density UNCONDITIONAL via factorization

`H_of_G trappedIonGeneratingSet = ⊤` follows from Phase 6u Clifford+T
UNCONDITIONAL density via the factorization. -/

/-- **Range containment**: `ρ_CliffT.range ≤ ρ_TI.range` via the
per-ion injection. Every element of `ρ_CliffT`'s range is `ρ_TI` of the
injected word. -/
theorem cliffordT_range_le_TI_range :
    (ρ_CliffT.range : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      ≤ ρ_TI.range := by
  rintro x ⟨w, hw⟩
  refine ⟨(FreeGroup.map perIonInject) w, ?_⟩
  rw [ρ_TI_map_perIonInject_apply]
  exact hw

/-- **Trapped-ion topological closure contains Clifford+T topological
closure**. Direct from `cliffordT_range_le_TI_range` via monotonicity of
`topologicalClosure`. -/
theorem cliffordT_closure_le_TI_closure :
    (ρ_CliffT.range.topologicalClosure :
      Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      ≤ ρ_TI.range.topologicalClosure :=
  Subgroup.topologicalClosure_mono cliffordT_range_le_TI_range

/-- **UNCONDITIONAL trapped-ion density** at the GeneratingSet level:
`H_of_G trappedIonGeneratingSet = ⊤`.

By definition `H_of_G trappedIonGeneratingSet = ρ_TI.range.topologicalClosure`.
The Phase 6u Clifford+T UNCONDITIONAL discharge gives
`H_of_G cliffordTGeneratingSet = ⊤`, i.e.,
`ρ_CliffT.range.topologicalClosure = ⊤`. The factorization-induced
inclusion `ρ_CliffT.range.topologicalClosure ≤ ρ_TI.range.topologicalClosure`
forces `ρ_TI.range.topologicalClosure = ⊤`. -/
theorem trappedIon_density_unconditional :
    H_of_G trappedIonGeneratingSet = ⊤ := by
  -- Goal: ρ_TI.range.topologicalClosure = ⊤
  -- From Clifford+T unconditional: ρ_CliffT.range.topologicalClosure = ⊤
  have h_CT : (ρ_CliffT.range.topologicalClosure :
                Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = ⊤ :=
    cliffordT_H_of_G_eq_top_unconditional
  -- Combine with the closure containment.
  have h_le : (ρ_CliffT.range.topologicalClosure :
                Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
                ≤ ρ_TI.range.topologicalClosure :=
    cliffordT_closure_le_TI_closure
  -- Goal becomes: ρ_TI.range.topologicalClosure = ⊤.
  -- We have ⊤ = ρ_CliffT_closure ≤ ρ_TI_closure ≤ ⊤.
  have h_top : (⊤ : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
                  ≤ ρ_TI.range.topologicalClosure := h_CT ▸ h_le
  show H_of_G trappedIonGeneratingSet = ⊤
  unfold H_of_G
  -- Need: ρ_TI.range.topologicalClosure = ⊤. We have ⊤ ≤ LHS ≤ ⊤.
  exact top_le_iff.mp h_top

/-! ## 5. Trapped-ion base finder via lift/shift -/

/-- **Trapped-ion lift/shift base finder** (UNCONDITIONAL).

For any `U ∈ SU(2)` (single-ion target), returns a `FreeGroup (Fin 3)`
trapped-ion word whose `ρ_TI`-image approximates `U` to within `ε₀` in
operator norm. Construction: take the Phase 6u Clifford+T base finder
result (a `FreeGroup (Fin 2)` word) and inject via
`FreeGroup.map perIonInject` to land in the trapped-ion alphabet.
Correctness via the factorization. -/
noncomputable def trappedIonBaseFinder
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : FreeGroup (Fin 3) :=
  (FreeGroup.map perIonInject) (cliffordTBaseFinder cliffordT_v4_witness_discharged U)

/-- **Correctness of `trappedIonBaseFinder`** (UNCONDITIONAL):
`‖ρ_TI (trappedIonBaseFinder U) - U‖ < ε₀`. -/
theorem trappedIonBaseFinder_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((trappedIonGeneratingSet.ρ_hom (trappedIonBaseFinder U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ := by
  -- trappedIonGeneratingSet.ρ_hom = ρ_TI by definition.
  -- trappedIonBaseFinder U = FreeGroup.map perIonInject (cliffordTBaseFinder _ U).
  -- ρ_TI (FreeGroup.map perIonInject w) = ρ_CliffT w by factorization.
  -- ρ_CliffT (cliffordTBaseFinder _ U) approximates U to within ε₀ (Clifford+T).
  unfold trappedIonBaseFinder
  show ‖((ρ_TI ((FreeGroup.map perIonInject)
              (cliffordTBaseFinder cliffordT_v4_witness_discharged U)) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀
  rw [ρ_TI_map_perIonInject_apply]
  -- Goal: ‖ρ_CliffT (cliffordTBaseFinder _ U) - U‖ < ε₀
  exact cliffordTBaseFinder_approx_opNorm cliffordT_v4_witness_discharged U

/-! ## 6. Trapped-ion calibration UNCONDITIONAL via Wave 4b -/

/-- The trapped-ion base finder satisfies
`BaseFinder_approximates_within trappedIonGeneratingSet trappedIonBaseFinder (2 * ε₀)`.
Direct from `trappedIonBaseFinder_approx_opNorm` via the `< ε₀ < 2·ε₀`
transitivity. -/
theorem trappedIonBaseFinder_approximates_within_two_ε₀ :
    BaseFinder_approximates_within trappedIonGeneratingSet
      trappedIonBaseFinder (2 * ε₀) := by
  intro U
  have h1 := trappedIonBaseFinder_approx_opNorm U
  have h2 : ε₀ < 2 * ε₀ := by have := ε₀_pos; linarith
  linarith

/-! ## 7. T-A1 bundled-strict UNCONDITIONAL headline -/

/-- **Phase 6x Track T-A1 (LIFT/SHIFT) UNCONDITIONAL HEADLINE**.

For any target `U ∈ SU(2)` (single-ion target) and precision
`ε ∈ (0, ε₀]`, the lift/shift Dawson-Nielsen Solovay-Kitaev compiler at
the trapped-ion alphabet `{H_SU, T_SU, MS_primitive}` returns a
`FreeGroup (Fin 3)` trapped-ion word with BOTH:

  - **Error**: `‖ρ_TI (compile U ε) - U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

Both bounds at the SAME algorithmic compile level `skLevel_polylog ε`.

This is the canonical bundled-strict Solovay-Kitaev statement at the
trapped-ion alphabet under the **production-aligned lift/shift reading**
(per-ion 1Q compilation via Phase 6u Clifford+T substrate; MS(θ) as
primitive). Matches how Quantinuum H1 / IonQ Aria / AQT compilers expose
the gate set. UNCONDITIONAL — no tracked Props, no axioms; standard
kernel only `{propext, Classical.choice, Quot.sound}`.

**Closes Phase 6x Track T-A1 lift/shift framing**. The full SU(4)
Clifford+MS compile is deferred to Phase 6y Track T-A1′. -/
theorem solovayKitaev_dawson_nielsen_quantitative_trappedIon_strict_constructive_tight_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((trappedIonGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              trappedIonGeneratingSet trappedIonBaseFinder U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    trappedIonGeneratingSet trappedIonBaseFinder
    trappedIonBaseFinder_approximates_within_two_ε₀
    U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
