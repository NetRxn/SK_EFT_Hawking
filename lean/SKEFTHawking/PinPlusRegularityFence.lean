/-
# The `k = 0` regularity fence — the C⁰ fork is NOT the ℤ/16 category

**Why this module exists.** `Phase5qH_LiteratureGradeUnconditional_Roadmap.md` §2 leg 2 promotes to a
**hard constraint**: the carrier must live in the *smooth* category, `k ≥ 1` (C¹ suffices — Whitney
gives a unique smooth structure), because

> at `k = 0` the honest group is topological Pin⁺ bordism `≅ ℤ/2 ⊕ ℤ/8` (Kirby–Siebenmann; E₈),
> i.e. the **WRONG group** … the C⁰ fork must never be silently conflated with the ℤ/16 target.

The audit of 2026-07-21 found the canonical KT provider declared at `k := 0`
(`PinPlusKTAssemblyResiduals.residualProv : CharPairWProviderPerOp (𝓡 4) 0`), so the assembly of
record concluded about `pinPlusCharPairData residualProv`, whose ambient is
`T2TangentialData.{0,1} PUnit 0 (𝓡 4)` — quantified over `SingularManifold PUnit 0 (𝓡 4)`. No
in-tree declaration transports that conclusion to a `k ≥ 1` carrier, and none can be generic:
`PinPlusRegularitySeparation.no_generic_zero_to_one_transport` refutes generic `C⁰ ⟹ C¹`.

**STATUS UPDATE (the regularity lift, same day).** The gap is now closed by *re-declaration*, which
is the only route the separation leaves open. `PinPlusKTAssemblyResiduals` carries a
regularity-generic core `kt_equiv_zmod16_of_residuals_ofKRS {k}` and a smooth headline
`kt_equiv_zmod16_of_residuals_smooth` / `rokhlin_sixteen_of_residuals_smooth` on
`residualProvK ⊤`, together with the UNCONDITIONAL non-vacuity of the smooth carrier
(`charPairBrown_surjective_smooth`, `rp4_ne_zero_smooth` — the `Cω` ℝP⁴ witness `rp4CharPairK ⊤`).
The `k = 0` theorems keep their exact statements and are now corollaries. **What is still `C⁰`-only**
is the KRS lane's *constructed supplier*: `SmoothSurgeryChartDatum.ofC0`,
`SingularSurgeryChartsConcrete.ambientTraceBordism_concrete` (whose
`he_smooth := contMDiff_zero_iff.mpr he_cont` IS the `k = 0` freebie), and everything downstream of
them — `ktHandleAttachment` / `SeamCollarDatum` / `SurgeredEndDatum` / `capstoneB` /
`KRSResidualRow`. The smooth statements therefore take the KRS leaf at the regularity-honest
`AmbientSurgeryDatum` row, whose `Bordism` fields carry `IsManifold … k` / `ContMDiff … k` for real.
This fence stands unchanged as the reason the lift was necessary.

**This module makes the consequence kernel-visible.** It does NOT refute the assembly and does NOT
narrow anyone's claim; it fixes the *category* the current statements are about, so the conflation
the roadmap forbids cannot happen silently.

## The sharp fact (sharper than "C⁰ instead of C^∞")

At `k = 0` the smoothness field of `SingularManifold` is not a weak constraint — it is **no
constraint at all**. Mathlib proves `contDiffGroupoid 0 I = continuousGroupoid H`
(`Mathlib/Geometry/Manifold/IsManifold/Basic.lean:694`) and therefore registers the **unconditional**
`instance : IsManifold I 0 M` (ibid.:860) for *every* charted space over the model. Since
`SingularManifold X k I` carries `[isManifold : IsManifold I k M]` as an instance field
(`Mathlib/Geometry/Manifold/Bordism.lean:120`), at `k = 0` that field is satisfied by any charted
space whatsoever. `isManifoldZero_free` and `singularManifoldZero_ofTopological` below record exactly
this.

So `SingularManifold PUnit 0 (𝓡 4)` is the class of **compact, boundaryless, charted topological
4-manifolds** — with zero differentiability. Kirby–Siebenmann applies there, and the E₈ manifold is
an element of that category; the ℤ/16 target is a *smooth* statement.

## What this does and does not establish

* **ESTABLISHED (kernel):** at `k = 0` the regularity binder is free; the `k = 0` carrier admits
  purely topological input. Hence every statement proved on `pinPlusCharPairData residualProv` is a
  statement about the C⁰ category and **must be quoted with its regularity level attached**.
* **NOT established here:** that the `k = 0` assembly's conclusion is *false*. It is not refuted —
  it is *uninterpreted* until either a `k = 0 ⟹ k ≥ 1` transport is proved, or the assembly is
  re-declared at `k ≥ 1`. Nothing below is evidence against the KT lane's mathematics.
* **ESTABLISHED ELSEWHERE (the stronger form — since landed):** the *separating witness* exists in
  tree. `PinPlusRegularitySeparationCarrier.exists_carrier_element_not_smooth` exhibits an
  `s : SingularManifold PUnit 0 (𝓡 4)` with `¬ IsManifold (𝓡 4) 1 s.M` (the kink-twisted ℝP⁴
  atlas), so the categories provably differ in-tree and re-declaring at `k ≥ 1` genuinely *removes*
  objects — the `k := 0` binder was never harmless generality.

See `docs/dev-loops/SETTLED_FORKS.md §5qH-capstone-regularity-level-k0-vs-k1-unbridged`.
-/

import Mathlib

namespace SKEFTHawking.PinPlusRegularityFence

open scoped Manifold

/-- **The `k = 0` regularity binder is FREE.** For *any* charted space over the model — no
differentiability hypothesis of any kind — the `C⁰` manifold constraint holds, because
`contDiffGroupoid 0 I` is the full continuous groupoid. This is the mechanism by which a `k := 0`
instantiation silently leaves the smooth category: the binder that is supposed to *carry* regularity
carries nothing at `0`. -/
theorem isManifoldZero_free {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] (I : ModelWithCorners ℝ E H) [ChartedSpace H M] :
    IsManifold I 0 M :=
  inferInstance

/-- **The `k = 0` Pin⁺ carrier admits purely TOPOLOGICAL 4-manifolds.** A compact, boundaryless,
charted space over `EuclideanSpace ℝ (Fin 4)` yields an element of `SingularManifold PUnit 0 (𝓡 4)`
— the very type `pinPlusCharPairData residualProv` quantifies over — with **no smoothness input**.
Note the binder list: there is no `[IsManifold (𝓡 4) 1 M]`, no `[IsManifold (𝓡 4) ∞ M]`; the
structure's regularity field is discharged by `isManifoldZero_free`.

This is the kernel-visible form of the roadmap's leg-2 hard constraint. Any `ℤ/16` conclusion drawn
on this carrier is a statement about the C⁰ category, where Kirby–Siebenmann gives
`Ω₄^{TopPin⁺} ≅ ℤ/2 ⊕ ℤ/8` — a different group. -/
noncomputable def singularManifoldZero_ofTopological (M : Type)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [CompactSpace M] [BoundarylessManifold (𝓡 4) M] :
    SingularManifold.{0} PUnit.{1} 0 (𝓡 4) where
  M := M
  f := fun _ => PUnit.unit
  hf := continuous_const

end SKEFTHawking.PinPlusRegularityFence
