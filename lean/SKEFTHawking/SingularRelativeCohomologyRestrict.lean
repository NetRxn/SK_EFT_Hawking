/-
# Phase 5q.F — contravariant restriction functoriality for relative ℤ/2 cohomology

The cohomology dual of `SingularRelativeMV.relIncl` / `relIncl_trans`. Cohomology is
**contravariant**, so for `S ⊆ T ⊆ M` the inclusion-of-pairs `(M, S) → (M, T)` induces a
RESTRICTION map going the *other* way, `Hⁿ(M, T) → Hⁿ(M, S)`. The construction is built from the
key monotonicity `S ⊆ T ⟹ subspaceChains S n ≤ subspaceChains T n`
(`SingularMayerVietoris.subspaceChains_mono`): a cochain vanishing on the *bigger* annihilator
target `subspaceChains T` vanishes on the *smaller* `subspaceChains S`, i.e. the relative cochains
are **antitone** `relCochains T n ≤ relCochains S n`. The inclusion of cochains commutes with the
relative coboundary `δ` (both cod-restrict the same absolute `coboundaryₗ`), so it descends to the
cohomology quotient via `Submodule.mapQ`, giving `relCohomRestrict` with `id`/`trans` functoriality
(arrows reversed). This is the foundation of the relative cohomology Mayer–Vietoris (next brick) for
Poincaré duality. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.SingularRelativeCohomologyRestrict

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularMayerVietoris

variable {M : TopCat}

/-! ## §1. Antitone relative cochains and the cochain-level restriction -/

/-- **Relative cochains are antitone**: for `S ⊆ T`, `relCochains T n ≤ relCochains S n`. A cochain
vanishing on the *bigger* subspace chains `subspaceChains T n` vanishes on the *smaller*
`subspaceChains S n` (`subspaceChains_mono : subspaceChains S n ≤ subspaceChains T n`). -/
theorem relCochains_antitone {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    relCochains T n ≤ relCochains S n := by
  intro f hf c hc
  exact hf c (subspaceChains_mono h n hc)

/-- The **cochain-level restriction** `Cⁿ(M, T) →ₗ Cⁿ(M, S)` for `S ⊆ T` — the identity on the
underlying singular cochain, with membership weakened along the antitone `relCochains T n ≤
relCochains S n`. -/
noncomputable def relCochainRestrict {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    relCochains T n →ₗ[ZMod 2] relCochains S n :=
  Submodule.inclusion (relCochains_antitone h n)

@[simp] theorem relCochainRestrict_coe {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) (f : relCochains T n) :
    (relCochainRestrict h n f : SingularCochain M n) = (f : SingularCochain M n) := rfl

/-- The cochain restriction **commutes with the relative coboundary** `δ`: both sides cod-restrict
the same absolute `coboundaryₗ`, so they agree on the underlying singular cochains. -/
theorem relCochainRestrict_coboundary {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) (f : relCochains T n) :
    relCochainRestrict h (n + 1) (relCoboundaryₗ T n f)
      = relCoboundaryₗ S n (relCochainRestrict h n f) := by
  apply Subtype.ext
  rw [relCochainRestrict_coe, relCoboundaryₗ_coe, relCoboundaryₗ_coe, relCochainRestrict_coe]

/-! ## §2. Restriction on cocycles and the descent to relative cohomology -/

/-- The cochain restriction maps **relative cocycles to relative cocycles**, `ker δ_T → ker δ_S`:
`δ_S (restrict z) = restrict (δ_T z) = restrict 0 = 0` (the commutation
`relCochainRestrict_coboundary`). -/
theorem relCochainRestrict_mem_ker {S T : Set ↑M} (h : S ⊆ T) (n : ℕ)
    (z : relCochains T n) (hz : z ∈ LinearMap.ker (relCoboundaryₗ T n)) :
    relCochainRestrict h n z ∈ LinearMap.ker (relCoboundaryₗ S n) := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [← relCochainRestrict_coboundary, hz, map_zero]

/-- The restriction on cocycles `ker δ_T →ₗ ker δ_S`. -/
noncomputable def relCocycleRestrict {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    LinearMap.ker (relCoboundaryₗ T n) →ₗ[ZMod 2] LinearMap.ker (relCoboundaryₗ S n) :=
  (relCochainRestrict h n).restrict (fun z hz => relCochainRestrict_mem_ker h n z hz)

@[simp] theorem relCocycleRestrict_coe {S T : Set ↑M} (h : S ⊆ T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryₗ T n)) :
    (relCocycleRestrict h n z : relCochains S n) = relCochainRestrict h n (z : relCochains T n) :=
  rfl

/-- The cochain restriction maps **relative coboundaries to relative coboundaries**,
`relCoboundaryRange T n → relCoboundaryRange S n`: the restriction of `δ_T g` is `δ_S (restrict g)`
(commutation), hence again in the range of `δ_S`. -/
theorem relCochainRestrict_mem_relCoboundaryRange {S T : Set ↑M} (h : S ⊆ T) (n : ℕ)
    (f : relCochains T n) (hf : f ∈ relCoboundaryRange T n) :
    relCochainRestrict h n f ∈ relCoboundaryRange S n := by
  cases n with
  | zero =>
    rw [relCoboundaryRange] at hf
    rw [Submodule.mem_bot] at hf
    rw [hf, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨relCochainRestrict h m g, relCochainRestrict_coboundary h m g⟩

/-! ## §3. The relative cohomology restriction `Hⁿ(M, T) → Hⁿ(M, S)` -/

/-- The cocycle restriction `relCocycleRestrict` carries the coboundary subgroup into the coboundary
subgroup — the `mapQ` compatibility `(relCoboundaryRange T n).submoduleOf (ker δ_T) ≤ comap …`. -/
theorem relCocycleRestrict_submoduleOf_le {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    (relCoboundaryRange T n).submoduleOf (LinearMap.ker (relCoboundaryₗ T n)) ≤
      Submodule.comap (relCocycleRestrict h n)
        ((relCoboundaryRange S n).submoduleOf (LinearMap.ker (relCoboundaryₗ S n))) := by
  intro z hz
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    relCocycleRestrict_coe] at hz ⊢
  exact relCochainRestrict_mem_relCoboundaryRange h n _ hz

/-- **The relative cohomology restriction** `Hⁿ(M, T; ℤ/2) →ₗ Hⁿ(M, S; ℤ/2)` for `S ⊆ T`. The
contravariant (cohomology) dual of the inclusion-of-pairs `relIncl : Hₙ(M, S) → Hₙ(M, T)`: the
cochain restriction `relCochainRestrict h n` descends to the cohomology quotient via
`Submodule.mapQ` (it sends cocycles to cocycles and coboundaries to coboundaries). -/
noncomputable def relCohomRestrict {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    RelativeCohomology T n →ₗ[ZMod 2] RelativeCohomology S n :=
  Submodule.mapQ _ _ (relCocycleRestrict h n) (relCocycleRestrict_submoduleOf_le h n)

/-- **Computation rule**: the restriction of a relative cohomology class `[z]_T` is
`[restrict z]_S`. -/
@[simp] theorem relCohomRestrict_mk {S T : Set ↑M} (h : S ⊆ T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryₗ T n)) :
    relCohomRestrict h n (RelativeCohomology.mk T n z)
      = RelativeCohomology.mk S n (relCocycleRestrict h n z) :=
  rfl

/-! ## §4. Contravariant functoriality (`id` and composition, arrows reversed) -/

/-- **Identity functoriality**: restriction along `S ⊆ S` is the identity on `Hⁿ(M, S)`
(the cochain restriction is the identity inclusion `relCochains S n ≤ relCochains S n`). -/
theorem relCohomRestrict_id {S : Set ↑M} (n : ℕ) (x : RelativeCohomology S n) :
    relCohomRestrict (le_refl S) n x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (Submodule.Quotient.mk z : RelativeCohomology S n) = RelativeCohomology.mk S n z := rfl
  rw [hz, relCohomRestrict_mk]
  rfl

/-- **Composition functoriality** (contravariant, arrows reversed): for `S ⊆ T ⊆ W` the composite
`Hⁿ(M, W) → Hⁿ(M, T) → Hⁿ(M, S)` is the single restriction along `S ⊆ W`. The cohomology dual of
`SingularRelativeMV.relIncl_trans`. -/
theorem relCohomRestrict_trans {S T W : Set ↑M} (h1 : S ⊆ T) (h2 : T ⊆ W) (n : ℕ)
    (x : RelativeCohomology W n) :
    relCohomRestrict h1 n (relCohomRestrict h2 n x) = relCohomRestrict (h1.trans h2) n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (Submodule.Quotient.mk z : RelativeCohomology W n) = RelativeCohomology.mk W n z := rfl
  rw [hz, relCohomRestrict_mk, relCohomRestrict_mk, relCohomRestrict_mk]
  rfl

end SKEFTHawking.SingularRelativeCohomologyRestrict
