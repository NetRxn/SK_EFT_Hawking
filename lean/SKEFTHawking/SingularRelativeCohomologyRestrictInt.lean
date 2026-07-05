/-
# Phase 5q.H (E1 integral topology) — contravariant restriction functoriality for integral relative cohomology

Integral (`ZMod 2 → ℤ`) mirror of `SingularRelativeCohomologyRestrict`. Cohomology is
**contravariant**, so for `S ⊆ T ⊆ X` the inclusion-of-pairs `(X, S) → (X, T)` induces a RESTRICTION
map going the *other* way, `Hⁿ(X, T; ℤ) → Hⁿ(X, S; ℤ)`. Built from the integral monotonicity
`S ⊆ T ⟹ subspaceChainsInt S n ≤ subspaceChainsInt T n`
(`SingularRelativeMVInt.subspaceChainsInt_mono`): a cochain vanishing on the *bigger* annihilator
target `subspaceChainsInt T` vanishes on the *smaller* `subspaceChainsInt S`, i.e. the integral
relative cochains are **antitone** `relCochainsInt T n ≤ relCochainsInt S n`. The inclusion of
cochains commutes with the relative coboundary `δ` (both cod-restrict the same absolute
`coboundaryₗ`), so it descends to the cohomology quotient via `Submodule.mapQ`, giving
`relCohomRestrictInt` with `id`/`trans` functoriality (arrows reversed — the cohomology dual of
`SingularRelativeMVConnectingInt.relInclInt` / `relInclInt_trans`).

**Why this brick.** This is the transition-map prerequisite for the integral compactly-supported
cohomology colimit `Hᵏ_c(M;ℤ) := colim_{K compact} Hᵏ(M | M∖K; ℤ)` — the top row of the integral
Poincaré-duality ladder (mirror of `SingularCohomologyColimit`, whose `cohomF` is exactly this
restriction). `(cohomG, relCohomRestrictInt)` is a `DirectedSystem` (`map_self` from
`relCohomRestrictInt_id`, `map_map` from `relCohomRestrictInt_trans`), so the `Module.DirectLimit`
is well-formed. Built in a NEW module (importing but never editing the leaf
`SingularEuclideanCapIsoInt` where `RelativeCohomologyInt` lives) so it composes with the Euclidean
base case without a harvest conflict.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularRelativeCohomologyRestrictInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

variable {X : TopCat}

/-! ## §1. Antitone integral relative cochains and the cochain-level restriction -/

/-- **Integral relative cochains are antitone**: for `S ⊆ T`, `relCochainsInt T n ≤ relCochainsInt S
n`. A cochain vanishing on the *bigger* subspace chains `subspaceChainsInt T n` vanishes on the
*smaller* `subspaceChainsInt S n` (`subspaceChainsInt_mono : subspaceChainsInt S n ≤
subspaceChainsInt T n`). -/
theorem relCochainsInt_antitone {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    relCochainsInt T n ≤ relCochainsInt S n := by
  intro f hf c hc
  exact hf c (subspaceChainsInt_mono h n hc)

/-- The **cochain-level restriction** `Cⁿ(X, T; ℤ) →ₗ Cⁿ(X, S; ℤ)` for `S ⊆ T` — the identity on the
underlying integral singular cochain, with membership weakened along the antitone `relCochainsInt T n
≤ relCochainsInt S n`. -/
noncomputable def relCochainRestrictInt {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    relCochainsInt T n →ₗ[ℤ] relCochainsInt S n :=
  Submodule.inclusion (relCochainsInt_antitone h n)

@[simp] theorem relCochainRestrictInt_coe {S T : Set X} (h : S ⊆ T) (n : ℕ) (f : relCochainsInt T n) :
    (relCochainRestrictInt h n f : SingularCochainInt X n) = (f : SingularCochainInt X n) := rfl

/-- The cochain restriction **commutes with the relative coboundary** `δ`: both sides cod-restrict
the same absolute `coboundaryₗ`, so they agree on the underlying integral singular cochains. -/
theorem relCochainRestrictInt_coboundary {S T : Set X} (h : S ⊆ T) (n : ℕ) (f : relCochainsInt T n) :
    relCochainRestrictInt h (n + 1) (relCoboundaryIntₗ T n f)
      = relCoboundaryIntₗ S n (relCochainRestrictInt h n f) := by
  apply Subtype.ext
  rw [relCochainRestrictInt_coe, relCoboundaryIntₗ_coe, relCoboundaryIntₗ_coe,
    relCochainRestrictInt_coe]

/-! ## §2. Restriction on cocycles and the descent to integral relative cohomology -/

/-- The cochain restriction maps **relative cocycles to relative cocycles**, `ker δ_T → ker δ_S`:
`δ_S (restrict z) = restrict (δ_T z) = restrict 0 = 0`. -/
theorem relCochainRestrictInt_mem_ker {S T : Set X} (h : S ⊆ T) (n : ℕ)
    (z : relCochainsInt T n) (hz : z ∈ LinearMap.ker (relCoboundaryIntₗ T n)) :
    relCochainRestrictInt h n z ∈ LinearMap.ker (relCoboundaryIntₗ S n) := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [← relCochainRestrictInt_coboundary, hz, map_zero]

/-- The restriction on integral cocycles `ker δ_T →ₗ ker δ_S`. -/
noncomputable def relCocycleRestrictInt {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    LinearMap.ker (relCoboundaryIntₗ T n) →ₗ[ℤ] LinearMap.ker (relCoboundaryIntₗ S n) :=
  (relCochainRestrictInt h n).restrict (fun z hz => relCochainRestrictInt_mem_ker h n z hz)

@[simp] theorem relCocycleRestrictInt_coe {S T : Set X} (h : S ⊆ T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    (relCocycleRestrictInt h n z : relCochainsInt S n)
      = relCochainRestrictInt h n (z : relCochainsInt T n) :=
  rfl

/-- The cochain restriction maps **relative coboundaries to relative coboundaries**,
`relCoboundaryRangeInt T n → relCoboundaryRangeInt S n`: the restriction of `δ_T g` is
`δ_S (restrict g)` (commutation), hence again in the range of `δ_S`. -/
theorem relCochainRestrictInt_mem_relCoboundaryRange {S T : Set X} (h : S ⊆ T) (n : ℕ)
    (f : relCochainsInt T n) (hf : f ∈ relCoboundaryRangeInt T n) :
    relCochainRestrictInt h n f ∈ relCoboundaryRangeInt S n := by
  cases n with
  | zero =>
    rw [relCoboundaryRangeInt] at hf
    rw [Submodule.mem_bot] at hf
    rw [hf, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨relCochainRestrictInt h m g, relCochainRestrictInt_coboundary h m g⟩

/-! ## §3. The integral relative cohomology restriction `Hⁿ(X, T; ℤ) → Hⁿ(X, S; ℤ)` -/

/-- The cocycle restriction `relCocycleRestrictInt` carries the coboundary subgroup into the
coboundary subgroup — the `mapQ` compatibility. -/
theorem relCocycleRestrictInt_submoduleOf_le {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (relCoboundaryRangeInt T n).submoduleOf (LinearMap.ker (relCoboundaryIntₗ T n)) ≤
      Submodule.comap (relCocycleRestrictInt h n)
        ((relCoboundaryRangeInt S n).submoduleOf (LinearMap.ker (relCoboundaryIntₗ S n))) := by
  intro z hz
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    relCocycleRestrictInt_coe] at hz ⊢
  exact relCochainRestrictInt_mem_relCoboundaryRange h n _ hz

/-- **The integral relative cohomology restriction** `Hⁿ(X, T; ℤ) →ₗ Hⁿ(X, S; ℤ)` for `S ⊆ T`. The
contravariant (cohomology) dual of the inclusion-of-pairs `relInclInt : Hₙ(X, S; ℤ) → Hₙ(X, T; ℤ)`:
the cochain restriction `relCochainRestrictInt h n` descends to the cohomology quotient via
`Submodule.mapQ` (it sends cocycles to cocycles and coboundaries to coboundaries). -/
noncomputable def relCohomRestrictInt {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    RelativeCohomologyInt T n →ₗ[ℤ] RelativeCohomologyInt S n :=
  Submodule.mapQ _ _ (relCocycleRestrictInt h n) (relCocycleRestrictInt_submoduleOf_le h n)

/-- **Computation rule**: the restriction of a relative cohomology class `[z]_T` is `[restrict z]_S`. -/
@[simp] theorem relCohomRestrictInt_mk {S T : Set X} (h : S ⊆ T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    relCohomRestrictInt h n (RelativeCohomologyInt.mk T n z)
      = RelativeCohomologyInt.mk S n (relCocycleRestrictInt h n z) :=
  rfl

/-! ## §4. Contravariant functoriality (`id` and composition, arrows reversed) -/

/-- **Identity functoriality**: restriction along `S ⊆ S` is the identity on `Hⁿ(X, S; ℤ)`
(the cochain restriction is the identity inclusion `relCochainsInt S n ≤ relCochainsInt S n`). -/
theorem relCohomRestrictInt_id {S : Set X} (n : ℕ) (x : RelativeCohomologyInt S n) :
    relCohomRestrictInt (le_refl S) n x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (Submodule.Quotient.mk z : RelativeCohomologyInt S n)
      = RelativeCohomologyInt.mk S n z := rfl
  rw [hz, relCohomRestrictInt_mk]
  rfl

/-- **Composition functoriality** (contravariant, arrows reversed): for `S ⊆ T ⊆ W` the composite
`Hⁿ(X, W; ℤ) → Hⁿ(X, T; ℤ) → Hⁿ(X, S; ℤ)` is the single restriction along `S ⊆ W`. The cohomology
dual of `SingularRelativeMVConnectingInt.relInclInt_trans`. -/
theorem relCohomRestrictInt_trans {S T W : Set X} (h1 : S ⊆ T) (h2 : T ⊆ W) (n : ℕ)
    (x : RelativeCohomologyInt W n) :
    relCohomRestrictInt h1 n (relCohomRestrictInt h2 n x) = relCohomRestrictInt (h1.trans h2) n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (Submodule.Quotient.mk z : RelativeCohomologyInt W n)
      = RelativeCohomologyInt.mk W n z := rfl
  rw [hz, relCohomRestrictInt_mk, relCohomRestrictInt_mk, relCohomRestrictInt_mk]
  rfl

end SKEFTHawking.SingularRelativeCohomologyRestrictInt
