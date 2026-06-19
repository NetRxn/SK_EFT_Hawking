import Mathlib
import SKEFTHawking.SingularRelativeDuality

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4f-a) — the degree-0 relative duality map `D_z⁰`

The `m+1`-indexed `SingularRelativeDuality.relativeDuality` (`Hᵏ(M,S) → H_{m+1}(M)`) cannot reach the
**degree-0** target `H₀` needed by the Poincaré-duality *base case* `D_x : Hⁿ(M|x) → H₀(M)` (cap a top
cocycle against the local fundamental cycle, landing in `H₀`). This module builds that `l = 0` cap
descent directly:
  `D_z⁰ : Hᵏ⁺¹(M, S) → H₀(M)`,    `[a] ↦ [a ⌢ z]`,
for `z` an absolute `(k+1)`-chain whose boundary `∂z` is a subspace chain (a relative cycle).

In degree `0` the cycle condition is vacuous (`cycles X 0 = ⊤`), so the only content is
well-definedness modulo relative coboundaries: a relative coboundary `δg` caps `z` to a `0`-**boundary**
(`cap_relCoboundary0_mem_boundaries`), proved from `cap_leibniz` at `m = 0`
(`∂₀(g ⌢ z) = (δg) ⌢ z + g ⌢ (∂z)`, with the middle term dead since `g` kills subspace chains and `∂z`
is one — the degree-0 specialization of `SingularRelativeDuality.cap_relCoboundary_mem_boundaries`,
where the degree cast `k+0+1 = k+1+0` is `rfl`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap SKEFTHawking.SingularRelativeDuality

namespace SKEFTHawking.SingularRelativeDuality0

variable {X : TopCat} (S : Set X)

/-- **The degree-0 relative-coboundary descent fact**: for a `k`-cochain `g` **vanishing on `S`** and a
relative cycle `z` (`∂z` a subspace chain), `δg` caps `z` to an absolute `0`-**boundary**. `cap_leibniz`
at `m = 0` gives `∂₀(g ⌢ z) = (δg) ⌢ z + g ⌢ (∂z)`; the last term dies because `g` kills subspace chains
(`cap_subspaceChain_eq_zero`, `∂z ∈ subspaceChains`), so `(δg) ⌢ z = ∂₀(g ⌢ z)` is a boundary. The
`l = 0` analogue of `SingularRelativeDuality.cap_relCoboundary_mem_boundaries` (no degree cast — `rfl`). -/
theorem cap_relCoboundary0_mem_boundaries {k : ℕ} (g : SingularCochain X k)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      g (simplexIncl S k τ) = 0)
    (z : SingularChain X (k + 1)) (hz : chainBoundary X k z ∈ subspaceChains S k) :
    cap (m := 0) (coboundary X k g) z ∈ boundaries X 0 := by
  have hleib := cap_leibniz (a := g) (c := z) (m := 0) rfl
  have hmid : cap (m := 0) g (chainBoundary X (k + 0) z) = 0 :=
    cap_subspaceChain_eq_zero S g hg hz
  rw [hmid, add_zero] at hleib
  exact ⟨cap (m := 1) g z, hleib⟩

/-! ## §2. The degree-0 cycle-level map and its descent -/

/-- The underlying linear map `a ↦ a ⌢ z` on relative `(k+1)`-cocycles, valued in `0`-chains — the
`l = 0` analogue of `SingularRelativeDuality.capCochainₗ` (the cap-by-`z` map composed with the two
subtype inclusions `ker → relCochains → Cᵏ⁺¹`). -/
noncomputable def capCochain0ₗ {k : ℕ} (z : SingularChain X (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] SingularChain X 0 :=
  ((capₗ (k + 1) 0).flip z).comp
    ((relCochains S (k + 1)).subtype.comp (LinearMap.ker (relCoboundaryₗ S (k + 1))).subtype)

@[simp] theorem capCochain0ₗ_apply {k : ℕ} (z : SingularChain X (k + 1))
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    capCochain0ₗ S z a = cap a.1.1 z := rfl

/-- For a fixed relative cycle `z`, the map `a ↦ [a ⌢ z]` on the relative `(k+1)`-cocycles, valued in
`H₀` — the degree-0 cycle-level map (every `0`-chain is a cycle, `cycles X 0 = ⊤`). -/
noncomputable def relDuality0ₗ {k : ℕ} (z : SingularChain X (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] Homology X 0 :=
  ((boundaries X 0).submoduleOf (cycles X 0)).mkQ.comp
    ((capCochain0ₗ S z).codRestrict (cycles X 0) (fun _ => Submodule.mem_top))

@[simp] theorem relDuality0ₗ_apply {k : ℕ} (z : SingularChain X (k + 1))
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    relDuality0ₗ S z a = Homology.mk X 0 ⟨cap a.1.1 z, Submodule.mem_top⟩ := rfl

/-! ## §3. The degree-0 relative Poincaré-duality map `D_z⁰` on relative cohomology -/

/-- **The degree-0 relative Poincaré-duality map** `D_z⁰ : Hᵏ⁺¹(M, S) → H₀(M)`, `[a] ↦ [a ⌢ z]`, for a
fixed relative fundamental cycle `z` (an absolute `(k+1)`-chain whose boundary `∂z` is a subspace
chain). Well-defined: a relative cocycle caps `z` to a `0`-chain (automatically a cycle), and a relative
coboundary caps `z` to a `0`-**boundary** (`cap_relCoboundary0_mem_boundaries`). The base-case duality
map of Poincaré duality (`k+1 = n`, the manifold dimension; `D_x : Hⁿ(M|x) → H₀`). -/
noncomputable def relativeDuality0 (k : ℕ) (z : SingularChain X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChains S k) :
    RelativeCohomology S (k + 1) →ₗ[ZMod 2] Homology X 0 :=
  Submodule.liftQ _ (relDuality0ₗ S z) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDuality0ₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    rw [show relCoboundaryRange S (k + 1) = LinearMap.range (relCoboundaryₗ S k) from rfl] at ha
    obtain ⟨g, hg⟩ := ha
    have hcob : (a.1.1 : SingularCochain X (k + 1)) = coboundary X k g.1 := by
      rw [← hg, relCoboundaryₗ_coe]
    rw [hcob]
    exact cap_relCoboundary0_mem_boundaries S g.1 (relCochain_vanish S g) z hz)

/-- **Computation rule for `D_z⁰`** on a relative cocycle: `[a] ↦ [a ⌢ z]`. -/
@[simp] theorem relativeDuality0_mk (k : ℕ) (z : SingularChain X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChains S k)
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    relativeDuality0 S k z hz (RelativeCohomology.mk S (k + 1) a)
      = Homology.mk X 0 ⟨cap a.1.1 z, Submodule.mem_top⟩ :=
  rfl

end SKEFTHawking.SingularRelativeDuality0
