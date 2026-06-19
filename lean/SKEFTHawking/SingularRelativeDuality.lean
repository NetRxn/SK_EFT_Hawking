import Mathlib
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularRelativeCohomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD3) — the relative Poincaré-duality map `D_z`

For a fixed (relative) fundamental cycle `z`, the chain-level relative-cap-cycle property
(`SingularRelativeCap.cap_relCycle_isCycle`) descends to a `ℤ/2`-linear map on relative cohomology
classes
  `D_z : Hᵏ(M, S) → Hₙ₋ₖ(M)`,    `[a] ↦ [a ⌢ z]`,
the core of Poincaré–Lefschetz duality. This mirrors `SingularCapHomology.capH` but descends the
**relative** cohomology quotient instead of the absolute one: a relative cocycle caps the relative
cycle `z` to an **absolute** cycle (`cap_relCycle_isCycle`), and a relative coboundary caps `z` to an
absolute **boundary** (`cap_leibniz` + `cap_subspaceChain_eq_zero`, the relative→absolute descent).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap

namespace SKEFTHawking.SingularRelativeDuality

variable {X : TopCat} (S : Set X)

/-! ## §1. Extracting the absolute-cochain hypotheses from relative-cocycle membership -/

/-- A relative cochain `a ∈ relCochains S k` vanishes on every `S`-simplex: applying the annihilator
condition at the subspace chain `chainIncl S k (single τ 1) ∈ subspaceChains S k` and simplifying the
Kronecker pairing gives `a (simplexIncl S k τ) = 0`. (The `ha` hypothesis of `cap_relCycle_isCycle`.) -/
theorem relCochain_vanish {k : ℕ} (a : relCochains S k)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))) :
    a.1 (simplexIncl S k τ) = 0 := by
  have hmem : chainIncl S k (Finsupp.single τ 1) ∈ subspaceChains S k :=
    ⟨Finsupp.single τ 1, rfl⟩
  have h := a.2 _ hmem
  rw [chainIncl_single, kronecker_single, one_mul] at h
  exact h

/-- A relative cocycle `a ∈ ker (relCoboundaryₗ S k)` has vanishing absolute coboundary:
`relCoboundaryₗ S k a = 0` means `coboundary X k a.1.1 = 0` (via `relCoboundaryₗ_coe` and `Subtype.ext`).
(The `hδa` hypothesis of `cap_relCycle_isCycle`.) -/
theorem relCocycle_coboundary_zero {k : ℕ} (a : LinearMap.ker (relCoboundaryₗ S k)) :
    coboundaryₗ X k a.1.1 = 0 := by
  have h : relCoboundaryₗ S k a.1 = 0 := LinearMap.mem_ker.mp a.2
  have h2 : (relCoboundaryₗ S k a.1 : SingularCochain X (k + 1)) = 0 := by rw [h]; rfl
  rw [relCoboundaryₗ_coe] at h2
  exact h2

/-! ## §2. The cycle-level map and its descent to relative cohomology -/

/-- For a relative cocycle `a` and a relative cycle `z`, `cap a.1.1 z` is an absolute `(m+1)`-cycle. -/
theorem cap_relCocycle_isCycle {k m : ℕ} (a : LinearMap.ker (relCoboundaryₗ S k))
    (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    cap a.1.1 z ∈ cycles X (m + 1) := by
  show chainBoundary X m (cap a.1.1 z) = 0
  exact cap_relCycle_isCycle S a.1.1 (relCochain_vanish S a.1)
    (relCocycle_coboundary_zero S a) hz

/-- The underlying linear map `f ↦ cap f z` on absolute `k`-cochains, restricted to the relative
cocycles `ker (relCoboundaryₗ S k)` — the composite of the two subtype inclusions
(`ker → relCochains → Cᵏ`) with the cap-by-`z` map `(capₗ k (m+1)).flip z`. Linearity is structural
(composition of linear maps), avoiding the heavy `whnf` of an ad-hoc `Subtype.ext` field proof. -/
noncomputable def capCochainₗ {k m : ℕ} (z : SingularChain X (k + m + 1)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] SingularChain X (m + 1) :=
  ((capₗ k (m + 1)).flip z).comp
    ((relCochains S k).subtype.comp (LinearMap.ker (relCoboundaryₗ S k)).subtype)

@[simp] theorem capCochainₗ_apply {k m : ℕ} (z : SingularChain X (k + m + 1))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    capCochainₗ S z a = cap a.1.1 z := rfl

/-- For a fixed relative cycle `z`, the map `a ↦ a ⌢ z` lands in the absolute `(m+1)`-cycles
(`cap_relCocycle_isCycle`), packaged as a `ℤ/2`-linear map `ker (relCoboundaryₗ S k) → cycles X (m+1)`
by cod-restricting `capCochainₗ`. -/
noncomputable def capRelCocycleₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] cycles X (m + 1) :=
  (capCochainₗ S z).codRestrict (cycles X (m + 1)) (fun a => cap_relCocycle_isCycle S a z hz)

@[simp] theorem capRelCocycleₗ_coe {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    (capRelCocycleₗ S z hz a : SingularChain X (m + 1)) = cap a.1.1 z := rfl

/-- For a fixed relative cycle `z`, the map `a ↦ [a ⌢ z]` on the relative cocycles, packaged as a
`ℤ/2`-linear map `ker (relCoboundaryₗ S k) → H_{m+1}` — the composition of `capRelCocycleₗ` with the
homology quotient map. The descent-ready cycle-level map. -/
noncomputable def relDualityₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] Homology X (m + 1) :=
  ((boundaries X (m + 1)).submoduleOf (cycles X (m + 1))).mkQ.comp (capRelCocycleₗ S z hz)

@[simp] theorem relDualityₗ_apply {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    relDualityₗ S z hz a = Homology.mk X (m + 1) (capRelCocycleₗ S z hz a) := rfl

/-! ## §3. Well-definedness modulo relative coboundaries -/

/-- `chainBoundary` commutes with a degree cast (generic re-indexing helper, proved by `subst`):
the boundary of a cast chain is the cast of the boundary. -/
private theorem chainBoundary_cast {a b : ℕ} (z : SingularChain X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) :
    chainBoundary X b (e ▸ z) = eb ▸ chainBoundary X a z := by
  subst eb
  rw [show e = rfl from rfl]

/-- A cast of a subspace chain is a subspace chain (transport of membership along a degree cast). -/
private theorem subspaceChains_cast {a b : ℕ} (c : SingularChain X a) (eb : a = b)
    (hc : c ∈ subspaceChains S a) : (eb ▸ c) ∈ subspaceChains S b := by
  subst eb; exact hc

/-- **The relative cohomology-argument descent fact**: for a `j`-cochain `g` **vanishing on `S`** and a
**relative cycle** `z` (its boundary `∂z` a subspace chain), the coboundary `δg` caps `z` to an absolute
`(m+1)`-**boundary**. `cap_leibniz` gives `∂(g ⌢ z) = (δg) ⌢ z + g ⌢ (∂z)`; the last term dies because
`g` kills subspace chains (`cap_subspaceChain_eq_zero`, `∂z ∈ subspaceChains`), so `(δg) ⌢ z = ∂(g ⌢ z)`
is a boundary. The relative analogue of `SingularCapHomology.cap_coboundary_cycle_mem_boundaries` — here
the middle term `g ⌢ (∂z)` vanishes by relativity rather than by `∂z = 0`. -/
theorem cap_relCoboundary_mem_boundaries {j m : ℕ} (g : SingularCochain X j)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk j))),
      g (simplexIncl S j τ) = 0)
    (z : SingularChain X (j + 1 + m + 1))
    (hz : chainBoundary X (j + 1 + m) z ∈ subspaceChains S (j + 1 + m)) :
    cap (m := m + 1) (coboundary X j g) z ∈ boundaries X (m + 1) := by
  -- Cast `z` into `cap_leibniz`'s convention degree `j + (m+1) + 1`; the casts cancel at the end.
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  refine ⟨cap (m := m + 2) g (e ▸ z), ?_⟩
  have hleib := cap_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  -- The middle term `g ⌢ (∂(e ▸ z))` vanishes: `∂(e ▸ z)` is a subspace chain and `g` kills them.
  have ed : j + 1 + m = j + (m + 1) := by omega
  have hmid : cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) = 0 := by
    apply cap_subspaceChain_eq_zero S g hg
    rw [chainBoundary_cast z e ed]
    exact subspaceChains_cast S _ ed hz
  rw [hmid, add_zero] at hleib
  -- `h ▸ (e ▸ z) = z`: the composite cast is over the defeq `j + 1 + m + 1 = j + 1 + (m + 1)`.
  have hcancel : (h ▸ (e ▸ z) : SingularChain X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rw [hcancel] at hleib
  exact hleib

/-! ## §4. The relative Poincaré-duality map `D_z` on relative cohomology -/

/-- **The relative Poincaré-duality map** `D_z : Hᵏ(M, S) → Hₙ₋ₖ(M)`, `[a] ↦ [a ⌢ z]`, for a fixed
relative fundamental cycle `z` (an absolute `(k+m+1)`-chain whose boundary `∂z` is a subspace chain).
Well-defined: a relative cocycle caps `z` to an absolute cycle (`cap_relCycle_isCycle`, descending the
cycle quotient via `relDualityₗ`), and a relative coboundary caps `z` to an absolute boundary
(`cap_relCoboundary_mem_boundaries`, descending the relative-cohomology quotient via `liftQ`). The
class-level core of Poincaré–Lefschetz duality, descended from the chain-level brick 72c-PD2. -/
noncomputable def relativeDuality (k m : ℕ) (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    RelativeCohomology S k →ₗ[ZMod 2] Homology X (m + 1) :=
  Submodule.liftQ _ (relDualityₗ S z hz) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      capRelCocycleₗ_coe]
    -- Reduce to: `cap a.1.1 z` is a `(m+1)`-boundary, with `a.1` a relative coboundary.
    cases k with
    | zero =>
        rw [show relCoboundaryRange S 0 = (⊥ : Submodule (ZMod 2) (relCochains S 0)) from rfl,
          Submodule.mem_bot] at ha
        have h0 : (a.1.1 : SingularCochain X 0) = 0 := by rw [ha]; rfl
        rw [h0]
        have hz0 : cap (0 : SingularCochain X 0) z = (0 : SingularChain X (m + 1)) := by
          rw [← capₗ_apply, map_zero]; rfl
        rw [hz0]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show relCoboundaryRange S (j + 1) = LinearMap.range (relCoboundaryₗ S j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        -- `a = δg` is a relative coboundary; `a.1.1 = coboundary X j g.1`.
        have hcob : (a.1.1 : SingularCochain X (j + 1)) = coboundary X j g.1 := by
          rw [← hg, relCoboundaryₗ_coe]
        rw [hcob]
        -- `(δg) ⌢ z = ∂(g ⌢ z)` is a boundary since `g` vanishes on `S` and `∂z` is a subspace chain.
        exact cap_relCoboundary_mem_boundaries S g.1 (relCochain_vanish S g) z hz)

/-- **Computation rule for `D_z`** on a relative cocycle: the duality map sends the relative cohomology
class `[a]` of a relative cocycle `a` to the homology class of the absolute cycle `a ⌢ z`. The
`liftQ` β-reduction — the definitional content of `relativeDuality` at a representative. -/
@[simp] theorem relativeDuality_mk (k m : ℕ) (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    relativeDuality S k m z hz (RelativeCohomology.mk S k a)
      = Homology.mk X (m + 1) ⟨cap a.1.1 z, cap_relCocycle_isCycle S a z hz⟩ :=
  rfl

end SKEFTHawking.SingularRelativeDuality
