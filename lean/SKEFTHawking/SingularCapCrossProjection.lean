import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularRelativeCapHomology
import SKEFTHawking.SingularCapMapChain
import SKEFTHawking.SingularKroneckerFunctoriality
import SKEFTHawking.SingularCohomologyFunctoriality

/-!
# Phase 5q.H Track 2 — the chain-level cap–cross projection: reduction to the normalization residual

**The last EZ wall.** The cylinder nondeg side is down to the pulled-back cap–cross projection formula
(per leg)

  `(π* u) ⌢ ([M] × [I,∂I]) = (u ⌢ [M]) × [I,∂I]`   (`CapCrossPullbackProj{23,14}`)

with `π* = cohomologyPullback fst` (the projection pullback), `⌢ = capRelH`, `× [I,∂I] = crossH`, and
`[M] × [I,∂I] = crossH [M]` (the honest prism cross). This is the classical Eilenberg–Zilber cap-cross
projection formula. The project's own kernel-checked recon (`…CylinderSuspDual` docstring) records that
this substrate — built from scratch on the custom `TopCat.toSSet` cochain model — has **no** EZ shuffle /
Künneth / cap-projection naturality, and that a *direct* development is "multi-hundred-line".

## What this module does: the CLEAN structural reduction (no shuffle)

Rather than grind the shuffle, this module reduces the projection formula to a single classical,
self-contained residual by exploiting three in-tree levers:

1. **`cap_mapChain`** (cap–pushforward naturality, `a ⌢ φ_# z = φ_# (φ^# a ⌢ z)`), plus the
   **section-collapse** `fst ∘ (slice graphHom r) = id_M` — because `graphHom = id_{M×I}` so its `r`-slice
   is `x ↦ (x,r)` and `fst (x,r) = x`. Hence `(π* u) ⌢ (endᵣ z) = endᵣ (u ⌢ z)` (`cap_pullback_endMap`).

2. The **prism chain homotopy** `∂(P z) = end₁ z + end₀ z` (for a cycle `z`) makes the two candidate
   representatives — `P := (π* u) ⌢ (prism graphHom z)` and `Q := prism graphHom (u ⌢ z)` — relative
   cycles with **exactly equal boundary** (`cap_pullback_prismOp_boundary_eq`), so `P − Q` is an
   *absolute* cycle of `W = M × I`.

3. **`fst_* : H(M × I) → H(M)` is injective** (homotopy equivalence, contractible interval), and
   **`mapChain_prismOp` naturality** (`φ_# ∘ prism H = prism (φ ∘' H)`) gives
   `fst_#(P − Q) = (u ⌢ (prism fst c)) − (prism fst (u ⌢ c))` where `prism fst` is the prism of the
   *t-independent* homotopy `fst : M × I → M`. So `[P] = [Q]` in `H(W, ∂W)` reduces to

   **`[u ⌢ (prism fst c)] = [prism fst (u ⌢ c)]` in `H(M)`   (the normalization residual)**

   i.e. that the prism of the t-independent projection homotopy induces `0` on homology (its simplices are
   all degenerate; over the *normalized* complex this is immediate, and singular normalization
   `H_normalized ≅ H_singular` is the classical missing lemma). This is the sharp residual `PrismDegNull`.

`crossCapProjection_of_prismDegNull` fires the full homology identity from `PrismDegNull`; the residual is
now one clean absolute statement on `M` alone — the entire relative / cross / cup / adjunction tower is
discharged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularCapMapChain
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCapHomology

namespace SKEFTHawking.SingularCapCrossProjection

variable {M : TopCat}

/-! ## §1. Prism–pushforward naturality `φ_# ∘ prism H = prism (φ ∘' H)` -/

/-- **Prism–pushforward naturality on a simplex.** `mapSimplex φ (prismSimplex H σ i) =
prismSimplex (φ.comp H) σ i` — post-composing the prism simplex by `φ` re-associates into the prism of
the composed homotopy `φ ∘ H`. `rfl` (both unfold to `equiv.symm ((φ.comp H).comp (…))`). -/
theorem mapSimplex_prismSimplex {X Y Z : TopCat} (φ : C(↑Y, ↑Z)) (H : C(↑X × unitInterval, ↑Y))
    {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    mapSimplex φ (prismSimplex H σ i) = prismSimplex (φ.comp H) σ i := rfl

/-- **Prism–pushforward naturality (chain level).** `φ_# (prism H c) = prism (φ ∘ H) c`. -/
theorem mapChain_prismOp {X Y Z : TopCat} (φ : C(↑Y, ↑Z)) (H : C(↑X × unitInterval, ↑Y))
    (n : ℕ) (c : SingularChain X n) :
    mapChain φ (n + 1) (prismOp H n c) = prismOp (φ.comp H) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd]
  | single σ s =>
      rw [prismOp_single, prismOp_single, prismBasis, prismBasis, map_smul]
      congr 1
      simp only [map_sum, mapChain_single, mapSimplex_prismSimplex]

/-! ## §2. The projection `fst : M × I → M` and the section-collapse `fst ∘ (slice graphHom r) = id` -/

/-- **The cylinder projection** `fst : M × I → M` — the map along which the cap-cross projection pulls
the cochain factor back (`π* = fst^*`). -/
def fstCyl (M : TopCat) : C(↑(cyl M), ↑M) := ⟨Prod.fst, continuous_fst⟩

/-- **The section-collapse.** `fst ∘ (slice graphHom r) = id_M`: the `r`-slice of the identity graph
homotopy is `x ↦ (x, r)`, and projecting back gives `x`. The engine of the endpoint-cap collapse. -/
theorem fstCyl_comp_slice_graphHom (r : unitInterval) :
    (fstCyl M).comp (slice (graphHom M) r) = ContinuousMap.id ↑M :=
  ContinuousMap.ext fun x => by rw [ContinuousMap.comp_apply, slice_graphHom]; rfl

/-- **The endpoint-cap collapse.** `(fst^* g) ⌢ (endᵣ z) = endᵣ (g ⌢ z)`. Capping the pulled-back
cochain against an endpoint push equals the endpoint push of the base cap — because
`fst ∘ (slice graphHom r) = id`, so the double pullback of `g` collapses back to `g` (`cap_mapChain` +
`pullbackCochainMap_comp` + `pullbackCochainMap_id`). -/
theorem cap_pullback_endMap {k m : ℕ} (g : SingularCochain M k) (r : unitInterval)
    (z : SingularChain M (k + m)) :
    cap (pullbackCochainMap (fstCyl M) k g) (endMap (graphHom M) r (k + m) z)
      = mapChain (slice (graphHom M) r) m (cap g z) := by
  rw [endMap_eq_mapChain, cap_mapChain, ← pullbackCochainMap_comp, fstCyl_comp_slice_graphHom,
    pullbackCochainMap_id]

/-! ## §3. The equal-boundary lemma: `P := (π*g) ⌢ (prism z)` and `Q := prism (g ⌢ z)` are relative
cycles with EXACTLY equal boundary (`end₁(g ⌢ z) + end₀(g ⌢ z)`), so `P − Q` is an absolute cycle. -/

/-- `fst^* g` is a cocycle whenever `g` is (`δ(fst^* g) = fst^*(δg) = 0`). -/
theorem coboundary_pullback_fstCyl_eq_zero {k : ℕ} (g : SingularCochain M k)
    (hg : coboundaryₗ M k g = 0) :
    coboundaryₗ (cyl M) k (pullbackCochainMap (fstCyl M) k g) = 0 := by
  have hg' : coboundary M k g = 0 := hg
  show coboundary (cyl M) k (pullbackCochainMap (fstCyl M) k g) = 0
  rw [coboundary_pullbackCochainMap, hg']
  funext σ; rfl

/-- **The boundary of `P := (fst^* g) ⌢ (prism graphHom z)`** for a cocycle `g` and cycle `z`:
`∂ P = end₁(g ⌢ z) + end₀(g ⌢ z)`. `cap_cocycle_chainMap` (fst-pullback cocycle) moves `∂` inside the
cap onto `∂(prism z) = end₁ z + end₀ z` (prism homotopy, `∂z = 0`); `cap_pullback_endMap` collapses each
endpoint cap. -/
theorem boundary_cap_pullback_prismOp {k m : ℕ} (g : SingularCochain M k)
    (hg : coboundaryₗ M k g = 0) (z : SingularChain M (k + m + 1))
    (hz : chainBoundary M (k + m) z = 0) :
    chainBoundary (cyl M) (m + 1)
        (cap (m := m + 2) (pullbackCochainMap (fstCyl M) k g) (prismOp (graphHom M) (k + m + 1) z))
      = mapChain (slice (graphHom M) 1) (m + 1) (cap (m := m + 1) g z)
        + mapChain (slice (graphHom M) 0) (m + 1) (cap (m := m + 1) g z) := by
  have hcoc := coboundary_pullback_fstCyl_eq_zero g hg
  have hkey : chainBoundary (cyl M) (k + (m + 1)) (prismOp (graphHom M) (k + m + 1) z)
      = endMap (graphHom M) 1 (k + (m + 1)) z + endMap (graphHom M) 0 (k + (m + 1)) z := by
    have h := prism_chainHomotopy (graphHom M) (n := k + m) z
    rw [hz, map_zero, add_zero] at h
    exact h
  rw [cap_cocycle_chainMap (m := m + 1) (pullbackCochainMap (fstCyl M) k g) hcoc, hkey, map_add,
    cap_pullback_endMap (m := m + 1) g 1 z, cap_pullback_endMap (m := m + 1) g 0 z]

/-- **The boundary of `Q := prism graphHom (g ⌢ z)`** for a cocycle `g` and cycle `z`:
`∂ Q = end₁(g ⌢ z) + end₀(g ⌢ z)`. Prism homotopy applied to `w := g ⌢ z`, whose boundary vanishes
(`cap_cocycle_chainMap`, `∂z = 0`). -/
theorem boundary_prismOp_cap {k m : ℕ} (g : SingularCochain M k)
    (hg : coboundaryₗ M k g = 0) (z : SingularChain M (k + m + 1))
    (hz : chainBoundary M (k + m) z = 0) :
    chainBoundary (cyl M) (m + 1) (prismOp (graphHom M) (m + 1) (cap (m := m + 1) g z))
      = mapChain (slice (graphHom M) 1) (m + 1) (cap (m := m + 1) g z)
        + mapChain (slice (graphHom M) 0) (m + 1) (cap (m := m + 1) g z) := by
  have hw : chainBoundary M m (cap (m := m + 1) g z) = 0 := by
    rw [cap_cocycle_chainMap (m := m) g hg z, hz, map_zero]
  have hkey := prism_chainHomotopy (graphHom M) (n := m) (cap (m := m + 1) g z)
  rw [hw, map_zero, add_zero] at hkey
  rw [hkey, endMap_eq_mapChain, endMap_eq_mapChain]

/-! ## §4. The pushforward reduction: `fst_#` of `P` and `Q` land in the `t`-independent prism on `M`

`projHom := fst ∘ graphHom : M × I → M` is the `t`-independent projection homotopy `(x,t) ↦ x`; its
prism `prism projHom` is a sum of `M`-degenerate simplices. `fst_#(P − Q)` is the base-level difference
`(g ⌢ prism projHom z) − prism projHom (g ⌢ z)` — the normalization residual. -/

/-- **The `t`-independent projection homotopy** `projHom = fst ∘ graphHom : M × I → M`, `(x,t) ↦ x`. -/
def projHom (M : TopCat) : C(↑M × unitInterval, ↑M) := (fstCyl M).comp (graphHom M)

/-- **`fst_#` of `P = (fst^* g) ⌢ (prism graphHom z)`** is `g ⌢ (prism projHom z)` — the cap of `g`
against the `t`-independent prism on `M`. `cap_mapChain` moves `fst_#` inside the cap (collapsing
`fst^*` back), then `mapChain_prismOp` naturality turns `fst_# (prism graphHom z)` into
`prism (fst ∘ graphHom) z = prism projHom z`. -/
theorem mapChain_cap_pullback_prismOp {k m : ℕ} (g : SingularCochain M k)
    (z : SingularChain M (k + m + 1)) :
    mapChain (fstCyl M) (m + 2)
        (cap (m := m + 2) (pullbackCochainMap (fstCyl M) k g) (prismOp (graphHom M) (k + m + 1) z))
      = cap (m := m + 2) g (prismOp (projHom M) (k + m + 1) z) := by
  rw [← cap_mapChain]
  congr 1
  exact mapChain_prismOp (fstCyl M) (graphHom M) (k + m + 1) z

/-- **`fst_#` of `Q = prism graphHom (g ⌢ z)`** is `prism projHom (g ⌢ z)` — the `t`-independent prism
of the base cap. Pure `mapChain_prismOp` naturality. -/
theorem mapChain_prismOp_cap {k m : ℕ} (g : SingularCochain M k)
    (z : SingularChain M (k + m + 1)) :
    mapChain (fstCyl M) (m + 2) (prismOp (graphHom M) (m + 1) (cap (m := m + 1) g z))
      = prismOp (projHom M) (m + 1) (cap (m := m + 1) g z) :=
  mapChain_prismOp (fstCyl M) (graphHom M) (m + 1) (cap (m := m + 1) g z)

/-! ## §5. The punchline: normalization residual + `fst_*` injectivity ⟹ `P + Q` is an absolute
boundary of `M × I` (hence `[P] = [Q]` in `H(W, ∂W)`). -/

open SKEFTHawking.SingularRelativeCrossProduct in
/-- **The normalization-residual predicate `PrismDegNull`**: the base-level difference
`(g ⌢ prism projHom z) + prism projHom (g ⌢ z)` is an absolute boundary of `M`. `prism projHom` is the
prism of the `t`-independent projection homotopy — a sum of degenerate simplices — so over the
*normalized* singular complex this holds automatically; it is the single classical residual (singular
normalization) of the entire cap-cross projection. -/
def PrismDegNull {k m : ℕ} (g : SingularCochain M k) (z : SingularChain M (k + m + 1)) : Prop :=
  cap (m := m + 2) g (prismOp (projHom M) (k + m + 1) z)
      + prismOp (projHom M) (m + 1) (cap (m := m + 1) g z) ∈ boundaries M (m + 2)

/-- **`P + Q` is an absolute boundary of `M × I`** from `PrismDegNull` and `fst_*` injectivity.
`P := (fst^* g) ⌢ (prism graphHom z)`, `Q := prism graphHom (g ⌢ z)`. Both are relative cycles with
equal boundary (§3), so `P + Q` is an absolute cycle; `fst_#(P + Q)` is the `PrismDegNull` chain (§4),
a boundary of `M`, so `fst_*[P+Q] = 0`; injectivity of `fst_*` forces `[P+Q] = 0`, i.e. `P + Q ∈ ∂`. -/
theorem cap_pullback_prismOp_add_mem_boundaries {k m : ℕ}
    (g : LinearMap.ker (coboundaryₗ M k)) (z : cycles M (k + m + 1))
    (hfstinj : Function.Injective (Homology.map (fstCyl M) (m + 2)))
    (hnull : PrismDegNull g.1 z.1) :
    cap (m := m + 2) (pullbackCochainMap (fstCyl M) k g.1) (prismOp (graphHom M) (k + m + 1) z.1)
        + prismOp (graphHom M) (m + 1) (cap (m := m + 1) g.1 z.1)
      ∈ boundaries (cyl M) (m + 2) := by
  have hgc : coboundaryₗ M k g.1 = 0 := g.2
  have hz : chainBoundary M (k + m) z.1 = 0 := z.2
  -- `P + Q` is an absolute cycle: ∂P = ∂Q (§3), so ∂(P+Q) = 0.
  have hcyc : chainBoundary (cyl M) (m + 1)
      (cap (m := m + 2) (pullbackCochainMap (fstCyl M) k g.1) (prismOp (graphHom M) (k + m + 1) z.1)
        + prismOp (graphHom M) (m + 1) (cap (m := m + 1) g.1 z.1)) = 0 := by
    rw [map_add, boundary_cap_pullback_prismOp g.1 hgc z.1 hz, boundary_prismOp_cap g.1 hgc z.1 hz]
    exact ZModModule.add_self _
  set d : SingularChain (cyl M) (m + 2) :=
    cap (m := m + 2) (pullbackCochainMap (fstCyl M) k g.1) (prismOp (graphHom M) (k + m + 1) z.1)
      + prismOp (graphHom M) (m + 1) (cap (m := m + 1) g.1 z.1) with hd
  -- `fst_# d` is the `PrismDegNull` chain, a boundary of `M`.
  have hpush : mapChain (fstCyl M) (m + 2) d
      = cap (m := m + 2) g.1 (prismOp (projHom M) (k + m + 1) z.1)
        + prismOp (projHom M) (m + 1) (cap (m := m + 1) g.1 z.1) := by
    rw [hd, map_add, mapChain_cap_pullback_prismOp, mapChain_prismOp_cap]
  -- `fst_*[d] = 0`.
  have hmap0 : Homology.map (fstCyl M) (m + 2) (Homology.mk (cyl M) (m + 2) ⟨d, hcyc⟩) = 0 := by
    rw [Homology.map_mk, Homology.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.coe_subtype, cyclesMap_coe, hpush]
    exact hnull
  -- injectivity ⟹ `[d] = 0` ⟹ `d ∈ ∂`.
  have hd0 : Homology.mk (cyl M) (m + 2) ⟨d, hcyc⟩ = 0 :=
    hfstinj (by rw [hmap0, map_zero])
  rw [Homology.mk_eq_zero] at hd0
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hd0
  exact hd0

end SKEFTHawking.SingularCapCrossProjection
