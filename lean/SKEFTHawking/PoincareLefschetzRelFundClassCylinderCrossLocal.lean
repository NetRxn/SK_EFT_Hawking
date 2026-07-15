/-
# Phase 5q.H (W-A arm 4) — the LOCAL cross map `H_{p+1}(M, M∖σ) → H_{p+2}(M×I, (M×I)∖x)`

The route-B infrastructure for the terminal `hcls` obligation. The frozen reduction
`PoincareLefschetzRelFundClassCylinderCrossRestrict.restrictBd_cylFundClassCandidate` exposes the
candidate's restriction at an interior point `x = (σ,t)` as the class of the SAME prism chain
`prismOp graphHom z` (`z` a cycle rep of `[M]`), now viewed rel the puncture `{x}ᶜ`. This module
builds the honest *local* cross product that this prism chain is the image of: a well-defined linear
map

  `crossHloc : H_{p+1}(M, M∖σ) → H_{p+2}(M×I, (M×I)∖x)`,     `[c] ↦ [prismOp graphHom c]`,

the puncture-relative analogue of `SingularRelativeCrossProduct.crossH` (whose target subspace is
the whole boundary `∂W = M×∂I`). Well-definedness rests on the **prism-rel-puncture engine**
`SingularRelativeHomotopyInvariance.prismOp_mem_subspaceChains`: the prism carries `{σ}ᶜ`-chains of
`M` to `{(σ,t)}ᶜ`-chains of `M×I` (because `a ≠ σ ⟹ (a,s) ≠ (σ,t)`), plus the endpoint slices
`M×{0}`, `M×{1}` land in `{x}ᶜ` (because `t ∉ {0,1}`). The construction is a faithful double-`mapQ`
mirror of `crossH`, one relative level up on the source.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the local cross chain map** `crossRelChainLM : C(M, M∖σ) → C(M×I, (M×I)∖x)` (`prismOp`
  descended through the source `{σ}ᶜ`-quotient by the puncture engine), with its `_mk` rule.
* **§2 — well-definedness on homology**: `crossRelChainLM` carries relative cycles to relative cycles
  (`prism_chainHomotopy` + endpoint-slice/puncture containments) and relative boundaries to relative
  boundaries — mirroring `crossChainLM_mem_relCycles`/`crossChainLM_mem_relBoundaries`.
* **§3 — the homology-level local cross** `crossHloc` (the second `mapQ` descent) and its `_mk` rule.

The residual crux (a separate deep arc) is the **injectivity** of `crossHloc` at every interior
point — equivalently the interior local-Künneth nonvanishing `[prismOp graphHom z] ≠ 0`. This module
provides the well-defined map that injectivity is *about* and the naturality wiring the cylinder
consumer needs; the injectivity itself (via a chart-excision product computation or a chain-level
retraction) is named, not faked.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularRelativeHomotopyInvariance

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeHomotopyInvariance (prismOp_mem_subspaceChains)

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal

noncomputable section

variable {M : TopCat} {x : ↑(cyl M)}

/-! ## §1. The local cross chain map `C(M, M∖σ) → C(M×I, (M×I)∖x)` -/

/-- **The local cross chain map** `C_{p+1}(M, M∖σ) → C_{p+2}(M×I, (M×I)∖x)`, the prism operator
`prismOp graphHom` descended through the source `{σ}ᶜ`-quotient. Well-defined because the prism
carries `{σ}ᶜ`-chains to `{x}ᶜ`-chains (`prismOp_mem_subspaceChains` with `hpunc`: `a ≠ σ ⟹
(a,s) ≠ x`). -/
noncomputable def crossRelChainLM
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ) :
    RelativeChain ({x.1}ᶜ : Set ↑M) (p + 1) →ₗ[ZMod 2]
      RelativeChain ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) :=
  Submodule.mapQ (subspaceChains ({x.1}ᶜ : Set ↑M) (p + 1))
    (subspaceChains ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)) (prismOp (graphHom M) (p + 1))
    (fun _c hc => prismOp_mem_subspaceChains (graphHom M) hpunc (p + 1) hc)

theorem crossRelChainLM_mk
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ) (c : SingularChain M (p + 1)) :
    crossRelChainLM hpunc p (RelativeChain.mk ({x.1}ᶜ : Set ↑M) (p + 1) c)
      = RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) (prismOp (graphHom M) (p + 1) c) :=
  Submodule.mapQ_apply _ _ _ _

/-! ## §2. Well-definedness on homology -/

/-- The local cross chain map carries **relative cycles to relative cycles**: for a relative cycle
`[c]` of `(M, M∖σ)` (`∂c` a `{σ}ᶜ`-chain), `∂(prismOp c) = end₁c + end₀c − prismOp(∂c)` is a
`{x}ᶜ`-chain — the endpoint slices land in `M×{0,1} ⊆ {x}ᶜ` and `prismOp(∂c)` in `{x}ᶜ` by the
puncture engine. -/
theorem crossRelChainLM_mem_relCycles
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ)
    (w : RelativeChain ({x.1}ᶜ : Set ↑M) (p + 1)) (hw : w ∈ relCycles ({x.1}ᶜ : Set ↑M) (p + 1)) :
    crossRelChainLM hpunc p w ∈ relCycles ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show crossRelChainLM hpunc p (RelativeChain.mk ({x.1}ᶜ : Set ↑M) (p + 1) c)
      ∈ LinearMap.ker (relBoundary ({x}ᶜ : Set ↑(cyl M)) (p + 1))
  rw [LinearMap.mem_ker, crossRelChainLM_mk, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
  -- `∂c` is a `{σ}ᶜ`-chain (cycle condition)
  have hbd : chainBoundary M p c ∈ subspaceChains ({x.1}ᶜ : Set ↑M) p := by
    have : RelativeChain.mk ({x.1}ᶜ : Set ↑M) p (chainBoundary M p c) = 0 := by
      rw [← relBoundary_mk]; exact hw
    rwa [RelativeChain.mk_eq_zero_iff] at this
  have hkey := prism_chainHomotopy (graphHom M) c
  rw [eq_sub_of_add_eq hkey]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact endMap_mem_subspaceChains h1 (p + 1) c
  · exact endMap_mem_subspaceChains h0 (p + 1) c
  · exact prismOp_mem_subspaceChains (graphHom M) hpunc p hbd

/-- The local cross chain map carries **relative boundaries to relative boundaries**: for
`w = ∂d` rel `{σ}ᶜ`, `prismOp(∂d) = end₁d + end₀d − ∂(prismOp d)` is, mod the `{x}ᶜ`-quotient, the
relative boundary of `[prismOp d]` (endpoint slices die). -/
theorem crossRelChainLM_mem_relBoundaries
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ)
    (w : RelativeChain ({x.1}ᶜ : Set ↑M) (p + 1)) (hw : w ∈ relBoundaries ({x.1}ᶜ : Set ↑M) (p + 1)) :
    crossRelChainLM hpunc p w ∈ relBoundaries ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) := by
  obtain ⟨v, rfl⟩ := hw
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  show crossRelChainLM hpunc p (relBoundary ({x.1}ᶜ : Set ↑M) (p + 1)
      (RelativeChain.mk ({x.1}ᶜ : Set ↑M) (p + 1 + 1) d))
    ∈ relBoundaries ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)
  rw [relBoundary_mk, crossRelChainLM_mk]
  -- goal: `[prismOp (∂d)]` rel `{x}ᶜ` is a relative boundary
  have hkey := prism_chainHomotopy (graphHom M) (n := p + 1) d
  have hmkadd : ∀ a b : SingularChain (cyl M) (p + 1 + 1),
      RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) (a + b)
        = RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) a
          + RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) b :=
    fun a b => map_add (Submodule.mkQ (subspaceChains ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1))) a b
  have hA : RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)
      (chainBoundary (cyl M) (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) d))
      ∈ relBoundaries ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) :=
    ⟨RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) d),
      relBoundary_mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) d)⟩
  have hD : RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)
      (endMap (graphHom M) 1 (p + 1 + 1) d + endMap (graphHom M) 0 (p + 1 + 1) d) = 0 := by
    rw [RelativeChain.mk_eq_zero_iff]
    exact Submodule.add_mem _ (endMap_mem_subspaceChains h1 _ d) (endMap_mem_subspaceChains h0 _ d)
  have hsum : RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)
        (chainBoundary (cyl M) (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) d))
      + RelativeChain.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1)
          (prismOp (graphHom M) (p + 1) (chainBoundary M (p + 1) d)) = 0 := by
    rw [← hmkadd, hkey]; exact hD
  rw [eq_neg_of_add_eq_zero_right hsum]
  exact Submodule.neg_mem _ hA

/-! ## §3. The homology-level local cross `H_{p+1}(M, M∖σ) → H_{p+2}(M×I, (M×I)∖x)` -/

/-- The local cross relative cycle: `[c] ↦ [prismOp graphHom c]` at the packaged-`relCycles` level. -/
noncomputable def crossRelCycleLoc
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ)
    (z : relCycles ({x.1}ᶜ : Set ↑M) (p + 1)) : relCycles ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) :=
  ⟨crossRelChainLM hpunc p (z : RelativeChain ({x.1}ᶜ : Set ↑M) (p + 1)),
    crossRelChainLM_mem_relCycles h1 h0 hpunc p z z.2⟩

/-- **The homology-level local cross product** `× [I, ∂I]_loc : H_{p+1}(M, M∖σ) → H_{p+2}(M×I,
(M×I)∖x)`, `[z] ↦ [prismOp graphHom z]`. Well-defined on homology by `crossRelChainLM_mem_relCycles`
(rel cycles ↦ rel cycles) and `crossRelChainLM_mem_relBoundaries` (rel boundaries ↦ rel boundaries).
The puncture-relative analogue of `SingularRelativeCrossProduct.crossH`. -/
noncomputable def crossHloc
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ) :
    RelativeHomology ({x.1}ᶜ : Set ↑M) (p + 1) →ₗ[ZMod 2]
      RelativeHomology ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) :=
  Submodule.mapQ _ _
    (LinearMap.restrict (crossRelChainLM hpunc p)
      (fun z hz => crossRelChainLM_mem_relCycles h1 h0 hpunc p z hz))
    (fun z hz => by
      rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
      exact crossRelChainLM_mem_relBoundaries h1 h0 hpunc p
        (z : RelativeChain ({x.1}ᶜ : Set ↑M) (p + 1))
        (by rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hz))

/-- **`crossHloc` on a relative cycle class**: it sends `[z]` to the class of `crossRelCycleLoc z`
(the concrete `[prismOp graphHom z]` representative rel `{x}ᶜ`). -/
theorem crossHloc_mk
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) ({x}ᶜ : Set ↑(cyl M)))
    (hpunc : ∀ a ∈ ({x.1}ᶜ : Set ↑M), ∀ s : unitInterval,
      graphHom M (a, s) ∈ ({x}ᶜ : Set ↑(cyl M))) (p : ℕ)
    (z : relCycles ({x.1}ᶜ : Set ↑M) (p + 1)) :
    crossHloc h1 h0 hpunc p (RelativeHomology.mk ({x.1}ᶜ : Set ↑M) (p + 1) z)
      = RelativeHomology.mk ({x}ᶜ : Set ↑(cyl M)) (p + 1 + 1) (crossRelCycleLoc h1 h0 hpunc p z) :=
  rfl

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
