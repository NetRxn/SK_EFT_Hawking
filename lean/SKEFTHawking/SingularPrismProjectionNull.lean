import Mathlib
import SKEFTHawking.SingularCapCrossProjection

/-!
# Phase 5q.H Track 2 — the normalization residual, collapsed to ONE classical statement

The predecessor's B2 reduction (`SingularCapCrossProjection`) discharged both cap-cross pullback
projections `CapCrossPullbackProj{23,14}` conditionally on the single normalization residual

  `PrismDegNull g z := cap g (prismOp projHom z) + prismOp projHom (cap g z) ∈ boundaries M`

where `projHom = fstCyl ∘ graphHom : M × I → M`, `(x,t) ↦ x`, is the **`t`-independent projection
homotopy** (`graphHom = id_{M×I}`, `fstCyl = fst`). Both time-slices of `projHom` are the identity, so
its prism `prismOp projHom` is the prism of the *constant/identity* self-homotopy of `M`; its simplices
are all degenerate (`prismSimplex projHom σ i = σ ∘ (affine degeneracy) = σ ∘ sᵢ`), and degenerate
cycles are null-homologous — the classical singular normalization theorem `H_normalized ≅ H_singular`.

## What this module does: the SHARP collapse

`PrismDegNull` is a two-term cap combination gated on a *cocycle* `g`. This module collapses it to a
single, clean, universally-quantified classical statement — **`PrismProjKillsHomology`: the
`t`-independent projection prism sends every cycle to a boundary** — and proves

  `PrismProjKillsHomology M ⟹ ∀ (cocycle g) (cycle z), PrismDegNull g z`.

The reduction is elementary once `PrismProjKillsHomology` is in hand:

* **Both time-slices are `id`** (`endMap_projHom`, since `projHom` ignores `t`), so by the prism chain
  homotopy `∂(prismOp projHom z) = end₁ z + end₀ z = z + z = 0`: `prismOp projHom` preserves cycles.
* **Term `prismOp projHom (cap g z)`** — `cap g z` is a cycle (cocycle `g`, `cap_cocycle_chainMap`), so
  `PrismProjKillsHomology` sends it into `boundaries` directly.
* **Term `cap g (prismOp projHom z)`** — `prismOp projHom z` is a cycle, so a boundary `= ∂b` by
  `PrismProjKillsHomology`; capping the *cocycle* `g` against `∂b` is `∂(cap g b)`
  (`cap_cocycle_chainMap`), again a boundary.

So the *entire* Track-2 nondeg residual is now exactly one named classical statement
(`PrismProjKillsHomology` = singular normalization: the identity-homotopy prism kills homology).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularCapCrossProjection

namespace SKEFTHawking.SingularPrismProjectionNull

variable {M : TopCat}

/-! ## §1. Both time-slices of `projHom` are the identity -/

/-- **Every time-slice of `projHom` is the identity simplex.** `projHom (x,t) = x` ignores the homotopy
time, so `endSimplex projHom r σ = σ`: the double `Equiv.symm ∘ Equiv` collapses once the composite
`projHom ∘ (σ.prodMk (const r))` is recognised as `σ` itself (`fst` of a `prodMk`). -/
theorem endSimplex_projHom {n : ℕ} (r : unitInterval)
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk n))) :
    endSimplex (projHom M) r σ = σ := by
  rw [endSimplex,
    show (projHom M).comp
        (((M.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).prodMk (ContinuousMap.const _ r))
      = (M.toSSetObjEquiv (op (SimplexCategory.mk n))) σ from ContinuousMap.ext fun a => rfl]
  exact (M.toSSetObjEquiv (op (SimplexCategory.mk n))).symm_apply_apply σ

/-- **The endpoint map of `projHom` is the identity** (both slices `id`, pointwise). -/
theorem endMap_projHom {n : ℕ} (r : unitInterval) (c : SingularChain M n) :
    endMap (projHom M) r n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add c d hc hd => rw [map_add, hc, hd]
  | single σ a => rw [endMap_single, endSimplex_projHom]

/-! ## §2. `prismOp projHom` preserves cycles -/

/-- **`prismOp projHom` sends cycles to cycles.** For a cycle `z` the prism chain homotopy gives
`∂(prismOp projHom z) = end₁ z + end₀ z = z + z = 0` (both endpoints are `id`, `endMap_projHom`). -/
theorem chainBoundary_prismOp_projHom {n : ℕ} (z : SingularChain M (n + 1))
    (hz : chainBoundary M n z = 0) :
    chainBoundary M (n + 1) (prismOp (projHom M) (n + 1) z) = 0 := by
  have h := prism_chainHomotopy (projHom M) (n := n) z
  rw [hz, map_zero, add_zero] at h
  rw [h, endMap_projHom, endMap_projHom]
  exact ZModModule.add_self z

/-! ## §3. The normalization statement and the reduction of `PrismDegNull` -/

/-- **`PrismProjKillsHomology`: the `t`-independent projection prism sends every cycle to a boundary.**
This is the single classical residual (singular normalization / "degenerate cycles bound") to which the
entire Track-2 nondeg side reduces. `prismOp projHom` is the prism of the identity self-homotopy of `M`,
all of whose simplices are degenerate; over the normalized complex it induces `0` on homology. -/
def PrismProjKillsHomology (M : TopCat) : Prop :=
  ∀ (n : ℕ) (w : SingularChain M (n + 1)), chainBoundary M n w = 0 →
    prismOp (projHom M) (n + 1) w ∈ boundaries M (n + 2)

/-- **`PrismProjKillsHomology ⟹ PrismDegNull` (for every cocycle `g` and cycle `z`).** The two-term cap
combination of `PrismDegNull` is a sum of two boundaries: `prismOp projHom (cap g z)` lands in
`boundaries` directly (`cap g z` is a cycle), and `cap g (prismOp projHom z)` is `cap g (∂b) = ∂(cap g b)`
since `prismOp projHom z` is a cycle-hence-boundary and `g` is a cocycle (`cap_cocycle_chainMap`). -/
theorem prismDegNull_of_kills (hkill : PrismProjKillsHomology M)
    {k m : ℕ} (g : SingularCochain M k) (hg : coboundaryₗ M k g = 0)
    (z : SingularChain M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0) :
    PrismDegNull g z := by
  -- Term A: `cap g (prismOp projHom z) ∈ boundaries` (`prismOp projHom z` is a boundary `∂b`).
  obtain ⟨b, hb⟩ := hkill (k + m) z hz
  have hA : cap (m := m + 2) g (prismOp (projHom M) (k + m + 1) z) ∈ boundaries M (m + 2) := by
    refine ⟨cap (m := m + 3) g b, ?_⟩
    rw [cap_cocycle_chainMap (m := m + 2) g hg b]
    exact congrArg (cap (m := m + 2) g) hb
  -- Term B: `prismOp projHom (cap g z) ∈ boundaries` (cap g z is a cycle).
  have hcapcyc : chainBoundary M m (cap (m := m + 1) g z) = 0 := by
    rw [cap_cocycle_chainMap g hg z, hz, map_zero]
  have hB : prismOp (projHom M) (m + 1) (cap (m := m + 1) g z) ∈ boundaries M (m + 2) :=
    hkill m (cap (m := m + 1) g z) hcapcyc
  exact Submodule.add_mem _ hA hB

end SKEFTHawking.SingularPrismProjectionNull
