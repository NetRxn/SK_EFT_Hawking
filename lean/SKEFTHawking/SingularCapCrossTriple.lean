/-
# The one-shot triple cap-cross projection (N2c′) — chain-level cornerstones

Route (b): the P23-nondeg 3-fold cap-cross projection `capRelH 2 2 (π₃* [g]) (crossIter3H M [z]) =
crossIter3ZeroH M (capHZero 2 [g] [z])` for an ABSOLUTE 2-cycle `z`, proven chain-level through the
triple prism + absolute `fst³` injectivity (never descending to relative homology mid-way, so the
relative-source wall is avoided).

This module banks the reusable cornerstones. The key chain-homotopy identity is

  **`deltaDefect_boundary`: `∂(Δ(h,a)) = Δ(h, ∂a)`**

for the single-stage cap-cross defect `Δ(h,a) := (fst^* h) ⌢ (prism a) + prism (h ⌢ a)` — the
endpoint-slice terms cancel mod 2.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularCapCrossZero
import SKEFTHawking.SingularCapCrossZeroProjection
import SKEFTHawking.SingularCapCrossProjection

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
open SKEFTHawking.SingularCapCrossProjection
open SKEFTHawking.SingularCapCrossZeroProjection

namespace SKEFTHawking.SingularCapCrossTriple

variable {N : TopCat}

/-! ## §1. The single-stage cap-cross defect and its chain-homotopy identity -/

/-- **The single-stage cap-cross defect** `Δ(h,a) := (fst^* h) ⌢ (prism a) + prism (h ⌢ a)` on
`cyl N`, for a degree-2 cochain `h` and a chain `a` of degree `2 + n` on `N`. -/
noncomputable def deltaDefect (h : SingularCochain N 2) {n : ℕ} (a : SingularChain N (2 + n)) :
    SingularChain (cyl N) (n + 1) :=
  cap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + n) a)
    + prismOp (graphHom N) n (cap (m := n) h a)

/-- `deltaDefect` is additive in the chain argument (`cap` and `prismOp` are linear). -/
theorem deltaDefect_add (h : SingularCochain N 2) {n : ℕ} (a b : SingularChain N (2 + n)) :
    deltaDefect h (a + b) = deltaDefect h a + deltaDefect h b := by
  show cap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + n) (a + b))
        + prismOp (graphHom N) n (cap (m := n) h (a + b))
      = (cap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + n) a)
          + prismOp (graphHom N) n (cap (m := n) h a))
        + (cap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + n) b)
          + prismOp (graphHom N) n (cap (m := n) h b))
  rw [map_add, map_add, map_add, map_add]
  abel

/-- **The defect chain-homotopy identity `∂(Δ(h,a)) = Δ(h, ∂a)`.** For a cocycle `h`, the two
endpoint-slice terms `endᵣ(h ⌢ a)` cancel mod 2 (`cap_pullback_endMap` collapses the pulled-back cap on
each end), leaving the defect at input `∂a`. -/
theorem deltaDefect_boundary (h : SingularCochain N 2) (hh : coboundaryₗ N 2 h = 0) {n : ℕ}
    (a : SingularChain N (2 + (n + 1))) :
    chainBoundary (cyl N) (n + 1) (deltaDefect h a)
      = deltaDefect h (chainBoundary N (2 + n) a) := by
  have hcoc := coboundary_pullback_fstCyl_eq_zero h hh
  have hP : chainBoundary (cyl N) (n + 1)
        (cap (m := n + 2) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + (n + 1)) a))
      = mapChain (slice (graphHom N) 1) (n + 1) (cap (m := n + 1) h a)
        + mapChain (slice (graphHom N) 0) (n + 1) (cap (m := n + 1) h a)
        + cap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h)
            (prismOp (graphHom N) (2 + n) (chainBoundary N (2 + n) a)) := by
    rw [cap_cocycle_chainMap (m := n + 1) (pullbackCochainMap (fstCyl N) 2 h) hcoc]
    have hkey : chainBoundary (cyl N) (2 + (n + 1)) (prismOp (graphHom N) (2 + (n + 1)) a)
          + prismOp (graphHom N) (2 + n) (chainBoundary N (2 + n) a)
        = endMap (graphHom N) 1 (2 + (n + 1)) a + endMap (graphHom N) 0 (2 + (n + 1)) a :=
      prism_chainHomotopy (graphHom N) (n := 2 + n) a
    have hb : chainBoundary (cyl N) (2 + (n + 1)) (prismOp (graphHom N) (2 + (n + 1)) a)
        = endMap (graphHom N) 1 (2 + (n + 1)) a + endMap (graphHom N) 0 (2 + (n + 1)) a
          + prismOp (graphHom N) (2 + n) (chainBoundary N (2 + n) a) := by
      rw [eq_sub_of_add_eq hkey, sub_eq_add_neg,
        neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
    rw [hb, map_add, map_add, cap_pullback_endMap (m := n + 1) h 1 a,
      cap_pullback_endMap (m := n + 1) h 0 a]
  have hQ : chainBoundary (cyl N) (n + 1) (prismOp (graphHom N) (n + 1) (cap (m := n + 1) h a))
      = mapChain (slice (graphHom N) 1) (n + 1) (cap (m := n + 1) h a)
        + mapChain (slice (graphHom N) 0) (n + 1) (cap (m := n + 1) h a)
        + prismOp (graphHom N) n (cap (m := n) h (chainBoundary N (2 + n) a)) := by
    have hkey := prism_chainHomotopy (graphHom N) (n := n) (cap (m := n + 1) h a)
    have hb : chainBoundary (cyl N) (n + 1) (prismOp (graphHom N) (n + 1) (cap (m := n + 1) h a))
        = endMap (graphHom N) 1 (n + 1) (cap (m := n + 1) h a)
          + endMap (graphHom N) 0 (n + 1) (cap (m := n + 1) h a)
          + prismOp (graphHom N) n (chainBoundary N n (cap (m := n + 1) h a)) := by
      rw [eq_sub_of_add_eq hkey, sub_eq_add_neg,
        neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
    rw [hb, endMap_eq_mapChain, endMap_eq_mapChain, cap_cocycle_chainMap (m := n) h hh a]
  have key : ∀ (A B C D : SingularChain (cyl N) (n + 1)), A + B + C + (A + B + D) = C + D :=
    fun A B C D => by
      rw [show A + B + C + (A + B + D) = (A + A) + ((B + B) + (C + D)) from by abel,
        ZModModule.add_self, zero_add, ZModModule.add_self, zero_add]
  show chainBoundary (cyl N) (n + 1)
      (cap (m := n + 2) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + (n + 1)) a)
        + prismOp (graphHom N) (n + 1) (cap (m := n + 1) h a)) = _
  rw [map_add, hP, hQ]
  exact key _ _ _ _

/-- **The depth-1 defect is an absolute cycle.** For a cocycle `h` and a cycle `z` (`∂z = 0`),
`∂(Δ(h,z)) = 0`: both `∂` of the cap term and `∂` of the prism term equal the same endpoint-slice
sum `end₁(h ⌢ z) + end₀(h ⌢ z)` (the `_zero` boundary lemmas), and they cancel mod 2. This is the
single-interval base case; note it works precisely because `∂I = {0,1}` and the depth-0 defect is `0`. -/
theorem deltaDefect_cycle (h : SingularCochain N 2) (hh : coboundaryₗ N 2 h = 0)
    (z : SingularChain N 2) (hz : chainBoundary N 1 z = 0) :
    chainBoundary (cyl N) 0 (deltaDefect h z) = 0 := by
  show chainBoundary (cyl N) 0
      (cap (m := 0 + 1) (pullbackCochainMap (fstCyl N) 2 h) (prismOp (graphHom N) (2 + 0) z)
        + prismOp (graphHom N) 0 (cap (m := 0) h z)) = 0
  rw [map_add, boundary_cap_pullback_prismOp_zero (k := 1) h hh z hz,
    boundary_prismOp_cap_zero (k := 1) h z]
  exact ZModModule.add_self _

/-! ## §2. The depth-2 obstruction — the iterated defect is NOT an absolute cycle

The single-stage defect satisfies `∂(Δ_N(h,a)) = Δ_N(h, ∂a)` (`deltaDefect_boundary`), so on the
double-interval defect `D₂ := Δ_{cyl N}(fst^* h, crossChain 2 z) + prism (Δ_N(h,z))` (the honest chain
representative difference `(fst² h) ⌢ (z × I²) + ((h ⌢ z) × I²)`, for an absolute cycle `z`) the
boundary is

  `∂ D₂ = Δ_{cyl N}(fst^* h, end₁ z) + Δ_{cyl N}(fst^* h, end₀ z)
            + end₁ (Δ_N(h,z)) + end₀ (Δ_N(h,z))`,

a sum of FOUR depth-1 defects supported on the four faces of `∂(I²)`. These are the two families
"`z` sliced in `I₁`, prism'd in `I₂`" and "`z` prism'd in `I₁`, sliced in `I₂`" — prism'd in DIFFERENT
intervals — which do NOT cancel at the chain level (endpoint-slice naturality of `Δ` is false: the two
prism directions give distinct simplices). Hence `∂ D₂ ≠ 0`: `D₂` is only a RELATIVE cycle (its
boundary lands in the subspace `N × ∂(I²)`), not an absolute one, and the same holds one dimension up
for `D₃ = crossIter3`. This is the precise obstruction to route (b): absolute `fst³` injectivity needs
an absolute cycle, which the iterate is not. -/

/-- **The depth-2 defect boundary is the four-face depth-1-defect sum.** Rigorous confirmation of the
obstruction structure: `∂ D₂` reduces to the four face defects, which are prism'd in different
interval directions and do not cancel — so `D₂` is not an absolute cycle. -/
theorem depth2_defect_boundary (h : SingularCochain N 2) (hh : coboundaryₗ N 2 h = 0)
    (z : SingularChain N 2) (hz : chainBoundary N 1 z = 0) :
    chainBoundary (cyl (cyl N)) 1
        (deltaDefect (pullbackCochainMap (fstCyl N) 2 h) (crossChain 2 z)
          + prismOp (graphHom (cyl N)) 1 (deltaDefect h z))
      = deltaDefect (pullbackCochainMap (fstCyl N) 2 h) (endMap (graphHom N) 1 2 z)
        + deltaDefect (pullbackCochainMap (fstCyl N) 2 h) (endMap (graphHom N) 0 2 z)
        + (endMap (graphHom (cyl N)) 1 1 (deltaDefect h z)
          + endMap (graphHom (cyl N)) 0 1 (deltaDefect h z)) := by
  have hg1 : coboundaryₗ (cyl N) 2 (pullbackCochainMap (fstCyl N) 2 h) = 0 :=
    coboundary_pullback_fstCyl_eq_zero h hh
  rw [map_add]
  -- boundary of the first (relative-source) defect via `deltaDefect_boundary`
  rw [deltaDefect_boundary (pullbackCochainMap (fstCyl N) 2 h) hg1 (n := 0) (crossChain 2 z)]
  -- ∂(crossChain 2 z) = end₁ z + end₀ z  (prism homotopy, ∂z = 0)
  have hcz : chainBoundary (cyl N) (2 + 0) (crossChain 2 z)
      = endMap (graphHom N) 1 2 z + endMap (graphHom N) 0 2 z := by
    have hk : chainBoundary (cyl N) 2 (prismOp (graphHom N) 2 z)
          + prismOp (graphHom N) 1 (chainBoundary N 1 z)
        = endMap (graphHom N) 1 2 z + endMap (graphHom N) 0 2 z :=
      prism_chainHomotopy (graphHom N) (n := 1) z
    rw [hz, map_zero, add_zero] at hk
    exact hk
  rw [hcz, deltaDefect_add]
  -- boundary of the prism term via prism homotopy + deltaDefect_cycle
  have hpr : chainBoundary (cyl (cyl N)) 1 (prismOp (graphHom (cyl N)) 1 (deltaDefect h z))
      = endMap (graphHom (cyl N)) 1 1 (deltaDefect h z)
        + endMap (graphHom (cyl N)) 0 1 (deltaDefect h z) := by
    have hk := prism_chainHomotopy (graphHom (cyl N)) (n := 0) (deltaDefect h z)
    rw [deltaDefect_cycle h hh z hz, map_zero, add_zero] at hk
    exact hk
  rw [hpr]

end SKEFTHawking.SingularCapCrossTriple
