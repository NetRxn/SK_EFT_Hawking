/-
# Phase 5q.H — the welded `K3` carrier and the resolution piece `E` are CONNECTED

The closed-manifold top-homology theorem `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`
(`SingularFundamentalClass.localDegree_bijective` / `homologyTopEquivZMod2`, Hatcher 3.26) needs
`[PreconnectedSpace M]` — without it the top mod-2 homology is `(ℤ/2)^{#components}` and the
fundamental class is not the unique nonzero class. The welded `K3` carrier
(`KummerWeld.KummerK3 = Q ∪_{16×ℝP³} (16 × E)`) had no connectivity instance in tree; this module
supplies it, together with the `E`-side prerequisite.

Both proofs are the same two-piece argument, run twice:

* **§2** — `E = D²×D² ⊔_clutch D²×D²` is preconnected: each chart is the continuous image of the
  path-connected `Disk × Disk` (§1: a closed disc is convex), the two chart images cover `E`
  (`Quotient.mk` is surjective on the sum), and they share the base-equator weld point
  `chart0 (1,0) = chart1 (1,0)` (§2's `glued_one_zero`, an instance of the clutch identity
  `q₁ = p₁⁻¹`, `q₂ = p₁² p₂` at `p = (1,0)`).
* **§3** — `K3 = qImage ∪ ⋃₁₆ eImage c` is preconnected: `qImage` is the continuous image of the
  path-connected free quotient `Q` (`KummerPuncturedPathConn`), each `eImage c` is the continuous
  image of the now-preconnected `E`, and each meets `qImage` at the seam
  (`KummerWeld.weldMk_seam`, `ℝP³` being nonempty).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedPathConn

namespace SKEFTHawking.KummerWeldConnected

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)

/-! ## §1. The closed disc and the chart `D² × D²` are path-connected -/

/-- **The closed unit disc in `ℂ` is path-connected** — it is convex (`convex_closedBall`) and
nonempty. -/
instance instPathConnectedDisk : PathConnectedSpace Disk := by
  have hconv : Convex ℝ {z : ℂ | ‖z‖ ≤ 1} := by
    have h := convex_closedBall (0 : ℂ) 1
    simpa [Metric.closedBall, Complex.dist_eq] using h
  have hpc : IsPathConnected {z : ℂ | ‖z‖ ≤ 1} := hconv.isPathConnected ⟨0, by simp⟩
  exact isPathConnected_iff_pathConnectedSpace.mp hpc

/-- **The resolution chart `D² × D²` is path-connected** — a product of path-connected spaces
(`KummerH0T4.pathConnectedSpace_prod`, the pinned-Mathlib stand-in for the product instance). -/
instance instPathConnectedResChart : PathConnectedSpace ResChart :=
  SKEFTHawking.KummerH0T4.pathConnectedSpace_prod

/-! ## §2. The resolution piece `E` is preconnected -/

/-- **The base-equator weld point.** `p = (1, 0)` lies on the base equator (`‖1‖ = 1`) and its clutch
image is `(1⁻¹, 1² · 0) = (1, 0)`, so chart-0 and chart-1 both contain the class of `(1,0)`. The
concrete point that joins the two charts. -/
theorem glued_one_zero :
    glued ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk))
      ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk)) := by
  refine ⟨by simp, by simp, by simp⟩

/-- `chart0` and `chart1` cover `E`: every class is that of an `inl` or an `inr`. -/
theorem range_chart0_union_chart1 :
    Set.range chart0 ∪ Set.range chart1 = (Set.univ : Set ResE) := by
  refine Set.eq_univ_of_forall (fun e => ?_)
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := resSetoid) e
  cases a with
  | inl p => exact Or.inl ⟨p, rfl⟩
  | inr q => exact Or.inr ⟨q, rfl⟩

/-- **`E` is preconnected** — two path-connected chart images sharing the base-equator weld point
`chart0 (1,0) = chart1 (1,0)`, covering `E`. -/
instance instPreconnectedResE : PreconnectedSpace ResE := by
  have h0 : IsPreconnected (Set.range chart0) := by
    have := (isPreconnected_univ (α := ResChart)).image chart0 continuous_chart0.continuousOn
    rwa [Set.image_univ] at this
  have h1 : IsPreconnected (Set.range chart1) := by
    have := (isPreconnected_univ (α := ResChart)).image chart1 continuous_chart1.continuousOn
    rwa [Set.image_univ] at this
  have hpt : chart0 ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk))
      = chart1 ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk)) :=
    Quotient.sound (Or.inr glued_one_zero)
  have hmem0 : chart0 ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk)) ∈ Set.range chart0 := ⟨_, rfl⟩
  have hmem1 : chart0 ((⟨1, by simp⟩ : Disk), (⟨0, by simp⟩ : Disk)) ∈ Set.range chart1 :=
    ⟨_, hpt.symm⟩
  refine ⟨?_⟩
  rw [← range_chart0_union_chart1]
  exact IsPreconnected.union _ hmem0 hmem1 h0 h1

/-! ## §3. The welded `K3` carrier is preconnected -/

/-- The `c`-th `E`-copy's image in `K3`. -/
def eCopyImage (c : EIndex) : Set KummerK3 := Set.range (fun e : ResE => weldMk (Sum.inr (c, e)))

/-- `qImage` is preconnected — the continuous image of the path-connected free quotient `Q`. -/
theorem isPreconnected_qImage : IsPreconnected (qImage) := by
  have := (isPreconnected_univ (α := FreeQuotient)).image
    (fun q : FreeQuotient => weldMk (Sum.inl q))
    (continuous_weldMk.comp continuous_inl).continuousOn
  rwa [Set.image_univ] at this

/-- Each `E`-copy image is preconnected — the continuous image of the preconnected `E` (§2). -/
theorem isPreconnected_eCopyImage (c : EIndex) : IsPreconnected (eCopyImage c) := by
  have := (isPreconnected_univ (α := ResE)).image (fun e : ResE => weldMk (Sum.inr (c, e)))
    (continuous_weldMk.comp (continuous_inr.comp (Continuous.prodMk continuous_const
      continuous_id))).continuousOn
  rwa [Set.image_univ] at this

/-- **Every `E`-copy meets `Q` at the seam.** For any `r : ℝP³`, `weldMk (inl (qBdryMap c r))` lies
in both `qImage` and `eCopyImage c` (`KummerWeld.weldMk_seam`) — the sixteen `ℝP³` seams are exactly
the overlaps that make the weld connected. -/
theorem seamPoint_mem (c : EIndex) (r : RP3) :
    weldMk (Sum.inl (qBdryMap c r)) ∈ qImage ∩ eCopyImage c :=
  ⟨⟨qBdryMap c r, rfl⟩, ⟨bdryMapRP3 r, (weldMk_seam c r).symm⟩⟩

/-- **`K3` is preconnected** — `qImage` (preconnected) together with each of the sixteen `E`-copy
images (preconnected, each meeting `qImage` at its `ℝP³` seam) covers the weld. This is the
connectivity instance the closed-manifold top-homology theorem
(`SingularFundamentalClass.localDegree_bijective`) requires on the `K3` carrier. -/
instance instPreconnectedKummerK3 : PreconnectedSpace KummerK3 := by
  classical
  obtain ⟨q₀⟩ : Nonempty FreeQuotient := inferInstance
  refine ⟨isPreconnected_of_forall (weldMk (Sum.inl q₀)) (fun y _ => ?_)⟩
  obtain ⟨a, rfl⟩ := weldMk_surjective y
  cases a with
  | inl q => exact ⟨qImage, Set.subset_univ _, ⟨q₀, rfl⟩, ⟨q, rfl⟩, isPreconnected_qImage⟩
  | inr p =>
      obtain ⟨r₀⟩ : Nonempty RP3 := inferInstance
      obtain ⟨hq, he⟩ := seamPoint_mem p.1 r₀
      refine ⟨qImage ∪ eCopyImage p.1, Set.subset_univ _, Or.inl ⟨q₀, rfl⟩, Or.inr ⟨p.2, rfl⟩,
        IsPreconnected.union _ hq he isPreconnected_qImage (isPreconnected_eCopyImage p.1)⟩

end SKEFTHawking.KummerWeldConnected
