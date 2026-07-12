/-
# Relative (pair) homotopy invariance of singular integral homology — the moving-puncture sub-device

The round-5 discharge plan for the S⁴ orientation freeze named a moving-puncture device: compare
local classes at nearby punctures by contracting the transition along a path, through relative
homology. Its honest reusable core is PAIR homotopy invariance: two maps of pairs
`f, g : (X, A) → (Y, B)` homotopic THROUGH maps of pairs induce the SAME map
`Hₙ(X, A; ℤ) → Hₙ(Y, B; ℤ)`. This module builds it with NO new prism: the in-tree signed prism
operator (`SingularHomotopyInvarianceInt.prismOpInt`) already restricts — a prism simplex over an
`A`-supported simplex realises inside `H(A × I) ⊆ B` (`range_realize_prismSimplex`), so the
absolute chain homotopy `∂P + P∂ = g_# − f_#` DESCENDS to the relative complex
(`prismOpInt_mem_subspaceChainsInt`), where the `P∂` term dies and `∂P` is a relative boundary.

The Euclidean moving-puncture instance (§3): for `p, q` in a convex `C ⊆ ℝ⁴`, the two translations
`y ↦ y − p` and `y ↦ y − q`, as maps of pairs `(ℝ⁴, Cᶜ) → (ℝ⁴, ℝ⁴∖0)`, induce the SAME map on
relative homology — the straight-line homotopy `y − ((1−t)p + tq)` never hits `0` on `Cᶜ × I`
because the moving puncture `(1−t)p + tq` stays inside `C` (convexity). This is the honest
device-shape for comparing `localHomologyAtPointIsoInt`-pinned generators at two punctures through
a common compact, entirely within ONE chart. (What it can NOT do — and why the round-5 freeze was
replaced rather than discharged: comparing generators pinned to two different `chartAt` charts
crosses Mathlib's per-point `stdOrthonormalBasis` choices; see `SphereFourOrientationDataInt`.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvarianceInt
import SKEFTHawking.SingularRelativeFunctorialityInt
import SKEFTHawking.SingularLocalModelChart

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularHomotopyInvarianceInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularPrism (prismSimplex)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularExcisionIsoInt (single_mem_subspaceChainsInt_of_subordinate)
open SKEFTHawking.SingularDisjointUnion (range_realize_simplexIncl)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularRelativeHomotopyInvarianceInt

/-! ## §1. The prism restricts: `A`-supported chains have `B`-supported prisms -/

/-- **A prism simplex over an `A`-supported simplex realises in `H(A × I)`**: if the homotopy `H`
maps `A × I` into `B` and `σ` realises inside `A`, every prism simplex `prismSimplex H σ i`
realises inside `B` — its realisation is `H ∘ (σ∘α i, β i)`, pointwise `H(σ(…), t)` with
`σ(…) ∈ A`. -/
theorem range_realize_prismSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    {A : Set ↑X} {B : Set ↑Y} (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    (hσ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ A) (i : Fin (n + 1)) :
    Set.range (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1))) (prismSimplex H σ i)) ⊆ B := by
  rw [prismSimplex, Equiv.apply_symm_apply]
  rintro y ⟨p, rfl⟩
  exact hH _ (hσ ⟨_, rfl⟩) _

/-- **The integral prism operator carries `A`-chains to `B`-chains** when the homotopy maps
`A × I` into `B` — the whole content of "the absolute prism descends to the pair"; no new prism
combinatorics. -/
theorem prismOpInt_mem_subspaceChainsInt {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y))
    {A : Set ↑X} {B : Set ↑Y} (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B) (n : ℕ)
    {c : SingularChainInt X n} (hc : c ∈ subspaceChainsInt A n) :
    prismOpInt H n c ∈ subspaceChainsInt B (n + 1) := by
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single τ a =>
      rw [chainIncl_single, prismOpInt_single, prismBasisInt, Finset.smul_sum]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      exact single_mem_subspaceChainsInt_of_subordinate
        (range_realize_prismSimplex H hH (simplexIncl A n τ) (range_realize_simplexIncl A τ) i)

/-! ## §2. Pair homotopy invariance -/

/-- **Relative (pair) homotopy invariance** (integral): two maps of pairs `f, g : (X, A) → (Y, B)`
homotopic through maps of pairs (`H` with `H(A × I) ⊆ B`, `H(·,0) = f`, `H(·,1) = g`) induce EQUAL
maps `Hₙ₊₁(X, A; ℤ) → Hₙ₊₁(Y, B; ℤ)`. The absolute signed chain homotopy `∂P + P∂ = g_# − f_#`
descends: on a relative cycle the `P∂` term is a `B`-chain (`prismOpInt_mem_subspaceChainsInt`) and
`∂P` is a relative boundary. The pair-level engine of the moving-puncture device. -/
theorem relHomologyInt_map_eq_of_homotopic_pair {X Y : TopCat} {A : Set ↑X} {B : Set ↑Y}
    {f g : C(↑X, ↑Y)} (H : C(↑X × unitInterval, ↑Y))
    (h0 : slice H 0 = f) (h1 : slice H 1 = g)
    (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
    RelHomologyInt.map g hg (n + 1) = RelHomologyInt.map f hf (n + 1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelHomologyInt.map_mk, RelHomologyInt.map_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  -- reduce to: relMapChainInt g (↑z) − relMapChainInt f (↑z) ∈ relBoundariesInt B (n+1)
  have hcoe : ((relCyclesMapInt g hg (n + 1) z - relCyclesMapInt f hf (n + 1) z :
        relCyclesInt B (n + 1)) : RelativeChainInt B (n + 1))
      = relMapChainInt g hg (n + 1) (z : RelativeChainInt A (n + 1))
        - relMapChainInt f hf (n + 1) (z : RelativeChainInt A (n + 1)) := by
    rw [Submodule.coe_sub, relCyclesMapInt_coe, relCyclesMapInt_coe]
  rw [hcoe]
  -- lift the relative cycle to an absolute chain c with ∂c an A-chain
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChainInt A (n + 1))
  have hzcyc : relBoundaryInt A n (z : RelativeChainInt A (n + 1)) = 0 := z.2
  have hzb : chainBoundary X n c ∈ subspaceChainsInt A n := by
    rw [← RelativeChainInt.mk_eq_zero_iff A n, ← relBoundaryInt_mk]
    rw [show (Submodule.Quotient.mk c : RelativeChainInt A (n + 1))
      = RelativeChainInt.mk A (n + 1) c from rfl] at hc
    rw [hc]
    exact hzcyc
  -- the signed prism identity, sliced to f and g
  have hkey := prism_chainHomotopyInt H c
  rw [endMapInt_eq_mapChainInt, endMapInt_eq_mapChainInt, h0, h1] at hkey
  refine ⟨RelativeChainInt.mk B (n + 1 + 1) (prismOpInt H (n + 1) c), ?_⟩
  have e1 : relBoundaryInt B (n + 1) (RelativeChainInt.mk B (n + 1 + 1) (prismOpInt H (n + 1) c))
      = RelativeChainInt.mk B (n + 1) (chainBoundary Y (n + 1) (prismOpInt H (n + 1) c)) :=
    relBoundaryInt_mk B (n + 1) _
  have e2 : RelativeChainInt.mk B (n + 1) (chainBoundary Y (n + 1) (prismOpInt H (n + 1) c))
      = RelativeChainInt.mk B (n + 1) (chainBoundary Y (n + 1) (prismOpInt H (n + 1) c)
          + prismOpInt H n (chainBoundary X n c)) :=
    (Submodule.Quotient.eq _).mpr (by
      have hd : chainBoundary Y (n + 1) (prismOpInt H (n + 1) c)
          - (chainBoundary Y (n + 1) (prismOpInt H (n + 1) c)
              + prismOpInt H n (chainBoundary X n c))
          = -(prismOpInt H n (chainBoundary X n c)) := by abel
      rw [hd]
      exact neg_mem (prismOpInt_mem_subspaceChainsInt H hH n hzb))
  have e3 : RelativeChainInt.mk B (n + 1) (chainBoundary Y (n + 1) (prismOpInt H (n + 1) c)
        + prismOpInt H n (chainBoundary X n c))
      = RelativeChainInt.mk B (n + 1) (mapChainInt g (n + 1) c - mapChainInt f (n + 1) c) :=
    congrArg (RelativeChainInt.mk B (n + 1)) hkey
  have e4 : RelativeChainInt.mk B (n + 1) (mapChainInt g (n + 1) c - mapChainInt f (n + 1) c)
      = RelativeChainInt.mk B (n + 1) (mapChainInt g (n + 1) c)
        - RelativeChainInt.mk B (n + 1) (mapChainInt f (n + 1) c) :=
    Submodule.Quotient.mk_sub _
  have e5 : RelativeChainInt.mk B (n + 1) (mapChainInt g (n + 1) c)
      = relMapChainInt g hg (n + 1) (z : RelativeChainInt A (n + 1)) := by
    rw [← hc]
    exact (relMapChainInt_mk g hg (n + 1) c).symm
  have e6 : RelativeChainInt.mk B (n + 1) (mapChainInt f (n + 1) c)
      = relMapChainInt f hf (n + 1) (z : RelativeChainInt A (n + 1)) := by
    rw [← hc]
    exact (relMapChainInt_mk f hf (n + 1) c).symm
  exact (((e1.trans e2).trans e3).trans e4).trans (by rw [e5, e6])

/-! ## §3. The Euclidean moving puncture: translations to two punctures in a convex body agree -/

open SKEFTHawking.SingularLocalModelChart (transl)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)

/-- The straight-line translation homotopy `H(y, t) = y − ((1−t)·p + t·q)` between `transl p` and
`transl q`, as a continuous map on `ℝ⁴ × I`. -/
noncomputable def translHomotopy (p q : EuclideanSpace ℝ (Fin 4)) :
    C(↑(Eucl 4) × unitInterval, ↑(Eucl 4)) :=
  ⟨fun yt => yt.1 - ((1 - (yt.2 : ℝ)) • p + (yt.2 : ℝ) • q), by fun_prop⟩

theorem translHomotopy_slice_zero (p q : EuclideanSpace ℝ (Fin 4)) :
    slice (translHomotopy p q) 0 = transl p := by
  refine ContinuousMap.ext fun y => ?_
  show y - ((1 - ((0 : unitInterval) : ℝ)) • p + ((0 : unitInterval) : ℝ) • q) = y - p
  norm_num

theorem translHomotopy_slice_one (p q : EuclideanSpace ℝ (Fin 4)) :
    slice (translHomotopy p q) 1 = transl q := by
  refine ContinuousMap.ext fun y => ?_
  show y - ((1 - ((1 : unitInterval) : ℝ)) • p + ((1 : unitInterval) : ℝ) • q) = y - q
  norm_num

/-- The moving puncture stays inside the convex body: on `Cᶜ × I` the homotopy avoids `0`. -/
theorem translHomotopy_mapsTo {C : Set (EuclideanSpace ℝ (Fin 4))} (hC : Convex ℝ C)
    {p q : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ C) (hq : q ∈ C) :
    ∀ y ∈ (Cᶜ : Set ↑(Eucl 4)), ∀ t : unitInterval,
      translHomotopy p q (y, t) ∈ ({w | w ≠ 0} : Set ↑(Eucl 4)) := by
  intro y hy t
  have hmem : (1 - (t : ℝ)) • p + (t : ℝ) • q ∈ C :=
    hC hp hq (by linarith [t.2.2] : (0:ℝ) ≤ 1 - (t : ℝ)) t.2.1 (by ring)
  show y - ((1 - (t : ℝ)) • p + (t : ℝ) • q) ≠ 0
  intro h0
  exact hy (by rwa [sub_eq_zero] at h0 ▸ hmem)

/-- `transl p` maps `Cᶜ` into `ℝ⁴∖0` when `p ∈ C`. -/
theorem transl_mapsTo_compl {C : Set (EuclideanSpace ℝ (Fin 4))}
    {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ C) :
    Set.MapsTo (transl p) (Cᶜ : Set ↑(Eucl 4)) ({w | w ≠ 0} : Set ↑(Eucl 4)) := by
  intro y hy
  show y - p ≠ 0
  intro h0
  exact hy (by rwa [sub_eq_zero] at h0 ▸ hp)

/-- **The Euclidean MOVING-PUNCTURE device**: for two punctures `p, q` inside a convex
`C ⊆ ℝ⁴`, the translations `transl p, transl q`, as maps of pairs `(ℝ⁴, Cᶜ) → (ℝ⁴, ℝ⁴∖0)`, induce
the SAME map `Hₙ₊₁(ℝ⁴ | C; ℤ) → Hₙ₊₁(ℝ⁴ | 0; ℤ)` — the straight-line homotopy moves the puncture
within `C`, so it is a homotopy of pair maps. Composed with `relInclInt`-naturality this compares
`localHomologyAtPointIsoInt p` and `localHomologyAtPointIsoInt q` on classes restricted from a
common convex compact — the honest single-chart comparison the freeze's discharge plan asked
for. -/
theorem relHomologyInt_map_transl_eq {C : Set (EuclideanSpace ℝ (Fin 4))} (hC : Convex ℝ C)
    {p q : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ C) (hq : q ∈ C) (n : ℕ) :
    RelHomologyInt.map (transl q) (transl_mapsTo_compl hq) (n + 1)
      = RelHomologyInt.map (transl p) (transl_mapsTo_compl hp) (n + 1) :=
  relHomologyInt_map_eq_of_homotopic_pair (translHomotopy p q)
    (translHomotopy_slice_zero p q) (translHomotopy_slice_one p q)
    (translHomotopy_mapsTo hC hp hq)
    (transl_mapsTo_compl hp) (transl_mapsTo_compl hq) n

end SKEFTHawking.SingularRelativeHomotopyInvarianceInt
