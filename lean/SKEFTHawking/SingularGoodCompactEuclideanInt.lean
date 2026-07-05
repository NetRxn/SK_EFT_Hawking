import Mathlib
import SKEFTHawking.SingularGoodCompactInt
import SKEFTHawking.SingularGoodCompactUnionInt
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularBallCover
import SKEFTHawking.SingularChainSupport

/-!
# The integral "good compact" property for an arbitrary Euclidean compact (Hatcher 3.27 step 3, ℤ)

The ℤ analog of the mod-2 `SingularGoodCompactEuclidean`. Assembles, over ℤ:

* the integral **direct-limit surjectivity** `exists_factor_through_compactInt` — every class of
  `Hₖ₊₁(M|K; ℤ)` factors through `Hₖ₊₁(M|C; ℤ)` for a compact neighbourhood `C ⊇ K` (via the
  coefficient-generic chain-support machinery, mirrored here over ℤ);
* `goodCompactInt_empty` — the empty set is good (its local homology is the zero module);
* `goodCompactInt_biUnion_convex` — a finite union of convex compacts is `goodCompactInt (m+2)`
  (over the on-main convex base `goodCompactInt_convexCompact`);
* `vanishAboveInt_eucl_compact` / `determinedByPointsInt_eucl_compact` / `goodCompactInt_eucl_compact`
  — an arbitrary compact `K ⊆ ℝⁿ` is `goodCompactInt (m+2)`, covering `K` by finitely many closed
  balls (`SingularBallCover.exists_finite_closedBall_cover`, coefficient-free, reused) inside a compact
  neighbourhood and pushing through the colimit + the radial restriction iso
  `restrictToPointInt_radial_bijective` (on-main).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt)
open SKEFTHawking.SingularGoodCompactInt

namespace SKEFTHawking.SingularGoodCompactEuclideanInt

variable {X : TopCat}

/-! ## §1. Integral chain-support + direct-limit surjectivity -/

/-- The **image of an integral singular chain** `c` — the union of the images of its (finitely many)
support simplices. The ℤ mirror of `SingularChainSupport.chainImage`. -/
def chainImageInt {n : ℕ} (c : SingularChainInt X n) : Set ↑X :=
  ⋃ τ ∈ c.support, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)

/-- An integral singular chain has **compact image**: finitely many support simplices, each a
continuous image of the compact standard simplex `Δⁿ`. -/
theorem isCompact_chainImageInt {n : ℕ} (c : SingularChainInt X n) : IsCompact (chainImageInt c) := by
  refine c.support.finite_toSet.isCompact_biUnion (fun τ _ => ?_)
  exact isCompact_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous

/-- A point lies in `chainImageInt c` iff it is in the image of some support simplex. -/
theorem mem_chainImageInt_iff {n : ℕ} (c : SingularChainInt X n) (x : ↑X) :
    x ∈ chainImageInt c ↔
      ∃ τ ∈ c.support, x ∈ Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  simp only [chainImageInt, Set.mem_iUnion, exists_prop]

/-- **`chainImageInt` is contained in any subspace the chain lives in**. -/
theorem chainImageInt_subset_of_mem_subspaceChainsInt {S : Set ↑X} {n : ℕ} {c : SingularChainInt X n}
    (hc : c ∈ subspaceChainsInt S n) : chainImageInt c ⊆ S := by
  intro x hx
  obtain ⟨τ, hτ, hxτ⟩ := (mem_chainImageInt_iff c x).mp hx
  exact range_of_mem_subspaceChainsInt hc hτ hxτ

/-- **Separation of an integral relative cycle's boundary from a compact `K`**: for a chain `c` whose
boundary `∂c` lies in `M∖K` (`subspaceChainsInt Kᶜ`), and a compact `K` in a locally-compact Hausdorff
space, there is a **compact neighbourhood** `C` of `K` with `∂c` still in `M∖C`. The ℤ mirror of
`SingularChainSupport.exists_compact_boundary_avoiding`. -/
theorem exists_compact_boundary_avoidingInt [T2Space ↑X] [LocallyCompactSpace ↑X]
    {n : ℕ} {K : Set ↑X} (hK : IsCompact K) {c : SingularChainInt X (n + 1)}
    (hc : chainBoundary X n c ∈ subspaceChainsInt Kᶜ n) :
    ∃ C : Set ↑X, IsCompact C ∧ K ⊆ interior C ∧ chainBoundary X n c ∈ subspaceChainsInt Cᶜ n := by
  have himg : chainImageInt (chainBoundary X n c) ⊆ Kᶜ :=
    chainImageInt_subset_of_mem_subspaceChainsInt hc
  have hdisj : K ⊆ (chainImageInt (chainBoundary X n c))ᶜ := fun x hxK hx => himg hx hxK
  obtain ⟨C, hCcompact, hKC, hCsub⟩ :=
    exists_compact_between hK
      (isCompact_chainImageInt (chainBoundary X n c)).isClosed.isOpen_compl hdisj
  refine ⟨C, hCcompact, hKC, mem_subspaceChainsInt_of_support (fun τ hτ x hx => ?_)⟩
  exact fun hxC => hCsub hxC ((mem_chainImageInt_iff _ x).mpr ⟨τ, hτ, hx⟩)

/-- **`Hᵢ(M | K; ℤ)` direct-limit surjectivity** (Hatcher 3.27, step 3): every relative homology class
`α ∈ Hₖ₊₁(M, M∖K; ℤ)` is the image, under the inclusion-of-pairs map `relInclInt`, of a class over a
**compact neighbourhood** `C` of `K`. The ℤ mirror of
`SingularLocalHomologyColimit.exists_factor_through_compact`. -/
theorem exists_factor_through_compactInt [T2Space ↑X] [LocallyCompactSpace ↑X]
    {K : Set ↑X} (hK : IsCompact K) {k : ℕ} (α : RelHomologyInt Kᶜ (k + 1)) :
    ∃ C : Set ↑X, IsCompact C ∧ ∃ (hKC : K ⊆ interior C),
      ∃ β : RelHomologyInt Cᶜ (k + 1),
        relInclInt (Set.compl_subset_compl.mpr (hKC.trans interior_subset)) (k + 1) β = α := by
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z₀ : RelativeChainInt Kᶜ (k + 1))
  have hz₀cyc : relBoundaryInt Kᶜ k (z₀ : RelativeChainInt Kᶜ (k + 1)) = 0 := LinearMap.mem_ker.mp z₀.2
  have hbd : chainBoundary X k c ∈ subspaceChainsInt Kᶜ k := by
    rw [← RelativeChainInt.mk_eq_zero_iff]
    have : relBoundaryInt Kᶜ k (RelativeChainInt.mk Kᶜ (k + 1) c) = 0 := by
      rw [show RelativeChainInt.mk Kᶜ (k + 1) c = (z₀ : RelativeChainInt Kᶜ (k + 1)) from hc, hz₀cyc]
    rwa [relBoundaryInt_mk] at this
  obtain ⟨C, hCcompact, hKC, hbdC⟩ := exists_compact_boundary_avoidingInt hK hbd
  refine ⟨C, hCcompact, hKC, ?_⟩
  have hcyc : RelativeChainInt.mk Cᶜ (k + 1) c ∈ relCyclesInt Cᶜ (k + 1) := by
    rw [relCyclesInt, LinearMap.mem_ker, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff]
    exact hbdC
  refine ⟨RelHomologyInt.mk Cᶜ (k + 1) ⟨RelativeChainInt.mk Cᶜ (k + 1) c, hcyc⟩, ?_⟩
  rw [show RelHomologyInt.mk Cᶜ (k + 1) ⟨RelativeChainInt.mk Cᶜ (k + 1) c, hcyc⟩
      = Submodule.Quotient.mk (⟨RelativeChainInt.mk Cᶜ (k + 1) c, hcyc⟩ : relCyclesInt Cᶜ (k + 1))
      from rfl, relInclInt, RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [relCyclesMapInt_coe, relMapChainInt_mk, SingularFunctorialityInt.mapChainInt_id]
  exact hc

/-! ## §2. `goodCompactInt_empty` -/

/-- `subspaceChainsInt (∅ᶜ) = ⊤`: every chain's support simplices land in `∅ᶜ = univ`. -/
theorem subspaceChainsInt_compl_empty_eq_top (n : ℕ) :
    subspaceChainsInt (∅ᶜ : Set ↑X) n = ⊤ := by
  refine eq_top_iff.2 (fun c _ => mem_subspaceChainsInt_of_support (fun τ _ x _ => ?_))
  exact Set.notMem_empty x

/-- The relative chain module of the pair `(X, X)` is the zero module (integral). -/
instance relativeChainInt_compl_empty_subsingleton (n : ℕ) :
    Subsingleton (RelativeChainInt (∅ᶜ : Set ↑X) n) := by
  rw [RelativeChainInt, subspaceChainsInt_compl_empty_eq_top]
  infer_instance

/-- `Hᵢ(X | ∅; ℤ) = Hᵢ(X, X; ℤ) = 0`. -/
theorem relHomologyInt_compl_empty_eq_zero (n : ℕ) (x : RelHomologyInt (∅ᶜ : Set ↑X) n) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show z = 0 from Subsingleton.elim z 0]
  exact Submodule.Quotient.mk_zero _

/-- **The empty set is `goodCompactInt`** (any `X`, any `n`). -/
theorem goodCompactInt_empty (n : ℕ) : goodCompactInt (X := X) n (∅ : Set ↑X) := by
  refine ⟨fun i _ x => relHomologyInt_compl_empty_eq_zero i x, fun α _ => ?_⟩
  exact relHomologyInt_compl_empty_eq_zero n α

/-! ## §3. `goodCompactInt_biUnion_convex` -/

/-- **A finite union of convex compact sets is `goodCompactInt`** (Hatcher 3.27 step 2, ℤ): for a
nonempty finite family `B i` (`i ∈ s`) of convex compact subsets of `ℝⁿ` (`n = m+2`), the union
`⋃ i∈s, B i` is `goodCompactInt (m+2)`. Every nonempty sub-intersection is convex compact
(`goodCompactInt_convexCompact`); the empty ones use `goodCompactInt_empty`. -/
theorem goodCompactInt_biUnion_convex {m : ℕ} {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (B : ι → Set (EuclideanSpace ℝ (Fin (m + 2))))
    (hconv : ∀ i ∈ s, Convex ℝ (B i)) (hcomp : ∀ i ∈ s, IsCompact (B i)) :
    goodCompactInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) (⋃ i ∈ s, B i) := by
  classical
  exact SingularGoodCompactUnionInt.goodCompactInt_biUnion
    (X := SingularEuclideanAcyclic.Eucl (m + 2)) hs B
    (fun t ht htne => by
      obtain ⟨j, hj⟩ := htne
      have hconvI : Convex ℝ (⋂ i ∈ t, B i) :=
        convex_iInter (fun i => convex_iInter (fun hi => hconv i (ht hi)))
      have hclosedI : IsClosed (⋂ i ∈ t, B i) :=
        isClosed_biInter (fun i hi => (hcomp i (ht hi)).isClosed)
      have hcompI : IsCompact (⋂ i ∈ t, B i) :=
        (hcomp j (ht hj)).of_isClosed_subset hclosedI (Set.biInter_subset_of_mem hj)
      refine ⟨hclosedI, ?_⟩
      by_cases hne : (⋂ i ∈ t, B i).Nonempty
      · obtain ⟨O, hO⟩ := hne
        exact SingularConvexRadialBaseInt.goodCompactInt_convexCompact hconvI hcompI hO
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact goodCompactInt_empty (m + 2))

/-! ## §4 (a) — `vanishAboveInt` for an arbitrary Euclidean compact -/

/-- **`vanishAboveInt (m+2) K` for an arbitrary compact `K ⊆ ℝⁿ`** (Hatcher 3.27 step 3, ℤ, high-degree
half). -/
theorem vanishAboveInt_eucl_compact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hK : IsCompact K) :
    vanishAboveInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact (goodCompactInt_empty (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2)).1
  · intro i hi α
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨C, hCcomp, hKC, β, hβ⟩ :=
      exists_factor_through_compactInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) hK α
    obtain ⟨s, r, hs, hsK, hrpos, hcov, hsub⟩ :=
      SingularBallCover.exists_finite_closedBall_cover hK isOpen_interior hKC hKne
    have hgoodC' : goodCompactInt
        (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) (⋃ c ∈ s, Metric.closedBall c (r c)) :=
      goodCompactInt_biUnion_convex hs (fun c => Metric.closedBall c (r c))
        (fun c _ => convex_closedBall c (r c)) (fun c _ => isCompact_closedBall c (r c))
    have hC'C : (⋃ c ∈ s, Metric.closedBall c (r c)) ⊆ C :=
      Set.iUnion₂_subset (fun c hc => (hsub c hc).trans interior_subset)
    have hCC' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
        ⊆ (⋃ c ∈ s, Metric.closedBall c (r c))ᶜ := Set.compl_subset_compl.mpr hC'C
    have hC'K : ((⋃ c ∈ s, Metric.closedBall c (r c))ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
        ⊆ Kᶜ := Set.compl_subset_compl.mpr hcov
    have hβ'0 : relInclInt hCC' (k + 1) β = 0 := hgoodC'.1 (k + 1) hi _
    calc α = relInclInt _ (k + 1) β := hβ.symm
      _ = relInclInt hC'K (k + 1) (relInclInt hCC' (k + 1) β) := (relInclInt_trans hCC' hC'K (k + 1) β).symm
      _ = relInclInt hC'K (k + 1) 0 := by rw [hβ'0]
      _ = 0 := map_zero _

/-! ## §4 (b) — `determinedByPointsInt` for an arbitrary Euclidean compact -/

/-- **`determinedByPointsInt (m+2) K` for an arbitrary compact `K ⊆ ℝⁿ`** (Hatcher 3.27 step 3, ℤ,
degree-`n` half). -/
theorem determinedByPointsInt_eucl_compact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hK : IsCompact K) :
    determinedByPointsInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]; exact (goodCompactInt_empty (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2)).2
  · intro α hα
    obtain ⟨C, hCcomp, hKC, β, hβ⟩ :=
      exists_factor_through_compactInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) hK α
    obtain ⟨s, r, hs, hsK, hrpos, hcov, hsub⟩ :=
      SingularBallCover.exists_finite_closedBall_cover hK isOpen_interior hKC hKne
    set C' : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)) := ⋃ c ∈ s, Metric.closedBall c (r c)
      with hC'def
    have hgoodC' : goodCompactInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) C' :=
      goodCompactInt_biUnion_convex hs (fun c => Metric.closedBall c (r c))
        (fun c _ => convex_closedBall c (r c)) (fun c _ => isCompact_closedBall c (r c))
    have hC'C : C' ⊆ C := Set.iUnion₂_subset (fun c hc => (hsub c hc).trans interior_subset)
    have hKC' : K ⊆ C' := hcov
    set β' := relInclInt (Set.compl_subset_compl.mpr hC'C) (m + 2) β with hβ'def
    have hαβ' : relInclInt (Set.compl_subset_compl.mpr hKC') (m + 2) β' = α := by
      rw [hβ'def, relInclInt_trans]; exact hβ
    have hβ'pt : ∀ (y : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (hy : y ∈ C'),
        restrictToPointInt hy (m + 2) β' = 0 := by
      intro y hy
      obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp (hC'def ▸ hy)
      have hcK : c ∈ K := hsK hc
      have hcBc : c ∈ Metric.closedBall c (r c) := Metric.mem_closedBall_self (hrpos c hc).le
      have hBcC' : Metric.closedBall c (r c) ⊆ C' := fun z hz => by
        rw [hC'def]; exact Set.mem_iUnion₂.mpr ⟨c, hc, hz⟩
      have hinj := (SingularConvexRadialBaseInt.restrictToPointInt_radial_bijective
        (convex_closedBall c (r c)) (isCompact_closedBall c (r c)) hcBc).injective
      have hcenter : restrictToPointInt hcBc (m + 2)
          (relInclInt (Set.compl_subset_compl.mpr hBcC') (m + 2) β') = 0 := by
        rw [restrictToPointInt_relInclInt hBcC' hcBc (m + 2) β']
        show restrictToPointInt (hKC' hcK) (m + 2) β' = 0
        rw [← restrictToPointInt_relInclInt hKC' hcK (m + 2) β', hαβ']
        exact hα c hcK
      have hballβ' : relInclInt (Set.compl_subset_compl.mpr hBcC') (m + 2) β' = 0 :=
        hinj (by rw [hcenter, map_zero])
      show restrictToPointInt (hBcC' hyc) (m + 2) β' = 0
      rw [← restrictToPointInt_relInclInt hBcC' hyc (m + 2) β', hballβ', map_zero]
    rw [← hαβ', hgoodC'.2 β' hβ'pt, map_zero]

/-! ## §4 — assembled: an arbitrary Euclidean compact is `goodCompactInt` -/

/-- **An arbitrary compact `K ⊆ ℝⁿ` is `goodCompactInt (m+2)`** (Hatcher 3.27 step 3, ℤ). -/
theorem goodCompactInt_eucl_compact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hK : IsCompact K) :
    goodCompactInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K :=
  ⟨vanishAboveInt_eucl_compact hK, determinedByPointsInt_eucl_compact hK⟩

end SKEFTHawking.SingularGoodCompactEuclideanInt
