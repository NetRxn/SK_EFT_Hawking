/-
# Phase 5q.H close-out — the ALL-DEGREE homology finiteness stock
# (subsingleton / empty / clopen-split / convex / product-with-contractible / joined-cover export)

The capstone cohomology MV datum (`PinPlusTraceCapstoneCohomologyMV.lean`) consumes all-degree
(`∀ n`) mod-2 homology finiteness of the two MV pieces, their overlap, and the boundary. The
existing stock is per-degree (`H₀` via joined covers, `H₁–H₃` via the PD windows, `H₄` via
point-restriction, `> 4` via `goodCompact` vanishing) and per-shape (convex acyclicity in degrees
`≥ 1` only, `splitH0` in degree `0` only). This module banks the GENERIC, carrier-agnostic
`∀ n`-assemblies:

* **`finiteDimensional_of_subsingleton`** — a subsingleton `ZMod 2`-module is finite-dimensional
  (the degenerate-degree closer used by every vanishing argument below).
* **`subsingleton_homology_of_isEmpty` / `finiteDimensional_homology_of_isEmpty`** — the empty
  carrier has trivial chains in every degree (`X : TopCat` form of the
  `PinPlusCharPairSurfaceTie` empty-space atom, re-banked at the substrate layer for the
  clopen-split brick's `U ∩ Uᶜ` overlap).
* **`finiteDimensional_homology_of_clopen_split`** — a clopen `U ⊆ X` with all-degree finite
  pieces gives all-degree finite `H_*(X)`: degree `0` by `splitH0Equiv`, degrees `≥ 1` by the
  Mayer–Vietoris opener with the EMPTY overlap `U ∩ Uᶜ`. The `∂W = M ⊔ M′` two-ends brick.
* **`finiteDimensional_homology_convexSub_all`** — a convex subspace of Euclidean space has
  all-degree finite homology (`H₀ ≅ ℤ/2` by the straight-line contraction, `H_{k+1} = 0` by
  convex acyclicity). The `D⁵` handle-side brick.
* **`iccContraction`** — the straight-line contraction of the unit interval onto `0`, in the
  project's `slice`-homotopy format (the collar/cylinder factor's contraction datum).
* **`joined_of_contraction`** — every point of a contracted space is joined to the basepoint.
* **`finiteDimensional_homology_prodContractible_succ`** — `H_{n+1}(Y × C) < ∞ ⟸ H_{n+1}(Y) < ∞`
  for a contractible factor `C` (the `prodFst`/`prodSect`/`prodHomotopy` homotopy equivalence fed
  through the mod-2 transfer). The cylinder-side (`M × I`) brick in positive degrees.
* **`finiteDimensional_h0_prodContractible`** — `H₀(Y × C) < ∞` from a finite joined cover of `Y`
  and a contraction of `C` (product paths). The cylinder-side degree-`0` brick.
* **`exists_finite_joinedCover`** — a compact charted manifold admits a FINITE joined cover
  (the cover construction inside `SingularH0Finite.finiteDimensional_h0`, exported as data so the
  product brick can consume it).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularMVCohomologyFinite
import SKEFTHawking.SingularDisjointUnion
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.SingularHomologyFiniteTransfer
import SKEFTHawking.SingularH0Finite

open Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularMVCohomologyFinite
open SKEFTHawking.SingularDisjointUnion
open SKEFTHawking.SingularConvexSubAcyclic
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularHomologyFiniteTransfer
open SKEFTHawking.SingularH0Finite
open SKEFTHawking.SingularH0PathConnected
open SKEFTHawking.SingularPDWindow

namespace SKEFTHawking.SingularHomologyFiniteAll

noncomputable section

/-! ## §1. The degenerate-degree closer: subsingleton modules are finite-dimensional. -/

/-- **A subsingleton `ZMod 2`-module is finite-dimensional** — the closer for every
vanishing-degree argument (`H_{>dim} = 0`, empty overlaps, convex acyclicity). -/
theorem finiteDimensional_of_subsingleton {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Subsingleton V] : FiniteDimensional (ZMod 2) V :=
  Module.Finite.of_surjective (0 : ZMod 2 →ₗ[ZMod 2] V)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)

/-! ## §2. The empty carrier: trivial chains, all-degree finiteness. -/

/-- The singular `n`-simplex object of an empty carrier is empty (`X : TopCat` form of the
`PinPlusCharPairSurfaceTie.isEmpty_simplex` atom). -/
theorem isEmpty_simplex_of_isEmpty {X : TopCat} [IsEmpty ↑X] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) := by
  constructor
  rintro ⟨f⟩
  obtain ⟨x⟩ : Nonempty ↑(SimplexCategory.toTop.obj (SimplexCategory.mk n)) := inferInstance
  exact (‹IsEmpty ↑X›).false (f.hom x)

/-- **The mod-2 homology of an empty carrier vanishes** (subsingleton) — the chains are trivial
in every degree. -/
theorem subsingleton_homology_of_isEmpty {X : TopCat} [IsEmpty ↑X] (n : ℕ) :
    Subsingleton (Homology X n) := by
  haveI := isEmpty_simplex_of_isEmpty (X := X) n
  haveI : Subsingleton (SingularChain X n) := inferInstance
  haveI : Subsingleton (cycles X n) := inferInstance
  exact (Submodule.Quotient.mk_surjective _).subsingleton

/-- **All-degree finiteness of the empty carrier.** -/
theorem finiteDimensional_homology_of_isEmpty {X : TopCat} [IsEmpty ↑X] (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology X n) :=
  haveI := subsingleton_homology_of_isEmpty (X := X) n
  finiteDimensional_of_subsingleton

/-! ## §3. The clopen split: all-degree finiteness of a two-ends carrier. -/

/-- **All-degree homology finiteness splits over a clopen piece**: if `U ⊆ X` is clopen and both
`H_*(U)` and `H_*(Uᶜ)` are finite in every degree, so is `H_*(X)` — degree `0` by
`splitH0Equiv`, degrees `≥ 1` by the Mayer–Vietoris opener with the empty overlap `U ∩ Uᶜ`.
The two-closed-ends boundary `∂W = M ⊔ M′` brick. -/
theorem finiteDimensional_homology_of_clopen_split {X : TopCat} {U : Set ↑X} (hU : IsClopen U)
    (hUf : ∀ n, FiniteDimensional (ZMod 2) (Homology (sub U) n))
    (hUcf : ∀ n, FiniteDimensional (ZMod 2) (Homology (sub Uᶜ) n)) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology X n) := by
  cases n with
  | zero =>
    haveI := hUf 0
    haveI := hUcf 0
    exact (splitH0Equiv hU).finiteDimensional
  | succ n =>
    have hcov : (⋃ V ∈ ({U, Uᶜ} : Set (Set ↑X)), interior V) = Set.univ := by
      rw [Set.biUnion_pair, hU.isOpen.interior_eq, hU.compl.isOpen.interior_eq,
        Set.union_compl_self]
    refine finiteDimensional_homology_of_mv_cover U Uᶜ n hcov (hUf (n + 1)) (hUcf (n + 1)) ?_
    haveI : IsEmpty ↥(U ∩ Uᶜ) := ⟨fun x => x.2.2 x.2.1⟩
    exact finiteDimensional_homology_of_isEmpty (X := sub (U ∩ Uᶜ)) n

/-! ## §4. Convex subspaces: all-degree finiteness (the `D⁵` handle-side brick). -/

/-- **All-degree homology finiteness of a convex subspace of Euclidean space** — `H₀ ≅ ℤ/2` by
the straight-line contraction (`homologyZeroContractibleEquiv`), `H_{k+1} = 0` by convex
acyclicity (`homology_convexSub_eq_zero`). -/
theorem finiteDimensional_homology_convexSub_all {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) (k : ℕ) :
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := SingularEuclideanAcyclic.Eucl n) C) k) := by
  cases k with
  | zero =>
    exact (homologyZeroContractibleEquiv (convexContraction hC hp₀) ⟨p₀, hp₀⟩
      (slice_convexContraction_zero hC hp₀)
      (slice_convexContraction_one hC hp₀)).symm.finiteDimensional
  | succ k =>
    haveI : Subsingleton (Homology (sub (X := SingularEuclideanAcyclic.Eucl n) C) (k + 1)) :=
      ⟨fun a b => (homology_convexSub_eq_zero hC hp₀ k a).trans
        (homology_convexSub_eq_zero hC hp₀ k b).symm⟩
    exact finiteDimensional_of_subsingleton

/-! ## §5. The unit-interval contraction (the collar/cylinder factor's contraction datum). -/

/-- **The straight-line contraction of the unit interval onto `0`**, in the project's
`slice`-homotopy format: `H(s, t) = (1 - t)·s`. -/
def iccContraction :
    C(↑(TopCat.of unitInterval) × unitInterval, ↑(TopCat.of unitInterval)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) * (p.1 : ℝ),
    Set.mem_Icc.mpr ⟨mul_nonneg (by linarith [p.2.2.2]) p.1.2.1,
      by
        have h1 : (1 - (p.2 : ℝ)) ≤ 1 := by linarith [p.2.2.1]
        have h2 : (p.1 : ℝ) ≤ 1 := p.1.2.2
        nlinarith [p.1.2.1, p.2.2.1]⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_subtype_val.comp continuous_fst)

theorem slice_iccContraction_zero :
    slice iccContraction 0 = ContinuousMap.id ↑(TopCat.of unitInterval) := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((0 : unitInterval) : ℝ)) * (x : ℝ) = (x : ℝ)
  simp

theorem slice_iccContraction_one :
    slice iccContraction 1 = ContinuousMap.const ↑(TopCat.of unitInterval) 0 := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((1 : unitInterval) : ℝ)) * (x : ℝ) = ((0 : unitInterval) : ℝ)
  simp

/-! ## §6. The product with a contractible factor: all-degree finiteness transfer. -/

/-- **Every point of a contracted space is joined to the basepoint** — the contraction's own
time-track is the path. -/
theorem joined_of_contraction {C : TopCat} (H : C(↑C × unitInterval, ↑C)) (c₀ : ↑C)
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀)
    (c : ↑C) : Joined c c₀ := by
  refine ⟨⟨⟨fun t => H (c, t), H.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    ?_, ?_⟩⟩
  · show H (c, 0) = c
    exact ContinuousMap.congr_fun h0 c
  · show H (c, 1) = c₀
    exact ContinuousMap.congr_fun h1 c

/-- **`H_{n+1}(Y × C) < ∞ ⟸ H_{n+1}(Y) < ∞` for a contractible factor `C`** — the
`prodFst`/`prodSect` homotopy equivalence (interpolated by `prodHomotopy`, strict on the other
side by `constHomotopy`) fed through the mod-2 finiteness transfer. -/
theorem finiteDimensional_homology_prodContractible_succ (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y (n + 1))) :
    FiniteDimensional (ZMod 2) (Homology (ProdSp Y C) (n + 1)) :=
  finiteDimensional_homology_of_homotopyEquiv (prodFst Y C) (prodSect Y C c₀)
    (prodHomotopy Y C H) (slice_prodHomotopy_zero Y C c₀ H h1)
    (slice_prodHomotopy_one Y C H h0) (constHomotopy Y)
    (by rw [slice_constHomotopy, prodFst_comp_prodSect]) (slice_constHomotopy Y 1) n h

/-- **Joined points pair to joined product points** (`Path.prod` packaged at the `Joined`
level). -/
theorem joined_prod {A B : TopCat} {a₁ a₂ : ↑A} {b₁ b₂ : ↑B} (ha : Joined a₁ a₂)
    (hb : Joined b₁ b₂) : Joined ((a₁, b₁) : ↑A × ↑B) (a₂, b₂) :=
  ⟨ha.somePath.prod hb.somePath⟩

/-- **`H₀(Y × C) < ∞` from a finite joined cover of `Y` and a contraction of `C`** — the points
`(p i, c₀)` are a finite joined cover of the product (product paths: contract the factor, then
travel the base). -/
theorem finiteDimensional_h0_prodContractible {ι : Type*} [DecidableEq ι] (Y C : TopCat)
    (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (t : Finset ι) (p : ι → ↑Y)
    (hcov : ∀ y : ↑Y, ∃ i ∈ t, Joined y (p i)) :
    FiniteDimensional (ZMod 2) (Homology (ProdSp Y C) 0) := by
  refine finiteDimensional_h0_of_cover (Y := ProdSp Y C) t (fun i => (p i, c₀)) ?_
  rintro ⟨y, c⟩
  obtain ⟨i, hit, hj⟩ := hcov y
  exact ⟨i, hit, (joined_prod (Joined.refl y) (joined_of_contraction H c₀ h0 h1 c)).trans
    (joined_prod hj (Joined.refl c₀))⟩

/-- **All-degree finiteness of a product with a contractible factor** — the combined supplier:
degree `0` from the finite joined cover, degrees `≥ 1` from the homotopy transfer. The exact
shape of the seam-overlap (`S_att × collar`) comparison finiteness: the collar contracts, the
attaching-region factor carries the joined cover + all-degree finiteness. -/
theorem finiteDimensional_homology_prodContractible_all {ι : Type*} [DecidableEq ι]
    (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀)
    (t : Finset ι) (p : ι → ↑Y) (hcov : ∀ y : ↑Y, ∃ i ∈ t, Joined y (p i))
    (hY : ∀ n, FiniteDimensional (ZMod 2) (Homology Y n)) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (ProdSp Y C) n) := by
  cases n with
  | zero => exact finiteDimensional_h0_prodContractible Y C c₀ H h0 h1 t p hcov
  | succ n =>
    exact finiteDimensional_homology_prodContractible_succ Y C c₀ H h0 h1 n (hY (n + 1))

/-! ## §7. The finite joined-cover export for compact charted manifolds. -/

open SKEFTHawking.SingularConvexSubAcyclic in
/-- **A compact charted manifold admits a finite joined cover** — the chart-ball pullback cover
construction inside `SingularH0Finite.finiteDimensional_h0`, exported as data (the finite point
set) so product/transfer bricks can consume it. -/
theorem exists_finite_joinedCover {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] :
    ∃ t : Finset M, ∀ x : M, ∃ p ∈ t, Joined x p := by
  classical
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  haveI : CompactSpace ↑(TopCat.of M) := inferInstanceAs (CompactSpace M)
  have hball : ∀ x : M, ∃ ε > 0, Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) ε
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).target :=
    fun x => Metric.isOpen_iff.mp (chartAt _ x).open_target _ (mem_chart_target _ x)
  choose ε hε hballT using hball
  set Wx : M → Set ↑(TopCat.of M) := fun x =>
    chartPull (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x)) with hWxdef
  have hWopen : ∀ x, IsOpen (Wx x) := fun x =>
    chartPull_isOpen (chartAt _ x).open_source _ Metric.isOpen_ball
  have hWmem : ∀ x : M, x ∈ Wx x := by
    intro x
    have := (mem_chartPull
      (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x))
      ⟨x, mem_chart_source _ x⟩).mpr
    refine this ?_
    show ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
      ⟨x, mem_chart_source _ x⟩ : EuclideanSpace ℝ (Fin (2 + 2)))
      ∈ Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x)
    rw [show ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
        ⟨x, mem_chart_source _ x⟩ : EuclideanSpace ℝ (Fin (2 + 2)))
      = chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x from rfl]
    exact Metric.mem_ball_self (hε x)
  have hWjoin : ∀ (x : M) (y : ↑(TopCat.of M)), y ∈ Wx x → Joined y (x : ↑(TopCat.of M)) := by
    intro x y hy
    haveI hpcsB : PathConnectedSpace ↥(sub (X := SingularEuclideanAcyclic.Eucl (2 + 2))
        (Metric.ball (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x x) (ε x))) :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_ball _ _).isPathConnected ⟨_, Metric.mem_ball_self (hε x)⟩)
    haveI hpcsW : PathConnectedSpace ↥(sub (X := TopCat.of M) (Wx x)) := by
      have φ := chartSubHomeo (M := TopCat.of M)
        (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).toHomeomorphSourceTarget
        (hballT x) (chartPull_subset _ _)
        (fun u => mem_chartPull _ _ u)
      exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous
    have hj := PathConnectedSpace.joined
      (⟨y, hy⟩ : ↥(sub (X := TopCat.of M) (Wx x)))
      (⟨x, hWmem x⟩ : ↥(sub (X := TopCat.of M) (Wx x)))
    exact ⟨hj.some.map continuous_subtype_val⟩
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := ↑(TopCat.of M)))
    Wx hWopen (fun y _ => Set.mem_iUnion.mpr ⟨y, hWmem y⟩)
  refine ⟨t, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact ⟨x, hxt, hWjoin x y hyx⟩

end

end SKEFTHawking.SingularHomologyFiniteAll
