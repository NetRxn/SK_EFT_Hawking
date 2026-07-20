/-
# Phase 5q.H · K1-b — the T⁴ cross-value keystone: the full `3H` Gram

**The Eilenberg–Zilber cross-value wall, closed.** This module computes the six complementary
off-diagonal entries `⟨e_{ij} ∪ e_{kl}, [T⁴]⟩ = ±1` of the integral intersection form of
`T⁴ = Tor (Tor TwoTorus)` — the entries six prior arcs could not reach — and assembles the full
`6×6` Gram: a `Module.Basis` of `H²(T⁴;ℤ)` on which `interMatrix t4IntFundClassHonest` is
`IntCongr` to the canonical `3H` block form `KummerInvolution.torusFourForm`.

**Method (EZ-free, termwise).** The coordinate 1-cocycles `b₀…b₃` are iterated factor pullbacks of
the winding cocycle `windS`; the fundamental 4-cycle `t4chain` is the iterated glued arc-cylinder
cross of the circle's two-arc 1-cycle. Every Gram entry is an integral Kronecker evaluation
`⟨(bᵢ ⌣ bⱼ) ⌣ (bₖ ⌣ bₗ), t4chain⟩`, computed by the `TorusCrossPeel` spine peels:
* one `snd` factor → the peel collapses the value one torus-factor down (weight `= ±1`),
* two `snd` factors → the basepoint slice kills the residue (`0`, termwise),
* no `snd` factor → the value factors through `H_{top}(smaller torus) = 0`.
The recursion grounds in `⟨windS, t1chain⟩ = 1` — pure winding arithmetic. Because
`H₄(T⁴;ℤ) = ℤ·[T⁴]` is banked, `[t4chain] = m·[T⁴]` automatically; a computed value `±1` forces
`m = ±1` with **no generator detection anywhere** — the honest-form entries follow with the same
global unit `m`.

Headlines:
* `interFormInt_honest_e01_e23 = t4m` (± its two complementary partners) — the cross values, `±1`.
* `t4m_unit : t4m = 1 ∨ t4m = -1`.
* `t4GramBasis` — the six `e`-classes ARE a ℤ-basis of `H²(T⁴;ℤ)` (unimodular Gram ⟹ basis).
* `interMatrix_t4_intCongr_torusFourForm` — `II(T⁴) ≅ 3H` (`IntCongr` to `torusFourForm`),
  discharging the K1-b Gram identity of the `KummerHomologyT4` honest boundary.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.TorusCrossPeel
import SKEFTHawking.KummerT4GramDiagonal
import SKEFTHawking.KummerHomologyT4H2
import SKEFTHawking.KummerInvolution
import SKEFTHawking.HyperbolicNormalForm
import SKEFTHawking.IntersectionMatrixInt

namespace SKEFTHawking.KummerT4GramCross

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_id)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt chainBoundary_mapChainInt)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply
  cochainPullbackInt_cup cochainPullbackInt_mem_ker kronecker_cochainPullbackInt)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.CircleWindingCocycle (windS windS_cocycle windS_const windS_pathEdge_arcA
  windS_pathEdge_arcB arcA arcB arcA_one_eq_arcB_zero arcB_one_eq_arcA_zero pathEdge rl rl_face
  rl_pathEdge iota faceC)
open SKEFTHawking.TorusCrossPeel

/-! ## §0. Subsingleton instances for the vanishing stages -/

instance : Subsingleton (Homology (Sph 1) 2) :=
  subsingleton_of_forall_eq 0 (fun x => SKEFTHawking.KummerHomologyT4.circleH_high 0 x)

instance : Subsingleton (Homology TwoTorus 3) := by
  have h := SKEFTHawking.KummerHomologyT4Full.twoTorus_three_free_finite
  haveI := h.1
  haveI := h.2.1
  exact (Module.finrank_zero_iff (R := ℤ)).mp h.2.2

/-! ## §1. The coordinate 1-cocycles (iterated factor pullbacks of `windS`) -/

/-- T² first-circle coordinate. -/
noncomputable def a2f : SingularCochainInt TwoTorus 1 :=
  cochainPullbackInt (prodFst (Sph 1) (Sph 1)) 1 windS

/-- T² second-circle coordinate. -/
noncomputable def a2s : SingularCochainInt TwoTorus 1 :=
  cochainPullbackInt (prodSnd (Sph 1) (Sph 1)) 1 windS

/-- T³ coordinates. -/
noncomputable def a3f : SingularCochainInt (Tor TwoTorus) 1 :=
  cochainPullbackInt (prodFst TwoTorus (Sph 1)) 1 a2f

noncomputable def a3g : SingularCochainInt (Tor TwoTorus) 1 :=
  cochainPullbackInt (prodFst TwoTorus (Sph 1)) 1 a2s

noncomputable def a3s : SingularCochainInt (Tor TwoTorus) 1 :=
  cochainPullbackInt (prodSnd TwoTorus (Sph 1)) 1 windS

/-- T⁴ coordinates `b₀ … b₃`. -/
noncomputable def b0 : SingularCochainInt (Tor (Tor TwoTorus)) 1 :=
  cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3f

noncomputable def b1 : SingularCochainInt (Tor (Tor TwoTorus)) 1 :=
  cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3g

noncomputable def b2 : SingularCochainInt (Tor (Tor TwoTorus)) 1 :=
  cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3s

noncomputable def b3 : SingularCochainInt (Tor (Tor TwoTorus)) 1 :=
  cochainPullbackInt (prodSnd (Tor TwoTorus) (Sph 1)) 1 windS

theorem a2f_eq : a2f = cochainPullbackInt (prodFst (Sph 1) (Sph 1)) 1 windS := rfl
theorem a2s_eq : a2s = cochainPullbackInt (prodSnd (Sph 1) (Sph 1)) 1 windS := rfl
theorem a3f_eq : a3f = cochainPullbackInt (prodFst TwoTorus (Sph 1)) 1 a2f := rfl
theorem a3g_eq : a3g = cochainPullbackInt (prodFst TwoTorus (Sph 1)) 1 a2s := rfl
theorem a3s_eq : a3s = cochainPullbackInt (prodSnd TwoTorus (Sph 1)) 1 windS := rfl
theorem b0_eq : b0 = cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3f := rfl
theorem b1_eq : b1 = cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3g := rfl
theorem b2_eq : b2 = cochainPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 1 a3s := rfl
theorem b3_eq : b3 = cochainPullbackInt (prodSnd (Tor TwoTorus) (Sph 1)) 1 windS := rfl

/-- Pullback preserves the cocycle property (unbundled form). -/
theorem pb_cocycle {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ} {a : SingularCochainInt Y n}
    (h : coboundaryₗ Y n a = 0) :
    coboundaryₗ X n (cochainPullbackInt φ n a) = 0 :=
  LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker φ ⟨a, LinearMap.mem_ker.mpr h⟩)

theorem a2f_cocycle : coboundaryₗ TwoTorus 1 a2f = 0 := pb_cocycle _ windS_cocycle
theorem a2s_cocycle : coboundaryₗ TwoTorus 1 a2s = 0 := pb_cocycle _ windS_cocycle
theorem a3f_cocycle : coboundaryₗ (Tor TwoTorus) 1 a3f = 0 := pb_cocycle _ a2f_cocycle
theorem a3g_cocycle : coboundaryₗ (Tor TwoTorus) 1 a3g = 0 := pb_cocycle _ a2s_cocycle
theorem a3s_cocycle : coboundaryₗ (Tor TwoTorus) 1 a3s = 0 := pb_cocycle _ windS_cocycle
theorem b0_cocycle : coboundaryₗ (Tor (Tor TwoTorus)) 1 b0 = 0 := pb_cocycle _ a3f_cocycle
theorem b1_cocycle : coboundaryₗ (Tor (Tor TwoTorus)) 1 b1 = 0 := pb_cocycle _ a3g_cocycle
theorem b2_cocycle : coboundaryₗ (Tor (Tor TwoTorus)) 1 b2 = 0 := pb_cocycle _ a3s_cocycle
theorem b3_cocycle : coboundaryₗ (Tor (Tor TwoTorus)) 1 b3 = 0 := pb_cocycle _ windS_cocycle

/-! ## §2. The iterated cross chains `t1 … t4` and their cycle laws -/

/-- The circle's glued two-arc 1-cycle (both arcs, coefficient `1`). -/
noncomputable def t1chain : SingularChainInt (Sph 1) 1 :=
  Finsupp.single (pathEdge (Sph 1) arcA) 1 + Finsupp.single (pathEdge (Sph 1) arcB) 1

/-- The two endpoint 0-faces of a path edge. -/
theorem face_zero_pathEdge (X : TopCat) (γ : C(unitInterval, ↑X)) :
    face (0 : Fin 2) (pathEdge X γ) = constSimplex (γ 1) 0 := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk 0))).injective
  show rl (face (0 : Fin 2) (pathEdge X γ)) = rl (constSimplex (γ 1) 0)
  rw [rl_face, rl_pathEdge]
  refine ContinuousMap.ext fun d => ?_
  show γ (iota (faceC (0 : Fin 2) d)) = γ 1
  congr 1
  apply Subtype.ext
  show ((iota (faceC (0 : Fin 2) d) : unitInterval) : ℝ) = ((1 : unitInterval) : ℝ)
  refine (stdSimplex_map_coord (⇑(ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2)))) d
    (1 : Fin 2)).trans ?_
  rw [Finset.filter_true_of_mem (fun j _ => by fin_cases j; decide)]
  exact d.2.2

theorem face_one_pathEdge (X : TopCat) (γ : C(unitInterval, ↑X)) :
    face (1 : Fin 2) (pathEdge X γ) = constSimplex (γ 0) 0 := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk 0))).injective
  show rl (face (1 : Fin 2) (pathEdge X γ)) = rl (constSimplex (γ 0) 0)
  rw [rl_face, rl_pathEdge]
  refine ContinuousMap.ext fun d => ?_
  show γ (iota (faceC (1 : Fin 2) d)) = γ 0
  congr 1
  apply Subtype.ext
  show ((iota (faceC (1 : Fin 2) d) : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ)
  refine (stdSimplex_map_coord (⇑(ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2)))) d
    (1 : Fin 2)).trans ?_
  rw [Finset.filter_false_of_mem (fun j _ => by fin_cases j; decide), Finset.sum_empty]
  rfl

/-- The boundary of a single edge. -/
theorem chainBoundary_single_edge (X : TopCat)
    (e : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 1))) :
    chainBoundary X 0 (Finsupp.single e 1)
      = Finsupp.single (face (0 : Fin 2) e) 1 - Finsupp.single (face (1 : Fin 2) e) 1 := by
  rw [chainBoundary_single, boundaryBasis]
  refine (Fin.sum_univ_two
    (f := fun i : Fin 2 => ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (face i e) (1 : ℤ))).trans ?_
  norm_num
  abel

/-- **`∂ t1chain = 0`** — the two arcs glue into a closed loop. -/
theorem t1_cycle : chainBoundary (Sph 1) 0 t1chain = 0 := by
  rw [t1chain, map_add, chainBoundary_single_edge, chainBoundary_single_edge,
    face_zero_pathEdge, face_one_pathEdge, face_zero_pathEdge, face_one_pathEdge,
    arcA_one_eq_arcB_zero, arcB_one_eq_arcA_zero]
  abel

/-- The T² cross 2-cycle. -/
noncomputable def t2chain : SingularChainInt TwoTorus 2 := torCross (Sph 1) 1 t1chain

theorem t2chain_eq : t2chain = torCross (Sph 1) 1 t1chain := rfl

theorem t2_cycle : chainBoundary TwoTorus 1 t2chain = 0 :=
  chainBoundary_torCross (Sph 1) 0 t1chain t1_cycle

/-- The T³ cross 3-cycle. -/
noncomputable def t3chain : SingularChainInt (Tor TwoTorus) 3 := torCross TwoTorus 2 t2chain

theorem t3chain_eq : t3chain = torCross TwoTorus 2 t2chain := rfl

theorem t3_cycle : chainBoundary (Tor TwoTorus) 2 t3chain = 0 :=
  chainBoundary_torCross TwoTorus 1 t2chain t2_cycle

/-- The T⁴ cross 4-cycle — the explicit chain-level `[S¹]×[S¹]×[S¹]×[S¹]`. -/
noncomputable def t4chain : SingularChainInt (Tor (Tor TwoTorus)) 4 :=
  torCross (Tor TwoTorus) 3 t3chain

theorem t4chain_eq : t4chain = torCross (Tor TwoTorus) 3 t3chain := rfl

theorem t4_cycle : chainBoundary (Tor (Tor TwoTorus)) 3 t4chain = 0 :=
  chainBoundary_torCross (Tor TwoTorus) 2 t3chain t3_cycle

/-! ## §3. Pullback helpers along the basepoint slice, and zero-cochain conveniences -/

/-- Pushforward composes (simplex level). -/
theorem mapSimplex_mapSimplex {X Y Z : TopCat} (φ : C(↑Y, ↑Z)) (ψ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapSimplex φ (mapSimplex ψ σ) = mapSimplex (φ.comp ψ) σ := by
  rw [mapSimplex, mapSimplex, mapSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_assoc]

/-- Basepoint-slice pullback undoes a first-factor pullback. -/
theorem pb_endAt_fst {Y : TopCat} {n : ℕ} (a : SingularCochainInt Y n) :
    cochainPullbackInt (endAt Y basePt) n
        (cochainPullbackInt (prodFst Y (Sph 1)) n a) = a := by
  funext σ
  rw [cochainPullbackInt_apply, cochainPullbackInt_apply, mapSimplex_mapSimplex]
  have hid : mapSimplex ((prodFst Y (Sph 1)).comp (endAt Y basePt)) σ = σ := by
    rw [show (prodFst Y (Sph 1)).comp (endAt Y basePt) = ContinuousMap.id ↑Y from
        ContinuousMap.ext fun _ => rfl]
    exact mapSimplex_id σ
  rw [hid]

/-- Cross-space constant pushforward: `mapSimplex (const b) σ = constSimplex b k`. -/
theorem mapSimplex_const' {X Y : TopCat} (b : ↑Y) {k : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk k))) :
    mapSimplex (ContinuousMap.const ↑X b : C(↑X, ↑Y)) σ = constSimplex b k := by
  rw [mapSimplex, constSimplex]
  congr 1

/-- Basepoint-slice pullback kills the second-factor winding cochain. -/
theorem pb_endAt_snd_windS {Y : TopCat} :
    cochainPullbackInt (endAt Y basePt) 1
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 windS) = 0 := by
  funext e
  show windS (mapSimplex (prodSnd Y (Sph 1)) (mapSimplex (endAt Y basePt) e)) = (0 : ℤ)
  rw [mapSimplex_mapSimplex]
  rw [show (prodSnd Y (Sph 1)).comp (endAt Y basePt)
      = ContinuousMap.const ↑Y basePt from ContinuousMap.ext fun _ => rfl]
  rw [mapSimplex_const']
  exact windS_const basePt

/-- Cup with the zero cochain (right). -/
theorem cup_zero_right {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p) :
    cup f (0 : SingularCochainInt X q) = 0 := by
  funext σ
  show f _ * 0 = 0
  rw [mul_zero]

/-- The Kronecker pairing of the zero cochain. -/
theorem kronecker_zero_left {X : TopCat} {n : ℕ} (c : SingularChainInt X n) :
    kronecker (0 : SingularCochainInt X n) c = 0 := by
  rw [kronecker_apply]
  simp

/-! ## §4. The cochain-level associativity `(x ⌣ (y ⌣ z)) = ((x ⌣ y) ⌣ z)` at `(2,1,1)` -/

theorem cup_assoc_2_1_1 {X : TopCat} (x : SingularCochainInt X 2)
    (y z : SingularCochainInt X 1) :
    cup x (cup y z) = cup (cup x y) z := by
  funext τ
  rw [cup_apply, cup_apply, cup_apply, cup_apply]
  have hx1 : frontFace (p := 2) (q := 1 + 1) τ
      = (TopCat.toSSet.obj X).map (frontIncl 2 (1 + 1)).op τ := rfl
  have hy1 : frontFace (p := 1) (q := 1) (backFace (p := 2) (q := 1 + 1) τ)
      = (TopCat.toSSet.obj X).map ((frontIncl 1 1 ≫ backIncl 2 (1 + 1))).op τ := by
    show (TopCat.toSSet.obj X).map (frontIncl 1 1).op
        ((TopCat.toSSet.obj X).map (backIncl 2 (1 + 1)).op τ) = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hz1 : backFace (p := 1) (q := 1) (backFace (p := 2) (q := 1 + 1) τ)
      = (TopCat.toSSet.obj X).map ((backIncl 1 1 ≫ backIncl 2 (1 + 1))).op τ := by
    show (TopCat.toSSet.obj X).map (backIncl 1 1).op
        ((TopCat.toSSet.obj X).map (backIncl 2 (1 + 1)).op τ) = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hx2 : frontFace (p := 2) (q := 1) (frontFace (p := 2 + 1) (q := 1) τ)
      = (TopCat.toSSet.obj X).map ((frontIncl 2 1 ≫ frontIncl (2 + 1) 1)).op τ := by
    show (TopCat.toSSet.obj X).map (frontIncl 2 1).op
        ((TopCat.toSSet.obj X).map (frontIncl (2 + 1) 1).op τ) = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hy2 : backFace (p := 2) (q := 1) (frontFace (p := 2 + 1) (q := 1) τ)
      = (TopCat.toSSet.obj X).map ((backIncl 2 1 ≫ frontIncl (2 + 1) 1)).op τ := by
    show (TopCat.toSSet.obj X).map (backIncl 2 1).op
        ((TopCat.toSSet.obj X).map (frontIncl (2 + 1) 1).op τ) = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hz2 : backFace (p := 2 + 1) (q := 1) τ
      = (TopCat.toSSet.obj X).map (backIncl (2 + 1) 1).op τ := rfl
  rw [hx1, hy1, hz1, hx2, hy2, hz2,
    show frontIncl 2 1 ≫ frontIncl (2 + 1) 1 = frontIncl 2 (1 + 1) from by decide,
    show backIncl 2 1 ≫ frontIncl (2 + 1) 1 = frontIncl 1 1 ≫ backIncl 2 (1 + 1) from by decide,
    show backIncl (2 + 1) 1 = backIncl 1 1 ≫ backIncl 2 (1 + 1) from by decide]
  ring

/-! ## §5. The value ledger — every Gram entry as an explicit integer

The base pairing, the four T² values, the nine T³ values, and the twenty-one T⁴ values (up to the
symmetry the class level supplies). Signs track the Koszul positions of the peeled circle. -/

/-- **The ground value**: the winding cochain counts the glued loop once. -/
theorem kronecker_windS_t1 : kronecker windS t1chain = 1 := by
  rw [t1chain, kronecker_add_right, kronecker_single, kronecker_single,
    windS_pathEdge_arcA, windS_pathEdge_arcB]
  norm_num

/-! ### T² values -/

theorem V2_ff : kronecker (cup a2f a2f) t2chain = 0 := by
  rw [a2f_eq, ← cochainPullbackInt_cup, kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Sph 1) (1 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Sph 1) 2))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 1) _
    (cup_cocycle _ _ windS_cocycle windS_cocycle) _
    (by rw [chainBoundary_mapChainInt, t2_cycle, map_zero])

theorem V2_fs : kronecker (cup a2f a2s) t2chain = -1 := by
  rw [a2f_eq, a2s_eq, t2chain_eq, kronecker_cup_snd_torCross, kronecker_windS_t1]
  norm_num

theorem V2_sf : kronecker (cup a2s a2f) t2chain = 1 := by
  rw [a2s_eq, t2chain_eq, kronecker_cupMid_torCross_0_1, a2f_eq, pb_endAt_fst,
    kronecker_windS_t1]

theorem V2_ss : kronecker (cup a2s a2s) t2chain = 0 := by
  rw [a2s_eq, t2chain_eq, kronecker_cupMid_torCross_0_1, pb_endAt_snd_windS,
    kronecker_zero_left]

/-! ### T³ values -/

theorem T3_ffg_f : kronecker (cup (cup a3f a3g) a3f) t3chain = 0 := by
  rw [a3f_eq, a3g_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology TwoTorus (2 + 1)) :=
    inferInstanceAs (Subsingleton (Homology TwoTorus 3))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 2) _
    (cup_cocycle _ _ (cup_cocycle _ _ a2f_cocycle a2s_cocycle) a2f_cocycle) _
    (by rw [chainBoundary_mapChainInt, t3_cycle, map_zero])

theorem T3_ffg_g : kronecker (cup (cup a3f a3g) a3g) t3chain = 0 := by
  rw [a3f_eq, a3g_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology TwoTorus (2 + 1)) :=
    inferInstanceAs (Subsingleton (Homology TwoTorus 3))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 2) _
    (cup_cocycle _ _ (cup_cocycle _ _ a2f_cocycle a2s_cocycle) a2s_cocycle) _
    (by rw [chainBoundary_mapChainInt, t3_cycle, map_zero])

theorem T3_ffg_s : kronecker (cup (cup a3f a3g) a3s) t3chain = -1 := by
  rw [a3f_eq, a3g_eq, ← cochainPullbackInt_cup, a3s_eq, t3chain_eq,
    kronecker_cup_snd_torCross, V2_fs]
  norm_num

theorem T3_fsf : kronecker (cup (cup a3f a3s) a3f) t3chain = 0 := by
  rw [a3f_eq, a3s_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_fst, V2_ff,
    neg_zero]

theorem T3_fsg : kronecker (cup (cup a3f a3s) a3g) t3chain = 1 := by
  rw [a3f_eq, a3s_eq, a3g_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_fst, V2_fs]
  norm_num

theorem T3_fss : kronecker (cup (cup a3f a3s) a3s) t3chain = 0 := by
  rw [a3f_eq, a3s_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_snd_windS,
    cup_zero_right, kronecker_zero_left, neg_zero]

theorem T3_gsf : kronecker (cup (cup a3g a3s) a3f) t3chain = -1 := by
  rw [a3g_eq, a3s_eq, a3f_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_fst, V2_sf]

theorem T3_gsg : kronecker (cup (cup a3g a3s) a3g) t3chain = 0 := by
  rw [a3g_eq, a3s_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_fst, V2_ss,
    neg_zero]

theorem T3_gss : kronecker (cup (cup a3g a3s) a3s) t3chain = 0 := by
  rw [a3g_eq, a3s_eq, t3chain_eq, kronecker_cupMid_torCross_1_1, pb_endAt_snd_windS,
    cup_zero_right, kronecker_zero_left, neg_zero]

/-! ### T⁴ values — the isotropic (no-`b₃`, all-first-factor) block -/

/-- The pushed-forward T⁴ cross cycle is a cycle (any target). -/
theorem hz4 {Z : TopCat} (φ : C(↑(Tor (Tor TwoTorus)), ↑Z)) :
    chainBoundary Z 3 (mapChainInt φ (3 + 1) t4chain) = 0 := by
  rw [chainBoundary_mapChainInt, t4_cycle, map_zero]

theorem V4_01_01 : kronecker (cup (cup b0 b1) (cup b0 b1)) t4chain = 0 := by
  rw [b0_eq, b1_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3f_cocycle a3g_cocycle)
      (cup_cocycle _ _ a3f_cocycle a3g_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

theorem V4_01_02 : kronecker (cup (cup b0 b1) (cup b0 b2)) t4chain = 0 := by
  rw [b0_eq, b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    ← cochainPullbackInt_cup, kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3f_cocycle a3g_cocycle)
      (cup_cocycle _ _ a3f_cocycle a3s_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

theorem V4_01_12 : kronecker (cup (cup b0 b1) (cup b1 b2)) t4chain = 0 := by
  rw [b0_eq, b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    ← cochainPullbackInt_cup, kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3f_cocycle a3g_cocycle)
      (cup_cocycle _ _ a3g_cocycle a3s_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

theorem V4_02_02 : kronecker (cup (cup b0 b2) (cup b0 b2)) t4chain = 0 := by
  rw [b0_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3f_cocycle a3s_cocycle)
      (cup_cocycle _ _ a3f_cocycle a3s_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

theorem V4_02_12 : kronecker (cup (cup b0 b2) (cup b1 b2)) t4chain = 0 := by
  rw [b0_eq, b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    ← cochainPullbackInt_cup, kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3f_cocycle a3s_cocycle)
      (cup_cocycle _ _ a3g_cocycle a3s_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

theorem V4_12_12 : kronecker (cup (cup b1 b2) (cup b1 b2)) t4chain = 0 := by
  rw [b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    kronecker_cochainPullbackInt]
  haveI : Subsingleton (Homology (Tor TwoTorus) (3 + 1)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  exact kronecker_eq_zero_of_cocycle_subsingleton (n := 3) _
    (cup_cocycle (p := 1 + 1) (q := 1 + 1) _ _ (cup_cocycle _ _ a3g_cocycle a3s_cocycle)
      (cup_cocycle _ _ a3g_cocycle a3s_cocycle)) _
    (hz4 (prodFst (Tor TwoTorus) (Sph 1)))

/-! ### T⁴ values — the cross block (one `b₃`) -/

theorem V4_01_03 : kronecker (cup (cup b0 b1) (cup b0 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b0_eq, b1_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_ffg_f]
  norm_num

theorem V4_01_13 : kronecker (cup (cup b0 b1) (cup b1 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b0_eq, b1_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_ffg_g]
  norm_num

/-- **The first complementary cross value**: `⟨(b₀⌣b₁) ⌣ (b₂⌣b₃), t4chain⟩ = 1`. -/
theorem V4_01_23 : kronecker (cup (cup b0 b1) (cup b2 b3)) t4chain = 1 := by
  rw [cup_assoc_2_1_1, b0_eq, b1_eq, ← cochainPullbackInt_cup, b2_eq,
    ← cochainPullbackInt_cup, b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_ffg_s]
  norm_num

theorem V4_02_03 : kronecker (cup (cup b0 b2) (cup b0 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b0_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_fsf]
  norm_num

/-- **The second complementary cross value**: `⟨(b₀⌣b₂) ⌣ (b₁⌣b₃), t4chain⟩ = −1`. -/
theorem V4_02_13 : kronecker (cup (cup b0 b2) (cup b1 b3)) t4chain = -1 := by
  rw [cup_assoc_2_1_1, b0_eq, b2_eq, ← cochainPullbackInt_cup, b1_eq,
    ← cochainPullbackInt_cup, b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_fsg]
  norm_num

theorem V4_02_23 : kronecker (cup (cup b0 b2) (cup b2 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b0_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_fss]
  norm_num

/-- **The third complementary cross value**: `⟨(b₁⌣b₂) ⌣ (b₀⌣b₃), t4chain⟩ = 1`. -/
theorem V4_12_03 : kronecker (cup (cup b1 b2) (cup b0 b3)) t4chain = 1 := by
  rw [cup_assoc_2_1_1, b1_eq, b2_eq, ← cochainPullbackInt_cup, b0_eq,
    ← cochainPullbackInt_cup, b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_gsf]
  norm_num

theorem V4_12_13 : kronecker (cup (cup b1 b2) (cup b1 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_gsg]
  norm_num

theorem V4_12_23 : kronecker (cup (cup b1 b2) (cup b2 b3)) t4chain = 0 := by
  rw [cup_assoc_2_1_1, b1_eq, b2_eq, ← cochainPullbackInt_cup, ← cochainPullbackInt_cup,
    b3_eq, t4chain_eq, kronecker_cup_snd_torCross, T3_gss]
  norm_num

/-! ### T⁴ values — the double-`b₃` block (basepoint slice kills the residue) -/

theorem V4_03_03 : kronecker (cup (cup b0 b3) (cup b0 b3)) t4chain = 0 := by
  rw [b0_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

theorem V4_03_13 : kronecker (cup (cup b0 b3) (cup b1 b3)) t4chain = 0 := by
  rw [b0_eq, b1_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

theorem V4_03_23 : kronecker (cup (cup b0 b3) (cup b2 b3)) t4chain = 0 := by
  rw [b0_eq, b2_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

theorem V4_13_13 : kronecker (cup (cup b1 b3) (cup b1 b3)) t4chain = 0 := by
  rw [b1_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

theorem V4_13_23 : kronecker (cup (cup b1 b3) (cup b2 b3)) t4chain = 0 := by
  rw [b1_eq, b2_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

theorem V4_23_23 : kronecker (cup (cup b2 b3) (cup b2 b3)) t4chain = 0 := by
  rw [b2_eq, b3_eq, t4chain_eq, kronecker_cupMid_torCross_1_2, cochainPullbackInt_cup,
    pb_endAt_snd_windS, cup_zero_right, cup_zero_right, kronecker_zero_left, neg_zero]

end SKEFTHawking.KummerT4GramCross
