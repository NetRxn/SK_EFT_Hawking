/-
# Phase 5q.H — K7 residual (a): explicit cycle detection on the `T⁴` step tower

The Kronecker detection substrate for the `τ_*`-eigenvalue solve: explicit slot 1-cycles and
pair 2-cycles (pushforwards of the banked `t1chain`/`t2chain` cross cycles along basepoint
inclusions) pair with the coordinate cocycles `b₀…b₃` and their cup squares in a `±identity`
matrix, so the Kronecker functionals **detect** `H₁(T⁴;ℤ)` and `H₂(T⁴;ℤ)` (a surjective map onto
`ℤ⁴`/`ℤ⁶` between equal-rank free modules is injective). Combined with the eigen-identities of
`KummerT4TowerInvolution` this pins the involution action:

* `tower_H1_fixed_eq_zero` — a `τ_*`-fixed `H₁`-class vanishes (`τ_* = −1` on `H₁`),
* `tower_H2_anti_eq_zero` — a `τ_*`-anti-fixed `H₂`-class vanishes (`τ_* = +1` on `H₂`),

transported to the actual `TorusFour = (S¹)⁴` along `fourStepHomeoTorusFour`
(the conjugation `fourStep ∘ inv4 = τ ∘ fourStep`):

* `t4_H1_fixed_eq_zero`, `t4_H2_anti_eq_zero` — the inputs of the `Q`-side Smith solve
  (`ker(1−τ_*) = 0` on `H₁(T⁴°)`, `ker(1+τ_*) = 0` on `H₂(T⁴°)`, after the puncture window).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerT4TowerInvolution
import SKEFTHawking.KummerHomologyT4Full

namespace SKEFTHawking.KummerT4CycleDetection

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary kronecker kroneckerₗ
  Homology cycles kroneckerHInt kroneckerHInt_mk_mk)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp mapSimplex_id)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt chainBoundary_mapChainInt
  Homology.mapInt Homology.mapInt_mk Homology.mapInt_comp)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply
  cochainPullbackInt_cup kronecker_cochainPullbackInt)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst)
open SKEFTHawking.TorusCrossPeel (prodSnd)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.CircleWindingCocycle (windS windS_cocycle windS_const)
open SKEFTHawking.KummerT4GramCross (a2f a2s a2f_eq a2s_eq t1chain t2chain t1_cycle t2_cycle
  kronecker_windS_t1 V2_fs)
open SKEFTHawking.KummerT4TowerInvolution (T4S inv4C bFam bFam_eq_pull bFam_cocycle piC
  kronecker_b_inv kronecker_cup_inv)
open SKEFTHawking.KummerCircleInvolutionWind (invSphC)
open SKEFTHawking.KummerInvolution (torusFourInvolution torusFourInvolution_continuous)
open SKEFTHawking.KummerK3Base (TorusFour)

noncomputable section

/-- The basepoint of `Sph 1` (the banked arc origin). -/
abbrev bp : ↑(Sph 1) := SKEFTHawking.TorusCrossPeel.basePt

/-! ## §0. Pullback toolkit -/

/-- Pullback along a composite is the iterated pullback. -/
theorem pull_pull {A B C : TopCat} (phi : C(↑A, ↑B)) (psi : C(↑B, ↑C)) {n : ℕ}
    (a : SingularCochainInt C n) :
    cochainPullbackInt phi n (cochainPullbackInt psi n a)
      = cochainPullbackInt (psi.comp phi) n a := by
  funext s
  show a (mapSimplex psi (mapSimplex phi s)) = a (mapSimplex (psi.comp phi) s)
  rw [mapSimplex_comp]

/-- Pullback along the identity. -/
theorem pull_id {A : TopCat} {n : ℕ} (a : SingularCochainInt A n) :
    cochainPullbackInt (ContinuousMap.id ↑A) n a = a := by
  funext s
  show a (mapSimplex (ContinuousMap.id ↑A) s) = a s
  rw [mapSimplex_id]

/-- The pushforward of any simplex under a constant map is the constant simplex. -/
theorem mapSimplex_constMap {A B : TopCat} (b : ↑B) {n : ℕ}
    (s : (TopCat.toSSet.obj A).obj (op (SimplexCategory.mk n))) :
    mapSimplex (ContinuousMap.const ↑A b) s = constSimplex b n := by
  rw [mapSimplex, constSimplex]
  congr 1

/-- Pulling the winding cocycle back along a constant map kills it. -/
theorem pull_const_windS {A : TopCat} (b : ↑(Sph 1)) :
    cochainPullbackInt (ContinuousMap.const ↑A b : C(↑A, ↑(Sph 1))) 1 windS = 0 := by
  funext s
  show windS (mapSimplex (ContinuousMap.const ↑A b) s) = 0
  rw [mapSimplex_constMap, windS_const]

/-- Cup with a zero left factor vanishes. -/
theorem cup_zero_left {X : TopCat} {p q : ℕ} (g : SingularCochainInt X q) :
    cup (0 : SingularCochainInt X p) g = 0 := by
  funext t
  rw [cup_apply]
  show (0 : ℤ) * _ = 0
  exact zero_mul _

/-- Cup with a zero right factor vanishes. -/
theorem cup_zero_right {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p) :
    cup f (0 : SingularCochainInt X q) = 0 := by
  funext t
  rw [cup_apply]
  show _ * (0 : ℤ) = 0
  exact mul_zero _

/-- Kronecker with a zero cochain vanishes. -/
theorem kronecker_zero {X : TopCat} {n : ℕ} (c : SingularChainInt X n) :
    kronecker (0 : SingularCochainInt X n) c = 0 :=
  LinearMap.map_zero₂ (kroneckerₗ n) c
/-! ## §1. The slot and pair inclusions -/

/-- The four slot inclusions `S¹ → T⁴` (basepoints elsewhere). -/
def iotaS : Fin 4 → C(↑(Sph 1), ↑T4S)
  | 0 => ⟨fun z => (((z, bp), bp), bp), by fun_prop⟩
  | 1 => ⟨fun z => (((bp, z), bp), bp), by fun_prop⟩
  | 2 => ⟨fun z => (((bp, bp), z), bp), by fun_prop⟩
  | 3 => ⟨fun z => (((bp, bp), bp), z), by fun_prop⟩

/-- The six pair inclusions `T² → T⁴` (lexicographic pairs, basepoints elsewhere). -/
def iotaP : Fin 6 → C(↑TwoTorus, ↑T4S)
  | 0 => ⟨fun q => (((q.1, q.2), bp), bp), by fun_prop⟩
  | 1 => ⟨fun q => (((q.1, bp), q.2), bp), by fun_prop⟩
  | 2 => ⟨fun q => (((q.1, bp), bp), q.2), by fun_prop⟩
  | 3 => ⟨fun q => (((bp, q.1), q.2), bp), by fun_prop⟩
  | 4 => ⟨fun q => (((bp, q.1), bp), q.2), by fun_prop⟩
  | 5 => ⟨fun q => (((bp, bp), q.1), q.2), by fun_prop⟩

/-! ## §2. Pullback collapses along the inclusions -/

theorem pull_iotaS_0_b0 :
    cochainPullbackInt (iotaS 0) 1 (bFam 0) = windS := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaS 0) = ContinuousMap.id ↑(Sph 1) from
      ContinuousMap.ext fun z => rfl, pull_id]

theorem pull_iotaS_1_b0 :
    cochainPullbackInt (iotaS 1) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaS 1) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_2_b0 :
    cochainPullbackInt (iotaS 2) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaS 2) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_3_b0 :
    cochainPullbackInt (iotaS 3) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaS 3) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_0_b1 :
    cochainPullbackInt (iotaS 0) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaS 0) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_1_b1 :
    cochainPullbackInt (iotaS 1) 1 (bFam 1) = windS := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaS 1) = ContinuousMap.id ↑(Sph 1) from
      ContinuousMap.ext fun z => rfl, pull_id]

theorem pull_iotaS_2_b1 :
    cochainPullbackInt (iotaS 2) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaS 2) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_3_b1 :
    cochainPullbackInt (iotaS 3) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaS 3) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_0_b2 :
    cochainPullbackInt (iotaS 0) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaS 0) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_1_b2 :
    cochainPullbackInt (iotaS 1) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaS 1) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_2_b2 :
    cochainPullbackInt (iotaS 2) 1 (bFam 2) = windS := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaS 2) = ContinuousMap.id ↑(Sph 1) from
      ContinuousMap.ext fun z => rfl, pull_id]

theorem pull_iotaS_3_b2 :
    cochainPullbackInt (iotaS 3) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaS 3) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_0_b3 :
    cochainPullbackInt (iotaS 0) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaS 0) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_1_b3 :
    cochainPullbackInt (iotaS 1) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaS 1) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_2_b3 :
    cochainPullbackInt (iotaS 2) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaS 2) = ContinuousMap.const ↑(Sph 1) bp from
      ContinuousMap.ext fun z => rfl, pull_const_windS]

theorem pull_iotaS_3_b3 :
    cochainPullbackInt (iotaS 3) 1 (bFam 3) = windS := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaS 3) = ContinuousMap.id ↑(Sph 1) from
      ContinuousMap.ext fun z => rfl, pull_id]

theorem pull_iotaP_0_b0 :
    cochainPullbackInt (iotaP 0) 1 (bFam 0) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 0) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_0_b1 :
    cochainPullbackInt (iotaP 0) 1 (bFam 1) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 0) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

theorem pull_iotaP_0_b2 :
    cochainPullbackInt (iotaP 0) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 0) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_0_b3 :
    cochainPullbackInt (iotaP 0) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 0) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_1_b0 :
    cochainPullbackInt (iotaP 1) 1 (bFam 0) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 1) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_1_b1 :
    cochainPullbackInt (iotaP 1) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 1) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_1_b2 :
    cochainPullbackInt (iotaP 1) 1 (bFam 2) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 1) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

theorem pull_iotaP_1_b3 :
    cochainPullbackInt (iotaP 1) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 1) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_2_b0 :
    cochainPullbackInt (iotaP 2) 1 (bFam 0) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 2) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_2_b1 :
    cochainPullbackInt (iotaP 2) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 2) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_2_b2 :
    cochainPullbackInt (iotaP 2) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 2) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_2_b3 :
    cochainPullbackInt (iotaP 2) 1 (bFam 3) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 2) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

theorem pull_iotaP_3_b0 :
    cochainPullbackInt (iotaP 3) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 3) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_3_b1 :
    cochainPullbackInt (iotaP 3) 1 (bFam 1) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 3) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_3_b2 :
    cochainPullbackInt (iotaP 3) 1 (bFam 2) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 3) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

theorem pull_iotaP_3_b3 :
    cochainPullbackInt (iotaP 3) 1 (bFam 3) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 3) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_4_b0 :
    cochainPullbackInt (iotaP 4) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 4) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_4_b1 :
    cochainPullbackInt (iotaP 4) 1 (bFam 1) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 4) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_4_b2 :
    cochainPullbackInt (iotaP 4) 1 (bFam 2) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 4) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_4_b3 :
    cochainPullbackInt (iotaP 4) 1 (bFam 3) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 4) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

theorem pull_iotaP_5_b0 :
    cochainPullbackInt (iotaP 5) 1 (bFam 0) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 0).comp (iotaP 5) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_5_b1 :
    cochainPullbackInt (iotaP 5) 1 (bFam 1) = 0 := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 1).comp (iotaP 5) = ContinuousMap.const ↑TwoTorus bp from
      ContinuousMap.ext fun q => rfl, pull_const_windS]

theorem pull_iotaP_5_b2 :
    cochainPullbackInt (iotaP 5) 1 (bFam 2) = a2f := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 2).comp (iotaP 5) = prodFst (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2f_eq.symm

theorem pull_iotaP_5_b3 :
    cochainPullbackInt (iotaP 5) 1 (bFam 3) = a2s := by
  rw [bFam_eq_pull, pull_pull,
    show (piC 3).comp (iotaP 5) = prodSnd (Sph 1) (Sph 1) from
      ContinuousMap.ext fun q => rfl]
  exact a2s_eq.symm

/-! ## §3. The explicit cycles and the pairing matrices -/

/-- The slot 1-cycles (the `j`-th circle factor). -/
def zS (j : Fin 4) : SingularChainInt T4S 1 := mapChainInt (iotaS j) 1 t1chain

theorem zS_cycle (j : Fin 4) : chainBoundary T4S 0 (zS j) = 0 := by
  rw [zS, chainBoundary_mapChainInt, t1_cycle, map_zero]

/-- The pair 2-cycles (the `(k,l)`-th coordinate 2-torus). -/
def zP (a : Fin 6) : SingularChainInt T4S 2 := mapChainInt (iotaP a) 2 t2chain

theorem zP_cycle (a : Fin 6) : chainBoundary T4S 1 (zP a) = 0 := by
  rw [zP, chainBoundary_mapChainInt, t2_cycle, map_zero]

/-- The lexicographic pair table. -/
def pFst : Fin 6 → Fin 4
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2

def pSnd : Fin 6 → Fin 4
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 2 | 4 => 3 | 5 => 3

/-- The six coordinate cup 2-cocycles. -/
def cupFam (a : Fin 6) : SingularCochainInt T4S 2 := cup (bFam (pFst a)) (bFam (pSnd a))

theorem cupFam_cocycle (a : Fin 6) : coboundaryₗ T4S 2 (cupFam a) = 0 :=
  cup_cocycle _ _ (bFam_cocycle _) (bFam_cocycle _)

/-- The reduced slot pairing: `⟨bᵢ, zⱼ⟩` as a Kronecker of the pulled-back cocycle. -/
theorem kr_slot_expand (i j : Fin 4) :
    kronecker (bFam i) (zS j) = kronecker (cochainPullbackInt (iotaS j) 1 (bFam i)) t1chain := by
  rw [zS, ← kronecker_cochainPullbackInt]

/-- **The slot pairing matrix is the identity**: `⟨bᵢ, zⱼ⟩ = δᵢⱼ`. -/
theorem kronecker_b_zS : ∀ i j : Fin 4, kronecker (bFam i) (zS j) = if i = j then 1 else 0
  | 0, 0 => by rw [kr_slot_expand, pull_iotaS_0_b0, kronecker_windS_t1]; decide
  | 0, 1 => by rw [kr_slot_expand, pull_iotaS_1_b0, kronecker_zero]; decide
  | 0, 2 => by rw [kr_slot_expand, pull_iotaS_2_b0, kronecker_zero]; decide
  | 0, 3 => by rw [kr_slot_expand, pull_iotaS_3_b0, kronecker_zero]; decide
  | 1, 0 => by rw [kr_slot_expand, pull_iotaS_0_b1, kronecker_zero]; decide
  | 1, 1 => by rw [kr_slot_expand, pull_iotaS_1_b1, kronecker_windS_t1]; decide
  | 1, 2 => by rw [kr_slot_expand, pull_iotaS_2_b1, kronecker_zero]; decide
  | 1, 3 => by rw [kr_slot_expand, pull_iotaS_3_b1, kronecker_zero]; decide
  | 2, 0 => by rw [kr_slot_expand, pull_iotaS_0_b2, kronecker_zero]; decide
  | 2, 1 => by rw [kr_slot_expand, pull_iotaS_1_b2, kronecker_zero]; decide
  | 2, 2 => by rw [kr_slot_expand, pull_iotaS_2_b2, kronecker_windS_t1]; decide
  | 2, 3 => by rw [kr_slot_expand, pull_iotaS_3_b2, kronecker_zero]; decide
  | 3, 0 => by rw [kr_slot_expand, pull_iotaS_0_b3, kronecker_zero]; decide
  | 3, 1 => by rw [kr_slot_expand, pull_iotaS_1_b3, kronecker_zero]; decide
  | 3, 2 => by rw [kr_slot_expand, pull_iotaS_2_b3, kronecker_zero]; decide
  | 3, 3 => by rw [kr_slot_expand, pull_iotaS_3_b3, kronecker_windS_t1]; decide

/-- The reduced pair pairing. -/
theorem kr_pair_expand (a b : Fin 6) :
    kronecker (cupFam a) (zP b)
      = kronecker (cup (cochainPullbackInt (iotaP b) 1 (bFam (pFst a)))
          (cochainPullbackInt (iotaP b) 1 (bFam (pSnd a)))) t2chain := by
  rw [zP, ← kronecker_cochainPullbackInt, cupFam]
  show kronecker (cochainPullbackInt (iotaP b) (1 + 1)
      (cup (bFam (pFst a)) (bFam (pSnd a)))) t2chain = _
  rw [cochainPullbackInt_cup]

/-- **The pair pairing matrix is `−1` times the identity.** -/
theorem kronecker_cup_zP : ∀ a b : Fin 6, kronecker (cupFam a) (zP b) = if a = b then -1 else 0
  | 0, 0 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_0_b0, pull_iotaP_0_b1, V2_fs]
    decide
  | 0, 1 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_1_b1, cup_zero_right, kronecker_zero]
    decide
  | 0, 2 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_2_b1, cup_zero_right, kronecker_zero]
    decide
  | 0, 3 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_3_b0, cup_zero_left, kronecker_zero]
    decide
  | 0, 4 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_4_b0, cup_zero_left, kronecker_zero]
    decide
  | 0, 5 => by
    rw [kr_pair_expand, show pFst 0 = (0 : Fin 4) from rfl,
      show pSnd 0 = (1 : Fin 4) from rfl,
      pull_iotaP_5_b0, cup_zero_left, kronecker_zero]
    decide
  | 1, 0 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_0_b2, cup_zero_right, kronecker_zero]
    decide
  | 1, 1 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_1_b0, pull_iotaP_1_b2, V2_fs]
    decide
  | 1, 2 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_2_b2, cup_zero_right, kronecker_zero]
    decide
  | 1, 3 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_3_b0, cup_zero_left, kronecker_zero]
    decide
  | 1, 4 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_4_b0, cup_zero_left, kronecker_zero]
    decide
  | 1, 5 => by
    rw [kr_pair_expand, show pFst 1 = (0 : Fin 4) from rfl,
      show pSnd 1 = (2 : Fin 4) from rfl,
      pull_iotaP_5_b0, cup_zero_left, kronecker_zero]
    decide
  | 2, 0 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_0_b3, cup_zero_right, kronecker_zero]
    decide
  | 2, 1 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_1_b3, cup_zero_right, kronecker_zero]
    decide
  | 2, 2 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_2_b0, pull_iotaP_2_b3, V2_fs]
    decide
  | 2, 3 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_3_b0, cup_zero_left, kronecker_zero]
    decide
  | 2, 4 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_4_b0, cup_zero_left, kronecker_zero]
    decide
  | 2, 5 => by
    rw [kr_pair_expand, show pFst 2 = (0 : Fin 4) from rfl,
      show pSnd 2 = (3 : Fin 4) from rfl,
      pull_iotaP_5_b0, cup_zero_left, kronecker_zero]
    decide
  | 3, 0 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_0_b2, cup_zero_right, kronecker_zero]
    decide
  | 3, 1 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_1_b1, cup_zero_left, kronecker_zero]
    decide
  | 3, 2 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_2_b1, cup_zero_left, kronecker_zero]
    decide
  | 3, 3 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_3_b1, pull_iotaP_3_b2, V2_fs]
    decide
  | 3, 4 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_4_b2, cup_zero_right, kronecker_zero]
    decide
  | 3, 5 => by
    rw [kr_pair_expand, show pFst 3 = (1 : Fin 4) from rfl,
      show pSnd 3 = (2 : Fin 4) from rfl,
      pull_iotaP_5_b1, cup_zero_left, kronecker_zero]
    decide
  | 4, 0 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_0_b3, cup_zero_right, kronecker_zero]
    decide
  | 4, 1 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_1_b1, cup_zero_left, kronecker_zero]
    decide
  | 4, 2 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_2_b1, cup_zero_left, kronecker_zero]
    decide
  | 4, 3 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_3_b3, cup_zero_right, kronecker_zero]
    decide
  | 4, 4 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_4_b1, pull_iotaP_4_b3, V2_fs]
    decide
  | 4, 5 => by
    rw [kr_pair_expand, show pFst 4 = (1 : Fin 4) from rfl,
      show pSnd 4 = (3 : Fin 4) from rfl,
      pull_iotaP_5_b1, cup_zero_left, kronecker_zero]
    decide
  | 5, 0 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_0_b2, cup_zero_left, kronecker_zero]
    decide
  | 5, 1 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_1_b3, cup_zero_right, kronecker_zero]
    decide
  | 5, 2 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_2_b2, cup_zero_left, kronecker_zero]
    decide
  | 5, 3 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_3_b3, cup_zero_right, kronecker_zero]
    decide
  | 5, 4 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_4_b2, cup_zero_left, kronecker_zero]
    decide
  | 5, 5 => by
    rw [kr_pair_expand, show pFst 5 = (2 : Fin 4) from rfl,
      show pSnd 5 = (3 : Fin 4) from rfl,
      pull_iotaP_5_b2, pull_iotaP_5_b3, V2_fs]
    decide

/-! ## §4. Class-level functionals and detection -/

/-- The degree-1 cohomology classes of the coordinate cocycles. -/
def bCls (i : Fin 4) : Cohomology T4S 1 :=
  Submodule.Quotient.mk ⟨bFam i, LinearMap.mem_ker.mpr (bFam_cocycle i)⟩

/-- The degree-2 cohomology classes of the coordinate cup squares. -/
def cupCls (a : Fin 6) : Cohomology T4S 2 :=
  Submodule.Quotient.mk ⟨cupFam a, LinearMap.mem_ker.mpr (cupFam_cocycle a)⟩

/-- The joint degree-1 Kronecker functional. -/
def Phi1 : Homology T4S 1 →ₗ[ℤ] (Fin 4 → ℤ) :=
  LinearMap.pi (fun i => kroneckerHInt 1 (bCls i))

/-- The joint degree-2 Kronecker functional. -/
def Phi2 : Homology T4S 2 →ₗ[ℤ] (Fin 6 → ℤ) :=
  LinearMap.pi (fun a => kroneckerHInt 2 (cupCls a))

/-- The slot-cycle classes as homology classes. -/
def zSCls (j : Fin 4) : Homology T4S 1 :=
  Submodule.Quotient.mk ⟨zS j, by
    show zS j ∈ cycles T4S 1
    exact LinearMap.mem_ker.mpr (zS_cycle j)⟩

/-- The pair-cycle classes as homology classes. -/
def zPCls (b : Fin 6) : Homology T4S 2 :=
  Submodule.Quotient.mk ⟨zP b, by
    show zP b ∈ cycles T4S 2
    exact LinearMap.mem_ker.mpr (zP_cycle b)⟩

/-- The slot-cycle classes hit the standard basis under `Phi1`. -/
theorem Phi1_zS (j : Fin 4) : Phi1 (zSCls j) = Pi.single j (1 : ℤ) := by
  funext i
  have h1 : Phi1 (zSCls j) i = kronecker (bFam i) (zS j) := kroneckerHInt_mk_mk _ _
  rw [h1, kronecker_b_zS]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

/-- The pair-cycle classes hit minus the standard basis under `Phi2`. -/
theorem Phi2_zP (b : Fin 6) : Phi2 (zPCls b) = -(Pi.single b (1 : ℤ)) := by
  funext a
  have h1 : Phi2 (zPCls b) a = kronecker (cupFam a) (zP b) := kroneckerHInt_mk_mk _ _
  rw [h1, kronecker_cup_zP]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Pi.neg_apply, Pi.single_eq_same]
  · rw [if_neg h, Pi.neg_apply, Pi.single_eq_of_ne h, neg_zero]

/-- `Phi1` is surjective (it hits the standard basis). -/
theorem Phi1_surjective : Function.Surjective Phi1 := by
  intro v
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1 : ℤ) := by
    funext i
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  have hmem : v ∈ LinearMap.range Phi1 := by
    rw [hv]
    exact Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ ⟨zSCls j, Phi1_zS j⟩)
  exact hmem

/-- `Phi2` is surjective (it hits minus the standard basis). -/
theorem Phi2_surjective : Function.Surjective Phi2 := by
  intro v
  have hv : v = ∑ b : Fin 6, v b • Pi.single b (1 : ℤ) := by
    funext a
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  have hmem : v ∈ LinearMap.range Phi2 := by
    rw [hv]
    refine Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ ?_)
    exact ⟨-(zPCls b), by rw [map_neg, Phi2_zP, neg_neg]⟩
  exact hmem

/-- **Degree-1 detection**: the four Kronecker functionals jointly detect `H₁(T⁴;ℤ) ≅ ℤ⁴`. -/
theorem Phi1_injective : Function.Injective Phi1 := by
  have e := SKEFTHawking.KummerHomologyT4Full.fourStepH1EquivFin4
  have hsurj : Function.Surjective
      (Phi1.comp (e.symm : (Fin 4 → ℤ) →ₗ[ℤ] Homology T4S 1)) :=
    Phi1_surjective.comp e.symm.surjective
  have hinj : Function.Injective
      (Phi1.comp (e.symm : (Fin 4 → ℤ) →ₗ[ℤ] Homology T4S 1)) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  intro x y hxy
  have h := hinj (a₁ := e x) (a₂ := e y) (by
    show Phi1 (e.symm (e x)) = Phi1 (e.symm (e y))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    exact hxy)
  exact e.injective h

/-- **Degree-2 detection**: the six Kronecker functionals jointly detect `H₂(T⁴;ℤ) ≅ ℤ⁶`. -/
theorem Phi2_injective : Function.Injective Phi2 := by
  have e := SKEFTHawking.KummerHomologyT4H2.fourStepH2EquivFin6
  have hsurj : Function.Surjective
      (Phi2.comp (e.symm : (Fin 6 → ℤ) →ₗ[ℤ] Homology T4S 2)) :=
    Phi2_surjective.comp e.symm.surjective
  have hinj : Function.Injective
      (Phi2.comp (e.symm : (Fin 6 → ℤ) →ₗ[ℤ] Homology T4S 2)) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  intro x y hxy
  have h := hinj (a₁ := e x) (a₂ := e y) (by
    show Phi2 (e.symm (e x)) = Phi2 (e.symm (e y))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    exact hxy)
  exact e.injective h

/-! ## §5. The eigen-vanishing on the step tower -/

/-- The class-level degree-1 eigen-identity. -/
theorem kroneckerHInt_b_inv (i : Fin 4) (y : Homology T4S 1) :
    kroneckerHInt 1 (bCls i) (Homology.mapInt inv4C 1 y)
      = -kroneckerHInt 1 (bCls i) y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hz : chainBoundary T4S 0 (z : SingularChainInt T4S 1) = 0 :=
    LinearMap.mem_ker.mp z.2
  have hL : kroneckerHInt 1 (bCls i)
        (Homology.mapInt inv4C 1 (Submodule.Quotient.mk z))
      = kronecker (bFam i) (mapChainInt inv4C 1 (z : SingularChainInt T4S 1)) := by
    rw [show (Submodule.Quotient.mk z : Homology T4S 1) = Homology.mk T4S 1 z from rfl,
      Homology.mapInt_mk]
    exact kroneckerHInt_mk_mk _ _
  have hR : kroneckerHInt 1 (bCls i) (Submodule.Quotient.mk z)
      = kronecker (bFam i) (z : SingularChainInt T4S 1) := kroneckerHInt_mk_mk _ _
  rw [hL, hR]
  exact kronecker_b_inv i _ hz

/-- The class-level degree-2 eigen-identity. -/
theorem kroneckerHInt_cup_inv (a : Fin 6) (y : Homology T4S 2) :
    kroneckerHInt 2 (cupCls a) (Homology.mapInt inv4C 2 y)
      = kroneckerHInt 2 (cupCls a) y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hz : chainBoundary T4S 1 (z : SingularChainInt T4S 2) = 0 :=
    LinearMap.mem_ker.mp z.2
  have hL : kroneckerHInt 2 (cupCls a)
        (Homology.mapInt inv4C 2 (Submodule.Quotient.mk z))
      = kronecker (cupFam a) (mapChainInt inv4C 2 (z : SingularChainInt T4S 2)) := by
    rw [show (Submodule.Quotient.mk z : Homology T4S 2) = Homology.mk T4S 2 z from rfl,
      Homology.mapInt_mk]
    exact kroneckerHInt_mk_mk _ _
  have hR : kroneckerHInt 2 (cupCls a) (Submodule.Quotient.mk z)
      = kronecker (cupFam a) (z : SingularChainInt T4S 2) := kroneckerHInt_mk_mk _ _
  rw [hL, hR]
  exact kronecker_cup_inv (pFst a) (pSnd a) _ hz

/-- **A `τ_*`-fixed `H₁`-class vanishes** (`τ_* = −1` on `H₁(T⁴;ℤ)`). -/
theorem tower_H1_fixed_eq_zero (y : Homology T4S 1)
    (h : Homology.mapInt inv4C 1 y = y) : y = 0 := by
  apply Phi1_injective
  rw [map_zero]
  funext i
  show kroneckerHInt 1 (bCls i) y = (0 : Fin 4 → ℤ) i
  have h1 := kroneckerHInt_b_inv i y
  rw [h] at h1
  have : kroneckerHInt 1 (bCls i) y = 0 := by omega
  rw [this]
  rfl

/-- **A `τ_*`-anti-fixed `H₂`-class vanishes** (`τ_* = +1` on `H₂(T⁴;ℤ)`). -/
theorem tower_H2_anti_eq_zero (y : Homology T4S 2)
    (h : Homology.mapInt inv4C 2 y = -y) : y = 0 := by
  apply Phi2_injective
  rw [map_zero]
  funext a
  show kroneckerHInt 2 (cupCls a) y = (0 : Fin 6 → ℤ) a
  have h1 := kroneckerHInt_cup_inv a y
  rw [h, map_neg] at h1
  have : kroneckerHInt 2 (cupCls a) y = 0 := by omega
  rw [this]
  rfl

/-! ## §6. Transport to the actual `TorusFour = (S¹)⁴` -/

/-- The step-tower homeomorphism as a continuous map. -/
def fourStepC : C(↑T4S, ↑(TopCat.of TorusFour)) :=
  ⟨SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour,
    SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour.continuous⟩

/-- Its inverse. -/
def fourStepInvC : C(↑(TopCat.of TorusFour), ↑T4S) :=
  ⟨SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour.symm,
    SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour.symm.continuous⟩

/-- The Kummer involution as a continuous map on the `TorusFour` carrier. -/
def tauT4C : C(↑(TopCat.of TorusFour), ↑(TopCat.of TorusFour)) :=
  ⟨torusFourInvolution, torusFourInvolution_continuous⟩

/-- **The conjugation**: the tower homeomorphism intertwines the coordinatewise tower involution
with the Kummer involution. -/
theorem fourStep_comp_inv4 : fourStepC.comp inv4C = tauT4C.comp fourStepC := by
  refine ContinuousMap.ext fun p => ?_
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := p
  have hkey : ∀ x : ↑(Sph 1),
      SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm (invSphC x)
        = (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm x)⁻¹ := by
    intro x
    show SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm
        (SKEFTHawking.KummerHomologyT4.circleHomeoSph1
          ((SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm x)⁻¹))
      = (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm x)⁻¹
    exact SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm_apply_apply _
  show ((SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm (invSphC a),
      (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm (invSphC b),
        (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm (invSphC c),
          SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm (invSphC d)))) : TorusFour)
    = torusFourInvolution (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm a,
        (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm b,
          (SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm c,
            SKEFTHawking.KummerHomologyT4.circleHomeoSph1.symm d)))
  rw [torusFourInvolution]
  exact Prod.ext (hkey a) (Prod.ext (hkey b) (Prod.ext (hkey c) (hkey d)))

theorem fourStep_comp_inv : fourStepC.comp fourStepInvC
    = ContinuousMap.id ↑(TopCat.of TorusFour) :=
  ContinuousMap.ext fun x =>
    SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour.apply_symm_apply x

theorem fourStepInv_comp : fourStepInvC.comp fourStepC = ContinuousMap.id ↑T4S :=
  ContinuousMap.ext fun x =>
    SKEFTHawking.KummerHomologyT4H2.fourStepHomeoTorusFour.symm_apply_apply x

/-- The tower homeomorphism induces bijections on homology. -/
theorem fourStep_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt fourStepC n) :=
  SKEFTHawking.SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all
    fourStepC fourStepInvC fourStepInv_comp fourStep_comp_inv n

/-- **A `τ_*`-fixed `H₁(T⁴;ℤ)`-class vanishes** — the `TorusFour` carrier form. -/
theorem t4_H1_fixed_eq_zero (y : Homology (TopCat.of TorusFour) 1)
    (h : Homology.mapInt tauT4C 1 y = y) : y = 0 := by
  obtain ⟨w, rfl⟩ := (fourStep_mapInt_bijective 1).surjective y
  have h1 : Homology.mapInt tauT4C 1 (Homology.mapInt fourStepC 1 w)
      = Homology.mapInt (tauT4C.comp fourStepC) 1 w := by
    rw [Homology.mapInt_comp]
    rfl
  have h2 : Homology.mapInt fourStepC 1 (Homology.mapInt inv4C 1 w)
      = Homology.mapInt (fourStepC.comp inv4C) 1 w := by
    rw [Homology.mapInt_comp]
    rfl
  rw [h1, ← fourStep_comp_inv4, ← h2] at h
  have hfix : Homology.mapInt inv4C 1 w = w := (fourStep_mapInt_bijective 1).injective h
  rw [tower_H1_fixed_eq_zero w hfix, map_zero]

/-- **A `τ_*`-anti-fixed `H₂(T⁴;ℤ)`-class vanishes** — the `TorusFour` carrier form: the input
of the `Q`-side Smith solve's injectivity leg. -/
theorem t4_H2_anti_eq_zero (y : Homology (TopCat.of TorusFour) 2)
    (h : Homology.mapInt tauT4C 2 y = -y) : y = 0 := by
  obtain ⟨w, rfl⟩ := (fourStep_mapInt_bijective 2).surjective y
  have h1 : Homology.mapInt tauT4C 2 (Homology.mapInt fourStepC 2 w)
      = Homology.mapInt (tauT4C.comp fourStepC) 2 w := by
    rw [Homology.mapInt_comp]
    rfl
  have h2 : Homology.mapInt fourStepC 2 (Homology.mapInt inv4C 2 w)
      = Homology.mapInt (fourStepC.comp inv4C) 2 w := by
    rw [Homology.mapInt_comp]
    rfl
  rw [h1, ← fourStep_comp_inv4, ← h2] at h
  have hanti : Homology.mapInt inv4C 2 w = -w := by
    apply (fourStep_mapInt_bijective 2).injective
    rw [h, map_neg]
  rw [tower_H2_anti_eq_zero w hanti, map_zero]

end

end SKEFTHawking.KummerT4CycleDetection
