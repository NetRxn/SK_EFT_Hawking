/-
# Phase 5q.H — K7 residual (a): the coordinatewise involution on the `T⁴` step tower

The step-tower (`Tor (Tor TwoTorus)`) form of the Kummer involution `τ : z ↦ z⁻¹` and its exact
cochain-level action on the coordinate 1-cocycles `b₀ … b₃` of `KummerT4GramCross`:

* `inv4C` — the coordinatewise conjugated inversion (each `Sph 1` factor through `invSphC`),
  an involution (`inv4C_comp_self`);
* `piC 0 … piC 3` — the four composite circle projections, with `bᵢ = πᵢ* windS`
  (`b_eq_pull`) and the intertwines `πᵢ ∘ inv4 = invSph ∘ πᵢ`;
* `b_inv` — **`inv4* bᵢ = −bᵢ − δuᵢ`** with the explicit correction `uᵢ = πᵢ* argCorrS`
  (from `KummerCircleInvolutionWind.windS_inv`);
* the Kronecker eigen-identities against cycles:
  `kronecker_b_inv` — `⟨bᵢ, (inv4)₊ z⟩ = −⟨bᵢ, z⟩` (degree 1),
  `kronecker_cup_inv` — `⟨bᵢ ⌣ bⱼ, (inv4)₊ z⟩ = ⟨bᵢ ⌣ bⱼ, z⟩` (degree 2; the corrections are
  coboundaries by the Leibniz rule, killed against cycles).

These are the `τ_* = −1` on `H₁` and `τ_* = +1` on `H₂` eigen-facts that drive the `Q`-side
Smith solve (`ker(1−τ_*) = 0` on `H₁(T⁴°)`, `ker(1+τ_*) = 0` on `H₂(T⁴°)`), via the cycle
detection of `KummerT4CycleDetection`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerCircleInvolutionWind
import SKEFTHawking.KummerT4GramCross

namespace SKEFTHawking.KummerT4TowerInvolution

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary kronecker kroneckerₗ
  kronecker_add_left kronecker_coboundary_chainBoundary)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply
  cochainPullbackInt_cup kronecker_cochainPullbackInt coboundary_cochainPullbackInt)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst)
open SKEFTHawking.TorusCrossPeel (prodSnd)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.KummerCircleInvolutionWind (invSphC invSphC_comp_self windS_inv argCorrS)
open SKEFTHawking.CircleWindingCocycle (windS windS_cocycle)
open SKEFTHawking.KummerT4GramCross (a2f a2s a3f a3g a3s b0 b1 b2 b3 a2f_eq a2s_eq a3f_eq a3g_eq
  a3s_eq b0_eq b1_eq b2_eq b3_eq b0_cocycle b1_cocycle b2_cocycle b3_cocycle)

noncomputable section

/-- The step-tower `T⁴` carrier. -/
abbrev T4S : TopCat := Tor (Tor TwoTorus)

/-! ## §1. The coordinatewise involution -/

/-- The coordinatewise inversion on `T²` (both `Sph 1` factors through `invSphC`). -/
def inv2C : C(↑TwoTorus, ↑TwoTorus) :=
  ⟨fun p => (invSphC p.1, invSphC p.2),
    (invSphC.continuous.comp continuous_fst).prodMk (invSphC.continuous.comp continuous_snd)⟩

/-- The coordinatewise inversion on `T³`. -/
def inv3C : C(↑(Tor TwoTorus), ↑(Tor TwoTorus)) :=
  ⟨fun p => (inv2C p.1, invSphC p.2),
    (inv2C.continuous.comp continuous_fst).prodMk (invSphC.continuous.comp continuous_snd)⟩

/-- **The coordinatewise inversion on the `T⁴` step tower** — the tower form of the Kummer
involution. -/
def inv4C : C(↑T4S, ↑T4S) :=
  ⟨fun p => (inv3C p.1, invSphC p.2),
    (inv3C.continuous.comp continuous_fst).prodMk (invSphC.continuous.comp continuous_snd)⟩

theorem inv2C_comp_self : inv2C.comp inv2C = ContinuousMap.id ↑TwoTorus := by
  refine ContinuousMap.ext fun p => ?_
  show (invSphC (invSphC p.1), invSphC (invSphC p.2)) = p
  have h1 := congrFun (congrArg DFunLike.coe invSphC_comp_self) p.1
  have h2 := congrFun (congrArg DFunLike.coe invSphC_comp_self) p.2
  exact Prod.ext h1 h2

theorem inv3C_comp_self : inv3C.comp inv3C = ContinuousMap.id ↑(Tor TwoTorus) := by
  refine ContinuousMap.ext fun p => ?_
  show (inv2C (inv2C p.1), invSphC (invSphC p.2)) = p
  have h1 := congrFun (congrArg DFunLike.coe inv2C_comp_self) p.1
  have h2 := congrFun (congrArg DFunLike.coe invSphC_comp_self) p.2
  exact Prod.ext h1 h2

/-- `inv4² = id` — the tower involution is an involution. -/
theorem inv4C_comp_self : inv4C.comp inv4C = ContinuousMap.id ↑T4S := by
  refine ContinuousMap.ext fun p => ?_
  show (inv3C (inv3C p.1), invSphC (invSphC p.2)) = p
  have h1 := congrFun (congrArg DFunLike.coe inv3C_comp_self) p.1
  have h2 := congrFun (congrArg DFunLike.coe invSphC_comp_self) p.2
  exact Prod.ext h1 h2

/-! ## §2. The four composite circle projections and the `b`-collapse -/

/-- The first-coordinate projection `T⁴ → S¹`. -/
def piC : Fin 4 → C(↑T4S, ↑(Sph 1))
  | 0 => ⟨fun p => p.1.1.1, by fun_prop⟩
  | 1 => ⟨fun p => p.1.1.2, by fun_prop⟩
  | 2 => ⟨fun p => p.1.2, by fun_prop⟩
  | 3 => ⟨fun p => p.2, by fun_prop⟩

/-- The four coordinate cocycles are the `πᵢ`-pullbacks of the winding cocycle. -/
theorem b_eq_pull : (b0 = cochainPullbackInt (piC 0) 1 windS)
    ∧ (b1 = cochainPullbackInt (piC 1) 1 windS)
    ∧ (b2 = cochainPullbackInt (piC 2) 1 windS)
    ∧ (b3 = cochainPullbackInt (piC 3) 1 windS) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext σ
  · show a3f (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ) = windS (mapSimplex (piC 0) σ)
    show a2f (mapSimplex (prodFst TwoTorus (Sph 1))
        (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ)) = _
    show windS (mapSimplex (prodFst (Sph 1) (Sph 1)) (mapSimplex (prodFst TwoTorus (Sph 1))
        (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ))) = _
    rw [← mapSimplex_comp, ← mapSimplex_comp]
    rfl
  · show a3g (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ) = windS (mapSimplex (piC 1) σ)
    show a2s (mapSimplex (prodFst TwoTorus (Sph 1))
        (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ)) = _
    show windS (mapSimplex (prodSnd (Sph 1) (Sph 1)) (mapSimplex (prodFst TwoTorus (Sph 1))
        (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ))) = _
    rw [← mapSimplex_comp, ← mapSimplex_comp]
    rfl
  · show a3s (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ) = windS (mapSimplex (piC 2) σ)
    show windS (mapSimplex (prodSnd TwoTorus (Sph 1))
        (mapSimplex (prodFst (Tor TwoTorus) (Sph 1)) σ)) = _
    rw [← mapSimplex_comp]
    rfl
  · rfl

/-- The intertwines: each projection conjugates the tower involution to the `Sph 1` inversion. -/
theorem piC_comp_inv4 (i : Fin 4) : (piC i).comp inv4C = invSphC.comp (piC i) := by
  fin_cases i <;> exact ContinuousMap.ext fun p => rfl

/-! ## §3. The correction cochains and `inv4* bᵢ = −bᵢ − δuᵢ` -/

/-- The four correction 0-cochains (pullbacks of the branch indicator). -/
def uCorr (i : Fin 4) : SingularCochainInt T4S 0 :=
  cochainPullbackInt (piC i) 0 argCorrS

/-- **The pullback-negation law for a windS-pullback along an intertwined projection.** -/
theorem pull_windS_inv (π : C(↑T4S, ↑(Sph 1))) (hπ : π.comp inv4C = invSphC.comp π)
    (σ : (TopCat.toSSet.obj T4S).obj (op (SimplexCategory.mk 1))) :
    cochainPullbackInt π 1 windS (mapSimplex inv4C σ)
      = -(cochainPullbackInt π 1 windS σ)
        - coboundary T4S 0 (cochainPullbackInt π 0 argCorrS) σ := by
  have h1 : cochainPullbackInt π 1 windS (mapSimplex inv4C σ)
      = windS (mapSimplex invSphC (mapSimplex π σ)) := by
    show windS (mapSimplex π (mapSimplex inv4C σ)) = _
    rw [← mapSimplex_comp, hπ, mapSimplex_comp]
  have h2 : coboundary T4S 0 (cochainPullbackInt π 0 argCorrS) σ
      = coboundary (Sph 1) 0 argCorrS (mapSimplex π σ) :=
    congrFun (coboundary_cochainPullbackInt π 0 argCorrS) σ
  rw [h1, windS_inv, h2]
  rfl

/-- The `b`-family as a `Fin 4`-indexed function. -/
def bFam : Fin 4 → SingularCochainInt T4S 1
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3

theorem bFam_eq_pull (i : Fin 4) : bFam i = cochainPullbackInt (piC i) 1 windS := by
  fin_cases i
  · exact b_eq_pull.1
  · exact b_eq_pull.2.1
  · exact b_eq_pull.2.2.1
  · exact b_eq_pull.2.2.2

theorem bFam_cocycle (i : Fin 4) : coboundaryₗ T4S 1 (bFam i) = 0 := by
  fin_cases i
  · exact b0_cocycle
  · exact b1_cocycle
  · exact b2_cocycle
  · exact b3_cocycle

/-- **`inv4* bᵢ = −bᵢ − δuᵢ`** — the coordinate cocycles negate under the tower involution up to
the explicit branch-indicator coboundaries. -/
theorem b_inv (i : Fin 4)
    (σ : (TopCat.toSSet.obj T4S).obj (op (SimplexCategory.mk 1))) :
    bFam i (mapSimplex inv4C σ) = -(bFam i σ) - coboundary T4S 0 (uCorr i) σ := by
  rw [bFam_eq_pull]
  exact pull_windS_inv (piC i) (piC_comp_inv4 i) σ

/-- The pullback of `bᵢ` along the involution, as a cochain identity. -/
theorem pull_inv4_b (i : Fin 4) :
    cochainPullbackInt inv4C 1 (bFam i)
      = -(bFam i) - coboundaryₗ T4S 0 (uCorr i) := by
  funext σ
  show bFam i (mapSimplex inv4C σ) = _
  rw [b_inv i σ]
  rfl

/-! ## §4. The Kronecker eigen-identities against cycles -/

/-- `⟨δw, z⟩ = 0` against a cycle. -/
theorem kronecker_coboundary_cycle {n : ℕ} (w : SingularCochainInt T4S n)
    (z : SingularChainInt T4S (n + 1)) (hz : chainBoundary T4S n z = 0) :
    kronecker (coboundary T4S n w) z = 0 := by
  rw [kronecker_coboundary_chainBoundary, hz]
  show kroneckerₗ n w (0 : SingularChainInt T4S n) = 0
  exact map_zero _

/-- **Degree-1 eigen-identity**: `⟨bᵢ, (inv4)₊ z⟩ = −⟨bᵢ, z⟩` on 1-cycles. -/
theorem kronecker_b_inv (i : Fin 4) (z : SingularChainInt T4S 1)
    (hz : chainBoundary T4S 0 z = 0) :
    kronecker (bFam i) (mapChainInt inv4C 1 z) = -kronecker (bFam i) z := by
  rw [← kronecker_cochainPullbackInt, pull_inv4_b]
  have h1 : kronecker (-(bFam i) - coboundaryₗ T4S 0 (uCorr i)) z
      = -kronecker (bFam i) z - kronecker (coboundaryₗ T4S 0 (uCorr i)) z := by
    show kroneckerₗ 1 (-(bFam i) - coboundaryₗ T4S 0 (uCorr i)) z = _
    rw [map_sub, map_neg]
    rfl
  rw [h1, show kronecker (coboundaryₗ T4S 0 (uCorr i)) z
      = kronecker (coboundary T4S 0 (uCorr i)) z from rfl,
    kronecker_coboundary_cycle _ z hz, sub_zero]

/-- The left Leibniz collapse at degrees `(0,1)`: `δa ⌣ g = δ(a ⌣ g)` for a 1-cocycle `g`. -/
theorem cup_coboundary_left_0_1 (a : SingularCochainInt T4S 0) (g : SingularCochainInt T4S 1)
    (hg : coboundaryₗ T4S 1 g = 0) :
    coboundaryₗ T4S (0 + 1) (cup a g) = cup (coboundaryₗ T4S 0 a) g := by
  funext τ
  show coboundary T4S (0 + 1) (cup a g) τ = cup (coboundaryₗ T4S 0 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary T4S 1 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, mul_zero, add_zero]
  rfl

/-- **Degree-2 eigen-identity**: `⟨bᵢ ⌣ bⱼ, (inv4)₊ z⟩ = ⟨bᵢ ⌣ bⱼ, z⟩` on 2-cycles — the two
negations cancel and the branch corrections are coboundaries. -/
theorem kronecker_cup_inv (i j : Fin 4) (z : SingularChainInt T4S 2)
    (hz : chainBoundary T4S 1 z = 0) :
    kronecker (cup (bFam i) (bFam j)) (mapChainInt inv4C 2 z)
      = kronecker (cup (bFam i) (bFam j)) z := by
  rw [← kronecker_cochainPullbackInt]
  have hpull : cochainPullbackInt inv4C 2 (cup (bFam i) (bFam j))
      = cup (cochainPullbackInt inv4C 1 (bFam i)) (cochainPullbackInt inv4C 1 (bFam j)) :=
    cochainPullbackInt_cup inv4C (bFam i) (bFam j)
  rw [hpull, pull_inv4_b, pull_inv4_b]
  -- expand the product of the two `−b − δu` factors
  have hexp : cup (-(bFam i) - coboundaryₗ T4S 0 (uCorr i))
        (-(bFam j) - coboundaryₗ T4S 0 (uCorr j))
      = cup (bFam i) (bFam j)
        + (cup (bFam i) (coboundaryₗ T4S 0 (uCorr j))
          + (cup (coboundaryₗ T4S 0 (uCorr i)) (bFam j)
            + cup (coboundaryₗ T4S 0 (uCorr i)) (coboundaryₗ T4S 0 (uCorr j)))) := by
    have h1 : -(bFam i) - coboundaryₗ T4S 0 (uCorr i)
        = (-1 : ℤ) • (bFam i + coboundaryₗ T4S 0 (uCorr i)) := by
      funext τ
      show -(bFam i τ) - _ = (-1 : ℤ) * (bFam i τ + _)
      ring
    have h2 : -(bFam j) - coboundaryₗ T4S 0 (uCorr j)
        = (-1 : ℤ) • (bFam j + coboundaryₗ T4S 0 (uCorr j)) := by
      funext τ
      show -(bFam j τ) - _ = (-1 : ℤ) * (bFam j τ + _)
      ring
    rw [h1, h2, cup_smul_left, cup_smul_right, smul_smul,
      show ((-1 : ℤ) * (-1 : ℤ)) = 1 by norm_num, one_smul, cup_add_left, cup_add_right,
      cup_add_right]
    abel
  rw [hexp]
  -- kronecker is additive; the three correction terms vanish against the cycle
  have hk : ∀ f g : SingularCochainInt T4S 2, kronecker (f + g) z
      = kronecker f z + kronecker g z := fun f g => kronecker_add_left f g z
  rw [hk, hk, hk]
  -- term `b ⌣ δu` is (−1)·δ(b ⌣ u)
  have ht1 : kronecker (cup (bFam i) (coboundaryₗ T4S 0 (uCorr j))) z = 0 := by
    have hL := cup_coboundary_right (X := T4S) (p := 1) (q := 0) (bFam i) (uCorr j)
      (bFam_cocycle i)
    have h2 : cup (bFam i) (coboundaryₗ T4S 0 (uCorr j))
        = (-1 : ℤ) • coboundaryₗ T4S (1 + 0) (cup (bFam i) (uCorr j)) := by
      rw [hL, smul_smul, show ((-1 : ℤ) * (-1 : ℤ) ^ (1 : ℕ)) = 1 by norm_num, one_smul]
    rw [h2, show ((-1 : ℤ) • coboundaryₗ T4S (1 + 0) (cup (bFam i) (uCorr j)))
        = (-1 : ℤ) • coboundary T4S 1 (cup (bFam i) (uCorr j)) from rfl]
    have := kronecker_coboundary_cycle (cup (bFam i) (uCorr j)) z hz
    show kroneckerₗ 2 ((-1 : ℤ) • coboundary T4S 1 (cup (bFam i) (uCorr j))) z = 0
    rw [map_smul]
    show (-1 : ℤ) • kronecker (coboundary T4S 1 (cup (bFam i) (uCorr j))) z = 0
    rw [this, smul_zero]
  -- term `δu ⌣ b` is δ(u ⌣ b)
  have ht2 : kronecker (cup (coboundaryₗ T4S 0 (uCorr i)) (bFam j)) z = 0 := by
    rw [← cup_coboundary_left_0_1 (uCorr i) (bFam j) (bFam_cocycle j),
      show coboundaryₗ T4S (0 + 1) (cup (uCorr i) (bFam j))
        = coboundary T4S 1 (cup (uCorr i) (bFam j)) from rfl]
    exact kronecker_coboundary_cycle _ z hz
  -- term `δu ⌣ δu` is δ(u ⌣ δu)
  have ht3 : kronecker (cup (coboundaryₗ T4S 0 (uCorr i)) (coboundaryₗ T4S 0 (uCorr j))) z
      = 0 := by
    have hcoc : coboundaryₗ T4S 1 (coboundaryₗ T4S 0 (uCorr j)) = 0 := by
      funext τ
      exact congrFun (congrArg _ rfl) τ |>.trans
        (coboundary_comp_coboundary T4S 0 (uCorr j) ▸ rfl)
    rw [← cup_coboundary_left_0_1 (uCorr i) (coboundaryₗ T4S 0 (uCorr j)) hcoc,
      show coboundaryₗ T4S (0 + 1) (cup (uCorr i) (coboundaryₗ T4S 0 (uCorr j)))
        = coboundary T4S 1 (cup (uCorr i) (coboundaryₗ T4S 0 (uCorr j))) from rfl]
    exact kronecker_coboundary_cycle _ z hz
  rw [ht1, ht2, ht3]
  ring

end

end SKEFTHawking.KummerT4TowerInvolution
