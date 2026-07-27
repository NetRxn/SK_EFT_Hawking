/-
# Phase 5q.H — the seam-winding parity vector, and the **discharge** of the K3 `h1Free` residual

`KummerK3H1SeamLattice.SeamWindingOdd` — the last residual of the K3 `h1Free` chain — still
quantified over lifts `y : H₁(T⁴°;ℤ)` and over connecting chains `v`. This module removes both,
computes what is left, and **closes the chain**: `free_h1K3_uncond` is `Module.Free ℤ H₁(K3;ℤ)`
with *no* hypothesis.

## §1–§4 — the reduction to sixteen integer 4-vectors

The mechanism is a cochain-level identity. Write `g = fourStepInv ∘ ι : T⁴° → (S¹-tower)`, and pull
the four coordinate winding cocycles `bᵢ` and their branch-correction 0-cochains `uᵢ`
(`KummerT4TowerInvolution.pull_inv4_b`: `inv* bᵢ = −bᵢ − δuᵢ`) back along `g`:

* `wPT i = g* bᵢ ∈ C¹(T⁴°;ℤ)`, `aPT i = g* uᵢ ∈ C⁰(T⁴°;ℤ)`, and
* `pull_tauC_wPT` — `τ* (wPT i) = −wPT i − δ (aPT i)` **on the nose**, at cochain level.

Evaluating on the explicit seam-difference cycle `γ_c − γ_{c'} + v − τ_# v`
(`KummerK3H1SeamLattice.seamDiffChain`) the connecting chain contributes
`⟨w, v⟩ − ⟨τ*w, v⟩ = 2⟨w, v⟩ + ⟨a, ∂v⟩`, and `∂v = pt_c − pt_{c'}` is *endpoint data only*. So

  `windowJ [γ_c − γ_{c'} + v − τ_# v] i = seamWind c i − seamWind c' i + 2·⟨wPT i, v⟩`

(`windowJ_seamDiffChain`), where the **seam-winding vector**

  `seamWind c i = wPT i (γ_c) + aPT i (pt_c)`

depends on `c` and `i` alone — no lift, no connecting path, no homology. The `v`-term is visibly
even, so the connecting path never has to be constructed: the discharge plan's "build an explicit
path in `T⁴°`" step is **provably unnecessary**.

## §5–§7 — the computation

`windowJ` in coordinates is a genuine winding number: `s2c ∘ πᵢ ∘ g = psiC i`, the `i`-th circle
coordinate of `T⁴ = (S¹)⁴` (`s2c_comp_piC_comp_gPT`), so `wPT i σ = windMap` of the `i`-th
coordinate edge (`wPT_apply`) and `aPT i` is the `arg = π` indicator (`aPT_constSimplex`).

The `c`-th seam half-loop is `t ↦ c · exp(ρ · a(t))` on the chart sphere, whose covering lift is
**linear in the chart coordinate** — `seamLift`, built by hand, no covering-space theory. Against
it `windMap_eq_of_char` computes everything, and since a fixed point has `c_i ∈ {1, −1}`
(`coordC_eIndex`), two cases per coordinate suffice:

* `c_i = 1` — the arc `exp(ρ) ⤳ exp(−ρ)` through `1`: winding `0`, branch bit `0`, `seamWind = 0`;
* `c_i = −1`, `i = 0` — the arc `−exp(ρ) ⤳ −exp(−ρ)` sweeps *through* `−1`: winding `−1`, branch
  bit `0`;
* `c_i = −1`, `i ≠ 0` — the loop sits *at* `−1`: winding `0`, branch bit `1`.

Either nontrivial case is odd: `seamWind_odd_iff` — **`seamWind c i` is odd exactly when `c_i = −1`**.
So `seamWind c` is literally the half-period bit vector of `c`, matching the geometric expectation
`seamWind c i ≡ 2(v_c)_i (mod 2)`. (The `i = 0` / `i ≠ 0` split is an artifact of the basepoint
`(1,0) ∈ ℂ² ⊃ S³`, whose chart image moves only in coordinate `0`; the *total* is basepoint-free.)

## §8 — the discharge

The 16 fixed points are `{±1}⁴`, so distinct ones differ in some coordinate, where one seam-winding
integer is `0` and the other odd: `seamWindParityInjective`. Hence `seamWindingOdd`,
`seamClass_injective`, `qLatticeInSeamSpan` and `free_h1K3_uncond` — all unconditional.

**Falsifiability.** The load-bearing statement `seamWind_odd_iff` is an *iff* against concrete
geometry: it pins `seamWind` (built from `sphereEmbedPTC`, `genS3Simplex`, `centeredChartParam`) to
the coordinate value of the fixed point. No geometry-free substitute satisfies it — a `c`-constant
`seamWind` is even-or-odd uniformly and cannot track `c_i`, and `seamWindParityInjective` fails
outright for it (`EIndex` has 16 elements, so `c ≠ c'` witnesses exist).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3H1SeamLattice
import SKEFTHawking.KummerK3E1Package

namespace SKEFTHawking.KummerK3SeamWindingParity

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt (Homology chainBoundary SingularChainInt cycles kronecker
  kroneckerₗ kroneckerHInt kroneckerHInt_mk_mk kronecker_single kronecker_add_right
  kronecker_coboundary_chainBoundary)
open SKEFTHawking.SingularCohomologyInt (SingularCochainInt coboundary coboundaryₗ Cohomology)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply
  kronecker_cochainPullbackInt coboundary_cochainPullbackInt)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_mk mapChainInt
  mapChainInt_comp mapChainInt_single cyclesMapInt cyclesMapInt_coe)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.CircleWindingCocycle (CircleT rl windC windC_apply windS windS_apply s2c
  windMap windMap_eq_of_char v0 v1 coe_v0_one coe_v1_one mapSimplex_constSimplex)
open SKEFTHawking.KummerCircleInvolutionWind (argCorr argCorrS d0)
open SKEFTHawking.KummerT4TowerInvolution (piC bFam_eq_pull)
open SKEFTHawking.TorusCrossPeel (rl_mapSimplex)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerInvolution (negOne torusFourInvolution)
open SKEFTHawking.KummerPuncturedTorus (centeredChartParam excisionRadius mem_fixedSet_iff)
open SKEFTHawking.KummerWeld (scaleToChart scaleToChart_negS3 continuous_scaleToChart
  eIndex_fixedSet)
open SKEFTHawking.KummerResolutionPiece (S3 negS3)
open SKEFTHawking.KummerRP3H1Pin (genS3Simplex genPath)
open SKEFTHawking.SingularH0PathConnected (pathSimplex pathSimplexMap toUnitInterval)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC tauC)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerQuotientDeckFunctional (sBase sphereEmbedPT sphereEmbedPTC liftChain)
open SKEFTHawking.KummerQuotientH2Solve (inclXC inclXC_comp_tauC)
open SKEFTHawking.KummerT4TowerInvolution (T4S inv4C uCorr bFam pull_inv4_b)
open SKEFTHawking.KummerT4CycleDetection (bCls fourStepC fourStepInvC tauT4C fourStep_comp_inv4
  fourStep_comp_inv fourStepInv_comp)
open SKEFTHawking.KummerRP3H1Pin (genS3Simplex)
open SKEFTHawking.ChainComplexLESInt (mem_cycles_succ)
open SKEFTHawking.KummerK3H1Vanish
open SKEFTHawking.KummerK3H1SeamLattice

noncomputable section

/-! ## §0. Kronecker sub/neg linearity (the additive companions of `kronecker_add_*`) -/

private theorem kron_sub_right {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c d : SingularChainInt X n) : kronecker f (c - d) = kronecker f c - kronecker f d := by
  simpa using map_sub (kroneckerₗ (X := X) n f) c d

private theorem kron_neg_left {X : TopCat} {n : ℕ} (f : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker (-f) c = -kronecker f c := by
  rw [← neg_one_smul ℤ f, SKEFTHawking.SingularHomologyInt.kronecker_smul_left, neg_one_smul]

private theorem kron_sub_left {X : TopCat} {n : ℕ} (f g : SingularCochainInt X n)
    (c : SingularChainInt X n) : kronecker (f - g) c = kronecker f c - kronecker g c := by
  rw [sub_eq_add_neg, SKEFTHawking.SingularHomologyInt.kronecker_add_left, kron_neg_left,
    ← sub_eq_add_neg]

/-! ## §1. The window map and the two pulled-back cochains -/

/-- **The window map** `T⁴° → (S¹-tower)`: the puncture inclusion followed by the tower
identification. This is exactly the map `windowJ` factors through. -/
def gPT : C(↑PTtop, ↑T4S) := fourStepInvC.comp inclXC

/-- **The `i`-th winding 1-cochain on `T⁴°`** — the pullback of `KummerT4TowerInvolution.bFam i`
along the window map. Its Kronecker pairing against a cycle is the `i`-th component of `windowJ`
(`windowJ_mk`). -/
def wPT (i : Fin 4) : SingularCochainInt PTtop 1 := cochainPullbackInt gPT 1 (bFam i)

/-- **The `i`-th branch-correction 0-cochain on `T⁴°`** — the pullback of
`KummerT4TowerInvolution.uCorr i`, i.e. the `arg = π` indicator of the `i`-th circle coordinate.
This is the primitive that makes `τ* w = −w` fail only by a coboundary. -/
def aPT (i : Fin 4) : SingularCochainInt PTtop 0 := cochainPullbackInt gPT 0 (uCorr i)

/-- The tower identification intertwines the Kummer involution with the coordinatewise one
(`fourStep_comp_inv4` read on the inverse side). -/
theorem fourStepInvC_comp_tauT4C : fourStepInvC.comp tauT4C = inv4C.comp fourStepInvC := by
  refine ContinuousMap.ext fun x => ?_
  have h1 : fourStepC (inv4C (fourStepInvC x)) = tauT4C (fourStepC (fourStepInvC x)) :=
    congrFun (congrArg DFunLike.coe fourStep_comp_inv4) (fourStepInvC x)
  have h2 : fourStepC (fourStepInvC x) = x :=
    congrFun (congrArg DFunLike.coe fourStep_comp_inv) x
  have h3 : fourStepInvC (fourStepC (inv4C (fourStepInvC x))) = inv4C (fourStepInvC x) :=
    congrFun (congrArg DFunLike.coe fourStepInv_comp) (inv4C (fourStepInvC x))
  rw [h2] at h1
  show fourStepInvC (tauT4C x) = inv4C (fourStepInvC x)
  rw [← h1, h3]

/-- **Equivariance of the window map**: `g ∘ τ = inv ∘ g`. The deck involution of the punctured
torus is the coordinatewise circle inversion, seen through the window. -/
theorem gPT_comp_tauC : gPT.comp tauC = inv4C.comp gPT := by
  show (fourStepInvC.comp inclXC).comp tauC = inv4C.comp (fourStepInvC.comp inclXC)
  rw [ContinuousMap.comp_assoc, inclXC_comp_tauC, ← ContinuousMap.comp_assoc,
    fourStepInvC_comp_tauT4C, ContinuousMap.comp_assoc]

/-! ## §2. `windowJ` is the Kronecker pairing against `wPT` -/

/-- **`windowJ` on an explicit cycle** — the four window functionals of `KummerK3H1SeamLattice` are
literally the Kronecker pairings of the four pulled-back winding cocycles. -/
theorem windowJ_mk (z : cycles PTtop 1) (i : Fin 4) :
    windowJ (Homology.mk PTtop 1 z) i = kronecker (wPT i) (z : SingularChainInt PTtop 1) := by
  rw [windowJ_apply, Homology.mapInt_mk, Homology.mapInt_mk]
  have h1 : kroneckerHInt 1 (bCls i)
        (Homology.mk T4S 1 (cyclesMapInt fourStepInvC 1 (cyclesMapInt inclXC 1 z)))
      = kronecker (bFam i)
        (mapChainInt fourStepInvC 1 (mapChainInt inclXC 1 (z : SingularChainInt PTtop 1))) :=
    kroneckerHInt_mk_mk _ _
  rw [h1, wPT, kronecker_cochainPullbackInt, gPT, mapChainInt_comp]

/-! ## §3. The cochain-level negation, and the connecting chain dropping out -/

/-- **`τ* wPT = −wPT − δ aPT`, at cochain level.** The pullback of the coordinate winding cocycle
along the deck involution negates up to the explicit branch coboundary
(`KummerT4TowerInvolution.pull_inv4_b`, transported through the equivariant window map). -/
theorem pull_tauC_wPT (i : Fin 4) :
    cochainPullbackInt tauC 1 (wPT i) = -(wPT i) - coboundaryₗ PTtop 0 (aPT i) := by
  have hcomp : cochainPullbackInt tauC 1 (wPT i)
      = cochainPullbackInt gPT 1 (cochainPullbackInt inv4C 1 (bFam i)) := by
    rw [wPT, SKEFTHawking.KummerT4CycleDetection.pull_pull,
      SKEFTHawking.KummerT4CycleDetection.pull_pull, gPT_comp_tauC]
  have hcob : coboundaryₗ PTtop 0 (aPT i)
      = cochainPullbackInt gPT 1 (coboundaryₗ T4S 0 (uCorr i)) := by
    rw [aPT]
    exact coboundary_cochainPullbackInt gPT 0 (uCorr i)
  rw [hcomp, pull_inv4_b, map_sub, map_neg, ← wPT, hcob]

/-- **The deck image of a chain, paired against the winding cochain**: `⟨w, τ_# v⟩ = −⟨w, v⟩ −
⟨a, ∂v⟩`. The *only* trace of `v` that survives mod 2 is its boundary. -/
theorem kronecker_wPT_mapChainInt_tauC (i : Fin 4) (v : SingularChainInt PTtop 1) :
    kronecker (wPT i) (mapChainInt tauC 1 v)
      = -kronecker (wPT i) v - kronecker (aPT i) (chainBoundary PTtop 0 v) := by
  rw [← kronecker_cochainPullbackInt, pull_tauC_wPT, kron_sub_left, kron_neg_left,
    show (coboundaryₗ PTtop 0 (aPT i)) = coboundary PTtop 0 (aPT i) from rfl,
    kronecker_coboundary_chainBoundary]

/-! ## §4. The seam-winding vector, and the residual as finite arithmetic -/

/-- **THE SEAM-WINDING VECTOR.** For each of the 16 exceptional indices `c`, the four integers

  `seamWind c i = ⟨wPT i, γ_c⟩ + aPT i (pt_c)`

— the winding number of the `c`-th chart-sphere half-loop in the `i`-th circle coordinate, plus the
`arg = π` branch indicator at its basepoint. No lift, no connecting path, no homology class enters:
this is a function of `c` and `i` only. -/
def seamWind (c : EIndex) (i : Fin 4) : ℤ :=
  wPT i (mapSimplex (sphereEmbedPTC c) genS3Simplex)
    + aPT i (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0)

/-- **THE EVALUATION.** The `i`-th window functional of the explicit seam-difference cycle is the
seam-winding difference, plus an explicitly even connecting-chain term. -/
theorem windowJ_seamDiffChain (c c' : EIndex) (v : SingularChainInt PTtop 1)
    (hv : chainBoundary PTtop 0 v = seamPtChain c - seamPtChain c') (i : Fin 4) :
    windowJ (Homology.mk PTtop 1
        ⟨seamDiffChain c c' v, mem_cycles_succ.mpr (seamDiffChain_cycle c c' v hv)⟩) i
      = (seamWind c i - seamWind c' i) + 2 * kronecker (wPT i) v := by
  rw [windowJ_mk]
  show kronecker (wPT i) (seamDiffChain c c' v) = _
  rw [seamDiffChain, kron_sub_right, kronecker_add_right, kron_sub_right,
    kronecker_wPT_mapChainInt_tauC, hv, liftChain, liftChain, kronecker_single, kronecker_single,
    kron_sub_right, seamPtChain, seamPtChain, kronecker_single, kronecker_single, seamWind,
    seamWind]
  ring

/-- **THE FINITE FORM OF THE RESIDUAL** — *the sixteen seam-winding vectors are pairwise distinct
mod 2.*

This is `KummerK3H1SeamLattice.SeamWindingOdd` with every quantifier over homology and over
connecting chains removed: a statement about `16 × 4` fixed integers. It is **discharged** in §8
(`seamWindParityInjective`); it survives as a named `Prop` because it is the exact hinge between
the homological reduction (§1–§4) and the analytic computation (§5–§7).

*Non-vacuity*: it is a distinctness claim about the concrete function `seamWind`, which is built
from the chart-sphere embeddings; any `c`-independent replacement of the geometry falsifies it
outright (`EIndex` has 16 elements, so `c ≠ c'` witnesses exist). -/
def SeamWindParityInjective : Prop :=
  ∀ c c' : EIndex, c ≠ c' → ∃ i : Fin 4, ¬ ((2 : ℤ) ∣ (seamWind c i - seamWind c' i))

/-- **`SeamWindingOdd` from the finite residual** — the connecting-chain term is even, so it cannot
change the parity. -/
theorem seamWindingOdd_of_parity (h : SeamWindParityInjective) : SeamWindingOdd := by
  refine seamWindingOdd_of_explicit ?_
  intro c c' hne v hv
  obtain ⟨i, hi⟩ := h c c' hne
  refine ⟨i, fun hdvd => hi ?_⟩
  rw [windowJ_seamDiffChain c c' v hv i] at hdvd
  omega

/-- **`QLatticeInSeamSpan` from the finite residual.** -/
theorem qLatticeInSeamSpan_of_parity (h : SeamWindParityInjective) : QLatticeInSeamSpan :=
  qLatticeInSeamSpan_of_seamWindingOdd (seamWindingOdd_of_parity h)

/-! ## §5. The window map in coordinates — `seamWind` is a winding number plus a branch bit -/

/-- The four circle coordinates of `T⁴ = (S¹)⁴`, bundled. -/
def coordC : Fin 4 → C(↑(TopCat.of TorusFour), ↑CircleT)
  | 0 => ⟨fun z => z.1, by fun_prop⟩
  | 1 => ⟨fun z => z.2.1, by fun_prop⟩
  | 2 => ⟨fun z => z.2.2.1, by fun_prop⟩
  | 3 => ⟨fun z => z.2.2.2, by fun_prop⟩

/-- **The `i`-th circle coordinate of a point of `T⁴°`.** This is what the `i`-th window functional
actually measures — `psiC_bridge` identifies it with the tower route `s2c ∘ πᵢ ∘ g`. -/
def psiC (i : Fin 4) : C(↑PTtop, ↑CircleT) := (coordC i).comp inclXC

/-- The tower identification really is "take the four circle coordinates". -/
theorem s2c_piC_fourStepInvC (i : Fin 4) (z : ↑(TopCat.of TorusFour)) :
    s2c (piC i (fourStepInvC z)) = coordC i z := by
  have hfs : fourStepC (fourStepInvC z) = z :=
    congrFun (congrArg DFunLike.coe fourStep_comp_inv) z
  have hform : fourStepC (fourStepInvC z)
      = (s2c (piC 0 (fourStepInvC z)), s2c (piC 1 (fourStepInvC z)),
         s2c (piC 2 (fourStepInvC z)), s2c (piC 3 (fourStepInvC z))) := rfl
  rw [hfs] at hform
  fin_cases i
  · exact (congrArg Prod.fst hform).symm
  · exact (congrArg (fun q : TorusFour => q.2.1) hform).symm
  · exact (congrArg (fun q : TorusFour => q.2.2.1) hform).symm
  · exact (congrArg (fun q : TorusFour => q.2.2.2) hform).symm

/-- **The window route collapses to the coordinate route**: `s2c ∘ πᵢ ∘ g = psiC i`. -/
theorem s2c_comp_piC_comp_gPT (i : Fin 4) : s2c.comp ((piC i).comp gPT) = psiC i :=
  ContinuousMap.ext fun p => s2c_piC_fourStepInvC i (inclXC p)

/-- **The winding cochain, evaluated**: `wPT i σ` is literally the winding number of the `i`-th
circle coordinate of the realized simplex. -/
theorem wPT_apply (i : Fin 4)
    (σ : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk 1))) :
    wPT i σ = windMap ((psiC i).comp (rl (X := PTtop) σ)) := by
  have h1 : wPT i σ = windS (mapSimplex ((piC i).comp gPT) σ) := by
    rw [wPT, cochainPullbackInt_apply, bFam_eq_pull, cochainPullbackInt_apply, mapSimplex_comp]
  rw [h1, windS_apply, ← mapSimplex_comp, s2c_comp_piC_comp_gPT, windC_apply, rl_mapSimplex]

/-- **The branch cochain, evaluated**: `aPT i` on a constant `0`-simplex is the `arg = π` indicator
of the `i`-th circle coordinate of the point. -/
theorem aPT_constSimplex (i : Fin 4) (p : ↑PTtop) :
    aPT i (constSimplex (X := PTtop) p 0)
      = if ((psiC i p : Circle) : ℂ).arg = Real.pi then 1 else 0 := by
  have h1 : aPT i (constSimplex (X := PTtop) p 0)
      = argCorr (mapSimplex ((psiC i)) (constSimplex (X := PTtop) p 0)) := by
    rw [aPT, cochainPullbackInt_apply,
      show uCorr i = cochainPullbackInt (piC i) 0 argCorrS from rfl, cochainPullbackInt_apply,
      show argCorrS = cochainPullbackInt s2c 0 argCorr from rfl, cochainPullbackInt_apply,
      ← mapSimplex_comp, ← mapSimplex_comp, ContinuousMap.comp_assoc, s2c_comp_piC_comp_gPT]
  rw [h1, mapSimplex_constSimplex, argCorr]
  congr 1

/-! ## §6. The chart-sphere half-loop, in coordinates -/

/-- The four real coordinates of the chart domain `ℝ⁴`. -/
def chartCoord : Fin 4 → C(ℝ × ℝ × ℝ × ℝ, ℝ)
  | 0 => ⟨fun t => t.1, by fun_prop⟩
  | 1 => ⟨fun t => t.2.1, by fun_prop⟩
  | 2 => ⟨fun t => t.2.2.1, by fun_prop⟩
  | 3 => ⟨fun t => t.2.2.2, by fun_prop⟩

/-- **The `i`-th coordinate of the chart sphere**: `ψᵢ(ι_c a) = c_i · exp(ρ aᵢ)`. The chart is a
translate of the exponential, so the `i`-th circle coordinate factors as the fixed point's
coordinate times the exponential of the `i`-th chart coordinate. -/
theorem psiC_sphereEmbedPT (i : Fin 4) (c : EIndex) (a : S3) :
    psiC i (sphereEmbedPT c a) = coordC i c.1 * Circle.exp (chartCoord i (scaleToChart a)) := by
  fin_cases i <;> rfl

/-- The `S³` basepoint's chart coordinates: `(ρ, 0, 0, 0)` with `ρ = excisionRadius = 1/2`. -/
def baseChart : Fin 4 → ℝ
  | 0 => 1 / 2
  | 1 => 0
  | 2 => 0
  | 3 => 0

theorem chartCoord_scaleToChart_sBase (i : Fin 4) :
    chartCoord i (scaleToChart sBase) = baseChart i := by
  fin_cases i <;>
    simp [chartCoord, baseChart, scaleToChart, excisionRadius,
      SKEFTHawking.KummerRP3SmithSES.basePt]

theorem chartCoord_scaleToChart_negS3_sBase (i : Fin 4) :
    chartCoord i (scaleToChart (negS3 sBase)) = -baseChart i := by
  rw [scaleToChart_negS3, ← chartCoord_scaleToChart_sBase]
  fin_cases i <;> rfl

theorem baseChart_lt_pi (i : Fin 4) : baseChart i < Real.pi := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  fin_cases i <;> · simp only [baseChart]; linarith

theorem baseChart_nonneg (i : Fin 4) : 0 ≤ baseChart i := by
  fin_cases i <;> · simp only [baseChart]; norm_num

/-- The realized half-loop starts at the `S³` basepoint. -/
theorem rl_genS3Simplex_v0 :
    rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex v0 = sBase := by
  have h : rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex = pathSimplexMap genPath :=
    Equiv.apply_symm_apply _ _
  rw [h]
  show genPath (toUnitInterval v0) = sBase
  rw [show toUnitInterval v0 = 0 from Subtype.ext coe_v0_one]
  exact genPath.source

/-- The realized half-loop ends at the antipode. -/
theorem rl_genS3Simplex_v1 :
    rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex v1 = negS3 sBase := by
  have h : rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex = pathSimplexMap genPath :=
    Equiv.apply_symm_apply _ _
  rw [h]
  show genPath (toUnitInterval v1) = negS3 sBase
  rw [show toUnitInterval v1 = 1 from Subtype.ext coe_v1_one]
  exact genPath.target

/-! ## §7. `seamWind` computed: the winding number plus the branch bit -/

/-- **The `c`-th seam half-loop, read in the `i`-th circle coordinate** — a genuine `Circle`-valued
edge `Δ¹ → S¹`. -/
def seamEdge (c : EIndex) (i : Fin 4) : C(stdSimplex ℝ (Fin 2), Circle) :=
  (psiC i).comp (rl (X := PTtop) (mapSimplex (sphereEmbedPTC c) genS3Simplex))

theorem seamEdge_apply (c : EIndex) (i : Fin 4) (t : stdSimplex ℝ (Fin 2)) :
    seamEdge c i t = coordC i c.1 * Circle.exp (chartCoord i (scaleToChart
      (rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex t))) := by
  rw [seamEdge, rl_mapSimplex]
  exact psiC_sphereEmbedPT i c _

/-- **The anchored lift of the seam half-loop**: the fixed point's argument plus the `i`-th chart
coordinate. It exists globally because the chart is `t ↦ c · exp t` — the covering lift is *linear*
in the chart coordinate, so no covering-space theory is needed to produce it. -/
def seamLift (c : EIndex) (i : Fin 4) : C(stdSimplex ℝ (Fin 2), ℝ) :=
  ⟨fun t => ((coordC i c.1 : Circle) : ℂ).arg
      + chartCoord i (scaleToChart (rl (X := SKEFTHawking.KummerRP3Covering.S3top)
        genS3Simplex t)),
    continuous_const.add ((chartCoord i).continuous.comp (continuous_scaleToChart.comp
      (rl (X := SKEFTHawking.KummerRP3Covering.S3top) genS3Simplex).continuous))⟩

theorem exp_seamLift (c : EIndex) (i : Fin 4) :
    ⇑Circle.exp ∘ ⇑(seamLift c i) = ⇑(seamEdge c i) := by
  funext t
  show Circle.exp (((coordC i c.1 : Circle) : ℂ).arg + _) = seamEdge c i t
  rw [Circle.exp_add, Circle.exp_arg, seamEdge_apply]

theorem seamLift_v0 (c : EIndex) (i : Fin 4) :
    seamLift c i v0 = ((coordC i c.1 : Circle) : ℂ).arg + baseChart i := by
  show ((coordC i c.1 : Circle) : ℂ).arg + chartCoord i (scaleToChart _) = _
  rw [rl_genS3Simplex_v0, chartCoord_scaleToChart_sBase]

theorem seamLift_v1 (c : EIndex) (i : Fin 4) :
    seamLift c i v1 = ((coordC i c.1 : Circle) : ℂ).arg - baseChart i := by
  show ((coordC i c.1 : Circle) : ℂ).arg + chartCoord i (scaleToChart _) = _
  rw [rl_genS3Simplex_v1, chartCoord_scaleToChart_negS3_sBase]
  ring

theorem seamEdge_v0 (c : EIndex) (i : Fin 4) :
    seamEdge c i v0 = coordC i c.1 * Circle.exp (baseChart i) := by
  rw [seamEdge_apply, rl_genS3Simplex_v0, chartCoord_scaleToChart_sBase]

theorem seamEdge_v1 (c : EIndex) (i : Fin 4) :
    seamEdge c i v1 = coordC i c.1 * Circle.exp (-baseChart i) := by
  rw [seamEdge_apply, rl_genS3Simplex_v1, chartCoord_scaleToChart_negS3_sBase]

/-- **`seamWind` in analytic terms** — the winding number of the coordinate half-loop plus the
`arg = π` indicator at its start point. -/
theorem seamWind_eq_windMap_add_branch (c : EIndex) (i : Fin 4) :
    seamWind c i
      = windMap (seamEdge c i) + (if ((seamEdge c i v0 : Circle) : ℂ).arg = Real.pi then 1 else 0)
        := by
  rw [seamWind, wPT_apply, aPT_constSimplex, psiC_sphereEmbedPT,
    chartCoord_scaleToChart_sBase, ← seamEdge_v0]
  rfl

/-! ### The two circle values a fixed-point coordinate can take -/

theorem coordC_eIndex (c : EIndex) (i : Fin 4) : coordC i c.1 = 1 ∨ coordC i c.1 = negOne := by
  have h := (mem_fixedSet_iff c.1).mp (eIndex_fixedSet c)
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem circle_exp_pi : Circle.exp Real.pi = negOne := by
  apply Subtype.ext
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  rfl

/-- **The trivial-coordinate seam winding vanishes.** When `c_i = 1` the half-loop is the short
chart arc `exp(ρ) ⤳ exp(−ρ)` through `1`, which winds `0` times and never meets the branch cut. -/
theorem seamWind_of_coord_one (c : EIndex) (i : Fin 4) (h : coordC i c.1 = 1) :
    seamWind c i = 0 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hnn : 0 ≤ baseChart i := baseChart_nonneg i
  have hlt : baseChart i < Real.pi := baseChart_lt_pi i
  have hlo : -Real.pi < baseChart i := by linarith
  have hhi : baseChart i ≤ Real.pi := le_of_lt hlt
  have hv0 : ((seamEdge c i v0 : Circle) : ℂ).arg = baseChart i := by
    rw [seamEdge_v0, h, one_mul, Circle.arg_exp hlo hhi]
  have hv1 : ((seamEdge c i v1 : Circle) : ℂ).arg = -baseChart i := by
    rw [seamEdge_v1, h, one_mul, Circle.arg_exp (by linarith) (by linarith)]
  have hw : windMap (seamEdge c i) = 0 := by
    refine windMap_eq_of_char (seamEdge c i) (seamLift c i) (exp_seamLift c i) 0 ?_
    rw [seamLift_v0, seamLift_v1, hv0, hv1, h]
    push_cast
    ring
  have hbr : ¬ (((seamEdge c i v0 : Circle) : ℂ).arg = Real.pi) := by
    rw [hv0]; exact ne_of_lt (baseChart_lt_pi i)
  rw [seamWind_eq_windMap_add_branch, hw, if_neg hbr]
  norm_num

/-- **The nontrivial-coordinate seam winding is odd**, in both regimes: when the half-loop actually
moves in the `i`-th coordinate (`ρ > 0`, i.e. `i = 0`) the winding is `−1` and the branch bit is
`0`; when it is constant (`i ≠ 0`) the winding is `0` and the branch bit is `1`. Either way the
total is odd — this is the `c_i = −1` half-period bit. -/
theorem seamWind_of_coord_negOne (c : EIndex) (i : Fin 4) (h : coordC i c.1 = negOne) :
    seamWind c i = if baseChart i = 0 then 1 else -1 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hnn : 0 ≤ baseChart i := baseChart_nonneg i
  have hlt : baseChart i < Real.pi := baseChart_lt_pi i
  have hprod : ∀ x : ℝ, negOne * Circle.exp x = Circle.exp (Real.pi + x) := by
    intro x
    rw [← circle_exp_pi, ← Circle.exp_add]
  have hv1 : ((seamEdge c i v1 : Circle) : ℂ).arg = Real.pi - baseChart i := by
    rw [seamEdge_v1, h, hprod, show Real.pi + -baseChart i = Real.pi - baseChart i from by ring,
      Circle.arg_exp (by linarith) (by linarith)]
  by_cases he : baseChart i = 0
  · have hv0 : ((seamEdge c i v0 : Circle) : ℂ).arg = Real.pi := by
      rw [seamEdge_v0, h, hprod, he, add_zero, Circle.arg_exp (by linarith) le_rfl]
    have hw : windMap (seamEdge c i) = 0 := by
      refine windMap_eq_of_char (seamEdge c i) (seamLift c i) (exp_seamLift c i) 0 ?_
      rw [seamLift_v0, seamLift_v1, hv0, hv1, he]
      push_cast
      ring
    rw [seamWind_eq_windMap_add_branch, hw, if_pos hv0, if_pos he]
    norm_num
  · have hpos : 0 < baseChart i := lt_of_le_of_ne hnn (Ne.symm he)
    have hshift : Circle.exp (Real.pi + baseChart i) = Circle.exp (baseChart i - Real.pi) := by
      have := Circle.periodic_exp.sub_eq (Real.pi + baseChart i)
      rw [show Real.pi + baseChart i - 2 * Real.pi = baseChart i - Real.pi from by ring] at this
      exact this.symm
    have hv0 : ((seamEdge c i v0 : Circle) : ℂ).arg = baseChart i - Real.pi := by
      rw [seamEdge_v0, h, hprod, hshift, Circle.arg_exp (by linarith) (by linarith)]
    have hw : windMap (seamEdge c i) = -1 := by
      refine windMap_eq_of_char (seamEdge c i) (seamLift c i) (exp_seamLift c i) (-1) ?_
      rw [seamLift_v0, seamLift_v1, hv0, hv1]
      push_cast
      ring
    have hbr : ¬ (((seamEdge c i v0 : Circle) : ℂ).arg = Real.pi) := by
      rw [hv0]; intro hc; linarith
    rw [seamWind_eq_windMap_add_branch, hw, if_neg hbr, if_neg he]
    norm_num

/-- **`seamWind` computed, in full**: the `i`-th seam-winding integer is **odd exactly when the
`i`-th coordinate of the fixed point is `−1`** — i.e. `seamWind c` reads off the half-period bit
vector of `c`. This is the falsifiable content: it fails for any geometry-free replacement of
`seamWind` (a constant function is even everywhere, hence never odd). -/
theorem seamWind_odd_iff (c : EIndex) (i : Fin 4) :
    ¬ ((2 : ℤ) ∣ seamWind c i) ↔ coordC i c.1 = negOne := by
  constructor
  · intro hodd
    rcases coordC_eIndex c i with h | h
    · exact absurd (by rw [seamWind_of_coord_one c i h]; exact dvd_zero 2) hodd
    · exact h
  · intro h
    rw [seamWind_of_coord_negOne c i h]
    by_cases he : baseChart i = 0
    · rw [if_pos he]; omega
    · rw [if_neg he]; omega

/-! ## §8. The discharge: the sixteen seam-winding vectors are pairwise distinct mod 2 -/

/-- Two distinct fixed points differ in some circle coordinate. -/
theorem exists_coord_ne (c c' : EIndex) (h : c ≠ c') :
    ∃ i : Fin 4, coordC i c.1 ≠ coordC i c'.1 := by
  by_contra hc
  push Not at hc
  refine h (Subtype.ext ?_)
  exact Prod.ext (hc 0) (Prod.ext (hc 1) (Prod.ext (hc 2) (hc 3)))

/-- **THE DISCHARGE** — `SeamWindParityInjective` holds. Two distinct half-periods differ in some
coordinate `i`; there one has `c_i = 1` (seam winding `0`) and the other `c_i = −1` (seam winding
odd), so the difference is odd. -/
theorem seamWindParityInjective : SeamWindParityInjective := by
  intro c c' hne
  obtain ⟨i, hi⟩ := exists_coord_ne c c' hne
  refine ⟨i, ?_⟩
  rcases coordC_eIndex c i with h | h
  · rcases coordC_eIndex c' i with h' | h'
    · exact absurd (h.trans h'.symm) hi
    · have hodd := (seamWind_odd_iff c' i).mpr h'
      rw [seamWind_of_coord_one c i h]
      omega
  · rcases coordC_eIndex c' i with h' | h'
    · have hodd := (seamWind_odd_iff c i).mpr h
      rw [seamWind_of_coord_one c' i h']
      omega
    · exact absurd (h.trans h'.symm) hi

/-- **`SeamWindingOdd`, unconditionally.** -/
theorem seamWindingOdd : SeamWindingOdd := seamWindingOdd_of_parity seamWindParityInjective

/-- **The sixteen seam classes are pairwise distinct**, unconditionally. -/
theorem seamClass_injective : Function.Injective seamClass :=
  seamClass_injective_of_seamWindingOdd seamWindingOdd

/-- **`QLatticeInSeamSpan`, unconditionally** — the residual of `KummerK3H1Vanish` is discharged. -/
theorem qLatticeInSeamSpan : QLatticeInSeamSpan :=
  qLatticeInSeamSpan_of_seamWindingOdd seamWindingOdd

/-- **`H₁(K3;ℤ) = 0`, unconditionally.** -/
theorem h1K3_eq_zero_uncond (x : Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) : x = 0 :=
  h1K3_eq_zero qLatticeInSeamSpan x

/-- **THE `h1Free` ATOM, DISCHARGED**: `H₁(K3;ℤ)` is a free `ℤ`-module — with no residual
hypothesis. This is the `h1Free` field of `KummerK3E1Package.KummerK3E1Residuals`. -/
theorem free_h1K3_uncond : Module.Free ℤ (Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) :=
  free_h1K3 qLatticeInSeamSpan

/-- **`H₁(K3;ℤ) = 0` from the finite residual.** -/
theorem h1K3_eq_zero_of_parity (h : SeamWindParityInjective)
    (x : Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) : x = 0 :=
  h1K3_eq_zero (qLatticeInSeamSpan_of_parity h) x

/-- **The `h1Free` residual field**, now resting on `16 × 4` integers. -/
theorem free_h1K3_of_parity (h : SeamWindParityInjective) :
    Module.Free ℤ (Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) :=
  free_h1K3 (qLatticeInSeamSpan_of_parity h)

/-! ## §9. The E1 residual ledger loses a field -/

section E1Ledger

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.KummerK3E1Package (KummerK3E1Residuals KummerK3E1Atoms KummerK3H3TwoTorsionFree
  kummerK3E1Atoms_of_residuals)
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.SingularHomologyInt (IntOrientation intFundamentalClassOfIntOrientation)
open SKEFTHawking.SingularCohomologyInt (IntPoincareDuality)

/-- **The E1 residual ledger drops from three inputs to two.** `KummerK3E1Package` recorded
`orientInput`, `h1Free`, `pdInput` as the three open homological inputs of the `K3` E1 package;
`h1Free` is now supplied by `free_h1K3_uncond`, so the ledger is assembled from the orientation and
Poincaré-duality inputs alone. -/
theorem kummerK3E1Residuals_of_orient_pd (orientInput : KummerK3H3TwoTorsionFree)
    (pdInput : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    KummerK3E1Residuals :=
  ⟨orientInput, free_h1K3_uncond, pdInput⟩

/-- **The E1 atom triple from two inputs** — `orient`/`B`/`pd` + `rank22` with no `h1Free`
obligation. -/
theorem nonempty_kummerK3E1Atoms_of_orient_pd (orientInput : KummerK3H3TwoTorsionFree)
    (pdInput : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    Nonempty KummerK3E1Atoms :=
  kummerK3E1Atoms_of_residuals (kummerK3E1Residuals_of_orient_pd orientInput pdInput)

end E1Ledger

end

end SKEFTHawking.KummerK3SeamWindingParity
