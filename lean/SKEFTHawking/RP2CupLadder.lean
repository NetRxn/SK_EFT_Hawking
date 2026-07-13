import Mathlib
import SKEFTHawking.RP2ProjectionFormula
import SKEFTHawking.RP2CohomologyLadder

/-!
# Phase 5q.G (B-arc, M3-i) — the ladder classes are cup powers

**`δS(u ⌣ g) = u ⌣ δS(g)`** — the cohomological Smith connecting map is an
`H^*(ℝP²)`-module map. The engine: the connecting class can be computed from *any*
`τ^#`-preimage of a representative (`smithCoConnecting_mk_of_transfer_rep`); choosing
`y := π^#u ⌣ s^#g` (a `τ^#`-preimage by the projection formula), the Alexander–Whitney
Leibniz rule collapses `δy` to `π^#u ⌣ δ(s^#g)` (`u` is a cocycle), whose plus-values are
exactly `u ⌣ connectingCochain g` — on the nose.

Seeding the ladder class with the right unit (`cup w 1 = w` at `(1,0)`) and peeling one
`δS` gives **`xpow 2 = x ⌣ x`** in the pinned class-level cup (`cupH`) — no cup associativity
ever needed. Combined with the ladder `xpow 2 ≠ 0`: the cup square of the generator is the
nonzero top class, the input to the surface intersection-form self-pairing `x · x = 1`.
(The degree-3,4 rungs of the `ℝP⁴` tower have no surface analogue and are dropped.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP2PointSet SKEFTHawking.RP2Transfer SKEFTHawking.RP2SmithCochain
open SKEFTHawking.RP2ProjectionFormula SKEFTHawking.RP2CohomologyLadder
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality

namespace SKEFTHawking.RP2CupLadder

private theorem sub_eq_add' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a b : M) :
    a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (by
    rw [← two_smul (ZMod 2) b, show (2 : ZMod 2) = 0 by decide, zero_smul])]

/-! ## §1. The any-preimage computation of `δS` -/

/-- A `τ^#`-killed cochain takes equal values on the two lifts. -/
theorem apply_liftMinus_eq {n : ℕ} (y : SingularCochain (TopCat.of S2) n)
    (hy : cochainTransfer n y = 0)
    (β : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk n))) :
    y (liftMinus β) = y (liftPlus β) := by
  have h0 : y (liftPlus β) + y (liftMinus β) = 0 := by simpa using congrFun hy β
  revert h0
  generalize y (liftPlus β) = a
  generalize y (liftMinus β) = b
  revert a b
  decide

/-- **`δS` computes from any `τ^#`-preimage**: if `τ^#y` represents the class, the connecting
class is `[plusValues(δy)]` — the section-based representative differs by the coboundary of
the plus-values of the (`τ^#`-killed) defect `s^#g + y`. -/
theorem smithCoConnecting_mk_of_transfer_rep {n : ℕ}
    (g : LinearMap.ker (coboundaryₗ (TopCat.of RP2) n))
    (y : SingularCochain (TopCat.of S2) n) (hy : cochainTransfer n y = g.1)
    (hmem : plusValues (n + 1) (coboundaryₗ (TopCat.of S2) n y)
      ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP2) (n + 1))) :
    smithCoConnecting n (Cohomology.mk (TopCat.of RP2) n g)
      = Cohomology.mk (TopCat.of RP2) (n + 1)
          ⟨plusValues (n + 1) (coboundaryₗ (TopCat.of S2) n y), hmem⟩ := by
  rw [smithCoConnecting_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  set d := cochainSection n g.1 + y with hd
  have hdker : cochainTransfer n d = 0 := by
    rw [hd, map_add, cochainTransfer_cochainSection, hy, ← two_smul (ZMod 2),
      show (2 : ZMod 2) = 0 by decide, zero_smul]
  refine ⟨plusValues n d, ?_⟩
  show coboundaryₗ (TopCat.of RP2) n (plusValues n d)
    = connectingCochain n g.1 - plusValues (n + 1) (coboundaryₗ (TopCat.of S2) n y)
  apply cochainPullback_injective (n + 1)
  have hyker : cochainTransfer (n + 1) (coboundaryₗ (TopCat.of S2) n y) = 0 := by
    rw [show (coboundaryₗ (TopCat.of S2) n) y = coboundary (TopCat.of S2) n y from rfl,
      ← coboundary_cochainTransfer, hy]
    exact LinearMap.mem_ker.mp g.2
  rw [map_sub,
    show cochainPullback mkC (n + 1) (coboundaryₗ (TopCat.of RP2) n (plusValues n d))
      = coboundary (TopCat.of S2) n (cochainPullback mkC n (plusValues n d)) from
      (coboundary_cochainPullback mkC n (plusValues n d)).symm,
    cochainPullback_plusValues d hdker,
    cochainPullback_connectingCochain g.1 (LinearMap.mem_ker.mp g.2),
    cochainPullback_plusValues (coboundaryₗ (TopCat.of S2) n y) hyker, hd]
  show coboundaryₗ (TopCat.of S2) n (cochainSection n g.1 + y)
    = coboundaryₗ (TopCat.of S2) n (cochainSection n g.1) - coboundaryₗ (TopCat.of S2) n y
  rw [map_add, sub_eq_add']

/-! ## §2. The Leibniz transport: `plusValues(δ(π^#u ⌣ s^#g)) = u ⌣ connectingCochain g` -/

/-- `frontSmall` commutes with the simplex pushforward (the `frontSmall`-native copy of the
F2 naturality — staying in one spelling avoids the cross-index rewrite wall). -/
theorem frontSmall_mapSimplex {X Y : TopCat} {p q : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    frontSmall (p := p) (q := q) (mapSimplex φ σ) = mapSimplex φ (frontSmall σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk p))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- `backSmall` commutes with the simplex pushforward. -/
theorem backSmall_mapSimplex {X Y : TopCat} {p q : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q + 1)))) :
    backSmall (p := p) (q := q) (mapSimplex φ σ) = mapSimplex φ (backSmall σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk (q + 1)))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- The pulled-back front-small factor on the plus-lift sees only the base. -/
theorem cochainPullback_frontSmall_lift {p q : ℕ}
    (a : SingularCochain (TopCat.of RP2) p)
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q + 1)))) :
    cochainPullback mkC p a (frontSmall (q := q) (liftPlus σ)) = a (frontSmall σ) := by
  rw [cochainPullback_apply, ← frontSmall_mapSimplex, mapSimplex_liftPlus]

/-- The back-small face of a lift is a lift of the back-small face. -/
theorem backSmall_lift_mem_pair {p q : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP2)).obj (op (SimplexCategory.mk (p + q + 1))))
    (τ : (TopCat.toSSet.obj (TopCat.of S2)).obj (op (SimplexCategory.mk (p + q + 1))))
    (hτ : mapSimplex mkC τ = σ) :
    backSmall (p := p) τ = liftPlus (backSmall σ)
      ∨ backSmall (p := p) τ = liftMinus (backSmall σ) := by
  have h := mem_pair_of_pushforward (backSmall (p := p) (q := q) τ)
  rwa [show mapSimplex mkC (backSmall (p := p) (q := q) τ) = backSmall σ from by
    rw [← backSmall_mapSimplex, hτ]] at h

/-- **The Leibniz transport** — with `u` a cocycle, the `δu`-term of the Alexander–Whitney
Leibniz rule dies, and the surviving term's plus-values are exactly `u ⌣ connectingCochain g`
(the back faces of the lifts carry the same `δ(s^#g)`-values as the lifts of the back face —
membership + the `τ^#`-killed equal-values trick). ON THE NOSE at cochain level. -/
theorem plusValues_coboundary_cup_section {p q : ℕ}
    (u : SingularCochain (TopCat.of RP2) p) (hu : coboundaryₗ (TopCat.of RP2) p u = 0)
    (g : SingularCochain (TopCat.of RP2) q) (hg : coboundaryₗ (TopCat.of RP2) q g = 0) :
    plusValues (p + q + 1) (coboundaryₗ (TopCat.of S2) (p + q)
        (cup (cochainPullback mkC p u) (cochainSection q g)))
      = cup u (connectingCochain q g) := by
  funext σ
  show coboundary (TopCat.of S2) (p + q)
      (cup (cochainPullback mkC p u) (cochainSection q g)) (liftPlus σ)
    = cup u (connectingCochain q g) σ
  rw [coboundary_cup]
  have h1 : coboundary (TopCat.of S2) p (cochainPullback mkC p u) = 0 := by
    rw [coboundary_cochainPullback,
      show coboundary (TopCat.of RP2) p u = coboundaryₗ (TopCat.of RP2) p u from rfl, hu,
      map_zero]
  rw [h1, Pi.zero_apply, zero_mul, zero_add, cup_apply,
    cochainPullback_frontSmall_lift u σ]
  congr 1
  rcases backSmall_lift_mem_pair σ (liftPlus σ) (mapSimplex_liftPlus σ) with h2 | h2
  · rw [h2]
    rfl
  · rw [h2, apply_liftMinus_eq (coboundary (TopCat.of S2) q (cochainSection q g))
      (cochainTransfer_coboundary_cochainSection g hg) (backSmall σ)]
    rfl

/-! ## §3. The class-level Leibniz: `δS([u ⌣ g]) = [u ⌣ connectingCochain g]` -/

/-- **`δS` is an `H^*`-module map** — on representatives: the connecting class of `[u ⌣ g]` is
`[u ⌣ connectingCochain g]`, exactly. -/
theorem smithCoConnecting_cup {p q : ℕ}
    (u : LinearMap.ker (coboundaryₗ (TopCat.of RP2) p))
    (g : LinearMap.ker (coboundaryₗ (TopCat.of RP2) q)) :
    smithCoConnecting (p + q) (Cohomology.mk (TopCat.of RP2) (p + q)
        ⟨cup (p := p) (q := q) u.1 g.1, LinearMap.mem_ker.mpr (cup_cocycle u.1 g.1
          (LinearMap.mem_ker.mp u.2) (LinearMap.mem_ker.mp g.2))⟩)
      = Cohomology.mk (TopCat.of RP2) (p + q + 1)
          ⟨cup (p := p) (q := q + 1) u.1 (connectingCochain q g.1), LinearMap.mem_ker.mpr
            (cup_cocycle u.1 (connectingCochain q g.1) (LinearMap.mem_ker.mp u.2)
              (connectingCochain_mem_ker g.1 (LinearMap.mem_ker.mp g.2)))⟩ := by
  have hy : cochainTransfer (p + q)
      (cup (cochainPullback mkC p u.1) (cochainSection q g.1)) = cup u.1 g.1 := by
    rw [cochainTransfer_cup_pullback, cochainTransfer_cochainSection]
  have hpv := plusValues_coboundary_cup_section u.1 (LinearMap.mem_ker.mp u.2) g.1
    (LinearMap.mem_ker.mp g.2)
  have hmem : plusValues (p + q + 1) (coboundaryₗ (TopCat.of S2) (p + q)
      (cup (cochainPullback mkC p u.1) (cochainSection q g.1)))
      ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP2) (p + q + 1)) := by
    rw [hpv]
    exact LinearMap.mem_ker.mpr (cup_cocycle u.1 (connectingCochain q g.1)
      (LinearMap.mem_ker.mp u.2)
      (connectingCochain_mem_ker g.1 (LinearMap.mem_ker.mp g.2)))
  rw [smithCoConnecting_mk_of_transfer_rep ⟨cup u.1 g.1, LinearMap.mem_ker.mpr
    (cup_cocycle u.1 g.1 (LinearMap.mem_ker.mp u.2) (LinearMap.mem_ker.mp g.2))⟩
    (cup (cochainPullback mkC p u.1) (cochainSection q g.1)) hy hmem]
  exact congrArg (Cohomology.mk (TopCat.of RP2) (p + q + 1)) (Subtype.ext hpv)

/-! ## §4. The cup-power identification (M3-i payoff) -/

/-- `frontFace` at `(p, 0)` is the identity (the front inclusion is the identity hom). -/
theorem frontFace_q_zero {X : TopCat} {p : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + 0)))) :
    frontFace (p := p) (q := 0) σ = σ := by
  show (TopCat.toSSet.obj X).map (frontIncl p 0).op σ = σ
  have h : frontIncl p 0 = 𝟙 (SimplexCategory.mk p) := by
    apply SimplexCategory.Hom.ext
    ext i
    rfl
  rw [h, op_id]
  exact CategoryTheory.FunctorToTypes.map_id_apply (TopCat.toSSet.obj X) σ

/-- The constant-`1` `0`-cochain on `ℝP²`, degree-pinned. -/
noncomputable def oneC : SingularCochain (TopCat.of RP2) 0 := fun _ => (1 : ZMod 2)

theorem oneC_mem_ker : oneC ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP2) 0) :=
  const_one_mem_ker

/-- **Right unit**: `f ⌣ 1 = f` at `(p, 0)`. -/
theorem cup_one_right {p : ℕ} (f : SingularCochain (TopCat.of RP2) p) :
    cup (p := p) (q := 0) f oneC = f := by
  funext σ
  rw [cup_apply, show oneC (backFace (p := p) (q := 0) σ) = 1 from rfl, mul_one,
    frontFace_q_zero]

/-- The canonical cocycle representative of `xpow 1` (`= connectingCochain 0 1`). -/
noncomputable def xRep : LinearMap.ker (coboundaryₗ (TopCat.of RP2) 1) :=
  ⟨connectingCochain 0 oneC, LinearMap.mem_ker.mpr
    (connectingCochain_mem_ker _ (LinearMap.mem_ker.mp oneC_mem_ker))⟩

/-- The canonical cocycle representative of `xpow 2` (`= connectingCochain 1 xRep`). -/
noncomputable def x2Rep : LinearMap.ker (coboundaryₗ (TopCat.of RP2) 2) :=
  ⟨connectingCochain 1 xRep.1, LinearMap.mem_ker.mpr
    (connectingCochain_mem_ker _ (LinearMap.mem_ker.mp xRep.2))⟩

theorem xpow_one_eq : xpow 1 = Cohomology.mk (TopCat.of RP2) 1 xRep := by
  show smithCoConnecting 0 (unitClass (TopCat.of RP2)) = _
  rw [unitClass, smithCoConnecting_mk]
  rfl

theorem xpow_two_eq : xpow 2 = Cohomology.mk (TopCat.of RP2) 2 x2Rep := by
  show smithCoConnecting 1 (xpow 1) = _
  rw [xpow_one_eq, smithCoConnecting_mk]
  rfl

/-- A class as its right-unit cup: `[w] = [w ⌣ 1]` (the Leibniz-step seed). -/
theorem mk_eq_mk_cup_one {p : ℕ} (w : LinearMap.ker (coboundaryₗ (TopCat.of RP2) p)) :
    Cohomology.mk (TopCat.of RP2) p w
      = Cohomology.mk (TopCat.of RP2) (p + 0)
          ⟨cup (p := p) (q := 0) w.1 oneC, LinearMap.mem_ker.mpr (cup_cocycle w.1 oneC
            (LinearMap.mem_ker.mp w.2) (LinearMap.mem_ker.mp oneC_mem_ker))⟩ :=
  congrArg (Cohomology.mk (TopCat.of RP2) p) (Subtype.ext (cup_one_right w.1).symm)

/-- **`xpow 2 = x ⌣ x`** — the degree-2 ladder class is the cup square of the generator. -/
theorem xpow_two_eq_cupH : xpow 2 = cupH (xpow 1) (xpow 1) := by
  have step := smithCoConnecting_cup xRep ⟨oneC, oneC_mem_ker⟩
  have lhs : xpow 2 = Cohomology.mk (TopCat.of RP2) 2
      ⟨cup (p := 1) (q := 1) xRep.1 xRep.1, LinearMap.mem_ker.mpr
        (cup_cocycle xRep.1 xRep.1 (LinearMap.mem_ker.mp xRep.2)
          (LinearMap.mem_ker.mp xRep.2))⟩ := by
    show smithCoConnecting 1 (xpow 1) = _
    rw [xpow_one_eq, mk_eq_mk_cup_one xRep]
    exact step
  rw [lhs, xpow_one_eq]
  show Submodule.Quotient.mk _
    = cupH (Submodule.Quotient.mk xRep) (Submodule.Quotient.mk xRep)
  rw [cupH_mk_mk]

end SKEFTHawking.RP2CupLadder
