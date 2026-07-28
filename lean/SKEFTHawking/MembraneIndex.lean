/-
# Phase 5q.H (E2 · `[G2]`/`[Q1]`) — the MEMBRANE INDEX `D·F + O(D) + d(C)`, **CONSTRUCTED**

`PinEnhancementTorsor` proved that the substrate's missing field is *exactly* one `H¹(F;ℤ/2)`-class
`w` (the enhancement torsor is simply transitive), and `GMTripleLayerForcing` proved that no
triple-level layer can supply it — the escape must be finer, and must be a predicate on the pin⁻
class rather than on `σ`. `Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md`
names what computes that class: nodes `[G2]`/`[Q1]`, Freedman–Kirby Lemma 2.6.1,

> `q_F(x) := D·F + O(D) + d(C) mod 2`, well-defined (independent of the membrane `D`).

**The constraint this module is built under.** A `MembraneIndexData` structure with an
`index : (ι → ZMod 2) → ZMod 4` field plus a refinement axiom is isomorphic to `Z4Quadratic` — new
docstrings, no new mathematics, P5 structural-tautology repackaging. So every summand here is
*computed from geometric data*, and nothing in `AmbientMembrane`/`FramedMembrane` is `ZMod`-valued:

* `D·F` (`intF`) — `Set.ncard` of `{p ∉ ∂S | D p ∈ F}`, a set the membrane map determines outright;
* `d(C)` (`dbl`) — `Set.ncard` of the map's double-point set `doubleSet D ⊆ Sym2 S`;
* `O(D)` (`obs`) — the **degree of the boundary framing-comparison loop**, computed through the
  in-tree lift-based winding number `CircleWindingCocycle.windMap`. (A rank-2 bundle over a compact
  surface-with-boundary is trivial, so `O(D)` is not a trivialization obstruction but the
  `π₁(SO(2)) ≅ ℤ` discrepancy between the `F`-induced boundary framing and a global one.) Degree
  additivity on loops is PROVED (`loopDegree_mul`) — structure no stored integer could have.

The structure's only added inputs are the two `Finite` **genericity/transversality** fields.

## What this buys, in theorems

* `geomEnhancement` — a `[Q2]`-compatible membrane index PRODUCES a genuine `Z4Quadratic` on
  `H₁(F;ℤ/2)` whose polar form **is** the surface's. This is the substrate `CharSurfaceFKVacuity` §3
  named as missing, supplied constructively.
* `exists_unique_pin_class` — hence `PinTorsor.shift_simply_transitive` yields the **unique class
  `w`** carrying `C.Q` to it. *The pin⁻ class is computed by the membrane index, not chosen.*
* `MembraneSystem.pin_class_indep_of_system` — under the corrected `[Q1]` that class is an invariant
  of the surface: circles, membranes and framings all drop out.
* `gmrelation_geomEnhancement_iff` — Guillou–Marin at the produced enhancement **is** the blueprint's
  `[FK]` line `Arf(q_F) = (σ − ξ·ξ)/8 mod 2`, now a predicate on the membrane index (so it passes
  `GMTripleLayerForcing`'s intensional admissibility criterion, where `GMrelation σ 0 C.Q` failed).
* `index_eq_of_pin_class_eq` — the extraction is injective: no geometry lost, no class invented.

## Two findings the lead should have

1. **Scope (`refines_forces_alternating`).** Any `μ` satisfying the `[Q2]` polarization identity
   against `Q.B` forces `B(v,v) = 0` for all `v`. So the mod-2 Freedman–Kirby index — blueprint
   Route A — reaches the **orientable stratum and, kernel-checkably, only that one**; the `ℝP²`
   stratum admits no such index at all (`not_exists_index_of_B_self_ne_zero`). This is not a defect:
   it is the exact content of the blueprint's remark that the Guillou–Marin `ℤ/4` form "is sharper …
   but costs nonorientable-surface + Pin⁻ normal data on top".
2. **A real defect, found and repaired (`indexWellDefined_false_of_framedMembrane`).** With the
   framing comparison carried as *free* data, `[Q1]` in its natural universal shape is **FALSE** —
   twisting the comparison by one full turn flips the index (`index_twist`). This is the same failure
   mode `CharSurfaceFKVacuity` found one level up (a free enhancement makes universal `[FK]` false,
   not merely vacuous), reappearing at the framing: `O(D)` must be *produced* from the smooth normal
   data. Repaired by `NormalFramingTie` (rigidity), whose twist-escape and inhabitedness requirements
   are both shown load-bearing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceMembrane
import SKEFTHawking.PinEnhancementTorsor
import SKEFTHawking.CircleWindingCocycle

namespace SKEFTHawking.MembraneIndex

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.CharSurface
open SKEFTHawking.CircleWindingCocycle
open scoped Manifold

/-! ## §1. The double-point set of a map -/

/-- The **double-point set** of a map `D : S → X`: the unordered pairs `{p, q}` with `p ≠ q` and
`D p = D q`. Constructed from the map alone. -/
def doubleSet {S X : Type*} (D : S → X) : Set (Sym2 S) :=
  {e | ¬ e.IsDiag ∧ ∀ p ∈ e, ∀ q ∈ e, D p = D q}

lemma mem_doubleSet {S X : Type*} (D : S → X) (p q : S) :
    s(p, q) ∈ doubleSet D ↔ p ≠ q ∧ D p = D q := by
  constructor
  · rintro ⟨hd, hall⟩
    exact ⟨fun h => hd (Sym2.mk_isDiag_iff.mpr h), hall p (by simp) q (by simp)⟩
  · rintro ⟨hne, heq⟩
    refine ⟨fun h => hne (Sym2.mk_isDiag_iff.mp h), ?_⟩
    intro a ha b hb
    rcases Sym2.mem_iff.mp ha with rfl | rfl <;> rcases Sym2.mem_iff.mp hb with rfl | rfl <;>
      first
        | rfl
        | exact heq
        | exact heq.symm

/-- An injective map has no double points. -/
theorem doubleSet_eq_empty_of_injective {S X : Type*} {D : S → X} (h : Function.Injective D) :
    doubleSet D = ∅ := by
  ext e
  refine ⟨?_, fun h => absurd h (Set.notMem_empty e)⟩
  induction e with
  | _ p q =>
    rw [mem_doubleSet]
    rintro ⟨hne, heq⟩
    exact absurd (h heq) hne

/-! ## §2. The degree of a loop in the circle — the engine of the framing obstruction

A rank-2 real vector bundle over a compact surface-with-boundary is trivial, so the normal-framing
obstruction `O(D)` of blueprint node `[G2]` is not an obstruction to trivializing the membrane's
normal bundle — it is the **discrepancy between the `F`-induced boundary framing and the restriction
of a global trivialization**, i.e. an element of `π₁(SO(2)) ≅ ℤ`, computed as the degree of the
comparison loop `∂S ≅ S¹ → SO(2) ≅ S¹`. That degree is what this section constructs, from the
in-tree lift-based winding number `CircleWindingCocycle.windMap` — no field, no declared value. -/

/-- **The degree of a loop in the circle**, computed through the canonical lift: the winding number
of the loop read as the edge `Δ¹ → S¹`. -/
noncomputable def loopDegree (c : C(↑unitInterval, Circle)) : ℤ := windMap (c.comp iota)

/-- The canonical `2π`-loop `t ↦ exp(2πit)`. -/
noncomputable def stdLoop : C(↑unitInterval, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩

/-- **The constant comparison has zero obstruction** (PROVED through the lift, not by fiat): a
boundary framing that agrees with the global trivialization contributes nothing. -/
theorem loopDegree_const (z : Circle) : loopDegree (ContinuousMap.const _ z) = 0 := by
  refine windMap_eq_of_char _ (ContinuousMap.const _ ((z : ℂ).arg)) ?_ 0 ?_
  · funext d
    exact Circle.exp_arg z
  · simp

/-- **The obstruction summand genuinely takes a nonzero value** (the vacuity attack on `O(D)`,
run): the standard `2π`-loop has degree `1`. So `O(D)` is not a dressed-up zero. -/
theorem loopDegree_stdLoop : loopDegree stdLoop = 1 := by
  refine windMap_eq_of_char _ ⟨fun d => 2 * Real.pi * ((iota d : ↑unitInterval) : ℝ),
    continuous_const.mul (continuous_subtype_val.comp iota.continuous)⟩ ?_ 1 ?_
  · funext d
    rfl
  · have h1 : ((stdLoop.comp iota) v1 : ℂ) = (1 : Circle) := by
      show ((Circle.exp (2 * Real.pi * ((iota v1 : ↑unitInterval) : ℝ)) : Circle) : ℂ) = _
      rw [iota_v1]
      norm_num [exp_two_pi]
    have h0 : ((stdLoop.comp iota) v0 : ℂ) = (1 : Circle) := by
      show ((Circle.exp (2 * Real.pi * ((iota v0 : ↑unitInterval) : ℝ)) : Circle) : ℂ) = _
      rw [iota_v0]
      norm_num
    rw [h1, h0]
    show 2 * Real.pi * ((iota v1 : ↑unitInterval) : ℝ)
      - 2 * Real.pi * ((iota v0 : ↑unitInterval) : ℝ) - _ = _
    rw [iota_v1, iota_v0]
    norm_num

/-- **Degree is additive on loops** (PROVED — the structural theorem that makes `O(D)` a genuine
`ℤ`-valued invariant rather than a stored number). If `L₁`, `L₂` lift `c₁`, `c₂` then `L₁ + L₂` lifts
the pointwise product, and for *loops* the argument-correction terms of `windMap_char` cancel, so the
winding numbers add. The framing obstruction is therefore a group homomorphism from comparison loops
to `ℤ` — a property no `ℤ`-valued field could have. -/
theorem loopDegree_mul {c₁ c₂ : C(↑unitInterval, Circle)}
    (h₁ : c₁ 1 = c₁ 0) (h₂ : c₂ 1 = c₂ 0) :
    loopDegree (c₁ * c₂) = loopDegree c₁ + loopDegree c₂ := by
  classical
  -- canonical lifts of the two edges
  set f₁ : C(↑(stdSimplex ℝ (Fin 2)), Circle) := c₁.comp iota with hf₁
  set f₂ : C(↑(stdSimplex ℝ (Fin 2)), Circle) := c₂.comp iota with hf₂
  set L₁ := liftMap f₁ v0 ((f₁ v0 : ℂ)).arg (Circle.exp_arg (f₁ v0)) with hL₁
  set L₂ := liftMap f₂ v0 ((f₂ v0 : ℂ)).arg (Circle.exp_arg (f₂ v0)) with hL₂
  have hlift₁ : ⇑Circle.exp ∘ ⇑L₁ = ⇑f₁ := liftMap_lifts _ _ _ _
  have hlift₂ : ⇑Circle.exp ∘ ⇑L₂ = ⇑f₂ := liftMap_lifts _ _ _ _
  -- the two edges are loops: their endpoint values agree
  have hloop₁ : f₁ v1 = f₁ v0 := by
    show c₁ (iota v1) = c₁ (iota v0)
    rw [iota_v1, iota_v0]; exact h₁
  have hloop₂ : f₂ v1 = f₂ v0 := by
    show c₂ (iota v1) = c₂ (iota v0)
    rw [iota_v1, iota_v0]; exact h₂
  -- the degree of each factor is the lift's total increment
  have hd₁ : (windMap f₁ : ℝ) * (2 * Real.pi) = L₁ v1 - L₁ v0 := by
    have := windMap_char f₁ L₁ hlift₁
    rw [hloop₁] at this
    linarith [this]
  have hd₂ : (windMap f₂ : ℝ) * (2 * Real.pi) = L₂ v1 - L₂ v0 := by
    have := windMap_char f₂ L₂ hlift₂
    rw [hloop₂] at this
    linarith [this]
  -- `L₁ + L₂` lifts the product edge
  have hprod : (c₁ * c₂).comp iota = f₁ * f₂ := rfl
  have hliftp : ⇑Circle.exp ∘ ⇑(L₁ + L₂) = ⇑((c₁ * c₂).comp iota) := by
    funext d
    show Circle.exp (L₁ d + L₂ d) = _
    rw [Circle.exp_add, hprod]
    show _ = f₁ d * f₂ d
    rw [show Circle.exp (L₁ d) = f₁ d from congrFun hlift₁ d,
      show Circle.exp (L₂ d) = f₂ d from congrFun hlift₂ d]
  have hloopp : ((c₁ * c₂).comp iota) v1 = ((c₁ * c₂).comp iota) v0 := by
    show f₁ v1 * f₂ v1 = f₁ v0 * f₂ v0
    rw [hloop₁, hloop₂]
  refine windMap_eq_of_char _ (L₁ + L₂) hliftp (windMap f₁ + windMap f₂) ?_
  rw [hloopp]
  show (L₁ v1 + L₂ v1) - (L₁ v0 + L₂ v0) - _ = _
  push_cast
  linarith [hd₁, hd₂]

/-! ## §3. The ambient membrane ([G2]) -/

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-- **An ambient membrane ([G2])** for an embedded circle `γ ⊂ F` inside the AMBIENT space `X`.

Distinct from `CharSurface.Membrane`, which lives in the *bounding 3-manifold* `V` and serves
Taylor's Theorem 1.1: this one is the Freedman–Kirby membrane of blueprint node `[G2]` — a compact
2-manifold-with-boundary `S` mapped into the ambient 4-manifold with `∂S` the circle `C ⊂ F`. The
three summands of the membrane index all live on this datum.

The two `Finite` fields are the **genericity/transversality inputs** (the membrane is put in general
position with respect to `F` and to itself). They do NOT carry the index values — those are
`Set.ncard` of sets that the map `D` determines outright. -/
structure AmbientMembrane (C : PinCharSurface X k) (γ : EmbeddedCircle C) where
  /-- The membrane's underlying compact 2-manifold-with-boundary. -/
  S : Type
  [topS : TopologicalSpace S]
  [chartS : ChartedSpace (EuclideanHalfSpace 2) S]
  [mfdS : IsManifold (𝓡∂ 2) k S]
  [compactS : CompactSpace S]
  /-- The boundary identification: a continuous injection of the circle onto `∂S`. -/
  bd : ↑Circle1 → S
  bd_cont : Continuous bd
  bd_inj : Function.Injective bd
  bd_boundary : Set.range bd = (𝓡∂ 2).boundary S
  /-- The membrane map into the AMBIENT space. -/
  D : S → X
  D_cont : Continuous D
  /-- Boundary factorization: `∂D` is the embedded circle sitting inside the characteristic
  surface `F ⊂ X`. -/
  factor : ∀ p, D (bd p) = C.F.f (γ.f p)
  /-- **Transversality to `F`** (genericity input): the membrane's interior meets the
  characteristic surface in finitely many points. -/
  transF : {p : S | p ∉ (𝓡∂ 2).boundary S ∧ D p ∈ Set.range C.F.f}.Finite
  /-- **Self-transversality** (genericity input): the membrane has finitely many double points. -/
  transD : (doubleSet D).Finite

namespace AmbientMembrane

variable {C : PinCharSurface X k} {γ : EmbeddedCircle C}

instance (m : AmbientMembrane C γ) : TopologicalSpace m.S := m.topS
instance (m : AmbientMembrane C γ) : ChartedSpace (EuclideanHalfSpace 2) m.S := m.chartS
instance (m : AmbientMembrane C γ) : IsManifold (𝓡∂ 2) k m.S := m.mfdS
instance (m : AmbientMembrane C γ) : CompactSpace m.S := m.compactS

/-! ### The first summand `D·F`: the interior intersection with the characteristic surface -/

/-- The set of interior points of the membrane lying on the characteristic surface. Determined by
`D` and `F` — nothing about it is a field. -/
def meetF (m : AmbientMembrane C γ) : Set m.S :=
  {p | p ∉ (𝓡∂ 2).boundary m.S ∧ m.D p ∈ Set.range C.F.f}

lemma meetF_finite (m : AmbientMembrane C γ) : m.meetF.Finite := m.transF

/-- **`D·F` — the first summand, CONSTRUCTED**: the mod-2 count of the membrane's interior
intersections with the characteristic surface. -/
noncomputable def intF (m : AmbientMembrane C γ) : ZMod 2 := (m.meetF.ncard : ZMod 2)

/-- A membrane whose interior misses `F` has `D·F = 0`. -/
theorem intF_eq_zero_of_meetF_empty (m : AmbientMembrane C γ) (h : m.meetF = ∅) : m.intF = 0 := by
  rw [intF, h, Set.ncard_empty]
  rfl

/-- A membrane whose interior meets `F` in exactly one point has `D·F = 1` — the summand is
genuinely nonzero-valued, not a dressed-up zero. -/
theorem intF_eq_one_of_meetF_singleton (m : AmbientMembrane C γ) {p : m.S}
    (h : m.meetF = {p}) : m.intF = 1 := by
  rw [intF, h, Set.ncard_singleton]
  rfl

/-! ### The third summand `d(C)`: the membrane's double points -/

/-- **`d(C)` — the third summand, CONSTRUCTED**: the mod-2 count of the membrane's double points
(unordered pairs of distinct points with the same image). -/
noncomputable def dbl (m : AmbientMembrane C γ) : ZMod 2 := ((doubleSet m.D).ncard : ZMod 2)

/-- An **embedded** membrane has no double points. -/
theorem dbl_eq_zero_of_injective (m : AmbientMembrane C γ) (h : Function.Injective m.D) :
    m.dbl = 0 := by
  rw [dbl, doubleSet_eq_empty_of_injective h, Set.ncard_empty]
  rfl

/-- A membrane with exactly one double point has `d(C) = 1`. -/
theorem dbl_eq_one_of_singleton (m : AmbientMembrane C γ) {e : Sym2 m.S}
    (h : doubleSet m.D = {e}) : m.dbl = 1 := by
  rw [dbl, h, Set.ncard_singleton]
  rfl

end AmbientMembrane

/-! ## §4. The framed membrane and THE INDEX `D·F + O(D) + d(C)` -/

/-- **A framed ambient membrane**: an `AmbientMembrane` together with the boundary framing
comparison — the loop `∂S ≅ S¹ → SO(2) ≅ S¹` measuring the discrepancy between the `F`-induced
normal framing along the circle and a global trivialization of the membrane's (necessarily trivial)
normal bundle. -/
structure FramedMembrane (C : PinCharSurface X k) (γ : EmbeddedCircle C)
    extends AmbientMembrane C γ where
  /-- The boundary framing comparison. -/
  cmp : C(↑unitInterval, Circle)
  /-- It is a loop (the boundary is a circle). -/
  cmp_loop : cmp 1 = cmp 0

namespace FramedMembrane

variable {C : PinCharSurface X k} {γ : EmbeddedCircle C}

/-- **`O(D)` — the second summand, CONSTRUCTED**: the degree of the framing comparison loop. -/
noncomputable def obs (m : FramedMembrane C γ) : ℤ := loopDegree m.cmp

/-- **THE MEMBRANE INDEX** — Freedman–Kirby Lemma 2.6.1 / blueprint `[Q1]`, verbatim:
`q_F(x) := D·F + O(D) + d(C) mod 2`.

Every summand is *computed* from the membrane datum — `Set.ncard` of a set the map `D` determines,
and the lift-based degree of the framing loop. There is no `ZMod`-valued field anywhere in
`FramedMembrane`, which is exactly what keeps this from being `Z4Quadratic` in new clothes. -/
noncomputable def index (m : FramedMembrane C γ) : ZMod 2 :=
  m.intF + ((m.obs : ZMod 2)) + m.dbl

/-- The index of an embedded, `F`-avoiding, untwisted membrane is `0` — all three summands
vanish for the simplest geometry. -/
theorem index_eq_zero (m : FramedMembrane C γ) (h1 : m.meetF = ∅) (h2 : Function.Injective m.D)
    (h3 : m.obs = 0) : m.index = 0 := by
  rw [index, m.intF_eq_zero_of_meetF_empty h1, m.dbl_eq_zero_of_injective h2, h3]
  decide

/-- **Each summand can flip the index on its own** (the per-summand vacuity attack, run): with the
other two vanishing, a single interior intersection, a single double point, or an odd framing degree
each gives `index = 1`. So the index is not a dressed-up constant and no summand is inert. -/
theorem index_eq_one_of_intF (m : FramedMembrane C γ) {p : m.S} (h1 : m.meetF = {p})
    (h2 : Function.Injective m.D) (h3 : m.obs = 0) : m.index = 1 := by
  rw [index, m.intF_eq_one_of_meetF_singleton h1, m.dbl_eq_zero_of_injective h2, h3]
  decide

theorem index_eq_one_of_dbl (m : FramedMembrane C γ) (h1 : m.meetF = ∅) {e : Sym2 m.S}
    (h2 : doubleSet m.D = {e}) (h3 : m.obs = 0) : m.index = 1 := by
  rw [index, m.intF_eq_zero_of_meetF_empty h1, m.dbl_eq_one_of_singleton h2, h3]
  decide

theorem index_eq_one_of_obs (m : FramedMembrane C γ) (h1 : m.meetF = ∅)
    (h2 : Function.Injective m.D) (h3 : m.obs = 1) : m.index = 1 := by
  rw [index, m.intF_eq_zero_of_meetF_empty h1, m.dbl_eq_zero_of_injective h2, h3]
  decide

end FramedMembrane

/-! ## §5. The named geometric statements ([G2] realization, [Q1] well-definedness, [Q2] sum) -/

/-- **[G2] realization**: every mod-2 homology class of the characteristic surface is carried by an
embedded circle bounding a framed membrane in the ambient. Pure existence — no index value, no
signature, no `σ` appears. -/
def MembraneRealizes (C : PinCharSurface X k) : Prop :=
  ∀ x : C.ι → ZMod 2, ∃ γ : EmbeddedCircle C, γ.cls = x ∧ Nonempty (FramedMembrane C γ)

/-- **[Q1] Freedman–Kirby Lemma 2.6.1** — *the* well-definedness statement of the blueprint: the
membrane index depends only on the circle's homology class, not on the circle, the membrane, or the
framing comparison. This is the single geometric theorem the whole construction rests on, and it is a
predicate purely on membranes: nothing in its statement mentions `σ`, so it passes the intensional
admissibility criterion of `GMTripleLayerForcing` by inspection. -/
def IndexWellDefined (C : PinCharSurface X k) : Prop :=
  ∀ (γ γ' : EmbeddedCircle C) (m : FramedMembrane C γ) (m' : FramedMembrane C γ'),
    γ.cls = γ'.cls → m.index = m'.index

/-- **A membrane system**: a choice of framed membrane for every class. Produced from `[G2]`
realization by choice (`nonempty_membraneSystem`), so it adds nothing beyond it. -/
structure MembraneSystem (C : PinCharSurface X k) where
  /-- The chosen representing circle. -/
  circle : (C.ι → ZMod 2) → EmbeddedCircle C
  /-- It represents the class. -/
  circle_cls : ∀ x, (circle x).cls = x
  /-- Its chosen framed membrane. -/
  memb : ∀ x, FramedMembrane C (circle x)

/-- Realization produces a membrane system (classical choice, no new geometry). -/
theorem nonempty_membraneSystem {C : PinCharSurface X k} (h : MembraneRealizes C) :
    Nonempty (MembraneSystem C) := by
  classical
  choose γ hcls hmem using h
  exact ⟨⟨γ, hcls, fun x => (hmem x).some⟩⟩

namespace MembraneSystem

variable {C : PinCharSurface X k}

/-- The geometric index function on `H₁(F;ℤ/2)`, read off the system's membranes. -/
noncomputable def index (sys : MembraneSystem C) (x : C.ι → ZMod 2) : ZMod 2 :=
  (sys.memb x).index

/-- **[Q2] the polarization identity** — the membrane-sum step of Freedman–Kirby: joining the
membranes of `x` and `y` produces a membrane for `x + y` whose index differs from the sum by exactly
the mutual intersection number, which is the mod-2 intersection form `B(x, y)`. Again a predicate
purely on membranes and the surface's own intersection form. -/
def Refines (sys : MembraneSystem C) : Prop :=
  ∀ x y, sys.index (x + y) = sys.index x + sys.index y + C.Q.B x y

end MembraneSystem

/-! ## §6. The enhancement PRODUCED from the membrane index — and the pin⁻ class `w` -/

section Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private lemma self_add_self (v : ι → ZMod 2) : v + v = 0 := by
  funext i
  exact (by decide : ∀ a : ZMod 2, a + a = 0) (v i)

/-- **The mod-2 membrane-index route forces an ALTERNATING intersection form** (new — the exact
scope of blueprint Route A, kernel-checked). If any function `μ` on `H₁(F;ℤ/2)` satisfies the
`[Q2]` polarization identity against `Q.B`, then `B(v,v) = 0` for every `v`. Setting `x = y = v`
gives `0 = μ(v) + μ(v) + B(v,v) = B(v,v)` because `μ(v) + μ(v) = 0` in `ZMod 2`.

Consequence (`not_exists_index_of_B_self_ne_zero`): the Freedman–Kirby mod-2 index provably cannot
produce the enhancement of a characteristic surface with an odd class — the `ℝP²` stratum. That is
not a defect of the construction; it is the precise content of the blueprint's remark that the
Guillou–Marin (Pin⁻, `ℤ/4`) form "is sharper … but costs nonorientable-surface + Pin⁻ normal data on
top". Route A reaches the orientable stratum and, kernel-checkably, only that one. -/
theorem refines_forces_alternating {Q : Z4Quadratic ι} {μ : (ι → ZMod 2) → ZMod 2}
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) (v : ι → ZMod 2) : Q.B v v = 0 := by
  have hz : μ 0 = 0 := by
    have h00 := h 0 0
    rw [add_zero, Q.B_zero_left] at h00
    revert h00
    generalize μ 0 = a
    revert a
    decide
  have hvv := h v v
  rw [self_add_self v, hz] at hvv
  revert hvv
  generalize μ v = a
  generalize Q.B v v = b
  revert a b
  decide

/-- **No mod-2 membrane index exists on a form with an odd value** (new — the refutation form). -/
theorem not_exists_index_of_B_self_ne_zero {Q : Z4Quadratic ι} {v : ι → ZMod 2}
    (hv : Q.B v v ≠ 0) :
    ¬ ∃ μ : (ι → ZMod 2) → ZMod 2, ∀ x y, μ (x + y) = μ x + μ y + Q.B x y := by
  rintro ⟨μ, h⟩
  exact hv (refines_forces_alternating h v)

/-- **THE ENHANCEMENT, PRODUCED FROM GEOMETRY** (new — the substrate `CharSurfaceFKVacuity` §3 named
as missing). Given a membrane index `μ` satisfying the `[Q2]` polarization identity against the
surface's own mod-2 intersection form, `embed2 ∘ μ` is a genuine `Z4Quadratic` on `H₁(F;ℤ/2)` — the
`ℤ/4` enhancement of the orientable (Arf) stratum, `q̂ = 2·q_F`. Only `refine'` consumes the
geometry; the polar form and all of its algebra come from the surface datum unchanged, which is
exactly what makes the produced enhancement comparable to `C.Q` along the torsor. -/
noncomputable def geomEnhancement (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) : Z4Quadratic ι where
  q v := embed2 (μ v)
  B := Q.B
  refine' x y := by rw [h x y, embed2_add, embed2_add]
  B_add_left := Q.B_add_left
  B_symm := Q.B_symm
  nondeg := Q.nondeg

@[simp] lemma geomEnhancement_B (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) : (geomEnhancement Q μ h).B = Q.B := rfl

@[simp] lemma geomEnhancement_q (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) (v : ι → ZMod 2) :
    (geomEnhancement Q μ h).q v = embed2 (μ v) := rfl

/-- The produced enhancement is even — it is `2 ×` the Arf form, so its Brown invariant is `4·Arf`. -/
theorem geomEnhancement_isEven (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) : Z4Quadratic.IsEven (geomEnhancement Q μ h) :=
  fun v => ⟨μ v, rfl⟩

/-- **THE PIN⁻ CLASS `w`, CONSTRUCTED FROM THE MEMBRANE INDEX** (new — the target of the whole
arc). The enhancement produced by the membrane index shares the surface's polar form by
construction, so the simply-transitive torsor theorem `PinTorsor.shift_simply_transitive` supplies a
**unique** class `w ∈ H₁(F;ℤ/2) ≅ H¹(F;ℤ/2)` carrying the substrate's recorded enhancement to the
geometric one. `PinEnhancementTorsor` proved that recording the polar form plus one such class
records the enhancement completely; this theorem says the class is *computed* by the blueprint's
`D·F + O(D) + d(C)`, not chosen. -/
theorem exists_unique_pin_class (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) :
    ∃! w : ι → ZMod 2, Q.shift w = geomEnhancement Q μ h :=
  SKEFTHawking.PinTorsor.shift_simply_transitive rfl

/-! ### The `[FK]` congruence at the produced enhancement -/

/-- The Guillou–Marin residue of an even form is `8·Arf` — so it can only be `0` or `8` in
`ZMod 16`. -/
theorem doubleBrown_of_isEven {Q : Z4Quadratic ι} (hE : Z4Quadratic.IsEven Q) :
    doubleBrown Q = 8 * ((Q.arf.val : ℕ) : ZMod 16) := by
  have hb := brown_eq_four_mul_arf Q hE
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) Q.arf with h0 | h1
  · rw [doubleBrown, hb, h0]; decide
  · rw [doubleBrown, hb, h1]; decide

/-- **The blueprint's `[FK]` congruence, at the PRODUCED enhancement** (new): Guillou–Marin for the
membrane-index enhancement is exactly *`Arf(q_F) = (σ − ξ·ξ)/8 mod 2`* — blueprint line `[FK]`,
re-typed over an enhancement that is computed from membranes rather than carried as a free field.
Its hypothesis is a predicate on the membrane index, so it passes the intensional admissibility
criterion of `GMTripleLayerForcing`. -/
theorem gmrelation_geomEnhancement_iff (Q : Z4Quadratic ι) (μ : (ι → ZMod 2) → ZMod 2)
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y) (σ F : ℤ) :
    GMrelation σ F (geomEnhancement Q μ h) ↔
      ((σ - F : ℤ) : ZMod 16) = 8 * (((geomEnhancement Q μ h).arf.val : ℕ) : ZMod 16) := by
  show ((σ - F : ℤ) : ZMod 16) = doubleBrown _ ↔ _
  rw [doubleBrown_of_isEven (geomEnhancement_isEven Q μ h)]

end Construction

/-! ## §7. The surface-level assembly -/

namespace MembraneSystem

variable {C : PinCharSurface X k}

/-- The enhancement of the characteristic surface produced by a membrane system satisfying `[Q2]`. -/
noncomputable def enhancement (sys : MembraneSystem C) (h : sys.Refines) : Z4Quadratic C.ι :=
  geomEnhancement C.Q sys.index h

/-- **The surface's pin⁻ class, computed from its membranes** — the surface-level statement of
`exists_unique_pin_class`. -/
theorem exists_unique_pin_class (sys : MembraneSystem C) (h : sys.Refines) :
    ∃! w : C.ι → ZMod 2, C.Q.shift w = sys.enhancement h :=
  SKEFTHawking.MembraneIndex.exists_unique_pin_class C.Q sys.index h

/-- **A membrane system satisfying `[Q2]` forces the surface's intersection form to be
alternating** — the surface-level scope statement. A characteristic surface carrying an odd class
admits no `[Q2]`-compatible membrane system at all. -/
theorem refines_forces_alternating (sys : MembraneSystem C) (h : sys.Refines)
    (v : C.ι → ZMod 2) : C.Q.B v v = 0 :=
  SKEFTHawking.MembraneIndex.refines_forces_alternating h v

end MembraneSystem

/-! ## §8. The two attacks on THIS layer, run and recorded as theorems

A statement layer that fails either attack is worse than nothing, because a later worker will
consume it. Both are run here, and the well-definedness attack **finds a genuine defect** in the
free-framing shape of `[Q1]` — recorded as a refutation and then repaired, in the same idiom as
`CharSurfaceFKVacuity`'s `charSurfaceFK_universal_over_free_enhancement_false` one level up. -/

namespace FramedMembrane

variable {C : PinCharSurface X k} {γ : EmbeddedCircle C}

/-- The standard `2π`-comparison is a loop. -/
theorem stdLoop_loop : stdLoop 1 = stdLoop 0 := by
  show Circle.exp (2 * Real.pi * ((1 : ↑unitInterval) : ℝ))
    = Circle.exp (2 * Real.pi * ((0 : ↑unitInterval) : ℝ))
  norm_num [exp_two_pi]

/-- **Twisting the boundary framing by one full turn**, leaving the underlying membrane untouched. -/
noncomputable def twist (m : FramedMembrane C γ) : FramedMembrane C γ :=
  { m with
    cmp := m.cmp * stdLoop
    cmp_loop := by
      show m.cmp 1 * stdLoop 1 = m.cmp 0 * stdLoop 0
      rw [m.cmp_loop, stdLoop_loop] }

@[simp] lemma twist_toAmbientMembrane (m : FramedMembrane C γ) :
    m.twist.toAmbientMembrane = m.toAmbientMembrane := rfl

/-- The twist adds one full turn to the framing obstruction (`loopDegree_mul`). -/
theorem obs_twist (m : FramedMembrane C γ) : m.twist.obs = m.obs + 1 := by
  show loopDegree (m.cmp * stdLoop) = loopDegree m.cmp + 1
  rw [loopDegree_mul m.cmp_loop stdLoop_loop, loopDegree_stdLoop]

/-- The twist flips the membrane index. -/
theorem index_twist (m : FramedMembrane C γ) : m.twist.index = m.index + 1 := by
  have h : m.twist.index = m.intF + ((m.twist.obs : ZMod 2)) + m.dbl := rfl
  rw [h, obs_twist, index]
  push_cast
  ring

/-- **P5 repackaging check — the layer PASSES** (new). The anti-pattern this module exists to avoid
is a `MembraneIndexData` structure carrying an `index : (ι → ZMod 2) → ZMod 4` field: such a thing
makes the index a function of the homology class **by construction**, and is `Z4Quadratic` in new
clothes. The constructed index provably is not: two framed membranes on the *same* circle — hence
carrying the same class — have different indices. The membrane layer is therefore strictly more data
than the enhancement it produces, which is exactly the asymmetry a field-carrying structure lacks. -/
theorem index_not_a_function_of_the_class (m : FramedMembrane C γ) :
    ∃ m' : FramedMembrane C γ, m'.index ≠ m.index := by
  refine ⟨m.twist, ?_⟩
  rw [index_twist]
  generalize m.index = a
  revert a
  decide

/-- **Well-definedness attack — the free-framing `[Q1]` layer is FALSE** (new; the refutation is the
content). `IndexWellDefined` quantifies over *all* framed membranes, and the framing comparison is
free data, so the twist refutes it outright the moment a single framed membrane exists. This is the
same failure mode `CharSurfaceFKVacuity` found one level up (a free enhancement makes the universal
`[FK]` statement false, not merely vacuous), reappearing at the framing: **`O(D)` must be *produced*
from the smooth normal data, not carried.** The repair is `NormalFramingTie` below. -/
theorem indexWellDefined_false_of_framedMembrane (m : FramedMembrane C γ) :
    ¬ IndexWellDefined C := by
  intro h
  have hEq : m.index = m.twist.index := h γ γ m m.twist rfl
  rw [index_twist] at hEq
  revert hEq
  generalize m.index = a
  revert a
  decide

end FramedMembrane

/-! ### The repair: the framing must be TIED to the normal data -/

/-- **A normal-framing tie** — the corrected shape of the framing input. It selects, among the
framing comparisons an ambient membrane can carry, those induced by the smooth normal data; its one
defining property is **rigidity**: tied framings on the same underlying membrane have the same
degree. This is the honest minimal content of "the normal bundle determines `O(D)`", and it is
exactly what the free-framing shape lacked. Producing a tie from the smooth normal bundles of `D`
and `F` is the residual smooth debt of node `[G2]`. -/
structure NormalFramingTie (C : PinCharSurface X k) where
  /-- Which framings are induced by the normal data. -/
  Tied : ∀ {γ : EmbeddedCircle C}, FramedMembrane C γ → Prop
  /-- **Rigidity**: the normal data determines the framing obstruction. -/
  rigid : ∀ {γ : EmbeddedCircle C} (m m' : FramedMembrane C γ),
    m.toAmbientMembrane = m'.toAmbientMembrane → Tied m → Tied m' → m.obs = m'.obs

namespace NormalFramingTie

variable {C : PinCharSurface X k}

/-- **The twist escapes a rigid tie** (PROVED): at most one of a framing and its full-turn twist is
induced by the normal data. So the refutation of `indexWellDefined_false_of_framedMembrane` does not
reach the tied layer — the repair is genuine, not cosmetic. -/
theorem not_tied_twist (tie : NormalFramingTie C) {γ : EmbeddedCircle C}
    {m : FramedMembrane C γ} (h : tie.Tied m) : ¬ tie.Tied m.twist := by
  intro htw
  have := tie.rigid m m.twist rfl h htw
  rw [FramedMembrane.obs_twist] at this
  omega

/-- **The tie is inhabited at an underlying membrane**: some framing on it is normal-data-induced.
Rigidity alone is satisfied by the empty tie (`trivialTie_rigid_but_uninhabited`), so this is the
load-bearing half. -/
def Inhabits (tie : NormalFramingTie C) {γ : EmbeddedCircle C} (a : AmbientMembrane C γ) : Prop :=
  ∃ m : FramedMembrane C γ, m.toAmbientMembrane = a ∧ tie.Tied m

/-- **A rigid, inhabited tie determines `O(D)` outright** (PROVED — the payoff of the repair): the
framing obstruction of an ambient membrane is a *unique* integer once the normal data selects the
framings. This is the precise sense in which `O(D)` becomes a function of the geometry. -/
theorem existsUnique_obs (tie : NormalFramingTie C) {γ : EmbeddedCircle C}
    {a : AmbientMembrane C γ} (h : tie.Inhabits a) :
    ∃! o : ℤ, ∃ m : FramedMembrane C γ, m.toAmbientMembrane = a ∧ tie.Tied m ∧ m.obs = o := by
  obtain ⟨m, hma, hmt⟩ := h
  refine ⟨m.obs, ⟨m, hma, hmt, rfl⟩, ?_⟩
  rintro o ⟨m', hm'a, hm't, rfl⟩
  exact (tie.rigid m' m (hm'a.trans hma.symm) hm't hmt)

/-- **The tie's own vacuity attack — rigidity alone is NOT enough** (new). The empty tie is rigid
and selects nothing, so `IndexWellDefinedTied` over it would be vacuously true. Inhabitedness is
therefore a genuine, separate requirement and not a decorative conjunct. -/
def trivialTie (C : PinCharSurface X k) : NormalFramingTie C where
  Tied _ := False
  rigid _ _ _ h := absurd h not_false

theorem trivialTie_rigid_but_uninhabited (C : PinCharSurface X k) {γ : EmbeddedCircle C}
    (a : AmbientMembrane C γ) : ¬ (trivialTie C).Inhabits a := by
  rintro ⟨m, -, hm⟩
  exact hm

end NormalFramingTie

/-- **`[Q1]` Freedman–Kirby Lemma 2.6.1, CORRECTED** — the well-definedness statement restricted to
normal-data-induced framings. Unlike `IndexWellDefined` (refuted by
`FramedMembrane.indexWellDefined_false_of_framedMembrane`) this shape survives the twist, by
`NormalFramingTie.not_tied_twist`. It remains a predicate purely on membranes: `σ` does not occur. -/
def IndexWellDefinedTied {C : PinCharSurface X k} (tie : NormalFramingTie C) : Prop :=
  ∀ (γ γ' : EmbeddedCircle C) (m : FramedMembrane C γ) (m' : FramedMembrane C γ'),
    tie.Tied m → tie.Tied m' → γ.cls = γ'.cls → m.index = m'.index

/-! ## §9. `[Q1]` closes the arc: the extracted pin⁻ class is an invariant of the surface -/

namespace MembraneSystem

variable {C : PinCharSurface X k}

/-- A membrane system is **tied** when every chosen framing is normal-data-induced. -/
def Tied (sys : MembraneSystem C) (tie : NormalFramingTie C) : Prop :=
  ∀ x, tie.Tied (sys.memb x)

/-- **Tied well-definedness makes the index choice-free** (PROVED): any two tied membrane systems on
the same characteristic surface compute the *same* index function on `H₁(F;ℤ/2)`. This is what the
corrected `[Q1]` buys — the circles, the membranes and the framings all drop out. -/
theorem index_eq_of_tied {tie : NormalFramingTie C} (hwd : IndexWellDefinedTied tie)
    {sys sys' : MembraneSystem C} (ht : sys.Tied tie) (ht' : sys'.Tied tie) :
    sys.index = sys'.index := by
  funext x
  exact hwd _ _ (sys.memb x) (sys'.memb x) (ht x) (ht' x)
    ((sys.circle_cls x).trans (sys'.circle_cls x).symm)

/-- Equal index functions produce the same enhancement. -/
theorem enhancement_eq {sys sys' : MembraneSystem C} (h : sys.Refines) (h' : sys'.Refines)
    (hidx : sys.index = sys'.index) : sys.enhancement h = sys'.enhancement h' := by
  refine Z4Quadratic.ext (funext fun v => ?_)
  show embed2 (sys.index v) = embed2 (sys'.index v)
  rw [hidx]

/-- **THE ARC'S CLOSING THEOREM** (new): under the corrected `[Q1]`, the pin⁻ class extracted from
the membrane index is an invariant of the characteristic surface — independent of the representing
circles, of the membranes, and of the framings. Combined with `exists_unique_pin_class` (the class
exists and is unique for a given system) this says the blueprint's `D·F + O(D) + d(C)` genuinely
*computes* the one `H¹(F;ℤ/2)`-class that `PinEnhancementTorsor` showed the substrate to be
missing. -/
theorem pin_class_indep_of_system {tie : NormalFramingTie C} (hwd : IndexWellDefinedTied tie)
    {sys sys' : MembraneSystem C} (ht : sys.Tied tie) (ht' : sys'.Tied tie)
    (h : sys.Refines) (h' : sys'.Refines) {w w' : C.ι → ZMod 2}
    (hw : C.Q.shift w = sys.enhancement h) (hw' : C.Q.shift w' = sys'.enhancement h') :
    w = w' := by
  refine SKEFTHawking.PinTorsor.shift_left_injective C.Q ?_
  rw [hw, hw', enhancement_eq h h' (index_eq_of_tied hwd ht ht')]

end MembraneSystem

/-! ### No information is lost or invented in the extraction -/

/-- **The membrane index is recoverable from the pin⁻ class** (new): distinct indices give distinct
classes. So the map "membrane index ↦ pin⁻ class `w`" of `exists_unique_pin_class` is injective —
the extraction neither loses the geometry nor manufactures a class the index did not determine. -/
theorem index_eq_of_pin_class_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    {μ μ' : (ι → ZMod 2) → ZMod 2}
    (h : ∀ x y, μ (x + y) = μ x + μ y + Q.B x y)
    (h' : ∀ x y, μ' (x + y) = μ' x + μ' y + Q.B x y) {w : ι → ZMod 2}
    (hw : Q.shift w = geomEnhancement Q μ h) (hw' : Q.shift w = geomEnhancement Q μ' h') :
    μ = μ' := by
  have heq : geomEnhancement Q μ h = geomEnhancement Q μ' h' := hw ▸ hw'
  funext v
  exact embed2_injective (congrArg (fun R : Z4Quadratic ι => R.q v) heq)

/-- **The Route-A scope statement, instantiated on the carrier the project actually cares about**
(new — the registry-ready refutation). `stdQuadratic 1` is the `ℝP²` enhancement, the surface half of
the `(ℝP⁴, ℝP²)` generator (`GuillouMarinBridge.GM_rp4`); its intersection form has `B(1,1) = 1`, so
**no mod-2 membrane index exists on it at all**. Concretely: the Freedman–Kirby `D·F + O(D) + d(C)`
construction of blueprint Route A cannot produce the pin⁻ class of a nonorientable characteristic
surface, and no amount of work on the membrane layer will change that — the obstruction is the
polarization identity itself, not a missing lemma. Reaching the `ℝP²` stratum requires the
Guillou–Marin `ℤ/4`-resolution index, whose coefficient split is *not* pinned by the in-tree
blueprint (which states only the mod-2 formula). -/
theorem no_mod2_index_on_rp2 :
    ¬ ∃ μ : (Fin 1 → ZMod 2) → ZMod 2,
        ∀ x y, μ (x + y) = μ x + μ y + (stdQuadratic 1).B x y := by
  refine not_exists_index_of_B_self_ne_zero (v := 1) ?_
  decide

/-! ## §10. The `[Q2]` polarization identity, DECOMPOSED into two pin-free geometric statements

`MembraneSystem.Refines` is the input `geomEnhancement` consumes. Left as a single Prop it would hide
the actual Freedman–Kirby computation, so it is split here — with the mutual intersection number of
two membranes *constructed*, exactly like the three index summands. -/

section Sum

variable {C : PinCharSurface X k} {γ₁ γ₂ : EmbeddedCircle C}

/-- The **mutual intersection set** of two membranes in the same ambient — determined by the two
maps, nothing declared. -/
def mutualSet (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂) : Set (m₁.S × m₂.S) :=
  {e | m₁.D e.1 = m₂.D e.2}

/-- **`D₁ · D₂` — the membrane-sum correction term, CONSTRUCTED**: the mod-2 count of the two
membranes' mutual intersections. -/
noncomputable def mutualInt (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂) : ZMod 2 :=
  ((mutualSet m₁ m₂).ncard : ZMod 2)

/-- Membranes with disjoint images do not intersect. -/
theorem mutualInt_eq_zero (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂)
    (h : mutualSet m₁ m₂ = ∅) : mutualInt m₁ m₂ = 0 := by
  rw [mutualInt, h, Set.ncard_empty]
  rfl

/-- **The mutual intersection number is symmetric** (PROVED, via `Prod.swap`) — as the mod-2
intersection form it is supposed to compute must be (`Z4Quadratic.B_symm`). -/
theorem mutualInt_symm (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂) :
    mutualInt m₂ m₁ = mutualInt m₁ m₂ := by
  have h : mutualSet m₂ m₁ = Prod.swap '' (mutualSet m₁ m₂) := by
    ext e
    constructor
    · intro he
      exact ⟨(e.2, e.1), he.symm, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp.symm
  rw [mutualInt, mutualInt, h, Set.ncard_image_of_injective _ Prod.swap_injective]

end Sum

variable {C : PinCharSurface X k}

/-- **`[Q2a]` the membrane-sum step** — the Freedman–Kirby computation itself: joining the membranes
of two circles produces a membrane for a circle carrying the sum class, whose index is the sum of the
two indices plus the mutual intersection correction. Pin-free, `σ`-free; the framings are required to
be normal-data-induced throughout, per the §8 repair. -/
def MembraneSumIndex (tie : NormalFramingTie C) : Prop :=
  ∀ (γ₁ γ₂ : EmbeddedCircle C) (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂),
    tie.Tied m₁ → tie.Tied m₂ →
      ∃ (γ : EmbeddedCircle C) (m : FramedMembrane C γ),
        γ.cls = γ₁.cls + γ₂.cls ∧ tie.Tied m ∧
          m.index = m₁.index + m₂.index + mutualInt m₁ m₂

/-- **`[Q2b]` the mutual intersection number IS the intersection form** — the classical transversality
statement that the mod-2 count of `D₁ ⋔ D₂` computes `B(x, y)` on `H₁(F;ℤ/2)`. Pin-free, `σ`-free,
and about membranes only. -/
def MutualIsForm (C : PinCharSurface X k) : Prop :=
  ∀ (γ₁ γ₂ : EmbeddedCircle C) (m₁ : FramedMembrane C γ₁) (m₂ : FramedMembrane C γ₂),
    mutualInt m₁ m₂ = C.Q.B γ₁.cls γ₂.cls

/-- **`[Q2]` SPLITS** (PROVED): the polarization identity that `geomEnhancement` consumes is
*derived* from the membrane-sum step, the transversality identification of the mutual intersection
number, and the corrected well-definedness — three strictly finer, pin-free, `σ`-free geometric
statements. Nothing about the enhancement is assumed; the algebra is all that is added. -/
theorem refines_of_membraneSum {tie : NormalFramingTie C} (hwd : IndexWellDefinedTied tie)
    (hsum : MembraneSumIndex tie) (hform : MutualIsForm C)
    (sys : MembraneSystem C) (ht : sys.Tied tie) : sys.Refines := by
  intro x y
  obtain ⟨γ, m, hcls, hmt, hidx⟩ :=
    hsum (sys.circle x) (sys.circle y) (sys.memb x) (sys.memb y) (ht x) (ht y)
  have hxy : γ.cls = (sys.circle (x + y)).cls := by
    rw [hcls, sys.circle_cls, sys.circle_cls, sys.circle_cls]
  have h1 : sys.index (x + y) = m.index :=
    hwd _ _ (sys.memb (x + y)) m (ht (x + y)) hmt hxy.symm
  rw [h1, hidx, hform, sys.circle_cls, sys.circle_cls]
  rfl

end SKEFTHawking.MembraneIndex
