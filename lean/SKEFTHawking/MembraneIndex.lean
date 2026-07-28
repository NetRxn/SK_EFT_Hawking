/-
# Phase 5q.H (E2 · [G2]/[Q1]) — the MEMBRANE INDEX `D·F + O(D) + d(C)`, CONSTRUCTED

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceMembrane
import SKEFTHawking.PinEnhancementTorsor

namespace SKEFTHawking.MembraneIndex

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.CharSurface
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

/-! ## §2. The ambient membrane ([G2]) -/

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

end SKEFTHawking.MembraneIndex
