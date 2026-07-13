/-
# Phase 5q.H (E2 · realization layer) — the EXACT split of Taylor Theorem 1.1's surface-realization
debt, and the kernel-restricted realization the composed end actually consumes

`CharSurfaceMembrane.lean` reduced the frozen `TaylorKernelVanishing` (Taylor `0802.0111` Thm 1.1)
to five pin-free residue nodes, two of which are the classical-topology realization ingredients:
`PinCharSurface.ClassesEmbedded` (surface-only: every nonzero mod-2 `H₁` class is represented by an
embedded circle) and `PinCharSurface.Bounding.KernelCirclesBound` (3-manifold-only: a circle dying
in `V` bounds a membrane), combining to `MembraneRealizes`.

This module does TWO things, each a THEOREM, no re-freeze of equal size:

* **The EXACT split of `ClassesEmbedded`.** The per-class predicate `RepresentedByEmbedded l`
  ("`l` is `γ.cls` for some embedded circle `γ`") is the atomic building block. Taylor Theorem 1.1
  consumes `ClassesEmbedded` exactly the way the classical simple-closed-curve theorem is proved —
  represent a basis of `H₁(F;ℤ/2)` by embedded circles, then band-sum. We make that decomposition
  precise and EXACT:
  - `BasisEmbedded` — the generator leg: each standard `H₁`-basis class `Pi.single i 1` is
    represented by an embedded circle (the SCC-for-a-primitive-class fact).
  - `EmbeddedSumClosed` — the band-sum leg: the "represented by an embedded circle" predicate is
    closed under the group operation on nonzero sums (the geometric band-sum / resolve-intersections
    operation on a surface).
  - `classesEmbedded_iff_basisEmbedded_sumClosed` (PROVED, both ways): `ClassesEmbedded ↔
    BasisEmbedded ∧ EmbeddedSumClosed`. Forward is a finite-support induction (write a nonzero class
    as a sum of basis vectors, every partial sum an indicator of a nonempty set hence nonzero);
    backward is immediate. The two legs are strictly-more-atomic named surface-topology primitives;
    neither is derivable in current Mathlib (there is no surface classification / SCC-representability
    substrate), so they are the honest residuals — but the split isolates the generator content from
    the band-sum content, exactly as the classical proof does.

* **The kernel-restricted realization the composed end actually consumes.** `MembraneRealizes`
  quantifies only over KERNEL classes, so the full `ClassesEmbedded` (all nonzero classes) is more
  than the composed end needs. `KernelClassesEmbedded` restricts the surface-representability to the
  metabolizer, and `membraneRealizes_of_kernelClassesEmbedded` (PROVED) rebuilds `MembraneRealizes`
  from it plus `KernelCirclesBound` — a strictly weaker surface debt than
  `membraneRealizes_of_classesEmbedded`. `kernelClassesEmbedded_of_classesEmbedded` (PROVED) shows it
  is genuinely implied by the full form, and `gmrelation_null_of_kernelClassesEmbedded_isotropic`
  (PROVED) is the re-composed GM end on the tightened surface hypothesis.

* `boundsMembraneIn_iff_mem_kernelL` (PROVED, given `KernelCirclesBound`): the exact logical content
  of `KernelCirclesBound` — bounding a membrane is EQUIVALENT to dying in `V`, the converse of the
  already-proved `cls_mem_kernelL_of_boundsMembraneIn`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceNormalShadow

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality
open scoped Manifold

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-! ## The per-class embedded-representability predicate and the EXACT split of `ClassesEmbedded` -/

/-- **The per-class embedded-representability predicate**: the class `l` is realized by an embedded
circle — the atomic building block of `ClassesEmbedded`. `ClassesEmbedded` is exactly "every nonzero
class is `RepresentedByEmbedded`" (`classesEmbedded_iff`). -/
def PinCharSurface.RepresentedByEmbedded (C : PinCharSurface X k) (l : C.ι → ZMod 2) : Prop :=
  ∃ γ : EmbeddedCircle C, γ.cls = l

/-- `ClassesEmbedded` unfolds to per-class representability of every nonzero class. -/
theorem PinCharSurface.classesEmbedded_iff (C : PinCharSurface X k) :
    C.ClassesEmbedded ↔ ∀ l : C.ι → ZMod 2, l ≠ 0 → C.RepresentedByEmbedded l := Iff.rfl

/-- **The generator leg** (surface topology): each standard `H₁(F;ℤ/2)`-basis class `Pi.single i 1`
is represented by an embedded circle. The simple-closed-curve-for-a-primitive-class fact, restricted
to the basis dual to `H1Iso`. -/
def PinCharSurface.BasisEmbedded (C : PinCharSurface X k) : Prop :=
  ∀ i : C.ι, C.RepresentedByEmbedded (Pi.single i 1)

/-- **The band-sum leg** (surface topology): the embedded-representability predicate is closed under
the group operation on nonzero sums — if `a` and `b` are each represented by embedded circles and
`a + b ≠ 0`, then so is `a + b`. This is the geometric band-sum / resolve-intersections operation on
a surface (two embedded circles are surgered along a band into one embedded circle representing the
sum). -/
def PinCharSurface.EmbeddedSumClosed (C : PinCharSurface X k) : Prop :=
  ∀ a b : C.ι → ZMod 2, C.RepresentedByEmbedded a → C.RepresentedByEmbedded b → a + b ≠ 0 →
    C.RepresentedByEmbedded (a + b)

variable {C : PinCharSurface X k}

/-- A nonempty finite sum of distinct standard basis vectors is `RepresentedByEmbedded` under the two
legs — the finite-support core of the forward split. Every partial sum over a nonempty subset is the
indicator of that subset, hence nonzero, so the band-sum leg applies at each step. -/
theorem PinCharSurface.representedByEmbedded_sum_single (hbasis : C.BasisEmbedded)
    (hsum : C.EmbeddedSumClosed) (s : Finset C.ι) (hs : s.Nonempty) :
    C.RepresentedByEmbedded (∑ i ∈ s, Pi.single i (1 : ZMod 2)) := by
  revert hs
  induction s using Finset.induction with
  | empty => intro hs; simp at hs
  | @insert a t ha ih =>
    intro _
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simpa using hbasis a
    · rw [Finset.sum_insert ha]
      refine hsum _ _ (hbasis a) (ih ht) ?_
      intro hzero
      have hval := congrFun hzero a
      rw [Pi.add_apply, Pi.single_eq_same, Finset.sum_apply, Pi.zero_apply] at hval
      have hsum0 : ∑ i ∈ t, (Pi.single i (1 : ZMod 2)) a = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi ha).symm 1
      rw [hsum0, add_zero] at hval
      exact one_ne_zero hval

/-- **The EXACT split of `ClassesEmbedded`** (PROVED, both ways): the surface realization ingredient
is EQUIVALENT to the generator leg (`BasisEmbedded`) and the band-sum leg (`EmbeddedSumClosed`).
Forward writes a nonzero class as a sum of its support's basis vectors and inducts via the band-sum
leg; backward is `ClassesEmbedded` itself on `Pi.single`/on sums. Isolates the two classical
ingredients of the simple-closed-curve theorem without inflating the debt. -/
theorem PinCharSurface.classesEmbedded_iff_basisEmbedded_sumClosed (C : PinCharSurface X k) :
    C.ClassesEmbedded ↔ C.BasisEmbedded ∧ C.EmbeddedSumClosed := by
  constructor
  · intro h
    refine ⟨fun i => h (Pi.single i 1) ?_, fun a b _ _ hne => h (a + b) hne⟩
    intro hzero
    have := congrFun hzero i
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  · rintro ⟨hbasis, hsum⟩ l hl
    classical
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    set s : Finset C.ι := Finset.univ.filter (fun i => l i = 1) with hs_def
    have hl_eq : l = ∑ i ∈ s, Pi.single i (1 : ZMod 2) := by
      funext j
      rw [Finset.sum_apply, hs_def, Finset.sum_filter]
      simp only [Pi.single_apply]
      rw [Finset.sum_eq_single j]
      · rcases h2 (l j) with hj | hj <;> simp [hj]
      · intro x _ hxj; simp [Ne.symm hxj]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hs_ne : s.Nonempty := by
      rcases Function.ne_iff.mp hl with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      rw [hs_def, Finset.mem_filter]
      exact ⟨Finset.mem_univ j, (h2 (l j)).resolve_left hj⟩
    rw [hl_eq]
    exact representedByEmbedded_sum_single hbasis hsum s hs_ne

/-- **The constructive discharge direction** (PROVED): the two atomic surface-topology legs —
generator representability and band-sum closure — build `ClassesEmbedded`. This is the direction a
future discharge of `ClassesEmbedded` would use: supply an embedded circle for each `H₁`-basis class
and a band-sum operation, and the full realization follows. -/
theorem PinCharSurface.classesEmbedded_of_basisEmbedded_sumClosed (C : PinCharSurface X k)
    (hbasis : C.BasisEmbedded) (hsum : C.EmbeddedSumClosed) : C.ClassesEmbedded :=
  (C.classesEmbedded_iff_basisEmbedded_sumClosed).mpr ⟨hbasis, hsum⟩

/-! ## The kernel-restricted realization the composed end consumes -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}

namespace PinCharSurface.Bounding

/-- **Kernel-restricted embedded representability**: the surface realization ingredient restricted to
the metabolizer — every nonzero class dying in `V` is represented by an embedded circle. This is all
of the surface-realization debt the composed GM end actually consumes; the full `ClassesEmbedded`
(every nonzero class) is more than needed. -/
def KernelClassesEmbedded (b : C.Bounding J) : Prop :=
  ∀ l ∈ b.kernelL, l ≠ 0 → C.RepresentedByEmbedded l

/-- **`ClassesEmbedded` is genuinely stronger** (PROVED): the full surface-realization ingredient
implies its kernel-restricted form by forgetting the membership hypothesis. -/
theorem kernelClassesEmbedded_of_classesEmbedded (b : C.Bounding J) (h : C.ClassesEmbedded) :
    b.KernelClassesEmbedded :=
  fun l _ h0 => h l h0

/-- **The realization freeze splits — tightened** (PROVED): kernel-restricted embedded
representability (the surface debt only on the metabolizer) plus membrane existence for dying circles
(3-manifold-only) yield the realization freeze. Strictly weaker surface hypothesis than
`membraneRealizes_of_classesEmbedded`. -/
theorem membraneRealizes_of_kernelClassesEmbedded (b : C.Bounding J)
    (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound) : b.MembraneRealizes := by
  intro l hl h0
  obtain ⟨γ, hcls⟩ := h1 l hl h0
  exact ⟨γ, hcls, h2 γ (hcls ▸ hl)⟩

/-- **The exact content of `KernelCirclesBound`** (PROVED, given the freeze): bounding a membrane in
`V` is EQUIVALENT to the class dying in `V`. The forward direction is `KernelCirclesBound`; the
reverse is the already-proved `cls_mem_kernelL_of_boundsMembraneIn`. Pins that `KernelCirclesBound`
is exactly the converse of the proved membrane-kills-class implication. -/
theorem boundsMembraneIn_iff_mem_kernelL (b : C.Bounding J) (h : b.KernelCirclesBound)
    (γ : EmbeddedCircle C) : γ.BoundsMembraneIn b ↔ γ.cls ∈ b.kernelL :=
  ⟨fun hm => γ.cls_mem_kernelL_of_boundsMembraneIn b hm, fun hl => h γ hl⟩

/-- **The re-composed GM end on the tightened surface hypothesis** (PROVED): the kernel-restricted
surface realization, membrane existence for dying circles, the single pin⁻ atom, and the classical
Lagrangian package force the null Guillou–Marin residue. Same conclusion as
`gmrelation_null_of_classesEmbedded_isotropic` with the surface debt reduced to the metabolizer. -/
theorem gmrelation_null_of_kernelClassesEmbedded_isotropic (b : C.Bounding J)
    (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    GMrelation 0 0 C.Q :=
  gmrelation_null_of_membranes_isotropic b
    (membraneRealizes_of_kernelClassesEmbedded b h1 h2) hspin hlag

end PinCharSurface.Bounding

end SKEFTHawking.CharSurface
