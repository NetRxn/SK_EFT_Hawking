/-
# Phase 5q.H (E2 · circle layer) — embedded circles, disk vanishing, and the surgery-descent freeze

The per-circle vocabulary of Taylor's Theorem 1.1 proof, one level below `CharSurfaceBounding`
(DAG items A5/A6, `Lit-Search/Phase-5qH/ABK_injectivity_routes_lemma_DAG_20260703.md`):

* `EmbeddedCircle` — an embedded circle datum in an enhanced characteristic surface: a continuous
  injective map `S¹ → F` carrying its circle homology class, whose `H₁(F;ℤ/2)`-image `cls` is tied
  to the REAL singular homology through the embedding and `H1Iso` (only the identification of the
  carried class with THE generator of `H₁(S¹;ℤ/2)` awaits an in-tree circle-homology computation).
  `embed2_selfPair` derives `q(x) ≡ x•x (mod 2)` NOW.
* `disk_homology_eq_zero` + `cls_mem_kernelL_of_boundsDiskIn` — PROVED: a circle that bounds a
  disk in the bounding 3-manifold has its class in the Taylor/Klug metabolizer `kernelL`
  (functoriality + the in-tree disk contraction `SingularDiskAcyclic`).
* `TaylorDiskVanishing` — **statement freeze, Taylor `0802.0111` Lemma 1.3** (bounds a disk ⟹
  `q = 0`, the base case of Theorem 1.1's handle-decomposition argument), PLUS the proved
  subsumption `taylorDiskVanishing_of_taylorKernelVanishing`: at class level the Theorem 1.1
  freeze (`TaylorKernelVanishing`) already implies it.
* `SurgeredSurface` / `TaylorSurgeryDescends` — **statement freeze, Taylor `0802.0111` Lemma 1.2,
  the DESCENT direction** (verbatim: *"One can do surgery on this embedding and extend the
  Pin⁻-structure to the trace of the surgery if and only if q(S¹) = 0"*): an isotropic,
  homologically nontrivial embedded circle admits a surgered enhanced surface whose enhancement is
  the isotropic reduction (`BrownSurgeryReduction.SurgeryReduction`). The induction step
  `brown_surgeredSurface` (β unchanged) is DERIVED, not frozen. **Deliberately NOT frozen:** the
  converse (`extends ⟹ q = 0`) — stating it faithfully needs the trace-of-surgery 3-manifold with
  a Pin⁻-structure-on-3-manifolds (equivalently the `Ω₁^{Spin} ≅ ℤ/2` framed-circle invariant),
  vocabulary not in tree; any enhancement-level surrogate is either false or a tautology.
* `PinCharSurface.shiftEnh` — the KT-LMS Lemma 3.7 vocabulary at surface level (change the Pin⁻
  structure by a torsor translate); Lemma 3.7's content is PROVEN in the algebra layer
  (`brown_shift`), with the surface action an involution (`shiftEnh_shiftEnh`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceBounding
import SKEFTHawking.BrownSurgeryReduction
import SKEFTHawking.SingularDiskAcyclic

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularDiskAcyclic (Disk)

/-! ## The circle, the disk, and disk-level vanishing -/

/-- The circle `S¹` as the unit sphere in `ℝ²`, matching the in-tree disk convention
(`SingularDiskAcyclic.Disk n` is the closed unit ball in `EuclideanSpace ℝ (Fin n)`). -/
abbrev Circle1 : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

/-- The boundary inclusion `S¹ ↪ D²`. -/
def diskIncl : C(↑Circle1, ↑(Disk 2)) :=
  ⟨Set.inclusion Metric.sphere_subset_closedBall,
    continuous_inclusion Metric.sphere_subset_closedBall⟩

/-- **The disk is acyclic at homology level**: `Hₖ₊₁(Dⁿ; ℤ/2) = 0` (from the in-tree straight-line
contraction `SingularDiskAcyclic.cycle_mem_boundaries`). -/
theorem disk_homology_eq_zero {n : ℕ} (k : ℕ) (x : Homology (Disk n) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  exact SKEFTHawking.SingularDiskAcyclic.cycle_mem_boundaries k z.1 z.2

/-! ## Embedded circles in an enhanced characteristic surface -/

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-- **An embedded circle datum in an enhanced characteristic surface** `C`: a continuous injective
map of the circle into the surface (embeddedness = DATA, per the E1 checklist idiom), carrying a
homology class `fund` of the circle. The surface-side class is DERIVED (`cls`), tied to the real
singular `H₁(F;ℤ/2)` through the embedding — the one un-tied residue is that `fund` be THE
generator of `H₁(S¹;ℤ/2) ≅ ℤ/2`, whose in-tree computation (circle homology) does not yet exist. -/
structure EmbeddedCircle (C : PinCharSurface X k) where
  /-- The embedded circle. -/
  f : C(↑Circle1, C.F.M)
  /-- Embeddedness as data: the map is injective. -/
  inj : Function.Injective f
  /-- The carried circle class (the fundamental class of `S¹`, as data — see structure docstring). -/
  fund : Homology Circle1 1

namespace EmbeddedCircle

variable {C : PinCharSurface X k}

/-- The circle's class in the enhancement's space: the image of the carried circle class under the
embedding, through the surface's `H1Iso`. This is the `x ∈ H₁(F;ℤ/2)` on which Taylor's `q(S¹)`
lives. -/
noncomputable def cls (γ : EmbeddedCircle C) : C.ι → ZMod 2 :=
  C.H1Iso (Homology.map (X := Circle1) (Y := TopCat.of C.F.M) γ.f 1 γ.fund)

/-- The circle's enhancement value `q(S¹) ∈ ℤ/4` — Taylor Lemma 1.2's surgery obstruction. -/
noncomputable def qVal (γ : EmbeddedCircle C) : ZMod 4 := C.Q.q γ.cls

/-- The circle's mod-2 self-pairing `x•x` — the normal-bundle/orientability shadow (`x•x = 0` for
an embedded circle with trivial normal bundle). -/
noncomputable def selfPair (γ : EmbeddedCircle C) : ZMod 2 := C.Q.B γ.cls γ.cls

/-- **`q(x) ≡ x•x (mod 2)`** for the embedded circle (DR §1: *"q(x) ≡ x•x mod 2 follows from the
axiom with y = x"*) — derived NOW from the enhancement axiom: `embed2 (x•x) = 2·q(x)`. In
particular an isotropic circle (`q = 0`) has trivial self-pairing. -/
theorem embed2_selfPair (γ : EmbeddedCircle C) : embed2 γ.selfPair = 2 * γ.qVal :=
  C.Q.embed2_B_self γ.cls

end EmbeddedCircle

/-! ## Disk-bounding circles die in the metabolizer (PROVED) -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k}

/-- **The circle bounds a disk in the bounding 3-manifold** (Taylor Lemma 1.3's hypothesis): the
embedded circle, pushed into `V` through the boundary identification, extends to a continuous map
of the closed 2-disk. -/
def EmbeddedCircle.BoundsDiskIn (γ : EmbeddedCircle C) (b : C.Bounding J) : Prop :=
  ∃ D : C(↑(Disk 2), b.V),
    D.comp diskIncl = (ContinuousMap.mk b.e b.he_smooth.continuous).comp γ.f

/-- **A disk-bounding circle dies in `V`** — its class lies in the Taylor/Klug metabolizer
`kernelL` (PROVED: functoriality of singular homology through the disk factorization + disk
acyclicity). This is the class-level content of "bounds a disk ⟹ null-homologous in `V`". -/
theorem EmbeddedCircle.cls_mem_kernelL_of_boundsDiskIn (γ : EmbeddedCircle C) (b : C.Bounding J)
    (hd : γ.BoundsDiskIn b) : γ.cls ∈ b.kernelL := by
  obtain ⟨D, hD⟩ := hd
  refine Submodule.mem_map.mpr
    ⟨Homology.map (X := Circle1) (Y := TopCat.of C.F.M) γ.f 1 γ.fund, ?_, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← Homology.map_comp, ← hD, Homology.map_comp,
    LinearMap.comp_apply,
    disk_homology_eq_zero 0 (Homology.map (X := Circle1) (Y := Disk 2) diskIncl 1 γ.fund),
    map_zero]

/-- **Statement freeze — Taylor `0802.0111` Lemma 1.3** (the base case of Theorem 1.1's
handle-decomposition proof; DR item A6): an embedded circle that bounds a disk in the bounding
Pin⁻ 3-manifold has vanishing enhancement value, `q(S¹) = 0`. The disk supplies the framing that
makes the induced spin structure on the circle bound. Falsifiable: the `ℝP²` generator circle
(`q = ±1`) can bound no disk in any bounding 3-manifold. -/
def PinCharSurface.Bounding.TaylorDiskVanishing (b : C.Bounding J) : Prop :=
  ∀ γ : EmbeddedCircle C, γ.BoundsDiskIn b → C.Q.q γ.cls = 0

/-- **The Lemma 1.3 freeze is subsumed by the Theorem 1.1 freeze at class level** (PROVED): a
disk-bounding circle's class dies in `V` (`cls_mem_kernelL_of_boundsDiskIn`), so kernel-vanishing
implies disk-vanishing. Geometrically Lemma 1.3 is an INPUT to Theorem 1.1's proof; at the
enhancement's class-level vocabulary the kernel statement is the master freeze, and this theorem
prevents the two freezes from double-counting geometric debt. -/
theorem PinCharSurface.Bounding.taylorDiskVanishing_of_taylorKernelVanishing (b : C.Bounding J)
    (h : b.TaylorKernelVanishing) : b.TaylorDiskVanishing :=
  fun γ hγ => h _ (γ.cls_mem_kernelL_of_boundsDiskIn b hγ)

/-! ## The surgered surface and the Lemma 1.2 descent freeze -/

/-- **A surgered enhanced-surface datum** for the embedded circle `γ`: the result of Taylor Lemma
1.2's surgery move, at the statement-layer vocabulary — a new characteristic-surface datum `C'`
(same ambient) whose enhancement is the isotropic reduction of `C.Q` at the circle class: the pair
complement of `(cls, z)` transported along `e` with matching enhancement values. The genuinely
geometric content (that `C'.F` is the trace-surgered surface and `C'.Q` its descended Pin⁻ shadow)
lives in the existence assertion `TaylorSurgeryDescends`; the enhancement tie here is the
checkable algebra. -/
structure SurgeredSurface (C : PinCharSurface X k) (γ : EmbeddedCircle C) where
  /-- The surgered characteristic surface (in the same ambient space). -/
  C' : PinCharSurface X k
  /-- The transverse partner of the circle class. -/
  z : C.ι → ZMod 2
  /-- Transversality: `B(cls, z) = 1`. -/
  pairing : C.Q.B γ.cls z = 1
  /-- The surgered surface's enhancement space IS the pair complement. -/
  e : (C'.ι → ZMod 2) ≃ₗ[ZMod 2] ↥(C.Q.pairComplement γ.cls z)
  /-- The enhancement descends: values agree through `e`. -/
  agree : ∀ u, C'.Q.q u = C.Q.q (e u)

/-- Repackage a surgered surface as the algebra-level reduction datum. -/
def SurgeredSurface.toSurgeryReduction {γ : EmbeddedCircle C} (S : SurgeredSurface C γ) :
    C.Q.SurgeryReduction γ.cls where
  z := S.z
  pairing := S.pairing
  κ := S.C'.ι
  R := S.C'.Q
  e := S.e
  agree := S.agree

/-- **The surgery induction step, DERIVED** (the consumer of Taylor Lemma 1.2 inside Theorem 1.1's
proof): surgering an isotropic circle leaves the Brown invariant unchanged, `β(F') = β(F)` — via
`brown_surgeryReduction`. -/
theorem brown_surgeredSurface {γ : EmbeddedCircle C} (S : SurgeredSurface C γ)
    (hq : C.Q.q γ.cls = 0) : C.Q.brown = S.C'.Q.brown :=
  C.Q.brown_surgeryReduction S.toSurgeryReduction hq

/-- **Statement freeze — Taylor `0802.0111` Lemma 1.2, the DESCENT direction** (DR item A5,
verbatim: *"Let S¹ ⊂ F be an embedded circle with trivial normal bundle… One can do surgery on
this embedding and extend the Pin⁻-structure to the trace of the surgery if and only if
q(S¹) = 0"*). Frozen here is the direction Theorem 1.1's induction consumes: every isotropic
(`q(S¹) = 0` — which already forces the trivial-normal-bundle shadow `S¹•S¹ = 0`,
`B_self_eq_zero_of_q_eq_zero`), homologically nontrivial embedded circle admits a surgered
enhanced surface — the Pin⁻ structure descends to the isotropic reduction. The CONVERSE direction
(extension over the trace ⟹ `q = 0`) is NOT frozen: stating it faithfully requires the trace
3-manifold `(F × I) ∪ (D² × D¹)` with a Pin⁻-structure-on-3-manifolds vocabulary (equivalently
the `Ω₁^{Spin} ≅ ℤ/2` framed-circle bounding invariant), which is not in tree; any
enhancement-level surrogate for "extends" is either false (the abstract reduction datum exists for
every transverse pair) or a tautology (if isotropy is baked into the datum). -/
def PinCharSurface.TaylorSurgeryDescends (C : PinCharSurface X k) : Prop :=
  ∀ γ : EmbeddedCircle C, C.Q.q γ.cls = 0 → γ.cls ≠ 0 → Nonempty (SurgeredSurface C γ)

/-! ## Changing the Pin⁻ structure at surface level (KT-LMS Lemma 3.7 vocabulary) -/

/-- **Changing the Pin⁻ structure on the surface** (KT-LMS Lemma 3.7 / DG Thm 3.12 torsor): the
same surface with the enhancement translated by the torsor action of `y ∈ H¹(F;ℤ/2)`, expressed
through its Poincaré dual `w = y ∩ [F]` (every functional is `B w ·` by nondegeneracy). Lemma
3.7's content — β changes by `2·q(w)` — is PROVEN in the algebra layer (`brown_shift`, GL/FK
sign: `β(shift) + 2·q(w) = β`); no freeze is needed. -/
def PinCharSurface.shiftEnh (C : PinCharSurface X k) (w : C.ι → ZMod 2) : PinCharSurface X k :=
  { C with Q := C.Q.shift w }

@[simp] lemma PinCharSurface.shiftEnh_Q (C : PinCharSurface X k) (w : C.ι → ZMod 2) :
    (C.shiftEnh w).Q = C.Q.shift w := rfl

/-- The surface-level structure change is an involution (the `H¹(F;ℤ/2)`-torsor is 2-torsion). -/
theorem PinCharSurface.shiftEnh_shiftEnh (C : PinCharSurface X k) (w : C.ι → ZMod 2) :
    (C.shiftEnh w).shiftEnh w = C := by
  show ({ C with Q := (C.Q.shift w).shift w } : PinCharSurface X k) = C
  rw [Z4Quadratic.shift_shift]

end SKEFTHawking.CharSurface
