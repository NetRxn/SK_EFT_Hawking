/-
# Phase 5q.H (E2 · normal-shadow layer) — the pin-FREE metabolizer isotropy, and the ABSORPTION of
Taylor Theorem 1.1's normal-shadow node into the classical Poincaré–Lefschetz Lagrangian package

`CharSurfaceMembrane.lean` decomposed the frozen `TaylorKernelVanishing` (Taylor `0802.0111`
Thm 1.1) into five geometric residue nodes: two realization nodes (`ClassesEmbedded`,
`KernelCirclesBound` → `MembraneRealizes`), the single pin⁻ atom `MembraneSpinKill`, the pin-free
normal shadow `MembraneTrivializesNormal`, and — for the composed `gmrelation_null` — the
Poincaré–Lefschetz maximality `KernelHalfLivesHalfDies`.

This module PINS the normal shadow to its classical home. It is the trivial-normal-bundle content
`γ • γ = 0` for a membrane-bounding circle — but at class level `γ • γ` is `B(cls, cls)`, the
DIAGONAL of the mod-2 intersection form, so the whole node is exactly the **isotropy** half of the
metabolizer (`ker(H₁(F) → H₁(V))` is a Lagrangian for `B`). We make that precise:

* `KernelIsotropic` — the pin-FREE diagonal isotropy `∀ l ∈ kernelL, B l l = 0` (only the
  intersection form `B`, no pin⁻ quadratic value `q`). This is the isotropy leg `L ⊆ L^⊥` of the
  metabolizer, the classical Poincaré–Lefschetz shadow, distinct from Thm 1.1.
* `kernelIsotropic_of_taylorKernelVanishing` — PROVED (no inflation): `q = 0` on `kernelL` forces
  the diagonal `B = 0` by polarization (`B_self_eq_zero_of_q_eq_zero`). The isotropy is no larger
  a debt than the master freeze it descends from.
* `membraneTrivializesNormal_of_kernelIsotropic` — PROVED: a membrane-bounding circle's class is in
  `kernelL` (`cls_mem_kernelL_of_boundsMembraneIn`), so isotropy kills its self-pairing. The
  normal-shadow node is IMPLIED by the pin-free kernel isotropy.
* `kernelIsotropic_of_membraneTrivializesNormal` and `kernelIsotropic_iff_membraneTrivializesNormal`
  — PROVED: under realization (`MembraneRealizes`, which the composed end assumes anyway) the two
  are EXACTLY equivalent, so the replacement of `MembraneTrivializesNormal` by `KernelIsotropic` is
  an equal-content substitution, not a re-freeze.
* `KernelLagrangianForB` = `KernelIsotropic ∧ KernelHalfLivesHalfDies` — the metabolizer is a
  Lagrangian for `B` (isotropy `L ⊆ L^⊥` + maximality `L^⊥ ⊆ L`, the two genuine opposite
  inclusions). This UNIFIES the normal shadow and half-lives-half-dies into ONE classical
  intersection-form statement, `kernelLagrangianForB_of_taylorKernelVanishing` witnessing no
  inflation over the pre-existing frozen pair.
* `taylorKernelVanishing_of_membranes_isotropic`, `gmrelation_null_of_membranes_isotropic`,
  `gmrelation_null_of_classesEmbedded_isotropic` — the re-composed ends with the normal shadow
  ABSORBED into the Lagrangian package, so the entire non-realization geometric residue collapses to
  {`MembraneSpinKill` (the one pin⁻ atom), `KernelLagrangianForB` (one classical Lagrangian fact)}.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceMembrane

namespace SKEFTHawking.Brown.Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- **Per-class algebraic split of `q = 0`** (PROVED): the pin⁻ quadratic value vanishes at a class
IFF its mod-2 self-pairing (`B x x`, the pin-free normal shadow) AND its halving spin reduction
(`toZ2 x`, the pin⁻ spin bit) both vanish. Pure `Z4Quadratic` algebra — no geometry, no realization.
Forward: `q x = 0` forces `B x x = 0` (`B_self_eq_zero_of_q_eq_zero`), whence `embed2 (toZ2 x) = q x`
(`embed2_toZ2_of_B_self_eq_zero`) kills `toZ2 x`. Backward: `embed2 (toZ2 x) = q x` with `toZ2 x = 0`
gives `q x = 0`. -/
theorem q_eq_zero_iff (x : ι → ZMod 2) :
    Q.q x = 0 ↔ Q.B x x = 0 ∧ Q.toZ2 x = 0 := by
  constructor
  · intro h
    have hB : Q.B x x = 0 := Q.B_self_eq_zero_of_q_eq_zero h
    refine ⟨hB, ?_⟩
    have he := Q.embed2_toZ2_of_B_self_eq_zero hB
    rw [h] at he
    exact embed2_injective (by rw [he]; decide)
  · rintro ⟨hB, hz⟩
    have he := Q.embed2_toZ2_of_B_self_eq_zero hB
    rw [hz, show embed2 (0 : ZMod 2) = 0 from by decide] at he
    exact he.symm

end SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}
variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k}

namespace PinCharSurface.Bounding

/-! ## The pin-free metabolizer isotropy (the normal shadow's classical home) -/

/-- **The pin-FREE metabolizer isotropy** — the isotropy leg `L ⊆ L^⊥` of the Taylor/Klug
metabolizer: every class dying in the bounding 3-manifold has vanishing mod-2 self-intersection.
Only the intersection form `B` appears — no pin⁻ quadratic value `q`, no membrane geometry. This is
the classical Poincaré–Lefschetz shadow (two classes bounding in `V` have zero intersection in
`F = ∂V`), the complement of `KernelHalfLivesHalfDies`'s maximality leg `L^⊥ ⊆ L`. Falsifiable: a
kernel class with `B l l = 1` refutes it. -/
def KernelIsotropic (b : C.Bounding J) : Prop :=
  ∀ l ∈ b.kernelL, C.Q.B l l = 0

/-- **No inflation over the master freeze** (PROVED): `TaylorKernelVanishing` (`q = 0` on `kernelL`)
forces the diagonal isotropy by polarization — `B_self_eq_zero_of_q_eq_zero` at each kernel class.
So the isotropy leg is a strictly-no-larger debt than Taylor Theorem 1.1 itself. -/
theorem kernelIsotropic_of_taylorKernelVanishing (b : C.Bounding J)
    (h : b.TaylorKernelVanishing) : b.KernelIsotropic :=
  fun l hl => C.Q.B_self_eq_zero_of_q_eq_zero (h l hl)

/-- **The normal shadow is implied by the pin-free isotropy** (PROVED): a membrane-bounding circle's
class lies in `kernelL` (`cls_mem_kernelL_of_boundsMembraneIn`), on which the diagonal intersection
form vanishes — and `γ.selfPair` is by definition `B(γ.cls, γ.cls)`. So `MembraneTrivializesNormal`
carries no content beyond the pin-free `KernelIsotropic`. -/
theorem membraneTrivializesNormal_of_kernelIsotropic (b : C.Bounding J)
    (h : b.KernelIsotropic) : b.MembraneTrivializesNormal :=
  fun γ hm => h γ.cls (γ.cls_mem_kernelL_of_boundsMembraneIn b hm)

/-- **The reverse under realization** (PROVED): given membrane realization of the nonzero kernel
classes (`MembraneRealizes` — the hypothesis the composed end assumes anyway), the normal shadow
recovers the full kernel isotropy. The zero class is handled by `B_zero_left`; a nonzero kernel
class is realized by a membrane-bounding circle on which `MembraneTrivializesNormal` kills the
self-pairing. -/
theorem kernelIsotropic_of_membraneTrivializesNormal (b : C.Bounding J)
    (hnorm : b.MembraneTrivializesNormal) (hreal : b.MembraneRealizes) : b.KernelIsotropic := by
  intro l hl
  by_cases h0 : l = 0
  · subst h0
    exact C.Q.B_zero_left 0
  · obtain ⟨γ, hcls, hm⟩ := hreal l hl h0
    rw [← hcls]
    exact hnorm γ hm

/-- **Exact accounting** (PROVED, both ways): under realization the pin-free kernel isotropy and the
membrane normal shadow are EQUIVALENT — the substitution of `KernelIsotropic` for
`MembraneTrivializesNormal` in the decomposition is content-preserving, not a re-freeze. -/
theorem kernelIsotropic_iff_membraneTrivializesNormal (b : C.Bounding J)
    (hreal : b.MembraneRealizes) : b.KernelIsotropic ↔ b.MembraneTrivializesNormal :=
  ⟨membraneTrivializesNormal_of_kernelIsotropic b,
    fun h => kernelIsotropic_of_membraneTrivializesNormal b h hreal⟩

/-! ## The Lagrangian package: normal shadow + maximality unified -/

/-- **The metabolizer is a Lagrangian for the mod-2 intersection form**: isotropy (`L ⊆ L^⊥`,
`KernelIsotropic`) together with maximality (`L^⊥ ⊆ L`, `KernelHalfLivesHalfDies`) — the two genuine
opposite inclusions of "`kernelL` is a Lagrangian for `B`," the single classical Poincaré–Lefschetz
statement for the bounding pair `(V, ∂V = F)`. Absorbs the pin-free normal shadow and the
half-lives-half-dies maximality into ONE intersection-form fact. -/
def KernelLagrangianForB (b : C.Bounding J) : Prop :=
  b.KernelIsotropic ∧ b.KernelHalfLivesHalfDies

/-- **No inflation of the Lagrangian package** (PROVED): the pre-existing frozen pair
`TaylorKernelVanishing ∧ KernelHalfLivesHalfDies` already yields the Lagrangian package (isotropy
descends from `q`-vanishing by polarization). The unified package is no larger a debt. -/
theorem kernelLagrangianForB_of_taylorKernelVanishing (b : C.Bounding J)
    (hq : b.TaylorKernelVanishing) (hmax : b.KernelHalfLivesHalfDies) : b.KernelLagrangianForB :=
  ⟨kernelIsotropic_of_taylorKernelVanishing b hq, hmax⟩

/-! ## The purely-algebraic kernel-level split (pin-free isotropy ∧ pin⁻ spin bit) -/

/-- **The pin⁻ spin bit on the metabolizer**: the halving spin reduction `toZ2` vanishes on every
class dying in the bounding 3-manifold. The class-level, framing-free form of the `Ω₁^{Spin} ≅ ℤ/2`
atom — the irreducible pin⁻ content that the mod-2 intersection form (E₈-visible) cannot see. -/
def KernelSpinVanishing (b : C.Bounding J) : Prop :=
  ∀ l ∈ b.kernelL, C.Q.toZ2 l = 0

/-- **Purely-algebraic split of Taylor Theorem 1.1's frozen target** (PROVED, both ways): the
enhancement vanishes on the metabolizer IFF the pin-free isotropy (`KernelIsotropic`, the
E₈-visible intersection-form leg) and the pin⁻ spin bit (`KernelSpinVanishing`) both hold. No
realization, no membrane, no surface embedding — the finest algebraic separation of the pin-free
and pin⁻ halves of the debt, via the per-class `q_eq_zero_iff`. This is the class-level mirror of
`taylorMembraneVanishing_iff` with the geometric quantifiers stripped, and directly witnesses the
negative-frontier split "intersection form (E₈-visible) + irreducible pin⁻ spin bit." -/
theorem taylorKernelVanishing_iff_isotropic_spin (b : C.Bounding J) :
    b.TaylorKernelVanishing ↔ b.KernelIsotropic ∧ b.KernelSpinVanishing := by
  constructor
  · intro h
    exact ⟨fun l hl => ((C.Q.q_eq_zero_iff l).mp (h l hl)).1,
      fun l hl => ((C.Q.q_eq_zero_iff l).mp (h l hl)).2⟩
  · rintro ⟨hiso, hspin⟩ l hl
    exact (C.Q.q_eq_zero_iff l).mpr ⟨hiso l hl, hspin l hl⟩

/-- **The kernel spin bit implies the membrane spin kill** (PROVED): a detection-coherent framed
circle bounding a membrane has `spinClass = toZ2 cls` (`spinClass_eq_toZ2_of_detects`) and its class
dies in `V` (`cls_mem_kernelL_of_boundsMembraneIn`), so the kernel spin bit kills it. No realization
needed — the class-level spin node is at least as strong as the geometric membrane spin atom. -/
theorem membraneSpinKill_of_kernelSpinVanishing (b : C.Bounding J)
    (h : b.KernelSpinVanishing) : b.MembraneSpinKill := by
  intro γ hdet hm
  rw [γ.spinClass_eq_toZ2_of_detects hdet]
  exact h γ.cls (γ.toEmbeddedCircle.cls_mem_kernelL_of_boundsMembraneIn b hm)

/-- **The reverse bridge — exact accounting for the spin bit** (PROVED): given membrane realization
and the pin-free isotropy (which the composed end assumes anyway), the geometric membrane spin atom
recovers the class-level kernel spin bit. A nonzero kernel class is realized by a membrane-bounding
circle whose canonical framing (`framed`, valid since isotropy gives the trivial normal shadow) is
detection-coherent (`framed_detects`); `MembraneSpinKill` kills its spin class, which is `toZ2 cls`
(`framed_spinClass`). The zero class is handled by `q_eq_zero_iff` at `q_zero`. Together with
`membraneSpinKill_of_kernelSpinVanishing` this makes the class-level and membrane-level spin nodes
EQUIVALENT under the assumed realization — the split is 1-1, not an inflation. -/
theorem kernelSpinVanishing_of_membraneSpinKill (b : C.Bounding J)
    (hspin : b.MembraneSpinKill) (hiso : b.KernelIsotropic) (hreal : b.MembraneRealizes) :
    b.KernelSpinVanishing := by
  intro l hl
  by_cases h0 : l = 0
  · subst h0
    exact ((C.Q.q_eq_zero_iff 0).mp C.Q.q_zero).2
  · obtain ⟨γ, hcls, hm⟩ := hreal l hl h0
    have hself : γ.selfPair = 0 := membraneTrivializesNormal_of_kernelIsotropic b hiso γ hm
    have hkill := hspin (γ.framed hself) (γ.framed_detects hself) hm
    rw [← hcls, ← γ.framed_spinClass hself]
    exact hkill

/-- **The cleanest composed end** (PROVED): the null Guillou–Marin residue follows from THREE
purely-kernel-level facts — the pin-free isotropy, the pin⁻ spin bit, and Poincaré–Lefschetz
maximality — with NO membrane, NO realization, NO surface-embedding machinery. The membrane and
realization layers are needed only to further reduce these kernel facts to per-circle geometric
witnesses; the GM conclusion itself rides purely on the metabolizer algebra. -/
theorem gmrelation_null_of_kernel_split (b : C.Bounding J)
    (hiso : b.KernelIsotropic) (hspin : b.KernelSpinVanishing)
    (hmax : b.KernelHalfLivesHalfDies) : GMrelation 0 0 C.Q :=
  b.gmrelation_null ((taylorKernelVanishing_iff_isotropic_spin b).mpr ⟨hiso, hspin⟩) hmax

/-! ## Re-composed ends with the normal shadow absorbed -/

/-- **The SHRINK with the pin-free isotropy** (PROVED): membrane realization, the single pin⁻ spin
atom, and the pin-free kernel isotropy imply Taylor Theorem 1.1's frozen target. The normal-shadow
node `MembraneTrivializesNormal` of `taylorMembraneVanishing_iff` is supplied by
`membraneTrivializesNormal_of_kernelIsotropic`, so only the classical intersection-form isotropy
appears. -/
theorem taylorKernelVanishing_of_membranes_isotropic (b : C.Bounding J)
    (hreal : b.MembraneRealizes) (hspin : b.MembraneSpinKill) (hiso : b.KernelIsotropic) :
    b.TaylorKernelVanishing :=
  taylorKernelVanishing_of_membranes b hreal
    ((taylorMembraneVanishing_iff b).mpr
      ⟨hspin, membraneTrivializesNormal_of_kernelIsotropic b hiso⟩)

/-- **The composed end through the Lagrangian package** (PROVED): membrane realization, the single
pin⁻ atom, and the classical Lagrangian package force the null Guillou–Marin residue. The entire
non-realization geometric residue is now {`MembraneSpinKill`, `KernelLagrangianForB`} — one pin⁻
atom and one classical intersection-form fact; the normal shadow is fully absorbed. -/
theorem gmrelation_null_of_membranes_isotropic (b : C.Bounding J)
    (hreal : b.MembraneRealizes) (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    GMrelation 0 0 C.Q :=
  b.gmrelation_null
    (taylorKernelVanishing_of_membranes_isotropic b hreal hspin hlag.1) hlag.2

/-- **The fully-decomposed composed end** (PROVED): the two finest realization ingredients
(`ClassesEmbedded` surface-only, `KernelCirclesBound` 3-manifold-only), the single pin⁻ atom
(`MembraneSpinKill`), and the classical Lagrangian package (`KernelLagrangianForB`) force the null
Guillou–Marin residue. Every hypothesis is either pin-free classical topology or the ONE isolated
pin⁻ ℤ/2 statement — Taylor Theorem 1.1's debt in its most-decomposed shape. -/
theorem gmrelation_null_of_classesEmbedded_isotropic (b : C.Bounding J)
    (h1 : C.ClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    GMrelation 0 0 C.Q :=
  gmrelation_null_of_membranes_isotropic b
    (membraneRealizes_of_classesEmbedded b h1 h2) hspin hlag

/-- **Brown-invariant form of the fully-decomposed end** (PROVED): the same hypotheses give
`β(F) = 0` for the bounded characteristic surface, through `brown_eq_zero`. -/
theorem brown_eq_zero_of_classesEmbedded_isotropic (b : C.Bounding J)
    (h1 : C.ClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    C.Q.brown = 0 :=
  b.brown_eq_zero
    (taylorKernelVanishing_of_membranes_isotropic b
      (membraneRealizes_of_classesEmbedded b h1 h2) hspin hlag.1) hlag.2

end PinCharSurface.Bounding

end SKEFTHawking.CharSurface
