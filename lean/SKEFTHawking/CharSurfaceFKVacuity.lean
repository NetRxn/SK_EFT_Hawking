/-
# Phase 5q.H (E2) — the general-σ `[FK]`/Guillou–Marin **statement layer**: what it actually costs

The atlas keystone `hyp:rokhlin_sigma_mod_16` (`SpinPresentationRow.hdvd : ∀ x, 16 ∣ R.sig x`) is
gated on ONE input: the Freedman–Kirby / Guillou–Marin congruence `GMrelation σ (F·F) Q` **at
general `σ`**. `CharSurfaceRokhlinAssembly` wires that input to `16 ∣ σ`
(`sixteen_dvd_sig_of_gm_realization`, `rokhlin_of_bounded_charSurface`) modulo the CharSurface
tower's geometric leaves. The obvious next brick is "supply `hgm` at general `σ`". **This module
determines, kernel-purely, what such a supplier can and cannot be.** Three findings, each a
theorem, not a note:

## §1 — the wire's `hgm` hypothesis is *equivalent to its own conclusion* (not a reduction)

`sixteen_dvd_sig_of_gm_realization` reads `GMrelation σ 0 C.Q → … → 16 ∣ σ`. But its own leaves
already force `β(C.Q) = 0` (`PinCharSurface.Bounding.brown_eq_zero`, via the metabolic theorem), and
its `F·F` slot is hard-coded to `0`. With `β = 0` and `F·F = 0` the congruence `σ − 0 ≡ 2·0 (16)`
**is** `16 ∣ σ`. `gm_realization_hypothesis_iff_conclusion` proves the biconditional. So the wire is
a restatement of Rokhlin at the same strength, not a discharge of it — and this is **independent of
whether the characteristic surface is empty**: emptiness was never what made it circular; `F·F = 0`
together with the metabolic leaves is.

## §2 — nonemptiness does NOT restore content: a zero-geometry supplier exists

`exists_pos_stdQuadratic_gmrelation`: for **every** `σ, F·F` with `σ − F·F` even (which spin forces —
`8 ∣ σ` is already a theorem and `F·F = c·c` is even on an even form) there is a **nonempty**-index
standard enhancement `stdQuadratic n`, `n > 0`, satisfying `GMrelation σ (F·F) (stdQuadratic n)`,
built with zero geometric input. So an `∃`-shaped general-σ statement layer over the substrate's
free `Q` is satisfiable without any geometry.

## §3 — the polar form does not determine the GM residue (the free-enhancement obstruction)

`exists_same_polar_form_incompatible_gm`: `stdQuadratic 1` and `(stdQuadratic 1).shift 1` are two
`Z4Quadratic (Fin 1)` with **identical** polar forms `B` (`shift_B`) and different Brown invariants
(`1` vs `7`, `brown_shift_rp2`); no `(σ, F·F)` satisfies the GM congruence for both. Since the
substrate's `PinCharSurface` ties only `B`-level data to the surface (`H1Iso` pins the *space*
`H₁(F;ℤ/2)`, and `Z4Quadratic.B` its mod-2 intersection form), **the enhancement `Q` is a free field
and its Brown invariant is not a function of anything the substrate records.** Consequently a
`∀`-shaped (universal) general-σ statement layer over the substrate as it stands is *false*, not
merely vacuous — `charSurfaceFK_universal_over_free_enhancement_false` exhibits the refutation. The
missing substrate is named: `Q` must be **produced from the surface's pin⁻ normal data**, not carried
as a field. That is the `H¹(F;ℤ/2)`-torsor of pin⁻ structures, made kernel-explicit here.

## §4 — the Kervaire–Milnor "sphere" bridge is the SAME degenerate Prop, not a lighter route

`Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md` flags KM (F-K Thm 3.3.2)
as "the cleanest single Lean target": `x` dual to `w₂` represented by an embedded 2-**sphere** ⟹
`x·x ≡ σ (16)`, with `H₁(S²) = 0 ⟹ Arf = 0` sidestepping the `q_F` machinery. Kernel-checked verdict:
at a spin ambient (`x = 0`, so `x·x = 0`) the sphere hypothesis gives `H₁(F;ℤ/2) = 0`, hence
`β = 0` (`brown_eq_zero_of_isEmpty`, proved here from the metabolic theorem at `L = ⊤`), hence the
congruence **is** `16 ∣ σ` (`km_sphere_case_iff_sixteen_dvd`) — the *same* biconditional as §1. KM's
sphere case is a different narration of the identical degenerate Prop; it relocates no geometry. (It
is also, historically, a *corollary* of Rokhlin rather than a route to it.)

Nothing here is a walk-back: no existing statement is narrowed, and every theorem below is new
content. The constructive companion is `CharSurfaceFKPresentation.lean`, which lands the missing
`SpinSigmaPresentation → SmoothSpinManifold4` bridge and the generating-set reduction of the
keystone.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceRokhlinAssembly
import SKEFTHawking.BrownSurgeryReduction

namespace SKEFTHawking.CharSurfaceFK

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.GMRokhlin
open SKEFTHawking.CharSurface

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The converse of the null-GM discharge — and the circularity it exposes -/

/-- **The converse of `sixteen_dvd_sig_of_gm_null`** (new): if `16 ∣ σ` and the characteristic
surface's Brown invariant vanishes, then the Guillou–Marin congruence `GMrelation σ 0 Q` *holds*.
Together with the forward direction this makes the congruence, at `F·F = 0` and `β = 0`, literally
the divisibility statement it was supposed to imply. -/
theorem gmrelation_null_of_sixteen_dvd {σ : ℤ} {Q : Z4Quadratic ι}
    (hσ : (16 : ℤ) ∣ σ) (hQ : Q.brown = 0) : GMrelation σ 0 Q := by
  have hz : (σ : ZMod 16) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd σ 16).mpr hσ
  show ((σ - 0 : ℤ) : ZMod 16) = doubleBrown Q
  rw [doubleBrown, hQ]
  push_cast
  rw [hz]
  simp

/-- **The circularity core** (new): at a null self-intersection with vanishing Brown invariant the
Guillou–Marin congruence is *equivalent* to `16 ∣ σ`. Any assembly whose hypotheses force
`β = 0` and whose `F·F` slot is `0` therefore consumes a hypothesis of exactly the strength of its
conclusion. -/
theorem gmrelation_null_iff_sixteen_dvd {σ : ℤ} {Q : Z4Quadratic ι} (hQ : Q.brown = 0) :
    GMrelation σ 0 Q ↔ (16 : ℤ) ∣ σ :=
  ⟨fun h => sixteen_dvd_sig_of_gm_null h rfl hQ, fun h => gmrelation_null_of_sixteen_dvd h hQ⟩

section Assembly

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}
variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k}

/-- **The CharSurface bounding assembly's `[FK]` hypothesis is equivalent to its conclusion**
(new; the `←` direction is the content). `sixteen_dvd_sig_of_gm_taylorKernel` reads
`GMrelation σ 0 C.Q → TaylorKernelVanishing → KernelHalfLivesHalfDies → 16 ∣ σ`; but those two
leaves already prove `β(C.Q) = 0` (`Bounding.brown_eq_zero`), so the `[FK]` hypothesis is
*recoverable from the conclusion*. The wire regrades Rokhlin; it does not reduce it. -/
theorem gm_hypothesis_iff_conclusion (b : C.Bounding J) {σ : ℤ}
    (hq : b.TaylorKernelVanishing) (hmax : b.KernelHalfLivesHalfDies) :
    GMrelation σ 0 C.Q ↔ (16 : ℤ) ∣ σ :=
  gmrelation_null_iff_sixteen_dvd (b.brown_eq_zero hq hmax)

/-- **The same equivalence at the tower's finest leaves** (new): the exact hypothesis set of
`sixteen_dvd_sig_of_gm_realization` / `topo_of_bounded_charSurface` /
`rokhlin_of_bounded_charSurface` — `KernelClassesEmbedded`, `KernelCirclesBound`, `MembraneSpinKill`,
`KernelLagrangianForB` — already makes `GMrelation σ 0 C.Q` and `16 ∣ σ` interderivable. So the
"disclosed residual = {the [FK] congruence} ∪ {the tower's leaves}" of `CharSurfaceRokhlinAssembly`
is, at the `[FK]` slot, the keystone itself: supplying `hgm` at general `σ` on THIS shape is
supplying Rokhlin. A genuine supplier must break `F·F = 0` or the metabolic `β = 0`. -/
theorem gm_realization_hypothesis_iff_conclusion (b : C.Bounding J) {σ : ℤ}
    (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    GMrelation σ 0 C.Q ↔ (16 : ℤ) ∣ σ :=
  gm_hypothesis_iff_conclusion b
    (b.taylorKernelVanishing_of_membranes_isotropic
      (b.membraneRealizes_of_kernelClassesEmbedded h1 h2) hspin hlag.1) hlag.2

end Assembly

/-! ## §2. Nonemptiness does not restore content — a zero-geometry supplier -/

/-- **Every even GM residue is realized by a nonempty standard enhancement** (new): for any `σ, F`
with `σ − F` even there is `n > 0` with `GMrelation σ F (stdQuadratic n)`. The witness is built from
`brown_stdQuadratic` alone — **no geometric input whatsoever** — and its index type `Fin n` is
nonempty, so requiring the characteristic surface to be nonempty does not make an `∃`-shaped
general-`σ` `[FK]` statement layer carry content. (Spin always satisfies the hypothesis: `8 ∣ σ` is a
theorem, and `F·F` is even on an even form.) -/
theorem exists_pos_stdQuadratic_gmrelation {σ F : ℤ} (h : (2 : ℤ) ∣ (σ - F)) :
    ∃ n : ℕ, 0 < n ∧ GMrelation σ F (stdQuadratic n) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨(t % 8).toNat + 8, by omega, ?_⟩
  have hm : ((t % 8).toNat : ℤ) = t % 8 := Int.toNat_of_nonneg (Int.emod_nonneg t (by norm_num))
  have hlt : (t % 8).toNat < 8 := by omega
  have hbr : (stdQuadratic ((t % 8).toNat + 8)).brown = (((t % 8).toNat : ℕ) : ZMod 8) := by
    rw [brown_stdQuadratic]
    push_cast
    rw [show (8 : ZMod 8) = 0 from by decide, add_zero]
  have hval : ((((t % 8).toNat : ℕ) : ZMod 8)).val = (t % 8).toNat :=
    ZMod.val_natCast_of_lt hlt
  show ((σ - F : ℤ) : ZMod 16) = doubleBrown (stdQuadratic ((t % 8).toNat + 8))
  rw [doubleBrown, hbr, hval, ht]
  have hsplit : t = (t % 8) + 8 * (t / 8) := by omega
  have : (2 * t : ℤ) = 2 * ((t % 8).toNat : ℤ) + 16 * (t / 8) := by rw [hm]; omega
  rw [this]
  push_cast
  rw [show (16 : ZMod 16) = 0 from by decide]
  ring

/-! ## §3. The free-enhancement obstruction: the polar form does not determine the GM residue -/

/-- **Two enhancements of the SAME polar form with incompatible GM residues** (new). `stdQuadratic 1`
(`β = 1`) and its torsor translate `(stdQuadratic 1).shift 1` (`β = 7`, `brown_shift_rp2`) share the
polar form `B` verbatim (`shift_B` is `rfl`), so every piece of data the substrate's `PinCharSurface`
records about the characteristic surface — the space `H₁(F;ℤ/2)` via `H1Iso`, and its mod-2
intersection form via `Z4Quadratic.B` — is identical for the two, while their Guillou–Marin residues
`2·β` differ. No `(σ, F·F)` satisfies the congruence for both. -/
theorem exists_same_polar_form_incompatible_gm :
    ∃ Q₁ Q₂ : Z4Quadratic (Fin 1), Q₁.B = Q₂.B ∧
      ∀ σ F : ℤ, ¬ (GMrelation σ F Q₁ ∧ GMrelation σ F Q₂) := by
  refine ⟨stdQuadratic 1, (stdQuadratic 1).shift 1, rfl, ?_⟩
  rintro σ F ⟨h₁, h₂⟩
  have hne : doubleBrown (stdQuadratic 1) ≠ doubleBrown ((stdQuadratic 1).shift 1) := by
    rw [doubleBrown, doubleBrown, brown_stdQuadratic, brown_shift_rp2]
    decide
  exact hne (h₁ ▸ h₂ ▸ rfl)

/-- **The universal general-`σ` `[FK]` statement over a free enhancement is FALSE** (new — the
refutation, not a vacuity). Reading the `[FK]` congruence as the universal statement "*every*
`(σ, F·F, Q)` compatible with the substrate's surface data satisfies Guillou–Marin" is refuted by the
torsor pair of `exists_same_polar_form_incompatible_gm`: two enhancements indistinguishable to the
substrate cannot both satisfy it. So the general-`σ` statement layer cannot be typed over
`Z4Quadratic` + `H1Iso` at all — it needs `Q` *computed* from the surface's pin⁻ normal data (the
`H¹(F;ℤ/2)`-torsor of pin⁻ structures, Mathlib-absent), which is precisely the blueprint's `[G2]`/`[Q1]`
smooth content. -/
theorem charSurfaceFK_universal_over_free_enhancement_false :
    ¬ ∀ (σ F : ℤ) (Q₁ Q₂ : Z4Quadratic (Fin 1)), Q₁.B = Q₂.B →
        GMrelation σ F Q₁ → GMrelation σ F Q₂ := by
  intro huniv
  -- `stdQuadratic 1` satisfies GM at `σ = 0`, `F = -2` (`GM_rp4`); transport it along `shift_B`.
  have hne : doubleBrown (stdQuadratic 1) ≠ doubleBrown ((stdQuadratic 1).shift 1) := by
    rw [doubleBrown, doubleBrown, brown_stdQuadratic, brown_shift_rp2]
    decide
  have h₂ : GMrelation (0 : ℤ) (-2) ((stdQuadratic 1).shift 1) :=
    huniv 0 (-2) (stdQuadratic 1) ((stdQuadratic 1).shift 1) rfl GM_rp4
  exact hne (GM_rp4 ▸ h₂ ▸ rfl)

/-! ## §4. The Kervaire–Milnor sphere case is the same degenerate Prop -/

/-- **`β = 0` for an enhancement on a vanishing `H₁`** (new): when the characteristic surface has
`H₁(F;ℤ/2) = 0` — the KM hypothesis "represented by an embedded 2-sphere" — its Brown invariant
vanishes. Proved from the metabolic theorem at the maximal (trivial) Lagrangian `L = ⊤`, so no new
input. -/
theorem brown_eq_zero_of_isEmpty [IsEmpty ι] (Q : Z4Quadratic ι) : Q.brown = 0 := by
  classical
  have hsub : Subsingleton (ι → ZMod 2) := inferInstance
  haveI : Fintype (⊤ : Submodule (ZMod 2) (ι → ZMod 2)) := Fintype.ofFinite _
  refine Q.brown_eq_zero_of_metabolic ⊤ (fun l _ => ?_) (fun v _ => Submodule.mem_top)
  rw [Subsingleton.elim l 0]
  exact Q.q_zero

/-- **The KM sphere case IS `16 ∣ σ`** (new — the verdict on the blueprint's "cleanest single Lean
target"). At a spin ambient the Kervaire–Milnor hypothesis gives `x = 0`, hence `x·x = 0`, and the
representing 2-sphere gives `H₁(F;ℤ/2) = 0`, hence `β = 0`; the Guillou–Marin congruence then
*equals* `16 ∣ σ`. So the KM specialization is the identical degenerate instance as `[FK]`-at-`∅`
(`gm_hypothesis_iff_conclusion`), differently narrated: it sidesteps the `q_F` machinery precisely by
throwing away the only slot that could carry the geometry. It is not a lighter route to Rokhlin. -/
theorem km_sphere_case_iff_sixteen_dvd [IsEmpty ι] (Q : Z4Quadratic ι) (σ : ℤ) :
    GMrelation σ 0 Q ↔ (16 : ℤ) ∣ σ :=
  gmrelation_null_iff_sixteen_dvd (brown_eq_zero_of_isEmpty Q)

end SKEFTHawking.CharSurfaceFK
