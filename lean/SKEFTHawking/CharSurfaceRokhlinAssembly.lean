/-
# Phase 5q.H (E2 · the general-M assembly wire) — connecting the CharSurface tower's minimal
geometric leaves to `SmoothSpinManifold4.topo` (`2 ∣ σ/8`), the impact-11 Rokhlin node

The CharSurface tower (`CharSurfaceBounding` → `CharSurfaceMembrane` → `CharSurfaceNormalShadow` →
`CharSurfaceRealization`) EXACTLY decomposed the null-bordant Guillou–Marin leg `GMrelation 0 0 C.Q`
into a minimal set of honest geometric leaves, and `GMRokhlinDischarge` reduced
`SmoothSpinManifold4.topo` (a bare divisibility posit) to the [FK] congruence `GMrelation σ 0 Q` plus `β(Q) = 0`
(`sixteen_dvd_sig_of_gm_metabolic`). But the two halves were NOT wired: nothing composed the tower's
finest leaves with the `SmoothSpinManifold4`-level discharge, so `topo` never actually consumed the
decomposition. **This module is that wire.**

It provides the general-M assembly: given a smooth spin 4-manifold `M` presented with a bounded
characteristic-surface datum (`PinCharSurface` + `Bounding`), the single M-specific input — the
Freedman–Kirby / Guillou–Marin congruence `GMrelation M.sig 0 C.Q` (the [FK] node, irreducibly
geometric per `RokhlinArfNoGo`: the lattice cannot see it, E₈ has `σ/8 = 1`) — together with the
tower's finest kernel-pure-composable geometric leaves discharges `SmoothSpinManifold4.topo`:

* `sixteen_dvd_sig_of_gm_taylorKernel` — the base wire: [FK] + Taylor Thm 1.1 (`TaylorKernelVanishing`)
  + half-lives-half-dies (`KernelHalfLivesHalfDies`) ⟹ `16 ∣ σ`, through
  `GMRokhlin.sixteen_dvd_sig_of_gm_metabolic` on the metabolizer `kernelL`.
* `sixteen_dvd_sig_of_gm_kernelSplit` — through the finest KERNEL-level split
  (`KernelIsotropic ∧ KernelSpinVanishing` for the Taylor freeze, via
  `taylorKernelVanishing_iff_isotropic_spin`).
* `sixteen_dvd_sig_of_gm_membranes` / `sixteen_dvd_sig_of_gm_realization` — through the membrane and
  the finest SURFACE/3-manifold realization leaves (`KernelClassesEmbedded`, `KernelCirclesBound`,
  `MembraneSpinKill`, the Lagrangian package), so the whole non-[FK] residue is exactly the tower's
  pin-free classical-topology leaves plus the ONE pin⁻ atom.
* `topo_of_bounded_charSurface` / `rokhlin_of_bounded_charSurface` — the headline: the same leaves
  discharge `SmoothSpinManifold4.topo` (`2 ∣ latticeSig form / 8`) and hence `16 ∣ latticeSig form`,
  routing the concrete Rokhlin conclusion through the decomposed geometry rather than the bare
  `topo` posit. This is the general-M `hdvd`/N2 input the `SpinSigmaRoute` σ-route consumes: `hdvd`
  is exactly `∀ p, 16 ∣ latticeSig (form p)`, one `rokhlin_of_bounded_charSurface` per manifold.
* `gmrelation_stdQuadratic` — a genuinely-additive strengthening of `GM_rp4`: the standard genus-`n`
  characteristic surface (`n` copies of `RP²`, `stdQuadratic n`, `F·F = −2n`, `σ = 0`) satisfies
  Guillou–Marin, so the GM congruence is CONSISTENT across the whole `RP⁴`-generated `ℤ/16` tower —
  the algebraic robustness of `[FK]`-by-bordism-invariance on the generator.

**Honest residual (the smallest disclosed set).** `16 ∣ σ` for a general spin manifold is NOT closed
here — it CANNOT be, kernel-purely: it is the irreducibly-geometric [FK] congruence (E₈ obstruction,
`RokhlinArfNoGo`; the spin carriers give at most `8 ∣ σ`). The wire discharges everything AROUND the
[FK] node kernel-pure, leaving the disclosed residual EXACTLY {the [FK] congruence `GMrelation M.sig
0 C.Q`; the tower's geometric leaves — `KernelClassesEmbedded`, `KernelCirclesBound`,
`MembraneSpinKill`, `KernelLagrangianForB` (or, coarser, `TaylorKernelVanishing` +
`KernelHalfLivesHalfDies`)}. All are Mathlib-absent manifold-topology facts; none is an axiom.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceRealization

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.GMRokhlin
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularFunctoriality

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}
variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k}

namespace PinCharSurface.Bounding

/-! ## The base wire: `[FK]` congruence + the two frozen geometric statements ⟹ `16 ∣ σ` -/

/-- **The base wire** (PROVED): the Freedman–Kirby / Guillou–Marin congruence `GMrelation σ 0 C.Q`
for a manifold of signature `σ`, together with Taylor Theorem 1.1 (`TaylorKernelVanishing`: `q` kills
the metabolizer) and half-lives-half-dies (`KernelHalfLivesHalfDies`: the metabolizer is Lagrangian),
gives `16 ∣ σ`. The metabolic theorem forces `β(C.Q) = 0` from the two frozen Props, and the [FK]
congruence then reads `σ ≡ 2·β = 0 (mod 16)`. This is the missing composition of the CharSurface
tower's frozen bounding statements with the `SmoothSpinManifold4`-level Rokhlin discharge. -/
theorem sixteen_dvd_sig_of_gm_taylorKernel (b : C.Bounding J) {σ : ℤ}
    (hgm : GMrelation σ 0 C.Q) (hq : b.TaylorKernelVanishing) (hmax : b.KernelHalfLivesHalfDies) :
    (16 : ℤ) ∣ σ :=
  sixteen_dvd_sig_of_gm_metabolic hgm b.kernelL hq hmax

/-- **Through the finest kernel-level split** (PROVED): the Taylor freeze `TaylorKernelVanishing` is
supplied by its EXACT purely-algebraic split — the pin-free metabolizer isotropy `KernelIsotropic`
(E₈-visible intersection-form leg) and the class-level pin⁻ spin bit `KernelSpinVanishing` — via
`taylorKernelVanishing_iff_isotropic_spin`. So the non-[FK] residue is the two finest kernel Props
plus half-lives-half-dies. -/
theorem sixteen_dvd_sig_of_gm_kernelSplit (b : C.Bounding J) {σ : ℤ}
    (hgm : GMrelation σ 0 C.Q) (hiso : b.KernelIsotropic) (hspin : b.KernelSpinVanishing)
    (hmax : b.KernelHalfLivesHalfDies) :
    (16 : ℤ) ∣ σ :=
  sixteen_dvd_sig_of_gm_taylorKernel b hgm
    ((taylorKernelVanishing_iff_isotropic_spin b).mpr ⟨hiso, hspin⟩) hmax

/-! ## Through the membrane and the finest surface/3-manifold realization leaves -/

/-- **Through the membrane primitives** (PROVED): membrane realization (`MembraneRealizes`), the single
pin⁻ atom (`MembraneSpinKill`), and the pin-free isotropy (`KernelIsotropic`) supply the Taylor freeze
via `taylorKernelVanishing_of_membranes_isotropic`; with half-lives-half-dies and the [FK] congruence
this gives `16 ∣ σ`. -/
theorem sixteen_dvd_sig_of_gm_membranes (b : C.Bounding J) {σ : ℤ}
    (hgm : GMrelation σ 0 C.Q) (hreal : b.MembraneRealizes) (hspin : b.MembraneSpinKill)
    (hiso : b.KernelIsotropic) (hmax : b.KernelHalfLivesHalfDies) :
    (16 : ℤ) ∣ σ :=
  sixteen_dvd_sig_of_gm_taylorKernel b hgm
    (taylorKernelVanishing_of_membranes_isotropic b hreal hspin hiso) hmax

/-- **Through the finest realization leaves** (PROVED): the two finest realization ingredients
(`KernelClassesEmbedded` surface-only on the metabolizer, `KernelCirclesBound` 3-manifold-only), the
single pin⁻ atom (`MembraneSpinKill`), and the classical Lagrangian package (`KernelLagrangianForB` =
isotropy ∧ maximality) discharge `16 ∣ σ` off the [FK] congruence. Every non-[FK] hypothesis is either
pin-free classical topology or the ONE isolated pin⁻ ℤ/2 statement — the tower's most-decomposed
shape, now wired to the signature conclusion. -/
theorem sixteen_dvd_sig_of_gm_realization (b : C.Bounding J) {σ : ℤ}
    (hgm : GMrelation σ 0 C.Q) (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    (16 : ℤ) ∣ σ :=
  sixteen_dvd_sig_of_gm_membranes b hgm
    (membraneRealizes_of_kernelClassesEmbedded b h1 h2) hspin hlag.1 hlag.2

/-! ## The headline: discharging `SmoothSpinManifold4.topo` through the decomposed geometry -/

/-- **`SmoothSpinManifold4.topo` from a bounded characteristic surface** (PROVED): for a smooth spin
4-manifold `M`, the [FK] congruence `GMrelation M.sig 0 C.Q` for a bounded characteristic surface plus
the tower's finest geometric leaves discharge the tracked topological factor `2 ∣ σ/8`. This routes
`topo` (the impact-11 Rokhlin node `hyp:rokhlin_sigma_mod_16`) through the CharSurface tower's
decomposition rather than the bare posit — the general-M assembly point the tower was building
toward. The residual is EXACTLY the [FK] congruence (the M-specific, irreducibly-geometric input) plus
the tower's pin-free/pin⁻ leaves. -/
theorem topo_of_bounded_charSurface (M : SmoothSpinManifold4) (b : C.Bounding J)
    (hgm : GMrelation M.sig 0 C.Q) (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    (2 : ℤ) ∣ latticeSig M.form / 8 :=
  two_dvd_div_eight_of_sixteen_dvd (sixteen_dvd_sig_of_gm_realization b hgm h1 h2 hspin hlag)

/-- **`16 ∣ latticeSig form` from a bounded characteristic surface** (PROVED): the concrete Rokhlin
conclusion for `M`, obtained by feeding the discharged `topo` back through
`SmoothSpinManifold4.rokhlin`. This is the general-M `16 ∣ σ` in the exact shape the `SpinSigmaRoute`
σ-route consumes as its `hdvd` binder: `hdvd = ∀ p, 16 ∣ latticeSig (form p)`, one instance per
structured spin manifold presented with a bounded characteristic surface. -/
theorem rokhlin_of_bounded_charSurface (M : SmoothSpinManifold4) (b : C.Bounding J)
    (hgm : GMrelation M.sig 0 C.Q) (h1 : b.KernelClassesEmbedded) (h2 : b.KernelCirclesBound)
    (hspin : b.MembraneSpinKill) (hlag : b.KernelLagrangianForB) :
    (16 : ℤ) ∣ latticeSig M.form :=
  sixteen_dvd_sig_of_gm_realization b hgm h1 h2 hspin hlag

end PinCharSurface.Bounding

/-! ## GM-consistency across the `RP⁴`-generated tower (a genuinely-additive strengthening of `GM_rp4`) -/

/-- **The standard genus-`n` characteristic surface satisfies Guillou–Marin** (PROVED): `n` copies of
`RP²` (`stdQuadratic n`, self-intersection `F·F = −2n`, ambient signature `σ = 0`) satisfy
`GMrelation 0 (−2n) (stdQuadratic n)`. Generalizes `GM_rp4` (the `n = 1` case) to the whole tower, so
the GM congruence is CONSISTENT across the `RP⁴`-generated `ℤ/16` cyclic structure — the algebraic
robustness core of `[FK]`-by-bordism-invariance on the generator. The content is the non-trivial
matching `(2n : ZMod 16) = 2·(n mod 8)` (the `−2n` self-intersection tracking the `β = n mod 8` Brown
value), witnessing that the `16`-periodicity of the GM residue is exactly the `8`-periodicity of the
Brown invariant doubled. -/
theorem gmrelation_stdQuadratic (n : ℕ) : GMrelation 0 (-2 * (n : ℤ)) (stdQuadratic n) := by
  show ((0 - (-2 * (n : ℤ)) : ℤ) : ZMod 16) = doubleBrown (stdQuadratic n)
  rw [doubleBrown_stdQuadratic, ZMod.val_natCast]
  have key : ((n : ℕ) : ZMod 16) = ((n % 8 : ℕ) : ZMod 16) + 8 * ((n / 8 : ℕ) : ZMod 16) := by
    conv_lhs => rw [← Nat.div_add_mod n 8]
    push_cast
    ring
  have h16 : (16 : ZMod 16) = 0 := by decide
  push_cast
  rw [key]
  ring_nf
  rw [show (16 : ZMod 16) = 0 from h16]
  ring

end SKEFTHawking.CharSurface
