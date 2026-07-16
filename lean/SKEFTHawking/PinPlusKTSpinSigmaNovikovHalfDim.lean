/-
# Phase 5q.H close-out — THE NOVIKOV HALF-DIM ATOM: `half` discharged to Lefschetz co-isotropy
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaNovikovOpener

namespace SKEFTHawking.PinPlusKTSpinSigmaNovikovHalfDim

open scoped Manifold
open QuadraticMap Module
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle
open SKEFTHawking.PinPlusKTSpinSigmaHbord
open SKEFTHawking.PinPlusKTSpinSigmaNovikovOpener

/-! ## §1. The core linear-algebra assembly — isotropy + co-isotropy + nondegeneracy ⟹ half-dim -/

theorem finrank_eq_two_mul_of_isotropic_coisotropic
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hND : B.Nondegenerate)
    (I : Submodule ℝ V)
    (hiso : I ≤ B.orthogonal I) (hco : B.orthogonal I ≤ I) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ I := by
  have hEq : B.orthogonal I = I := le_antisymm hco hiso
  have key := B.finrank_orthogonal hND I
  rw [hEq] at key
  have hle : Module.finrank ℝ I ≤ Module.finrank ℝ V := Submodule.finrank_le I
  omega

/-! ## §2. The bridge — matrix quadratic-form isotropy + nondegeneracy + polar co-isotropy ⟹ half-dim -/

theorem finrank_eq_half_of_isotropic_coisotropic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hnd : (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (I : Submodule ℝ (Fin n → ℝ))
    (hiso : ∀ x ∈ I, (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0)
    (hco : LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') I ≤ I) :
    n = 2 * Module.finrank ℝ I := by
  set Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' with hQ
  set B : LinearMap.BilinForm ℝ (Fin n → ℝ) := QuadraticMap.polarBilin Q with hB
  have hker : LinearMap.ker B = ⊥ := by
    rw [hB, ← QuadraticMap.radical_eq_ker_polarBilin]; exact hnd
  have hND : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr hker
  have hisoB : I ≤ B.orthogonal I := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    simp only [LinearMap.BilinForm.isOrtho_def, hB, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar]
    rw [hiso _ (I.add_mem hy hx), hiso _ hy, hiso _ hx]
    ring
  have hVdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hmain := finrank_eq_two_mul_of_isotropic_coisotropic B hND I hisoB hco
  rw [hVdim] at hmain
  exact hmain

/-! ## §3. The opener structure's `half` field, DISCHARGED to co-isotropy -/

/-- **`NovikovBoundaryRestriction.half` is FORCED by nondegeneracy + Lefschetz co-isotropy.** For a
boundary-restriction substrate `d` whose boundary matrix `Bd` has nondegenerate real form (`radical = ⊥`,
banked from even-unimodularity) and whose restriction image `im ι* = range d.rest2` is **co-isotropic**
(`im^⊥ ⊆ im`, the deep Poincaré–Lefschetz input `ker(H²(∂W)→H³(W,∂W)) ⊆ im(H²(W)→H²(∂W))` intertwined by
PD), the half-dimensionality `n = 2·dim(im ι*)` is a THEOREM — no longer a disclosed field. Isotropy
(`im ⊆ im^⊥`) is `d.isotropic` (banked from `func`/`bvanish`/`gram`, #172); nondegeneracy supplies the
orthogonal-complement dimension formula `dim im + dim im^⊥ = n`; co-isotropy closes `im = im^⊥`. So the
opener structure's single non-theorem field is reduced to exactly the co-isotropy residual. -/
theorem NovikovBoundaryRestriction.half_of_coisotropic {n : ℕ} {Bd : Matrix (Fin n) (Fin n) ℤ}
    (d : NovikovBoundaryRestriction Bd)
    (hnd : (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hco : LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
        (LinearMap.range d.rest2) ≤ LinearMap.range d.rest2) :
    n = 2 * Module.finrank ℝ (LinearMap.range d.rest2) :=
  finrank_eq_half_of_isotropic_coisotropic Bd hnd (LinearMap.range d.rest2)
    (fun _ hx => d.isotropic hx) hco

/-! ## §4. The residual co-isotropy atom — half-dim discharged, nondeg banked, only Lefschetz left -/

variable (prov : CharPairWProviderPerOp (𝓡 4) 0)

/-- **The residual co-isotropy atom.** For each data-bordant pair `p, q`, a subspace `L` of the boundary
block form `blockDiag (II M_p) (−(II M_q))` that is **isotropic** (`Q_∂ x = 0` on `L` — banked, classes
extending over `W`) AND **co-isotropic** (`L^⊥ ⊆ L` for the polar form — the deep Poincaré–Lefschetz "half
lives, half dies" input, `im ι* ⊇ (im ι*)^⊥`). This SHARPENS `NovikovLagrangianAtom`: its half-dimensional
conjunct `rank + rank = 2·dim L` is replaced by the co-isotropy input, from which the half-dimensionality
becomes a THEOREM (`novikovLagrangian_of_novikovCoIso`) once nondegeneracy is banked from the boundary
form's even-unimodularity. So the σ-descent's last geometric atom is reduced from "an isotropic
half-dimensional Lagrangian exists" to "an isotropic co-isotropic subspace exists" — the honest classical
Novikov split, with the dimension count discharged to linear algebra. Spin-side, `k₀`-free. -/
def NovikovCoIsoAtom (a : SpinSigmaAtoms prov) : Prop :=
  ∀ p q : StrMfd (spinEmptyData prov), IsDataBordant (spinEmptyData prov) p q →
    ∃ L : Submodule ℝ (Fin ((a.B p).rank + (a.B q).rank) → ℝ),
      (∀ x ∈ L, ((blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q))).map
          (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0) ∧
      LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin ((blockDiag (interMatrix (a.fc p) (a.B p))
          (-interMatrix (a.fc q) (a.B q))).map (Int.cast : ℤ → ℝ)).toQuadraticMap') L ≤ L

variable {prov}

/-- **`NovikovLagrangianAtom` DISCHARGED from the residual co-isotropy atom.** Given, per data-bordant pair,
an isotropic co-isotropic subspace `L` (`NovikovCoIsoAtom`), the full Novikov-Lagrangian disclosure follows:
the boundary block form is even-unimodular (from `a.wu`/`a.pd` via `isEvenUnimodular_of_intPD` +
`isEvenUnimodular_neg` + `isEvenUnimodular_blockDiag`), hence nondegenerate; then
`finrank_eq_half_of_isotropic_coisotropic` turns isotropy + co-isotropy into the half-dimensionality
`rank + rank = 2·dim L`. So `NovikovLagrangianAtom` collapses onto the co-isotropy atom — the half-dim
conjunct now a theorem, only the Lefschetz co-isotropy carried. -/
theorem novikovLagrangian_of_novikovCoIso {a : SpinSigmaAtoms prov}
    (h : NovikovCoIsoAtom prov a) : NovikovLagrangianAtom prov a := by
  intro p q hb
  obtain ⟨L, hiso, hco⟩ := h p q hb
  refine ⟨L, ?_, hiso⟩
  have heuP := isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p)
  have heuQ := isEvenUnimodular_of_intPD (a.fc q) (a.B q) (a.wu q) (a.pd q)
  have heuNegQ := isEvenUnimodular_neg _ heuQ
  have hbd_eu := isEvenUnimodular_blockDiag (interMatrix (a.fc p) (a.B p))
    (-interMatrix (a.fc q) (a.B q)) heuP heuNegQ
  exact finrank_eq_half_of_isotropic_coisotropic _ hbd_eu.radical_eq_bot L hiso hco

/-- **`NovikovHalfDimAtom` DISCHARGED from the residual co-isotropy atom** — routing the opener's
structure-based reduction through the sharper co-isotropy atom (via `novikovLagrangian_of_novikovCoIso`
and the opener's faithfulness `novikovHalfDim_of_novikovLagrangian`). -/
theorem novikovHalfDim_of_novikovCoIso {a : SpinSigmaAtoms prov}
    (h : NovikovCoIsoAtom prov a) : NovikovHalfDimAtom prov a :=
  novikovHalfDim_of_novikovLagrangian (novikovLagrangian_of_novikovCoIso h)

/-! ## §5. `hbord` and the σ-descent COMPLETE, modulo only the Lefschetz co-isotropy -/

/-- **`hbord` discharged from the co-isotropy atom** — the σ-descent's bordism-invariance of the lattice
signature, now needing only the isotropic co-isotropic subspace (half-dimensionality discharged to linear
algebra). Chains `novikovLagrangian_of_novikovCoIso` into `hbord_of_novikovLagrangian`: for data-bordant
`p, q`, `σ(II M_p) = σ(II M_q)`. This is the sharpest reduction of the σ-descent — `hbord` reduced past the
full Lagrangian, past the half-dimensionality, to just the Lefschetz co-isotropy `im^⊥ ⊆ im`. -/
theorem hbord_of_novikovCoIso (a : SpinSigmaAtoms prov) (h : NovikovCoIsoAtom prov a) :
    ∀ p q, IsDataBordant (spinEmptyData prov) p q →
      latticeSig (interMatrix (a.fc p) (a.B p)) = latticeSig (interMatrix (a.fc q) (a.B q)) :=
  hbord_of_novikovLagrangian a (novikovLagrangian_of_novikovCoIso h)

/-- **The canonical bundle's Thom signature hom from the co-isotropy atom** (no free `hbord`, no full
Lagrangian, no half-dim disclosure). With `hbord` discharged from `NovikovCoIsoAtom`, the bordism-invariant
signature `Ω → ℤ` is built with the deep bordism-invariance supplied by just the isotropic co-isotropic
subspace. The σ-descent COMPLETES on the canonical construction modulo the single Lefschetz co-isotropy
residual. -/
noncomputable def sigThomNovikovCoIsoCanonical (c : CanonicalSpinSigmaAtoms prov)
    (h : NovikovCoIsoAtom prov c.toSpinSigmaAtoms) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  c.sigThom (hbord_of_novikovCoIso c.toSpinSigmaAtoms h)

/-- **The completed Thom hom computes the lattice signature on classes** (`rfl`) — the `sig_eq`
obligation, automatic, for the co-isotropy-atom-driven Thom hom. -/
@[simp] theorem sigThomNovikovCoIsoCanonical_mk (c : CanonicalSpinSigmaAtoms prov)
    (h : NovikovCoIsoAtom prov c.toSpinSigmaAtoms) (p : StrMfd (spinEmptyData prov)) :
    sigThomNovikovCoIsoCanonical c h (DataBordismGrp.mk (spinEmptyData prov) p)
      = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p)) :=
  rfl

/-- **The disclosed `sig` field is FORCED by the single co-isotropy atom.** Both `c.sig` and
`sigThomNovikovCoIsoCanonical c h` are `AddMonoidHom`s on `DataBordismGrp = Quot _` agreeing on every
generator, hence equal. So on the canonical construction the whole σ-presentation collapses onto the
Lefschetz co-isotropy of the boundary restriction — the sharpest honest statement of the σ-descent's last
residual. -/
theorem sig_eq_sigThomNovikovCoIsoCanonical (c : CanonicalSpinSigmaAtoms prov)
    (h : NovikovCoIsoAtom prov c.toSpinSigmaAtoms) :
    c.toSpinSigmaAtoms.sig = sigThomNovikovCoIsoCanonical c h :=
  c.sig_eq_sigThom (hbord_of_novikovCoIso c.toSpinSigmaAtoms h)

end SKEFTHawking.PinPlusKTSpinSigmaNovikovHalfDim
