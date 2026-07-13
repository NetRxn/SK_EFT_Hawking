import Mathlib
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.PoincareDualityConstruct
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.SingularCupCapHomology
import SKEFTHawking.SingularCapChainIncl

/-!
# W-A (new-build 2) — the 2-dimensional Poincaré-duality substrate for closed surfaces

The free-standing surface siblings of the closed-4-manifold PD instances
(`SingularPD4Instances`), assembled from the dimension-generic singular mod-2 stack at the base
level `m = 0` (a surface is charted on `E² = EuclideanSpace ℝ (Fin (0 + 2))`, top degree `0 + 2 = 2`).

For a closed (compact, `T2`, `Nonempty`, charted-on-`E²`) surface `Σ`:

* **`surfaceFundamentalClass = [Σ] ∈ H₂(Σ;ℤ/2)`** — the *canonical* top-degree mod-2 homology
  class (`fundamentalClass (m := 0)`, a single `def`, NOT a chosen representative), with its
  characterizing property `surfaceFundamentalClass_restricts`: it restricts to the local generator
  at every point.
* **`surfaceFundamentalFunctional = μ = ⟨·, [Σ]⟩ : H²(Σ;ℤ/2) → ℤ/2`** — the Kronecker pairing
  against `[Σ]` (`fundamentalFunctional (m := 0)`); the H⁰↔H₂ / top duality datum.
* **`intersectionForm : H¹(Σ;ℤ/2) →ₗ H¹(Σ;ℤ/2) →ₗ ℤ/2`** — the mod-2 intersection form, the cup
  pairing `cupH : H¹ × H¹ → H²` (`SingularCohomologyMod2`) composed with `μ`. It is a genuine
  **symmetric** `ℤ/2`-bilinear form (`intersectionForm_isSymm`, from graded commutativity
  `cupH_symm`), and it satisfies the **cap–cup adjunction** `⟨a,b⟩ = ⟨b, a ⌢ [Σ]⟩`
  (`intersectionForm_eq_kronecker_cap`) — the algebraic heart of middle-dimension PD (H¹↔H₁).

This is the free-standing object the faithful carrier's `hpolar` anchor will equate with a
`Brown.Z4Quadratic`'s polar form. The middle-dimension *non-degeneracy* (full PD) requires the
dim-2 openDuality-window, which is NOT supplied here (see the module footnote); the form, its
symmetry, and the adjunction are window-independent.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.SingularSurfaceIntersectionForm

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]

/-- **The mod-2 fundamental class `[Σ] ∈ H₂(Σ;ℤ/2)`** of a closed surface — the base-level
(`m = 0`) instance of the canonical `fundamentalClass`. -/
noncomputable def surfaceFundamentalClass : Homology (TopCat.of M) (0 + 2) :=
  fundamentalClass (m := 0) (M := M)

/-- **`[Σ]` restricts to the local generator at every point** — the characterizing property of the
canonical fundamental class (Hatcher 3.26 at `m = 0`); this is what makes `[Σ]` canonical, not a
chosen cycle. -/
theorem surfaceFundamentalClass_restricts (x : M) :
    restrictHomologyToPoint (X := TopCat.of M) x (0 + 2) surfaceFundamentalClass
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1 :=
  fundamentalClass_restricts (m := 0) x

/-- **The fundamental-class functional `μ = ⟨·, [Σ]⟩ : H²(Σ;ℤ/2) → ℤ/2`** — the surface's top
(H⁰↔H₂) duality datum, the Kronecker pairing against `[Σ]`. -/
noncomputable def surfaceFundamentalFunctional :
    Cohomology (TopCat.of M) (0 + 2) →ₗ[ZMod 2] ZMod 2 :=
  fundamentalFunctional (m := 0) (M := M)

@[simp] theorem surfaceFundamentalFunctional_apply (ω : Cohomology (TopCat.of M) (0 + 2)) :
    surfaceFundamentalFunctional (M := M) ω
      = kroneckerH (X := TopCat.of M) (0 + 2) ω surfaceFundamentalClass :=
  rfl

/-- **The mod-2 intersection form of a closed surface** `H¹(Σ;ℤ/2) × H¹(Σ;ℤ/2) → ℤ/2` — the cup
pairing `cupH` composed with the fundamental-class functional `μ = ⟨·, [Σ]⟩`. The middle-dimension
(H¹↔H₁) Poincaré-duality form; the algebraic core of the Guillou–Marin intersection form on the
characteristic surface. -/
noncomputable def intersectionForm :
    Cohomology (TopCat.of M) 1 →ₗ[ZMod 2] Cohomology (TopCat.of M) 1 →ₗ[ZMod 2] ZMod 2 :=
  (cupH (X := TopCat.of M)).compr₂ (surfaceFundamentalFunctional (M := M))

@[simp] theorem intersectionForm_apply (a b : Cohomology (TopCat.of M) 1) :
    intersectionForm (M := M) a b = surfaceFundamentalFunctional (M := M) (cupH a b) :=
  rfl

/-- **The intersection form is symmetric** — `⟨a,b⟩ = ⟨b,a⟩`, from graded commutativity of the
degree-`(1,1)` cup product (`cupH_symm`). -/
theorem intersectionForm_symm (a b : Cohomology (TopCat.of M) 1) :
    intersectionForm (M := M) a b = intersectionForm (M := M) b a := by
  simp only [intersectionForm_apply, cupH_symm a b]

/-- **The intersection form packaged as a symmetric `ℤ/2`-bilinear form** (`LinearMap.BilinForm`
`IsSymm`), the direct consequence of `intersectionForm_symm`. -/
theorem intersectionForm_isSymm :
    LinearMap.BilinForm.IsSymm (intersectionForm (M := M)) :=
  LinearMap.BilinForm.isSymm_def.mpr (fun a b => intersectionForm_symm (M := M) a b)

/-- **The cap–cup adjunction of the surface intersection form** (`m = 0`): `⟨a,b⟩ = ⟨b, a ⌢ [Σ]⟩`,
the cohomology-level form of `kronecker_cup_cap` evaluated against `[Σ]`. The bridge from the cup
pairing `(a,b) ↦ ⟨a∪b, [Σ]⟩` to the middle-dimension duality map `a ↦ a ⌢ [Σ] : H¹ → H₁`; the
`m = 0` mirror of `fundamentalFunctional_cupH24`. -/
theorem intersectionForm_eq_kronecker_cap (a b : Cohomology (TopCat.of M) 1) :
    intersectionForm (M := M) a b
      = kroneckerH (X := TopCat.of M) 1 b (capH 1 0 a (surfaceFundamentalClass (M := M))) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zM, hzM⟩ := Submodule.Quotient.mk_surjective _ (surfaceFundamentalClass (M := M))
  rw [intersectionForm_apply, surfaceFundamentalFunctional_apply, ← hzM]
  simp only [cupH_mk_mk, kroneckerH_mk_mk]
  exact SKEFTHawking.SingularCapChainIncl.kronecker_cup_cap fa.1 fb.1 zM.1

/-- **`[Σ] ≠ 0`** — the fundamental class is a genuine nonzero top-homology generator (it restricts
to the local generator `1 ≠ 0` at each point), the `m = 0` instance of `fundamentalClass_ne_zero`. -/
theorem surfaceFundamentalClass_ne_zero : surfaceFundamentalClass (M := M) ≠ 0 :=
  fundamentalClass_ne_zero (m := 0) (Classical.arbitrary M)

/-- **The top (H⁰↔H₂) pairing is non-degenerate on the `[Σ]`-line**: `μ = ⟨·,[Σ]⟩ ≠ 0`. Since
`[Σ] ≠ 0`, universal coefficients over `ℤ/2` (`homology_eq_zero_of_kroneckerH`) gives a class
pairing nontrivially with it, so the functional is nonzero (surjective onto `ℤ/2`). -/
theorem surfaceFundamentalFunctional_ne_zero :
    surfaceFundamentalFunctional (M := M) ≠ 0 := by
  intro hμ
  refine surfaceFundamentalClass_ne_zero (M := M) ?_
  refine homology_eq_zero_of_kroneckerH (0 + 2) _ (fun ω => ?_)
  have := LinearMap.congr_fun hμ ω
  rwa [surfaceFundamentalFunctional_apply, LinearMap.zero_apply] at this

/-- **The middle-dimension (H¹↔H₁) Poincaré-duality non-degeneracy of the surface intersection form
reduces to PD-injectivity of the duality map** `a ↦ a ⌢ [Σ] : H¹ → H₁`: if that cap map is
injective, the intersection form is non-degenerate (injective as `H¹ → (H¹)^*`). A class `a` with
`⟨a,b⟩ = 0` for all `b` has `⟨b, a⌢[Σ]⟩ = 0` for all `b` (adjunction
`intersectionForm_eq_kronecker_cap`), so `a⌢[Σ] = 0` (universal coefficients
`homology_eq_zero_of_kroneckerH`), so `a = 0`. The `m = 0` mirror of `nondeg_of_duality_injective`;
this isolates the remaining PD obligation to exactly the surface middle-cap injectivity (which the
dim-2 openDuality-`(1,0)` window would discharge — see the module footnote). -/
theorem intersectionForm_nondeg_of_cap_injective
    (hPD : Function.Injective fun a : Cohomology (TopCat.of M) 1 =>
      capH 1 0 a (surfaceFundamentalClass (M := M))) :
    Function.Injective ⇑(intersectionForm (M := M)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine hPD ?_
  show capH 1 0 a (surfaceFundamentalClass (M := M))
    = capH 1 0 0 (surfaceFundamentalClass (M := M))
  rw [map_zero, LinearMap.zero_apply]
  refine homology_eq_zero_of_kroneckerH 1 _ (fun ω => ?_)
  rw [← intersectionForm_eq_kronecker_cap]
  exact LinearMap.congr_fun ha ω

/-- **The self-intersection is the fundamental functional of the cup square** — `⟨a,a⟩ = μ(a ⌣ a)`.
The diagonal of the intersection form is `surfaceFundamentalFunctional ∘ cupSquare`, the mod-2
shadow of the Guillou–Marin `ℤ/4`-quadratic refinement (`cupSquareHom : H¹ →+ H²`); the object the
faithful carrier's `hchar` anchor pairs against a `Brown.Z4Quadratic`. -/
theorem intersectionForm_self_eq_cupSquare (a : Cohomology (TopCat.of M) 1) :
    intersectionForm (M := M) a a = surfaceFundamentalFunctional (M := M) (cupSquare a) :=
  rfl

/-! ## Footnote — the remaining (window-dependent) middle-dimension non-degeneracy

The unconditional discharge of `intersectionForm_nondeg_of_cap_injective`'s hypothesis
(`a ↦ a ⌢ [Σ]` injective) reduces — via the generic bridges
`capH_injective_of_fundamentalDuality_injective (k := 1) (m := 0)` and
`fundamentalDuality_injective_of_openDuality_univ_injective (k := 1) (m := 0)` — to
`openDuality (k := 1) (m := 0)` being injective on `univ` for a compact charted-on-`E²` surface.
That is supplied for the closed 4-manifold by the deg-4 window tower `pdWindowP`/`pdWindowP4`
(hardcoded to `SingularChain _ (1 + 0 + 3)`, degree `2 + 1 + 2`, `Fin (2 + 2)`). The dim-2 analog
(a "P₂ window") is NOT built here: the base-case ingredients are already dimension-generic
(`SingularBaseCaseD0.openDuality₀_bijective_of_chartConvex` and
`SingularCSCConvexChart.cscOpen_one_eq_zero_of_chartConvex` — the `k = 1` companion to the
`2 ≤ k` upper base case — together with `homology_chartConvexSub_eq_zero`), and the union/colimit
engines are `N`-generic (`openDuality_union_bijective_bot` at `N = 0`,
`openDuality₀_union_bijective` at `N = 0`), so no NEW mathematics is required — only the mechanical
mirror of the `pdWindowP`/`pdWindowP4` finite-chart-cover assembly at `m = 0`. Everything above the
footnote (the form, its symmetry, the cap–cup adjunction, and this conditional non-degeneracy) is
window-independent and complete. -/

end SKEFTHawking.SingularSurfaceIntersectionForm
