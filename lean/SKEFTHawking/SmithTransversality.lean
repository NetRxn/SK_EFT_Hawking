/-
# Phase 5q.F W5 — transversality foundation for the geometric Smith map `[M] ↦ [PD(a)]`

The genuine geometric Smith map of the Smith-LES spine (`Lit-Search/Phase-5qF/Smith_sequence.md` §2)
sends a closed manifold `[M]` to the class `[N]` of the **Poincaré-dual submanifold** `N = PD(a)` of a
class `a ∈ H¹(M;ℤ/2)` — concretely, the zero locus of a section, transverse to the zero section, of the
real line bundle `L_a`. This module ships the analytic bottom brick that the PD construction rests on:
the **local structure of the zero locus of a real submersion** (transversality / the regular-value
theorem, local form), built on Mathlib's implicit function theorem
(`HasStrictFDerivAt.implicitFunction`).

For a strictly-differentiable `f : E → ℝ` with surjective derivative `f'` at a regular point `a`
(`f a = 0`), the zero locus `f⁻¹(0)` is, near `a`, the image of the implicit function
`φ := f.implicitFunction f' 0 : ker f' → E`:

  - `submersion_zero_locus_param` — `f (φ k) = 0` for `k` near `0` (the zero locus IS the local graph);
  - `submersion_zero_locus_immersion` — `φ` is a strict-differentiable immersion at `0` (its derivative
    is the inclusion `ker f' ↪ E`), so the local zero locus is a genuine **smooth codimension-1
    submanifold** chart;
  - `submersion_zero_locus_base` — `φ` passes through the basepoint (`φ(f a, 0) = a`).

This is the analytic local model of `PD(a)` (`w₁(N) = a`, and via `SmithMechanism.smith_w2_vanishes`
`w₂(N) = w₂(M) − a² = 0`, so `N` is Pin⁺). Building it on Mathlib's IFT is the goal's "build the thin
classical inputs genuinely, brick by brick" — the manifold-global PD, the line bundle `L_a`, and the
Smith homomorphism on `DataBordismGrp` are the continuation bricks of W5.

Kernel-pure; no axioms beyond Mathlib's core.
-/
import Mathlib

namespace SKEFTHawking.SmithTransversality

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Local parametrization of a real submersion's zero locus (transversality, local form).** For a
strictly-differentiable `f : E → ℝ` with surjective derivative `f'` at `a` and `f a = 0`, the zero locus
`f⁻¹(0)` is, near `a`, the image of the implicit function `φ := f.implicitFunction f' 0 : ker f' → E`:
`f (φ k) = 0` for all `k` in a neighbourhood of `0`. The codimension-1 subspace `ker f'` is the model
for the tangent space of `PD(a)`. -/
theorem submersion_zero_locus_param (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
    (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (h0 : f a = 0) :
    ∀ᶠ k in 𝓝 (0 : LinearMap.ker (f' : E →ₗ[ℝ] ℝ)), f (hf.implicitFunction f f' hf' 0 k) = 0 := by
  have key := hf.map_implicitFunction_eq hf'
  rw [h0] at key
  have hcont : Filter.Tendsto (fun k : LinearMap.ker (f' : E →ₗ[ℝ] ℝ) => ((0 : ℝ), k))
      (𝓝 0) (𝓝 ((0 : ℝ), 0)) := by
    rw [nhds_prod_eq]; exact Filter.Tendsto.prodMk tendsto_const_nhds Filter.tendsto_id
  exact hcont.eventually key

/-- **The zero-locus parametrization is a smooth immersion at `0`.** The implicit function
`φ := f.implicitFunction f' 0 : ker f' → E` is strictly differentiable at `0` with derivative the
inclusion `ker f' ↪ E` (`(ker f').subtypeL`), which is injective — so the local zero locus is a genuine
smooth codimension-1 submanifold (not merely a closed set). -/
theorem submersion_zero_locus_immersion (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
    (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (h0 : f a = 0) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' 0)
      (LinearMap.ker (f' : E →ₗ[ℝ] ℝ)).subtypeL 0 := by
  have h := hf.to_implicitFunction hf'
  rwa [h0] at h

/-- **The parametrization passes through the basepoint** `a`: `φ(f a, 0) = a`. With `f a = 0`, the
zero-locus chart `φ := f.implicitFunction f' 0` satisfies `φ 0 = a`, so `a ∈ PD(a)` locally. -/
theorem submersion_zero_locus_base (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
    (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a :=
  hf.implicitFunction_apply_image hf'

/-- **The Poincaré-dual submanifold has codimension exactly 1.** The model `ker f'` of the zero locus
has codimension 1 in `E` (rank–nullity, with `range f' = ℝ`). This is the dimension drop `d ↦ d − 1`
the Smith map `s : Ω_d → Ω_{d−1}` produces — `PD(a) = N^{d−1} ⊂ M^d`, `w₁(N) = a`. -/
theorem submersion_ker_codim_one [FiniteDimensional ℝ E] (f' : E →L[ℝ] ℝ)
    (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    Module.finrank ℝ (LinearMap.ker (f' : E →ₗ[ℝ] ℝ)) + 1 = Module.finrank ℝ E := by
  have hrn := (f' : E →ₗ[ℝ] ℝ).finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ (LinearMap.range (f' : E →ₗ[ℝ] ℝ)) = 1 := by
    have htop : LinearMap.range (f' : E →ₗ[ℝ] ℝ) = ⊤ := hf'
    rw [htop, finrank_top, Module.finrank_self]
  omega

/-- **The zero locus is locally exactly the immersion's range.** Within the IFT chart's source, every
point of `f⁻¹(0)` lies in the range of the codim-1 immersion `φ := f.implicitFunction f' 0` (since
`φ = Φ.symm` on the `{0}`-slice and `(Φ x).1 = f x`). Together with `submersion_zero_locus_param`
(`f (φ k) = 0` near `0`), this gives `f⁻¹(0) ∩ chart = range φ` locally — the level set near a regular
point IS a smooth codim-1 embedded submanifold (the local model of `PD(a)`). -/
theorem zero_locus_locally_range (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
    (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) :
    ∀ x ∈ (hf.implicitToOpenPartialHomeomorph f f' hf').source,
      f x = 0 → x ∈ Set.range (hf.implicitFunction f f' hf' 0) := by
  intro x hx hfx
  set Φ := hf.implicitToOpenPartialHomeomorph f f' hf' with hΦ
  refine ⟨(Φ x).2, ?_⟩
  have hfst : (Φ x).1 = f x := hf.implicitToOpenPartialHomeomorph_fst hf' x
  have hsymm : Φ.symm (Φ x) = x := Φ.left_inv hx
  have hrw : hf.implicitFunction f f' hf' 0 (Φ x).2 = Φ.symm (0, (Φ x).2) := rfl
  rw [hrw, ← hfx, ← hfst, hsymm]

end SKEFTHawking.SmithTransversality
