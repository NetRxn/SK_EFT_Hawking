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

end SKEFTHawking.SmithTransversality
