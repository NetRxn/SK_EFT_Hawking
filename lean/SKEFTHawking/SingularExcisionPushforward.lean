/-
# Phase 5q.F (w₂-foundation, brick 6c-c7) — the pushforward bridge: affine `Sd`/`D` → singular chains

The barycentric subdivision `Sd` and homotopy `D` are fully verified on the **affine** chain complex
`LinChain(Δⁿ)` (`SingularExcisionMod2`: `∂²=0`, `∂Sd=Sd∂`, `∂D+D∂=1−Sd`). To use them for excision they
must be transported to the **singular** chains of an arbitrary space `X`: a singular `n`-simplex
`σ : Δⁿ → X` post-composes an affine simplex `[w]` (vertices in `Δⁿ`) to a singular simplex
`σ ∘ affineSimplex(w)`, and `Sd(σ) := σ_#(Sd(ι_n))`. The chain-map / homotopy identities then transport
from the affine ones via the **naturality of `σ_#`** (it commutes with `∂` — the one place the
`toSSet`/`toTopHomeo` plumbing is needed; built on Mathlib's `toTopHomeo_naturality`).

Sub-brick c7a: the affine simplex with vertices in the standard simplex `Δᴺ`, **landing in `Δᴺ`** (by
convexity, `convex_stdSimplex`) — `C(Δⁿ, Δᴺ)`, ready to post-compose with a singular `N`-simplex.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2

namespace SKEFTHawking.SingularExcisionPushforward

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2

/-- The affine `n`-simplex with vertices `w : Fin (n+1) → Δᴺ` **landing in `Δᴺ`** (the convex
combination of points of the standard simplex stays in it): `C(Δⁿ, Δᴺ)`. The geometric realization of
an affine simplex *of* `Δᴺ`, ready to post-compose with a singular `N`-simplex `σ : Δᴺ → X`. -/
noncomputable def affineSimplexStd {N n : ℕ} (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (N + 1))) where
  toFun t := ⟨affineSimplex (fun i => (w i : Fin (N + 1) → ℝ)) t, by
    rw [affineSimplex_apply]
    exact (convex_stdSimplex ℝ (Fin (N + 1))).sum_mem (fun i _ => t.2.1 i) t.2.2
      (fun i _ => (w i).2)⟩
  continuous_toFun :=
    (affineSimplex (fun i => (w i : Fin (N + 1) → ℝ))).continuous.subtype_mk _

@[simp] theorem affineSimplexStd_coe_apply {N n : ℕ} (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1)))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    ((affineSimplexStd w t : stdSimplex ℝ (Fin (N + 1))) : Fin (N + 1) → ℝ)
      = ∑ i, (t : Fin (n + 1) → ℝ) i • (w i : Fin (N + 1) → ℝ) := by
  show affineSimplex (fun i => (w i : Fin (N + 1) → ℝ)) t = _
  rw [affineSimplex_apply]

end SKEFTHawking.SingularExcisionPushforward
