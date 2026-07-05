/-
# Phase 5q.H (E1 integral topology) — Hom(−, R) of a split-exact sequence is exact

A general homological-algebra helper: for a right-split short exact sequence `M →f N →g P` (exact, `g`
has a section `l` with `g ∘ l = id`), the dualized sequence `P* →^{g*} N* →^{f*} M*` is exact —
`Hom(−, R)` preserves exactness of a split SES. Mathlib has no ready form of this for `Module.Dual`, so
it is proved directly (no equiv transport): `φ ∈ ker f*` (`φ ∘ f = 0`) is `(φ ∘ l) ∘ g` because
`l(g n) − n ∈ ker g = range f` (from `g ∘ l = id` + exactness) and `φ` kills `range f`.

Used to Hom-dualize the (split, `SingularRelativeMVSplitInt`) relative-homology MV chain SES into the
relative-cohomology MV — the field-UC-free route.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib

namespace SKEFTHawking.LinearAlgebraDualExactInt

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- **`Hom(−, R)` of a right-split short exact sequence is exact.** -/
theorem exact_dualMap_of_split {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Function.Exact f g)
    (l : P →ₗ[R] N) (hl : g ∘ₗ l = LinearMap.id) :
    Function.Exact (g.dualMap : Module.Dual R P →ₗ[R] Module.Dual R N) f.dualMap := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · -- ker f* ⊆ range g*
    intro φ hφ
    rw [LinearMap.mem_ker, LinearMap.dualMap_apply'] at hφ
    refine ⟨φ ∘ₗ l, ?_⟩
    rw [LinearMap.dualMap_apply']
    apply LinearMap.ext
    intro n
    have hker : l (g n) - n ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hl, LinearMap.id_apply, sub_self]
    obtain ⟨m, hm⟩ := (hfg (l (g n) - n)).1 hker
    have hz : φ (l (g n) - n) = 0 := by
      rw [← hm, ← LinearMap.comp_apply, hφ, LinearMap.zero_apply]
    rw [map_sub] at hz
    show φ (l (g n)) = φ n
    exact sub_eq_zero.mp hz
  · -- range g* ⊆ ker f*
    rintro φ ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.dualMap_apply']
    apply LinearMap.ext
    intro m
    show ψ (g (f m)) = 0
    rw [hfg.apply_apply_eq_zero m, map_zero]

/-- **A retraction-split injection's `dualMap` is surjective.** If `ret ∘ f = id`, then `f.dualMap` has
the right inverse `ret.dualMap`, so it is surjective. (Applied to the split MV `Diag` to get the
cochain-MV `Sum` surjective under the pairing.) -/
theorem surjective_dualMap_of_retraction {f : M →ₗ[R] N} (ret : N →ₗ[R] M)
    (hret : ret ∘ₗ f = LinearMap.id) :
    Function.Surjective (f.dualMap : Module.Dual R N →ₗ[R] Module.Dual R M) := by
  intro φ
  refine ⟨ret.dualMap φ, ?_⟩
  rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, hret, LinearMap.dualMap_id,
    LinearMap.id_apply]

end SKEFTHawking.LinearAlgebraDualExactInt
