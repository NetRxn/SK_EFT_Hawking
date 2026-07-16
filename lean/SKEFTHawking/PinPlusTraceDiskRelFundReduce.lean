/-
# Phase 5q.H close-out — THE D⁵ RELATIVE FUNDAMENTAL CLASS, REDUCED TO ONE GEOMETRIC FACT

The disk-side deepest atom of the capstone cover-glue is
`HasRelFundClass (TopCat.of D⁵) (∂D⁵) (interiorGenFamily …)` — the disk's `[D⁵, S⁴]` class. This
module discharges it MODULO a single geometric input via the pair long-exact-sequence route.

**The route.** `D⁵` is convex/contractible, so it is acyclic (`SingularDiskAcyclic`): `H₅(D⁵) = 0`
and `H₄(D⁵) = 0`. The pair-LES connecting map is therefore an isomorphism
`∂ : H₅(D⁵, S⁴) ≅ H₄(S⁴)` (`connecting_bijective_of_acyclic`). Pick a nonzero `β ∈ H₄(S⁴)`, pull it
back to `α = ∂⁻¹ β ∈ H₅(D⁵, S⁴)`. At each interior point `x` (`‖x‖ < 1`), the interior detection
`restrictBd α = generator` is — over `ℤ/2`, where the unique nonzero element IS the generator —
exactly `restrictBd α ≠ 0`. By connecting-map naturality (`connecting_relIncl`) and the two acyclic
connecting isos (for `S⁴` and for `D⁵ ∖ {x}`), this equals `Homology.map (S⁴ ↪ D⁵∖{x}) β ≠ 0` — which
holds precisely when the boundary inclusion `S⁴ ↪ D⁵∖{x}` is injective on `H₄`. The latter is the
punctured-disk-retracts-to-boundary fact — the ONE geometric residual left of the entire disk core.

So `hasRelFundClass_D5_of_boundaryIncl` reduces the disk relative fundamental class to:
* `(β, hβ)` — `H₄(S⁴) ≠ 0` (a nonzero boundary-sphere class; `= ℤ/2` via `topSphereIso`);
* `hincl` — the boundary inclusion `S⁴ ↪ D⁵∖{x}` is `H₄`-injective at every interior `x`.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularDiskAcyclic
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularConvexRestrictionIso
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularConvexRestrictionIso
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.DiskChartGeneric (D5)

namespace SKEFTHawking.PinPlusTraceDiskRelFundReduce

noncomputable section

/-- **`Dⁿ` is acyclic in positive degree** (abstract disk): `Hₖ₊₁(Dⁿ; ℤ/2) = 0`, from the in-tree
straight-line contraction `SingularDiskAcyclic.cycle_mem_boundaries`. Stated for the abstract
`SingularDiskAcyclic.Disk n` so the heavy `rw` never runs on the concrete `TopCat.of D⁵` type (which
whnf-times-out over the `closedBall`/`WithLp` instances). -/
theorem disk_homology_zero_abstract {n : ℕ} (k : ℕ)
    (x : Homology (SingularDiskAcyclic.Disk n) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  exact SingularDiskAcyclic.cycle_mem_boundaries k z.1 z.2

/-- **`D⁵` is acyclic in positive degree**: `Hₖ₊₁(D⁵; ℤ/2) = 0`. The `n = 5` instance of
`disk_homology_zero_abstract` (`TopCat.of D⁵ = Disk 5` definitionally); supplies both flanking-term
vanishings of the pair LES `H₅(D⁵) = 0`, `H₄(D⁵) = 0`. -/
theorem disk_homology_zero (k : ℕ) (x : Homology (TopCat.of D5) (k + 1)) : x = 0 :=
  disk_homology_zero_abstract (n := 5) k x

/-- **`restrictBd` is definitionally the pair-inclusion** (generic, `D⁵`-free): `restrictBd S hx n`
is `relIncl (S ⊆ {x}ᶜ) n`. Proven abstractly so the `rfl` is checked over an abstract `X` — never
forcing the concrete-`D⁵` whnf that the same `rfl` triggers inline. -/
theorem restrictBd_eq_relIncl {X : TopCat} (S : Set ↑X) {x : ↑X} (hx : x ∉ S) (n : ℕ)
    (α : RelativeHomology S n) :
    restrictBd S hx n α = relIncl (Set.subset_compl_singleton_iff.mpr hx) n α := rfl

/-- **Relative fundamental class from an acyclic ambient + a detecting boundary class** (generic,
ambient-abstract). If the ambient `X` is acyclic in degrees `m+1` and `m+2`, `β ∈ Hₘ₊₁(S)` is
nonzero, and the inclusion `S ↪ {x}ᶜ` is `Hₘ₊₁`-injective at every interior point `x ∉ S`, then
`Hₘ₊₂(X, S)` has a relative fundamental class restricting to the local generator `gen` everywhere.
Proof: `α = ∂⁻¹β` (surjectivity of the acyclic connecting map, `connecting_bijective_of_acyclic`);
connecting naturality (`connecting_relIncl`) plus the connecting iso at `{x}ᶜ` identify
`restrictBd α` with `Homology.map (S ↪ {x}ᶜ) β`, nonzero by `hincl` + `hβ`; over `ℤ/2` a nonzero
local restriction IS the generator. Stated abstractly so the whole homology argument is checked over
an abstract `X` — never touching the whnf-hostile concrete `D⁵`. -/
theorem hasRelFundClass_of_acyclic_boundaryIncl {X : TopCat} {m : ℕ} (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (h_ac1 : ∀ z : Homology X (m + 2), z = 0) (h_ac0 : ∀ z : Homology X (m + 1), z = 0)
    (β : Homology (sub S) (m + 1)) (hβ : β ≠ 0)
    (hincl : ∀ (x : ↑X) (hx : x ∉ S),
      Function.Injective
        (Homology.map (subIncl (Set.subset_compl_singleton_iff.mpr hx)) (m + 1))) :
    HasRelFundClass (X := X) S gen := by
  obtain ⟨α, hα⟩ :=
    (connecting_bijective_of_acyclic S (m + 1) h_ac1 h_ac0).surjective β
  refine ⟨α, ?_⟩
  intro x hx
  have hsub : (S : Set ↑X) ⊆ {x}ᶜ := Set.subset_compl_singleton_iff.mpr hx
  -- Connecting naturality: `connecting {x}ᶜ (m+1) (restrictBd α) = Homology.map (subIncl) (m+1) β`.
  have hnat : connecting ({x}ᶜ) (m + 1) (restrictBd S hx (m + 2) α)
      = Homology.map (subIncl hsub) (m + 1) β := by
    rw [restrictBd_eq_relIncl, connecting_relIncl hsub (m + 1) α, hα]
  -- The boundary-inclusion image is nonzero (`hincl` injective + `β ≠ 0`).
  have hmap_ne : Homology.map (subIncl hsub) (m + 1) β ≠ 0 := fun heq =>
    hβ (hincl x hx (heq.trans (map_zero _).symm))
  -- Hence `restrictBd α ≠ 0` (connecting `{x}ᶜ` is injective over the acyclic ambient).
  have hrestr_ne : restrictBd S hx (m + 2) α ≠ 0 := fun h0 =>
    hmap_ne (by rw [← hnat, h0, map_zero])
  -- Over `ℤ/2`, a nonzero local restriction IS the generator.
  have hg_ne : gen x hx (restrictBd S hx (m + 2) α) ≠ 0 := fun h0 =>
    hrestr_ne ((gen x hx).injective (by rw [h0, map_zero]))
  have hg1 : gen x hx (restrictBd S hx (m + 2) α) = 1 :=
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hg_ne
  rw [← (gen x hx).symm_apply_apply (restrictBd S hx (m + 2) α), hg1]

/-- **The `D⁵` relative fundamental class, reduced to boundary-inclusion `H₄`-injectivity.** The
`X = TopCat.of D⁵`, `m = 3` instance of `hasRelFundClass_of_acyclic_boundaryIncl`: given a nonzero
`β ∈ H₄(∂D⁵)` and that the boundary inclusion `∂D⁵ ↪ D⁵∖{x}` is `H₄`-injective at every interior
point `x`, the disk has a relative fundamental class
`HasRelFundClass (TopCat.of D⁵) (∂D⁵) (interiorGenFamily …)`. `D⁵`'s acyclicity `H₅(D⁵)=0`,
`H₄(D⁵)=0` is `disk_homology_zero`. THE remaining geometric residual of the whole disk core is
`hincl` — the punctured-disk-retracts-to-boundary fact. -/
theorem hasRelFundClass_D5_of_boundaryIncl
    (β : Homology (sub (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5)) 4)
    (hβ : β ≠ 0)
    (hincl : ∀ (x : ↑(TopCat.of D5)) (hx : x ∉ ((𝓡 4).prod (𝓡∂ 1)).boundary D5),
      Function.Injective
        (Homology.map (subIncl (X := TopCat.of D5)
          (Set.subset_compl_singleton_iff.mpr hx)) 4)) :
    HasRelFundClass (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5)
      (interiorGenFamily (W := D5) ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasRelFundClass_of_acyclic_boundaryIncl (X := TopCat.of D5) (m := 3)
    (((𝓡 4).prod (𝓡∂ 1)).boundary D5)
    (interiorGenFamily (W := D5) ((𝓡 4).prod (𝓡∂ 1)) εtrace)
    (disk_homology_zero 4) (disk_homology_zero 3) β hβ hincl

end

end SKEFTHawking.PinPlusTraceDiskRelFundReduce
