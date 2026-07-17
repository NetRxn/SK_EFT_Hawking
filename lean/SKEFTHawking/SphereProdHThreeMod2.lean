/-
# Phase 5q.H · Root 2 — mod-2 `H₃(S²×S²) = 0`
# and `Subsingleton (RelativeHomology sphereDiskBoundarySet 4)`

This module closes **Root 2** of the `S²×D³` coboundary
(`PinPlusKTSphereProdHomologyRoots`, §5): the last missing input to the pair-LES squeeze
`Subsingleton (RelativeHomology sphereDiskBoundarySet 4)` was `H₃(S²×S²; ℤ/2) = 0`.

The in-tree `S²×S²` product-homology computations are all **ℤ-coefficient**
(`SphereProdHTwoInt`, `SphereProdHFourInt`). No Universal-Coefficient bridge exists in-tree, and
`H₃(S²×S²;ℤ) = 0` does not by itself imply the mod-2 statement. Instead of porting the ~1000-line
polar-cover Mayer–Vietoris argument to ℤ/2, we prove the **general homological-algebra lemma** that
supplies exactly the missing UCT ingredient at the chain level, using the already-banked
ℤ→ℤ/2 chain reduction bridge `SingularHomologyInt.redChain`:

> **`homologyMod2_top_eq_zero_of_int`**: if `Hₙ₊₁(X;ℤ) = 0` and `Hₙ(X;ℤ)` is 2-torsion-free, then
> `Hₙ₊₁(X;ℤ/2) = 0`.

Proof is a direct **lift / halve / bound** argument (no full Bockstein LES): a mod-2 cycle `z` lifts
to an integral chain `z̃` (`intLift`), whose integral boundary `∂z̃` reduces to `0` mod 2 hence is
`2·w` for an integral `w`; `w` is an integral cycle (torsion-freeness of `Finsupp`-into-ℤ chains),
`[2w] = [∂z̃] = 0` so `2[w] = 0`, and 2-torsion-freeness gives `[w] = 0`, i.e. `w = ∂u`; then
`∂(z̃ − 2u) = 0` and `Hₙ₊₁(X;ℤ) = 0` give `z̃ − 2u = ∂v`, whose mod-2 reduction is `z`, so `z` is a
mod-2 boundary and `[z] = 0`.

At `n := 2`, `X := S²×S²` the two integral inputs are banked
(`SphereProdHFourInt.sphereProd_homology_three_eq_zero`,
`SphereProdHTwoInt.sphereProdHTwoEquivInt`), giving `H₃(S²×S²;ℤ/2) = 0`, transported along
`sphereDiskInclHomeo` to `Subsingleton (Homology (sub sphereDiskBoundarySet) 3)` and fed to
`subsingleton_relativeHomology_of_squeeze` (with the banked Bonus `H₄(S²×D³;ℤ/2) = 0`) to close
Root 2.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new axiom.
-/
import Mathlib
import SKEFTHawking.IntFundamentalClassOrientation
import SKEFTHawking.SphereProdHFourInt
import SKEFTHawking.SphereProdHTwoInt
import SKEFTHawking.PinPlusKTSphereProdHomologyRoots
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

namespace SKEFTHawking.SphereProdHThreeMod2

open CategoryTheory Opposite
open SKEFTHawking
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots (sphereDiskInclHomeo)

/-! ## §1. Chain-level helpers for the ℤ→ℤ/2 lift/halve argument -/

/-- The pointwise `{0,1}`-integral lift of a mod-2 chain (`a ↦ (a.val : ℤ)`), the homological
companion of `BocksteinIntegralLift.liftInt`. -/
noncomputable def intLift {X : TopCat} {n : ℕ}
    (c : SingularHomologyMod2.SingularChain X n) : SingularHomologyInt.SingularChainInt X n :=
  Finsupp.mapRange (fun a : ZMod 2 => (a.val : ℤ)) (by simp) c

/-- The pointwise value of the reduction `redChain`: `(redChain c) σ = ((c σ : ℤ) : ZMod 2)`. -/
theorem redChain_apply {X : TopCat} {n : ℕ} (c : SingularHomologyInt.SingularChainInt X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    SingularHomologyInt.redChain X n c σ = ((c σ : ℤ) : ZMod 2) := by
  rw [SingularHomologyInt.redChain, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]
  rfl

/-- The reduction of the integral lift is the identity: `redChain (intLift c) = c`. -/
theorem redChain_intLift {X : TopCat} {n : ℕ} (c : SingularHomologyMod2.SingularChain X n) :
    SingularHomologyInt.redChain X n (intLift c) = c := by
  refine Finsupp.ext (fun σ => ?_)
  rw [redChain_apply, intLift, Finsupp.mapRange_apply, Int.cast_natCast, ZMod.natCast_val,
    ZMod.cast_id]

/-- `(2:ℤ) • y = 0` for any mod-2 chain `y` (char-2 pointwise). -/
theorem two_zsmul_mod2_eq_zero {X : TopCat} {n : ℕ}
    (y : SingularHomologyMod2.SingularChain X n) : (2 : ℤ) • y = 0 := by
  refine Finsupp.ext (fun σ => ?_)
  rw [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, zsmul_eq_mul,
    show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]

/-- `SingularChainInt` is 2-torsion-free: `2 • g = 0 → g = 0` (pointwise; ℤ is a domain). -/
theorem intChain_two_smul_eq_zero {X : TopCat} {n : ℕ}
    (g : SingularHomologyInt.SingularChainInt X n) (h : (2 : ℤ) • g = 0) : g = 0 := by
  refine Finsupp.ext (fun σ => ?_)
  have hσ := DFunLike.congr_fun h σ
  rw [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at hσ
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- **Integral homology class of a boundary is zero** (iff form): `[c] = 0 ↔ ↑c ∈ boundaries`. -/
theorem intHomology_mk_eq_zero_iff {X : TopCat} {n : ℕ} (c : SingularHomologyInt.cycles X n) :
    SingularHomologyInt.Homology.mk X n c = 0 ↔
      (c : SingularHomologyInt.SingularChainInt X n) ∈ SingularHomologyInt.boundaries X n := by
  rw [SingularHomologyInt.Homology.mk]
  constructor
  · intro h
    have := (Submodule.Quotient.mk_eq_zero _).mp h
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using this
  · intro h
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using h

/-- **Mod-2 homology class of a boundary is zero** (iff form): `[c] = 0 ↔ ↑c ∈ boundaries`. -/
theorem mod2Homology_mk_eq_zero_iff {X : TopCat} {n : ℕ} (c : SingularHomologyMod2.cycles X n) :
    SingularHomologyMod2.Homology.mk X n c = 0 ↔
      (c : SingularHomologyMod2.SingularChain X n) ∈ SingularHomologyMod2.boundaries X n := by
  rw [SingularHomologyMod2.Homology.mk]
  constructor
  · intro h
    have := (Submodule.Quotient.mk_eq_zero _).mp h
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using this
  · intro h
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using h

/-- `(2:ℤ) • [a] = [2 • a]` for an integral homology class. -/
theorem intHomology_two_smul_mk {X : TopCat} {n : ℕ} (a : SingularHomologyInt.cycles X n) :
    (2 : ℤ) • SingularHomologyInt.Homology.mk X n a
      = SingularHomologyInt.Homology.mk X n ((2 : ℤ) • a) := rfl

/-- If `2 • w = ∂z̃` then `w` is an integral cycle (torsion-freeness closes the `∂w = 0` step). -/
theorem intCycle_of_two_smul_boundary {X : TopCat} {n : ℕ}
    (w : SingularHomologyInt.SingularChainInt X n)
    (zt : SingularHomologyInt.SingularChainInt X (n + 1))
    (h2w : (2 : ℤ) • w = SingularHomologyInt.chainBoundary X n zt) :
    w ∈ SingularHomologyInt.cycles X n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    refine LinearMap.mem_ker.mpr ?_
    apply intChain_two_smul_eq_zero
    rw [← map_smul, h2w, SingularHomologyInt.boundary_comp_boundary]

/-! ## §2. The general lift/halve/bound lemma -/

/-- **`Hₙ₊₁(X;ℤ) = 0` and `Hₙ(X;ℤ)` 2-torsion-free ⟹ `Hₙ₊₁(X;ℤ/2) = 0`.** The chain-level UCT
ingredient, proved by the direct lift/halve/bound argument (no Bockstein LES). -/
theorem homologyMod2_top_eq_zero_of_int {X : TopCat} (n : ℕ)
    (hHtop : ∀ x : SingularHomologyInt.Homology X (n + 1), x = 0)
    (hHtors : ∀ x : SingularHomologyInt.Homology X n, (2 : ℤ) • x = 0 → x = 0)
    (y : SingularHomologyMod2.Homology X (n + 1)) : y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- z : cycles X (n+1); ↑z its underlying chain
  have hz : SingularHomologyMod2.chainBoundary X n (z : _) = 0 := z.2
  -- lift
  have hred_zt : SingularHomologyInt.redChain X (n + 1) (intLift (z : _)) = (z : _) :=
    redChain_intLift _
  -- d := ∂z̃, reduces to 0 mod 2
  have hredd : SingularHomologyInt.redChain X n
      (SingularHomologyInt.chainBoundary X n (intLift (z : _))) = 0 := by
    rw [SingularHomologyInt.redChain_chainBoundary, hred_zt, hz]
  -- 2 ∣ (∂z̃) σ for every σ
  have hdvd : ∀ σ, (2 : ℤ) ∣ SingularHomologyInt.chainBoundary X n (intLift (z : _)) σ := by
    intro σ
    have h0 : ((SingularHomologyInt.chainBoundary X n (intLift (z : _)) σ : ℤ) : ZMod 2) = 0 := by
      rw [← redChain_apply, hredd]; simp
    exact_mod_cast
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (SingularHomologyInt.chainBoundary X n (intLift (z : _)) σ) 2).mp h0
  -- w := (∂z̃)/2 pointwise; 2 • w = ∂z̃
  have h2w : (2 : ℤ) • (Finsupp.mapRange (fun k : ℤ => k / 2) (by simp)
      (SingularHomologyInt.chainBoundary X n (intLift (z : _))))
      = SingularHomologyInt.chainBoundary X n (intLift (z : _)) := by
    refine Finsupp.ext (fun σ => ?_)
    rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hdvd σ)
  -- w is an integral cycle
  have hwcyc : (Finsupp.mapRange (fun k : ℤ => k / 2) (by simp)
      (SingularHomologyInt.chainBoundary X n (intLift (z : _))))
      ∈ SingularHomologyInt.cycles X n :=
    intCycle_of_two_smul_boundary _ (intLift (z : _)) h2w
  -- 2 • [w] = 0
  have h2clw : (2 : ℤ) • SingularHomologyInt.Homology.mk X n ⟨_, hwcyc⟩ = 0 := by
    rw [intHomology_two_smul_mk, intHomology_mk_eq_zero_iff]
    rw [SetLike.val_smul, h2w]
    exact ⟨intLift (z : _), rfl⟩
  -- [w] = 0 ⟹ w ∈ boundaries
  have hclw0 : SingularHomologyInt.Homology.mk X n ⟨_, hwcyc⟩ = 0 := hHtors _ h2clw
  have hwb : (Finsupp.mapRange (fun k : ℤ => k / 2) (by simp)
      (SingularHomologyInt.chainBoundary X n (intLift (z : _))))
      ∈ SingularHomologyInt.boundaries X n :=
    (intHomology_mk_eq_zero_iff ⟨_, hwcyc⟩).mp hclw0
  obtain ⟨u, hu⟩ := hwb
  -- z̃ − 2u is an integral cycle
  have hcyc2 : SingularHomologyInt.chainBoundary X n (intLift (z : _) - (2 : ℤ) • u) = 0 := by
    rw [map_sub, map_smul, hu, h2w, sub_self]
  have hcyc2mem : (intLift (z : _) - (2 : ℤ) • u) ∈ SingularHomologyInt.cycles X (n + 1) :=
    LinearMap.mem_ker.mpr hcyc2
  -- [z̃ − 2u] = 0 ⟹ z̃ − 2u ∈ boundaries
  have hcl2_0 : SingularHomologyInt.Homology.mk X (n + 1) ⟨_, hcyc2mem⟩ = 0 := hHtop _
  have hz2u_b : (intLift (z : _) - (2 : ℤ) • u) ∈ SingularHomologyInt.boundaries X (n + 1) :=
    (intHomology_mk_eq_zero_iff ⟨_, hcyc2mem⟩).mp hcl2_0
  obtain ⟨v, hv⟩ := hz2u_b
  -- reduce mod 2: z = ∂(redChain v), a mod-2 boundary
  have hzc_b : (z : SingularHomologyMod2.SingularChain X (n + 1))
      ∈ SingularHomologyMod2.boundaries X (n + 1) := by
    refine ⟨SingularHomologyInt.redChain X (n + 2) v, ?_⟩
    rw [← SingularHomologyInt.redChain_chainBoundary, hv, map_sub, hred_zt, map_zsmul,
      two_zsmul_mod2_eq_zero, sub_zero]
  show SingularHomologyMod2.Homology.mk X (n + 1) z = 0
  exact (mod2Homology_mk_eq_zero_iff z).mpr hzc_b

/-! ## §3. Application to `S²×S²` and Root 2 -/

/-- `Hₙ(S²×S²; ℤ)` is 2-torsion-free at `n = 2`, via `sphereProdHTwoEquivInt : H₂ ≃ₗ[ℤ] ℤ × ℤ`
(`ℤ × ℤ` is 2-torsion-free) — the second integral input to the general lift/halve lemma. -/
theorem sphereProd_intHomology_two_torsionFree
    (x : SingularHomologyInt.Homology (TopCat.of SphereProd) 2) (hx : (2 : ℤ) • x = 0) : x = 0 := by
  apply SphereProdHTwoInt.sphereProdHTwoEquivInt.injective
  rw [map_zero]
  have h2 : (2 : ℤ) • SphereProdHTwoInt.sphereProdHTwoEquivInt x = 0 := by
    rw [← map_smul, hx, map_zero]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **`H₃(S²×S²; ℤ/2) = 0`** — the missing Root-2 input. From the general lift/halve lemma at
`n = 2`, `X = S²×S²`, fed the two banked integral facts `H₃(S²×S²;ℤ) = 0`
(`sphereProd_homology_three_eq_zero`) and `H₂(S²×S²;ℤ)` 2-torsion-free
(`sphereProd_intHomology_two_torsionFree`). -/
theorem sphereProd_homologyMod2_three_eq_zero
    (y : SingularHomologyMod2.Homology (TopCat.of SphereProd) 3) : y = 0 :=
  homologyMod2_top_eq_zero_of_int 2 SphereProdHFourInt.sphereProd_homology_three_eq_zero
    sphereProd_intHomology_two_torsionFree y

/-- **`H₃(S²×S²; ℤ/2) = 0` on the boundary set** — transported from
`sphereProd_homologyMod2_three_eq_zero` along the boundary-inclusion homeomorphism
`sphereDiskInclHomeo`. This is the second squeeze input for Root 2. -/
instance : Subsingleton (SingularHomologyMod2.Homology
    (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 3) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ w : SingularHomologyMod2.Homology
      (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 3, w = 0 := by
    intro w
    have hpre : (homeoHomologyEquiv sphereDiskInclHomeo 3).symm w = 0 :=
      sphereProd_homologyMod2_three_eq_zero _
    calc w = homeoHomologyEquiv sphereDiskInclHomeo 3
              ((homeoHomologyEquiv sphereDiskInclHomeo 3).symm w) :=
            (LinearEquiv.apply_symm_apply _ _).symm
      _ = homeoHomologyEquiv sphereDiskInclHomeo 3 0 := by rw [hpre]
      _ = 0 := map_zero _
  rw [key a, key b]

/-- **Root 2 — `Subsingleton (RelativeHomology sphereDiskBoundarySet 4)`.** The pair-LES squeeze
`subsingleton_relativeHomology_of_squeeze` at `X = S²×D³`, `S = S²×S²`, `n = 3`, using the banked
Bonus `H₄(S²×D³;ℤ/2) = 0` and the freshly-closed `H₃(S²×S²;ℤ/2) = 0` above. Closes the last atom of
the `S²×D³` coboundary consumed by `PinPlusKTSphereProdCohomology`. -/
instance rootTwo_subsingleton :
    Subsingleton (SingularRelativeHomologyMod2.RelativeHomology
      (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4) := by
  haveI : Subsingleton (SingularHomologyMod2.Homology (TopCat.of SphereDisk) (3 + 1)) :=
    (inferInstance : Subsingleton (SingularHomologyMod2.Homology (TopCat.of SphereDisk) 4))
  exact PinPlusKTSphereProdHomologyRoots.subsingleton_relativeHomology_of_squeeze
    (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3

end SKEFTHawking.SphereProdHThreeMod2
