/-
# Phase 5q.H · Root 2 companion — mod-2 `dim H₂(S²×S²;ℤ/2) = 2` (the rank UCT)

`SphereProdHThreeMod2` closed the VANISHING case of the ℤ→ℤ/2 lift/halve argument
(`homologyMod2_top_eq_zero_of_int`: `Hₙ₊₁(X;ℤ)=0` ∧ `Hₙ(X;ℤ)` 2-tf ⟹ `Hₙ₊₁(X;ℤ/2)=0`).
This module GENERALISES that argument from the vanishing case to a genuine **rank** identity, the
chain-level Universal-Coefficient ingredient at free rank `r`:

> if `Hₙ(X;ℤ)` is 2-torsion-free then the comparison map `redHomology X (n+1)` is **surjective**
> with **kernel exactly `2·Hₙ₊₁(X;ℤ)`** — i.e. it descends to `Hₙ₊₁(X;ℤ)/2 ≃ Hₙ₊₁(X;ℤ/2)`
> (`Tor(Hₙ, ℤ/2) = 0` from 2-torsion-freeness, `⊗ℤ/2` realised by `redHomology`).

Both halves reuse the banked lift/halve scaffolding of `SphereProdHThreeMod2` (`intLift`,
`redChain_intLift`, `intCycle_of_two_smul_boundary`, `intChain_two_smul_eq_zero`, the
`*_mk_eq_zero_iff` lemmas). No new Mayer–Vietoris.

## Application to `S²×S²` at degree `2`

`Hₙ₊₁(X;ℤ)` free of rank `r` ⟹ `dim_{ℤ/2} Hₙ₊₁(X;ℤ/2) = r`. At `X = S²×S²`, `n+1 = 2`:
`H₂(S²×S²;ℤ) ≅ ℤ²` free rank 2 (`SphereProdHTwoInt.sphereProdHTwoEquivInt`) and `H₁ = 0`
(`SphereProdHOneInt`, hence 2-torsion-free) give

> **`finrank_sphereProd_homologyMod2_two`** — `dim_{ℤ/2} H₂(S²×S²;ℤ/2) = 2`.

The rank-2 endgame builds the explicit `ℤ/2`-linear bijection `(ℤ/2)² ≃ H₂(S²×S²;ℤ/2)`,
`(a,c) ↦ a·[S²×pt] + c·[pt×S²]` (reductions of the two integral generators), whose surjectivity
is `redHomology` surjectivity and whose injectivity is the `2·H₂` kernel identity.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdHThreeMod2
import SKEFTHawking.SphereProdHOneInt

namespace SKEFTHawking.SphereProdHTwoMod2

open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SphereProdHThreeMod2

noncomputable section

/-! ## §1. The rank UCT core — surjectivity and kernel of `redHomology`. -/

/-- **A chain reducing to `0` mod 2 is exactly `2·(a chain)`** — the pointwise halving. Isolated as
its own declaration (own heartbeat budget) so the callers stay light. -/
theorem exists_half_of_redChain_eq_zero {X : TopCat} (k : ℕ)
    (d : SingularHomologyInt.SingularChainInt X k)
    (hd : SingularHomologyInt.redChain X k d = 0) : ∃ w, (2 : ℤ) • w = d := by
  have hdvd : ∀ σ, (2 : ℤ) ∣ d σ := by
    intro σ
    have h0 : ((d σ : ℤ) : ZMod 2) = 0 := by rw [← redChain_apply, hd]; simp
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (d σ) 2).mp h0
  refine ⟨Finsupp.mapRange (fun k : ℤ => k / 2) (by simp) d, Finsupp.ext (fun σ => ?_)⟩
  rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel' (hdvd σ)

/-- **Every mod-2 cycle in degree `n+1` lifts to an integral cycle whose reduction is that cycle**,
given `Hₙ(X;ℤ)` 2-torsion-free. The lift/halve/bound argument of `homologyMod2_top_eq_zero_of_int`,
stopped one step early: instead of concluding the class is `0` from `Hₙ₊₁(X;ℤ)=0`, it returns the
integral cycle `z̃ − 2u` whose mod-2 reduction is `z`. -/
theorem exists_intCycle_redChain_eq {X : TopCat} (n : ℕ)
    (hHtors : ∀ x : SingularHomologyInt.Homology X n, (2 : ℤ) • x = 0 → x = 0)
    (z : SingularHomologyMod2.cycles X (n + 1)) :
    ∃ c : SingularHomologyInt.cycles X (n + 1),
      SingularHomologyInt.redChain X (n + 1) (c : _) = (z : _) := by
  have hz : SingularHomologyMod2.chainBoundary X n (z : _) = 0 := z.2
  have hred_zt : SingularHomologyInt.redChain X (n + 1) (intLift (z : _)) = (z : _) :=
    redChain_intLift _
  have hredd : SingularHomologyInt.redChain X n
      (SingularHomologyInt.chainBoundary X n (intLift (z : _))) = 0 := by
    rw [SingularHomologyInt.redChain_chainBoundary, hred_zt, hz]
  obtain ⟨w, hw⟩ := exists_half_of_redChain_eq_zero n _ hredd
  have hwcyc : w ∈ SingularHomologyInt.cycles X n :=
    intCycle_of_two_smul_boundary w (intLift (z : _)) hw
  have h2clw : (2 : ℤ) • SingularHomologyInt.Homology.mk X n ⟨w, hwcyc⟩ = 0 := by
    rw [intHomology_two_smul_mk, intHomology_mk_eq_zero_iff]
    exact ⟨intLift (z : _), by rw [SetLike.val_smul]; exact hw.symm⟩
  have hclw0 : SingularHomologyInt.Homology.mk X n ⟨w, hwcyc⟩ = 0 := hHtors _ h2clw
  obtain ⟨u, hu⟩ := (intHomology_mk_eq_zero_iff ⟨w, hwcyc⟩).mp hclw0
  have hcyc2 : SingularHomologyInt.chainBoundary X n (intLift (z : _) - (2 : ℤ) • u) = 0 := by
    rw [map_sub, map_smul, hu]
    exact sub_eq_zero.mpr hw.symm
  have hcyc2mem : (intLift (z : _) - (2 : ℤ) • u) ∈ SingularHomologyInt.cycles X (n + 1) :=
    LinearMap.mem_ker.mpr hcyc2
  have hfinal : SingularHomologyInt.redChain X (n + 1) (intLift (z : _) - (2 : ℤ) • u)
      = (z : _) := by
    rw [map_sub, hred_zt, map_zsmul, two_zsmul_mod2_eq_zero, sub_zero]
  exact ⟨⟨_, hcyc2mem⟩, hfinal⟩

/-- **`redHomology X (n+1)` is surjective** when `Hₙ(X;ℤ)` is 2-torsion-free. Direct from
`exists_intCycle_redChain_eq`: any mod-2 class is `[z]`, whose integral lift `c` satisfies
`redHomology [c] = [redChain c] = [z]`. -/
theorem redHomology_surjective {X : TopCat} (n : ℕ)
    (hHtors : ∀ x : SingularHomologyInt.Homology X n, (2 : ℤ) • x = 0 → x = 0) :
    Function.Surjective (SingularHomologyInt.redHomology X (n + 1)) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨c, hc⟩ := exists_intCycle_redChain_eq n hHtors z
  refine ⟨SingularHomologyInt.Homology.mk X (n + 1) c, ?_⟩
  rw [SingularHomologyInt.redHomology_mk]
  exact congrArg _ (Subtype.ext hc)

/-- **The kernel of `redHomology X (n+1)` is contained in `2·Hₙ₊₁(X;ℤ)`** (unconditional): if
`redHomology [c] = 0` then `[c] = 2·d`. The halve/bound argument: `redChain c = ∂b` mod 2 lifts to
`∂(intLift b)`, whose integral difference `∂(intLift b) − c` reduces to `0` hence is `2·g`, so
`c + 2·g = ∂(intLift b)` is a boundary and `[c] = 2·(−[g])`. -/
theorem exists_two_smul_of_redHomology_eq_zero {X : TopCat} (n : ℕ)
    (x : SingularHomologyInt.Homology X (n + 1))
    (hx : SingularHomologyInt.redHomology X (n + 1) x = 0) :
    ∃ d, x = (2 : ℤ) • d := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show ∃ d, SingularHomologyInt.Homology.mk X (n + 1) c = (2 : ℤ) • d
  have hx' : SingularHomologyMod2.Homology.mk X (n + 1)
      (SingularHomologyInt.redCyclesHom X (n + 1) c) = 0 := by
    rw [← SingularHomologyInt.redHomology_mk]; exact hx
  have hb := (mod2Homology_mk_eq_zero_iff (SingularHomologyInt.redCyclesHom X (n + 1) c)).mp hx'
  obtain ⟨b, hb⟩ := hb
  -- b : mod-2 chain in degree n+2, ∂b = redChain c
  have hrb : SingularHomologyInt.redChain X (n + 2) (intLift b) = b := redChain_intLift _
  have hredc : SingularHomologyInt.redChain X (n + 1)
      (SingularHomologyInt.chainBoundary X (n + 1) (intLift b))
      = SingularHomologyInt.redChain X (n + 1) (c : _) := by
    rw [SingularHomologyInt.redChain_chainBoundary, hrb, hb]
    rfl
  -- `D := ∂(intLift b) − c` reduces to 0 mod 2
  set D := SingularHomologyInt.chainBoundary X (n + 1) (intLift b)
    - (c : SingularHomologyInt.SingularChainInt X (n + 1)) with hD
  have hredsub : SingularHomologyInt.redChain X (n + 1) D = 0 := by
    rw [hD, map_sub, hredc, sub_self]
  have hdvd : ∀ σ, (2 : ℤ) ∣ D σ := by
    intro σ
    have h0 : ((D σ : ℤ) : ZMod 2) = 0 := by rw [← redChain_apply, hredsub]; simp
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (D σ) 2).mp h0
  set g := Finsupp.mapRange (fun k : ℤ => k / 2) (by simp) D with hg
  have h2g : (2 : ℤ) • g = D := by
    refine Finsupp.ext (fun σ => ?_)
    rw [hg, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hdvd σ)
  -- 2·g is a cycle (c is a cycle, ∂(intLift b) is a cycle) ⟹ g is a cycle
  have hc0 : SingularHomologyInt.chainBoundary X n (c : _) = 0 := LinearMap.mem_ker.mp c.2
  have h2g_cyc : SingularHomologyInt.chainBoundary X n ((2 : ℤ) • g) = 0 := by
    rw [h2g, hD, map_sub, SingularHomologyInt.boundary_comp_boundary, hc0, sub_zero]
  have hg_cyc : g ∈ SingularHomologyInt.cycles X (n + 1) := by
    refine LinearMap.mem_ker.mpr ?_
    apply intChain_two_smul_eq_zero
    rw [← map_smul]; exact h2g_cyc
  refine ⟨-SingularHomologyInt.Homology.mk X (n + 1) ⟨g, hg_cyc⟩, ?_⟩
  have hbnd : (c : SingularHomologyInt.SingularChainInt X (n + 1)) + (2 : ℤ) • g
      ∈ SingularHomologyInt.boundaries X (n + 1) :=
    LinearMap.mem_range.mpr ⟨intLift b, by rw [h2g, hD]; abel⟩
  have hmk0 : SingularHomologyInt.Homology.mk X (n + 1)
      (c + (2 : ℤ) • ⟨g, hg_cyc⟩) = 0 := by
    rw [intHomology_mk_eq_zero_iff]
    simpa using hbnd
  have hadd : SingularHomologyInt.Homology.mk X (n + 1)
      (c + (2 : ℤ) • ⟨g, hg_cyc⟩)
      = SingularHomologyInt.Homology.mk X (n + 1) c
        + (2 : ℤ) • SingularHomologyInt.Homology.mk X (n + 1) ⟨g, hg_cyc⟩ := by
    rw [intHomology_two_smul_mk]; rfl
  rw [hmk0] at hadd
  rw [smul_neg]
  exact eq_neg_of_add_eq_zero_left hadd.symm

/-! ## §2. Application to `S²×S²` at degree 2 — `dim H₂(S²×S²;ℤ/2) = 2`. -/

/-- The reduction of the first integral generator `[S²×pt]` of `H₂(S²×S²;ℤ)` into `H₂(S²×S²;ℤ/2)`. -/
noncomputable def gen0 : SingularHomologyMod2.Homology (TopCat.of SphereProd) 2 :=
  SingularHomologyInt.redHomology (TopCat.of SphereProd) 2
    (SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (1, 0))

/-- The reduction of the second integral generator `[pt×S²]` of `H₂(S²×S²;ℤ)` into `H₂(S²×S²;ℤ/2)`. -/
noncomputable def gen1 : SingularHomologyMod2.Homology (TopCat.of SphereProd) 2 :=
  SingularHomologyInt.redHomology (TopCat.of SphereProd) 2
    (SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (0, 1))

/-- `H₁(S²×S²;ℤ)` is 2-torsion-free (it vanishes, `SphereProdHOneInt`). -/
theorem sphereProd_intHomology_one_torsionFree
    (x : SingularHomologyInt.Homology (TopCat.of SphereProd) 1) (_ : (2 : ℤ) • x = 0) : x = 0 :=
  Subsingleton.elim x 0

/-- `redHomology (e.symm (s,m)) = (s:ℤ/2)·gen0 + (m:ℤ/2)·gen1` — the reduction of an integral class
written in the `ℤ²` basis, pushed to the `ℤ/2`-linear combination of the two mod-2 generators. -/
theorem redHomology_symm_apply (s m : ℤ) :
    SingularHomologyInt.redHomology (TopCat.of SphereProd) 2
        (SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (s, m))
      = (s : ZMod 2) • gen0 + (m : ZMod 2) • gen1 := by
  have h1 : SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (s, m)
      = s • SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (1, 0)
        + m • SphereProdHTwoInt.sphereProdHTwoEquivInt.symm (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [h1, map_add, map_zsmul, map_zsmul, gen0, gen1,
    Int.cast_smul_eq_zsmul (ZMod 2) s, Int.cast_smul_eq_zsmul (ZMod 2) m]

/-- **`dim_{ℤ/2} H₂(S²×S²;ℤ/2) = 2`.** The `ℤ/2`-linear map `(a,c) ↦ a·gen0 + c·gen1` from `(ℤ/2)²`
is a bijection: surjective by `redHomology` surjectivity (`H₁(S²×S²;ℤ)` 2-torsion-free), injective by
the `2·H₂` kernel identity. So `H₂(S²×S²;ℤ/2) ≃ₗ (ℤ/2)²` and the rank is `2`. -/
theorem finrank_sphereProd_homologyMod2_two :
    Module.finrank (ZMod 2) (SingularHomologyMod2.Homology (TopCat.of SphereProd) 2) = 2 := by
  set V := SingularHomologyMod2.Homology (TopCat.of SphereProd) 2
  let Ψ : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] V :=
    LinearMap.coprod (LinearMap.toSpanSingleton (ZMod 2) V gen0)
      (LinearMap.toSpanSingleton (ZMod 2) V gen1)
  have hΨ : ∀ p : ZMod 2 × ZMod 2, Ψ p = p.1 • gen0 + p.2 • gen1 := fun p => rfl
  have hsurj : Function.Surjective Ψ := by
    intro v
    obtain ⟨x, hx⟩ := redHomology_surjective (X := TopCat.of SphereProd) 1
      sphereProd_intHomology_one_torsionFree v
    refine ⟨(((SphereProdHTwoInt.sphereProdHTwoEquivInt x).1 : ZMod 2),
      ((SphereProdHTwoInt.sphereProdHTwoEquivInt x).2 : ZMod 2)), ?_⟩
    rw [hΨ, ← redHomology_symm_apply,
      show ((SphereProdHTwoInt.sphereProdHTwoEquivInt x).1,
          (SphereProdHTwoInt.sphereProdHTwoEquivInt x).2)
          = SphereProdHTwoInt.sphereProdHTwoEquivInt x from rfl,
      SphereProdHTwoInt.sphereProdHTwoEquivInt.symm_apply_apply]
    exact hx
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    rintro ⟨a, c⟩ hac
    rw [hΨ] at hac
    -- a·gen0 + c·gen1 = 0 ⟹ redHomology (e.symm (a.val, c.val)) = 0
    have hac' : SingularHomologyInt.redHomology (TopCat.of SphereProd) 2
        (SphereProdHTwoInt.sphereProdHTwoEquivInt.symm ((a.val : ℤ), (c.val : ℤ))) = 0 := by
      rw [redHomology_symm_apply]
      simpa [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id] using hac
    obtain ⟨d, hd⟩ :=
      exists_two_smul_of_redHomology_eq_zero (X := TopCat.of SphereProd) 1 _ hac'
    -- e.symm (a.val, c.val) = 2·d ⟹ (a.val, c.val) = 2·(e d)
    have hval : ((a.val : ℤ), (c.val : ℤ))
        = (2 : ℤ) • SphereProdHTwoInt.sphereProdHTwoEquivInt d := by
      have := congrArg SphereProdHTwoInt.sphereProdHTwoEquivInt hd
      rwa [SphereProdHTwoInt.sphereProdHTwoEquivInt.apply_symm_apply, map_zsmul] at this
    have ha2 : (2 : ℤ) ∣ (a.val : ℤ) := ⟨(SphereProdHTwoInt.sphereProdHTwoEquivInt d).1, by
      have := congrArg Prod.fst hval; simpa [Prod.smul_fst, smul_eq_mul] using this⟩
    have hc2 : (2 : ℤ) ∣ (c.val : ℤ) := ⟨(SphereProdHTwoInt.sphereProdHTwoEquivInt d).2, by
      have := congrArg Prod.snd hval; simpa [Prod.smul_snd, smul_eq_mul] using this⟩
    have ha2n : 2 ∣ a.val := by exact_mod_cast ha2
    have hc2n : 2 ∣ c.val := by exact_mod_cast hc2
    have hva : a.val = 0 := by have := ZMod.val_lt a; omega
    have hvc : c.val = 0 := by have := ZMod.val_lt c; omega
    have haa : a = 0 := by
      have h := ZMod.natCast_rightInverse (n := 2) a
      rw [hva] at h; simpa using h.symm
    have hcc : c = 0 := by
      have h := ZMod.natCast_rightInverse (n := 2) c
      rw [hvc] at h; simpa using h.symm
    exact Prod.ext haa hcc
  have : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) :=
    (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm.finrank_eq
  rw [this, Module.finrank_prod, Module.finrank_self]

end

end SKEFTHawking.SphereProdHTwoMod2
