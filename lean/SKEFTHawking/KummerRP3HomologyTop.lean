import Mathlib
import SKEFTHawking.KummerRP3HomologySolve
import SKEFTHawking.KummerRP3TauHomotopy

/-!
# `H₃(ℝP³;ℤ) ≅ ℤ` and `Hₙ(ℝP³;ℤ) = 0` for `n ≥ 4` — the top-degree Smith solve

The upward half of the `H_*(ℝP³;ℤ)` computation, chaining the interlocking integral Smith long
exact sequences (`KummerRP3SmithSES`) against the **one geometric termination input**
`H₄(ℝP³;ℤ) = H₅(ℝP³;ℤ) = 0` (below dimension the two LESes alone cannot pin the top — the
`ℝP^∞`-pattern survives both, so a genuine geometric input is required; that input is the 4-chart
good-cover Mayer–Vietoris telescope, discharged separately).

Given the termination hypotheses `h4`, `h5`, this module proves:

* **`hmlB_three_eq_zero` / `hmlB_four_eq_zero`** — `H₃(B;ℤ) = H₄(B;ℤ) = 0` (the difference
  subcomplex terminates);
* **`rp3H3EquivInt`** — `H₃(ℝP³;ℤ) ≅ ℤ`, transported from `H₃(A) ≅ H₃(S³) ≅ ℤ` along the integral
  transfer chain isomorphism `C(ℝP³) ≅ A = N·C(S³)`;
* **`rp3_hml_high` / `rp3_homology_high`** — `Hₙ(ℝP³;ℤ) = 0` for `n ≥ 4` (the two-step recursion
  `Hₙ(ℝP³) ≅ Hₙ₋₂(ℝP³)` off the banked S³ high-vanishing).

The core algebraic engine is `A ≅ C(ℝP³)`: the integral transfer `tr` is a levelwise chain
isomorphism onto the norm subcomplex `A` (`range tr = range N = A`, `tr` injective), so
`Hₙ(A) ≅ Hₙ(ℝP³)` in every degree (`Hmap_bijective_of_bijective`); combined with the
`τ_* = 1` odd-sphere facts (`diffHom_S3_eq_zero`) it collapses the Smith ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top RP3top negS3C mkRP3C diffChain normChain diffHom)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt Homology.mapInt)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3SmithSES
open SKEFTHawking.KummerRP3HomologySolve
open SKEFTHawking.KummerRP3TauHomotopy (diffHom_S3_eq_zero)
open SKEFTHawking.KummerRP3TransferInt (transferChainInt range_transferChainInt_eq_range_normChain
  transferChainInt_injective chainBoundary_transferChainInt)

namespace SKEFTHawking.KummerRP3HomologyTop

noncomputable section

/-! ## §0. The middle-term exactness of both Smith SESs (engine `exact_Hmap_Hmap`) -/

/-- SES-III LES exactness at `Hₙ(S³)`: `ker H(p₊) = im H(B ↪ C)`. -/
theorem exact_inclBH_projH (n : ℕ) : Function.Exact (inclBH n) (projH n) :=
  exact_Hmap_Hmap hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- SES-I LES exactness at `Hₙ(S³)`: `ker H(D') = im H(A ↪ C)`. -/
theorem exact_inclAH_diffH (n : ℕ) : Function.Exact (inclAH n) (diffH n) :=
  exact_Hmap_Hmap hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-! ## §1. The banked `S³` high-degree vanishing, in engine `Hml` form -/

/-- Transported sphere input: `Hml`-form `Hₚ(S³;ℤ) = 0` for `p > 3`. -/
theorem hml_s3_high (p : ℕ) (hp : 3 < p) (x : Hml (chainBoundary S3top) p) : x = 0 := by
  have h := SKEFTHawking.KummerRP3SphereHomeo.s3_homology_high p hp (hmlEquivHomology S3top p x)
  have h2 := (hmlEquivHomology S3top p).symm_apply_apply x
  rw [h, map_zero] at h2
  exact h2.symm

/-! ## §2. The transfer chain isomorphism `C(ℝP³) ≅ A` and `Hₙ(A) ≅ Hₙ(ℝP³)` -/

/-- The integral transfer, corestricted to its range `A = N·C(S³)`: a levelwise linear map
`C(ℝP³) → A`. -/
def trA (n : ℕ) : SingularChainInt RP3top n →ₗ[ℤ] Ac n :=
  (transferChainInt n).codRestrict (Amod n) (fun c => by
    have : transferChainInt n c ∈ LinearMap.range (transferChainInt n) := ⟨c, rfl⟩
    rwa [range_transferChainInt_eq_range_normChain] at this)

/-- `tr : C(ℝP³) → A` is a chain map (it commutes with the boundary). -/
theorem trA_chain (n : ℕ) (x : SingularChainInt RP3top (n + 1)) :
    dA n (trA (n + 1) x) = trA n (chainBoundary RP3top n x) :=
  Subtype.ext (chainBoundary_transferChainInt n x)

/-- `tr : C(ℝP³) → A` is a levelwise isomorphism (injective + surjective onto `A`). -/
theorem trA_bijective (n : ℕ) : Function.Bijective (trA n) := by
  constructor
  · intro a b hab
    exact transferChainInt_injective n (congrArg Subtype.val hab)
  · rintro ⟨y, hy⟩
    rw [Amod, ← range_transferChainInt_eq_range_normChain] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩

/-- **`Hₙ(ℝP³;ℤ) ≅ Hₙ(A;ℤ)`** (engine form) — the integral transfer is a levelwise chain iso onto
the norm subcomplex, hence a homology iso in every degree. -/
def rHmlEquivAHml (n : ℕ) : Hml (chainBoundary RP3top) n ≃ₗ[ℤ] Hml dA n :=
  LinearEquiv.ofBijective (Hmap trA_chain n) (Hmap_bijective_of_bijective trA_chain trA_bijective n)

/-- `Hₙ(A;ℤ) = 0` whenever `Hₙ(ℝP³;ℤ) = 0` (engine form), through the transfer iso. -/
theorem hml_a_eq_zero_of {n : ℕ} (hr : ∀ x : Hml (chainBoundary RP3top) n, x = 0)
    (x : Hml dA n) : x = 0 := by
  have h := hr ((rHmlEquivAHml n).symm x)
  have h2 := congrArg (rHmlEquivAHml n) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

/-- `H₂(A;ℤ) = 0` (the banked `H₂(ℝP³;ℤ) = 0`, through the transfer iso). -/
theorem hml_a_two_eq_zero (x : Hml dA 2) : x = 0 :=
  hml_a_eq_zero_of hml_rp3_two_eq_zero x

/-! ## §3. The composition relation `H(B ↪ C) ∘ H(D') = 0` -/

/-- **`H(B ↪ C) ∘ H(D') = 0` on `Hₙ₊₁(S³)`** — the SES-I epi leg `H(D')` followed by the SES-III
mono leg `H(B ↪ C)` sends `[z]` to the class of `D z = z − τ_# z`, which is `D_*[z] = 0` on the odd
sphere (`diffHom_S3_eq_zero`, `τ_* = 1`). -/
theorem inclBH_diffH_eq_zero (n : ℕ) (x : Hml (chainBoundary S3top) (n + 1)) :
    inclBH (n + 1) (diffH (n + 1) x) = 0 := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary S3top) (n + 1) x
  rw [show inclBH (n + 1) (diffH (n + 1) (Hml.mk (chainBoundary S3top) (n + 1) z))
        = Hml.mk (chainBoundary S3top) (n + 1)
            (cyclesMap hf_inclB (n + 1) (cyclesMap hg_diff (n + 1) z)) from rfl,
      Hml.mk_eq_zero_iff]
  -- Goal: `D z = ↑(cyclesMap hf_inclB (cyclesMap hg_diff z)) ∈ engine boundaries`.
  have hz2 : (z : SingularChainInt S3top (n + 1))
      ∈ SKEFTHawking.SingularHomologyInt.cycles S3top (n + 1) := z.2
  set z' : SKEFTHawking.SingularHomologyInt.cycles S3top (n + 1) :=
    ⟨(z : SingularChainInt S3top (n + 1)), hz2⟩ with hz'def
  have hd : diffHom negS3C (n + 1)
      (SKEFTHawking.SingularHomologyInt.Homology.mk S3top (n + 1) z') = 0 :=
    diffHom_S3_eq_zero n _
  rw [show diffHom negS3C (n + 1)
          (SKEFTHawking.SingularHomologyInt.Homology.mk S3top (n + 1) z')
        = SKEFTHawking.SingularHomologyInt.Homology.mk S3top (n + 1) z'
          - Homology.mapInt negS3C (n + 1)
              (SKEFTHawking.SingularHomologyInt.Homology.mk S3top (n + 1) z') from rfl,
      SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk, sub_eq_zero] at hd
  have hmem := Submodule.mem_comap.mp ((Submodule.Quotient.eq _).mp hd)
  have hcoe : (SKEFTHawking.SingularHomologyInt.cycles S3top (n + 1)).subtype
        (z' - SKEFTHawking.SingularFunctorialityInt.cyclesMapInt negS3C (n + 1) z')
      = diffChain negS3C (n + 1) (z : SingularChainInt S3top (n + 1)) := by
    show (z : SingularChainInt S3top (n + 1))
        - mapChainInt negS3C (n + 1) (z : SingularChainInt S3top (n + 1))
      = diffChain negS3C (n + 1) (z : SingularChainInt S3top (n + 1))
    rw [diffChain]; simp only [LinearMap.sub_apply, LinearMap.id_apply]
  rw [hcoe] at hmem
  show diffChain negS3C (n + 1) (z : SingularChainInt S3top (n + 1))
      ∈ ChainComplexLESInt.boundaries (chainBoundary S3top) (n + 1)
  exact hmem

/-! ## §4. `H₄(B;ℤ) = 0` and `H₃(B;ℤ) = 0` — the difference subcomplex terminates -/

/-- **`H₄(B;ℤ) = 0`** (given `H₅(ℝP³) = 0`): SES-III exactness at `H₄(B)`, with `H₄(S³) = 0`, makes
`H₄(B) = im(δ₄)`, and `δ₄` lands in `H₅(ℝP³) = 0`. -/
theorem hmlB_four_eq_zero (h5 : ∀ x : Hml (chainBoundary RP3top) 5, x = 0) (x : Hml dB 4) : x = 0 := by
  have hs : inclBH 4 x = 0 := hml_s3_high 4 (by norm_num) (inclBH 4 x)
  obtain ⟨y, hy⟩ := (exact_deltaIII_inclBH 4 x).mp hs
  rw [← hy, h5 y, map_zero]

/-- **`H₃(B;ℤ) = 0`** (given `H₄(ℝP³) = 0`): `H₃(B) = im H(D')` (SES-I, `H₂(A) ≅ H₂(ℝP³) = 0`);
`H(B ↪ C)` is injective (SES-III, `H₄(ℝP³) = 0`); and `H(B ↪ C) ∘ H(D') = 0` (odd-sphere `D_* = 0`)
— so `H₃(B)` injects to `0`. -/
theorem hmlB_three_eq_zero (h4 : ∀ x : Hml (chainBoundary RP3top) 4, x = 0) (x : Hml dB 3) : x = 0 := by
  have hinj : Function.Injective (inclBH 3) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨y, hy⟩ := (exact_deltaIII_inclBH 3 a).mp ha
    rw [← hy, h4 y, map_zero]
  have hda : deltaI 2 x = 0 := hml_a_two_eq_zero _
  obtain ⟨w, hw⟩ := (exact_diffH_deltaI 2 x).mp hda
  apply hinj
  rw [map_zero, ← hw]
  exact inclBH_diffH_eq_zero 2 w

/-! ## §5. `H₃(ℝP³;ℤ) ≅ ℤ` -/

/-- `H(A ↪ C) : H₃(A;ℤ) → H₃(S³;ℤ)` is bijective: injective from `H₄(B) = 0` (SES-I), surjective
from `H₃(B) = 0` (`H(D') = 0`, SES-I middle exactness). -/
theorem inclAH_three_bijective (h4 : ∀ x : Hml (chainBoundary RP3top) 4, x = 0)
    (h5 : ∀ x : Hml (chainBoundary RP3top) 5, x = 0) : Function.Bijective (inclAH 3) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨y, hy⟩ := (exact_deltaI_inclAH 3 a).mp ha
    rw [← hy, hmlB_four_eq_zero h5 y, map_zero]
  · intro s
    exact (exact_inclAH_diffH 3 s).mp (hmlB_three_eq_zero h4 _)

/-- **`H₃(ℝP³;ℤ) ≅ ℤ`** — the fundamental class of the closed `3`-manifold, transported from
`H₃(A) ≅ H₃(S³) ≅ ℤ` along the transfer chain iso `C(ℝP³) ≅ A`. Conditional on the geometric
termination input `H₄(ℝP³) = H₅(ℝP³) = 0`. -/
def rp3H3EquivInt (h4 : ∀ x : Hml (chainBoundary RP3top) 4, x = 0)
    (h5 : ∀ x : Hml (chainBoundary RP3top) 5, x = 0) : Homology RP3top 3 ≃ₗ[ℤ] ℤ :=
  (((hmlEquivHomology RP3top 3).symm.trans (rHmlEquivAHml 3)).trans
      (LinearEquiv.ofBijective (inclAH 3) (inclAH_three_bijective h4 h5))).trans
    ((hmlEquivHomology S3top 3).trans SKEFTHawking.KummerRP3SphereHomeo.s3H3EquivInt)

/-! ## §6. `Hₙ(ℝP³;ℤ) = 0` for `n ≥ 4` — the two-step recursion `Hₙ ≅ Hₙ₋₂` -/

/-- **The recursion step** `Hₘ(ℝP³) = 0 ⟹ Hₘ₊₂(ℝP³) = 0` for `m ≥ 4`: `δ₃(m+1) : Hₘ₊₂(ℝP³) → Hₘ₊₁(B)`
and `δ'(m) : Hₘ₊₁(B) → Hₘ(A)` are both injective (their kernels come from `Hₘ₊₂(S³) = Hₘ₊₁(S³) = 0`),
and `Hₘ(A) ≅ Hₘ(ℝP³) = 0` (transfer iso). -/
theorem rp3_hml_step (m : ℕ) (hm : 4 ≤ m) (hind : ∀ x : Hml (chainBoundary RP3top) m, x = 0)
    (x : Hml (chainBoundary RP3top) (m + 2)) : x = 0 := by
  have hs2 : 3 < m + 2 := by omega
  have hs1 : 3 < m + 1 := by omega
  have h0 : deltaI m (deltaIII (m + 1) x) = 0 := hml_a_eq_zero_of hind _
  have hdI : deltaIII (m + 1) x = 0 := by
    obtain ⟨w, hw⟩ := (exact_diffH_deltaI m (deltaIII (m + 1) x)).mp h0
    rw [← hw, hml_s3_high (m + 1) hs1 w, map_zero]
  obtain ⟨t, ht⟩ := (exact_projH_deltaIII (m + 1) x).mp hdI
  rw [← ht, hml_s3_high (m + 2) hs2 t, map_zero]

/-- **`Hₙ₊₄(ℝP³;ℤ) = 0` for every `n`** (engine form) — strong induction on `n`: base cases
`n = 0, 1` are the termination inputs `H₄ = H₅ = 0`; the step `n = k + 2` reduces degree `k + 6`
to `k + 4` by `rp3_hml_step`. -/
theorem rp3_hml_high_shift (h4 : ∀ x : Hml (chainBoundary RP3top) 4, x = 0)
    (h5 : ∀ x : Hml (chainBoundary RP3top) 5, x = 0) :
    ∀ n, ∀ x : Hml (chainBoundary RP3top) (n + 4), x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h4
    | 1, _ => exact h5
    | (k + 2), ih =>
        intro x
        exact rp3_hml_step (k + 4) (by omega) (ih k (by omega)) x

/-- **`Hₙ(ℝP³;ℤ) = 0` for `n ≥ 4`** (engine form). -/
theorem rp3_hml_high (h4 : ∀ x : Hml (chainBoundary RP3top) 4, x = 0)
    (h5 : ∀ x : Hml (chainBoundary RP3top) 5, x = 0) (n : ℕ) (hn : 4 ≤ n)
    (x : Hml (chainBoundary RP3top) n) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  exact rp3_hml_high_shift h4 h5 k x

/-- **`Hₙ(ℝP³;ℤ) = 0` for `n ≥ 4`** — the top-degree vanishing of the K7 seam carrier's integral
homology. Conditional on the geometric termination input `H₄(ℝP³) = H₅(ℝP³) = 0`. -/
theorem rp3_homology_high (h4 : ∀ x : Homology RP3top 4, x = 0)
    (h5 : ∀ x : Homology RP3top 5, x = 0) (n : ℕ) (hn : 4 ≤ n) (x : Homology RP3top n) : x = 0 := by
  have h := rp3_hml_high h4 h5 n hn ((hmlEquivHomology RP3top n).symm x)
  have h2 := congrArg (hmlEquivHomology RP3top n) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

end

end SKEFTHawking.KummerRP3HomologyTop
