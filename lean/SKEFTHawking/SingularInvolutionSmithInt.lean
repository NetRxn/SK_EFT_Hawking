import Mathlib
import SKEFTHawking.KummerRP3Covering

/-!
# Chain-level Smith exactness for a free involution — `ker D = im N`, `ker N = im D` (integral)

For an involution `t : C(X, X)` (`t ∘ t = id`) acting **freely on singular simplices**
(`mapSimplex t σ ≠ σ`), the singular integral chain groups are free `ℤ[ℤ/2]`-modules on the
simplex orbits, and the norm/difference operators `N_# = 1 + τ_#`, `D_# = 1 − τ_#` of
`KummerRP3Covering` are exactly exact against each other in each level:

* `ker_diffChain_eq_range_normChain` : `ker D_# = im N_#`,
* `ker_normChain_eq_range_diffChain` : `ker N_# = im D_#`.

The inclusions `⊇` are the banked Smith identities `D∘N = N∘D = 0`; the inclusions `⊆` are the
orbit-pairing support-strip induction (a `τ`-(anti)invariant chain has its coefficients paired
along the free orbits `{σ, tσ}`, so subtracting one `N`/`D`-image of a single simplex strips the
whole orbit from the support). Freeness enters exactly once: `σ ≠ tσ` keeps the strip honest.

Stated **generically** (arbitrary involution + pointwise-free hypothesis, upgraded to simplex
freeness by evaluating realizations): the same engine drives the `Q = T⁴°/τ` transfer of the
Kummer accounting — the downstream consumer after `H_*(ℝP³;ℤ)` (`KummerRP3TransferInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp mapSimplex_id)
open SKEFTHawking.KummerRP3Covering (normChain diffChain tauChain_apply_apply
  diffChain_normChain normChain_diffChain)

namespace SKEFTHawking.SingularInvolutionSmithInt

variable {X : TopCat} {t : C(↑X, ↑X)}

/-- Simplex-level involutivity: `mapSimplex t (mapSimplex t σ) = σ` when `t ∘ t = id`. -/
theorem mapSimplex_mapSimplex (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapSimplex t (mapSimplex t σ) = σ := by
  rw [← mapSimplex_comp, ht, mapSimplex_id]

/-- **Pointwise freeness upgrades to simplex freeness**: if `t` moves every point, it moves every
singular simplex (evaluate the realization anywhere). -/
theorem mapSimplex_ne_of_forall_ne (hfree : ∀ x : ↑X, t x ≠ x) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapSimplex t σ ≠ σ := by
  intro h
  have h1 := congrArg (X.toSSetObjEquiv (op (SimplexCategory.mk n))) h
  rw [mapSimplex, Equiv.apply_symm_apply] at h1
  have hpt : Nonempty ↥(stdSimplex ℝ (Fin (n + 1))) := inferInstance
  obtain ⟨d⟩ := hpt
  exact hfree ((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) d)
    (congrFun (congrArg DFunLike.coe h1) d)

/-- The coefficient formula of the involution pushforward: `(τ_# c)(σ) = c(tσ)`. -/
theorem mapChainInt_apply_of_involutive (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (c : SingularChainInt X n) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapChainInt t n c σ = c (mapSimplex t σ) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single σ' a =>
      classical
      rw [mapChainInt_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : mapSimplex t σ' = σ
      · rw [if_pos h, if_pos (by rw [← h, mapSimplex_mapSimplex ht])]
      · rw [if_neg h, if_neg (fun h2 => h (by rw [h2, mapSimplex_mapSimplex ht]))]

/-- `N_#` on a single simplex: `N(a·σ) = a·σ + a·(tσ)`. -/
theorem normChain_single (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    normChain t n (Finsupp.single σ a)
      = Finsupp.single σ a + Finsupp.single (mapSimplex t σ) a := by
  show Finsupp.single σ a + mapChainInt t n (Finsupp.single σ a) = _
  rw [mapChainInt_single]

/-- `D_#` on a single simplex: `D(a·σ) = a·σ − a·(tσ)`. -/
theorem diffChain_single (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    diffChain t n (Finsupp.single σ a)
      = Finsupp.single σ a - Finsupp.single (mapSimplex t σ) a := by
  show Finsupp.single σ a - mapChainInt t n (Finsupp.single σ a) = _
  rw [mapChainInt_single]

/-- **`ker D_# ⊆ im N_#`**, by the orbit support-strip induction: a `τ`-invariant chain has
`c(σ) = c(tσ)`, so subtracting `N(c(σ₀)·σ₀)` strips the whole orbit `{σ₀, tσ₀}`. -/
theorem mem_range_normChain_of_diffChain_eq_zero
    (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (hfree : ∀ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)), mapSimplex t σ ≠ σ)
    (c : SingularChainInt X n) (hc : diffChain t n c = 0) :
    c ∈ LinearMap.range (normChain t n) := by
  classical
  suffices H : ∀ (N : ℕ) (c : SingularChainInt X n), c.support.card ≤ N →
      diffChain t n c = 0 → c ∈ LinearMap.range (normChain t n) from H _ c le_rfl hc
  intro N
  induction N with
  | zero =>
      intro c hcard _
      have hc0 : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact ⟨0, by rw [map_zero, hc0]⟩
  | succ N ih =>
      intro c hcard hc
      rcases Finset.eq_empty_or_nonempty c.support with hemp | ⟨σ₀, hσ₀⟩
      · exact ⟨0, by rw [map_zero, Finsupp.support_eq_empty.mp hemp]⟩
      · -- τ-invariance of the coefficients
        have hinv : ∀ σ, c σ = c (mapSimplex t σ) := by
          intro σ
          have h1 : c σ - c (mapSimplex t σ) = 0 := by
            have h2 := congrArg (fun d => d σ) hc
            simpa [diffChain, mapChainInt_apply_of_involutive ht] using h2
          linarith [h1]
        set a := c σ₀ with ha
        set c' := c - normChain t n (Finsupp.single σ₀ a) with hc'
        have hDc' : diffChain t n c' = 0 := by
          rw [hc', map_sub, hc, ← LinearMap.comp_apply, diffChain_normChain ht,
            LinearMap.zero_apply, sub_self]
        have hne : mapSimplex t σ₀ ≠ σ₀ := hfree σ₀
        have hsupp : c'.support ⊆ c.support.erase σ₀ := by
          intro x hx
          have hx0 : c' x ≠ 0 := Finsupp.mem_support_iff.mp hx
          rw [hc', Finsupp.sub_apply, normChain_single, Finsupp.add_apply,
            Finsupp.single_apply, Finsupp.single_apply] at hx0
          rw [Finset.mem_erase, Finsupp.mem_support_iff]
          by_cases h1 : σ₀ = x
          · exfalso
            apply hx0
            rw [if_pos h1, if_neg (fun h2 => hne (h2.trans h1.symm)), ← h1, ← ha]
            ring
          · by_cases h2 : mapSimplex t σ₀ = x
            · exfalso
              apply hx0
              rw [if_neg h1, if_pos h2, ← h2, ← hinv σ₀, ← ha]
              ring
            · rw [if_neg h1, if_neg h2] at hx0
              exact ⟨fun h => h1 h.symm, by simpa using hx0⟩
        have hmem : σ₀ ∈ c.support := hσ₀
        have hcard' : c'.support.card ≤ N := by
          have h1 := Finset.card_le_card hsupp
          have h2 : (c.support.erase σ₀).card = c.support.card - 1 :=
            Finset.card_erase_of_mem hmem
          omega
        obtain ⟨d, hd⟩ := ih c' hcard' hDc'
        refine ⟨d + Finsupp.single σ₀ a, ?_⟩
        rw [map_add, hd, hc']
        abel

/-- **`ker N_# ⊆ im D_#`**, by the orbit support-strip induction: a `τ`-anti-invariant chain has
`c(σ) = −c(tσ)`, so subtracting `D(c(σ₀)·σ₀)` strips the whole orbit `{σ₀, tσ₀}`. -/
theorem mem_range_diffChain_of_normChain_eq_zero
    (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (hfree : ∀ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)), mapSimplex t σ ≠ σ)
    (c : SingularChainInt X n) (hc : normChain t n c = 0) :
    c ∈ LinearMap.range (diffChain t n) := by
  classical
  suffices H : ∀ (N : ℕ) (c : SingularChainInt X n), c.support.card ≤ N →
      normChain t n c = 0 → c ∈ LinearMap.range (diffChain t n) from H _ c le_rfl hc
  intro N
  induction N with
  | zero =>
      intro c hcard _
      have hc0 : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact ⟨0, by rw [map_zero, hc0]⟩
  | succ N ih =>
      intro c hcard hc
      rcases Finset.eq_empty_or_nonempty c.support with hemp | ⟨σ₀, hσ₀⟩
      · exact ⟨0, by rw [map_zero, Finsupp.support_eq_empty.mp hemp]⟩
      · -- τ-anti-invariance of the coefficients
        have hinv : ∀ σ, c σ = - c (mapSimplex t σ) := by
          intro σ
          have h1 : c σ + c (mapSimplex t σ) = 0 := by
            have h2 := congrArg (fun d => d σ) hc
            simpa [normChain, mapChainInt_apply_of_involutive ht] using h2
          linarith [h1]
        set a := c σ₀ with ha
        set c' := c - diffChain t n (Finsupp.single σ₀ a) with hc'
        have hNc' : normChain t n c' = 0 := by
          rw [hc', map_sub, hc, ← LinearMap.comp_apply, normChain_diffChain ht,
            LinearMap.zero_apply, sub_self]
        have hne : mapSimplex t σ₀ ≠ σ₀ := hfree σ₀
        have hsupp : c'.support ⊆ c.support.erase σ₀ := by
          intro x hx
          have hx0 : c' x ≠ 0 := Finsupp.mem_support_iff.mp hx
          rw [hc', Finsupp.sub_apply, diffChain_single, Finsupp.sub_apply,
            Finsupp.single_apply, Finsupp.single_apply] at hx0
          rw [Finset.mem_erase, Finsupp.mem_support_iff]
          by_cases h1 : σ₀ = x
          · exfalso
            apply hx0
            rw [if_pos h1, if_neg (fun h2 => hne (h2.trans h1.symm)), ← h1, ← ha]
            ring
          · by_cases h2 : mapSimplex t σ₀ = x
            · exfalso
              apply hx0
              rw [if_neg h1, if_pos h2, ← h2]
              have := hinv σ₀
              rw [← ha] at this
              rw [this]
              ring
            · rw [if_neg h1, if_neg h2] at hx0
              exact ⟨fun h => h1 h.symm, by simpa using hx0⟩
        have hmem : σ₀ ∈ c.support := hσ₀
        have hcard' : c'.support.card ≤ N := by
          have h1 := Finset.card_le_card hsupp
          have h2 : (c.support.erase σ₀).card = c.support.card - 1 :=
            Finset.card_erase_of_mem hmem
          omega
        obtain ⟨d, hd⟩ := ih c' hcard' hNc'
        refine ⟨d + Finsupp.single σ₀ a, ?_⟩
        rw [map_add, hd, hc']
        abel

/-- **Chain-level Smith exactness I**: `ker D_# = im N_#` for a free involution. -/
theorem ker_diffChain_eq_range_normChain (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (hfree : ∀ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)), mapSimplex t σ ≠ σ) :
    LinearMap.ker (diffChain t n) = LinearMap.range (normChain t n) := by
  ext c
  constructor
  · exact fun hc => mem_range_normChain_of_diffChain_eq_zero ht hfree c
      (LinearMap.mem_ker.mp hc)
  · rintro ⟨d, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, diffChain_normChain ht, LinearMap.zero_apply]

/-- **Chain-level Smith exactness II**: `ker N_# = im D_#` for a free involution. -/
theorem ker_normChain_eq_range_diffChain (ht : t.comp t = ContinuousMap.id ↑X) {n : ℕ}
    (hfree : ∀ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)), mapSimplex t σ ≠ σ) :
    LinearMap.ker (normChain t n) = LinearMap.range (diffChain t n) := by
  ext c
  constructor
  · exact fun hc => mem_range_diffChain_of_normChain_eq_zero ht hfree c
      (LinearMap.mem_ker.mp hc)
  · rintro ⟨d, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, normChain_diffChain ht, LinearMap.zero_apply]

end SKEFTHawking.SingularInvolutionSmithInt
