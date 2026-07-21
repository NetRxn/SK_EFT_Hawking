import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.SingularFunctorialityInt

/-!
# The antipodal double cover `S³ → ℝP³` and the generic ℤ/2 chain-transfer engine

This module opens **the double-cover transfer route to `H_*(ℝP³; ℤ)`** — the K7 seam's main
homology input (`SingularFiniteProdDiscreteHnInt.eIndexProdHnEquivInt` reduces `Hₙ(seam)` to
`EIndex → Hₙ(TopCat.of RP3)`, so every seam-`b₂` accounting fact factors through
`Homology (TopCat.of RP3) n`).

The carrier `ℝP³ = S³/±` lives in `KummerResolutionPiece` (`RP3`, `mkRP3`, `continuous_mkRP3`,
the free involution `negS3`). Here we build the **algebraic core** of the transfer:

* `§1` — the ℤ/2-transfer operators for an **arbitrary** involution `t : C(X, X)` (`t ∘ t = id`):
  the chain-level **norm** `N_# = 1 + τ_#` and **difference** `D_# = 1 - τ_#`, with the
  Smith-type identities `D_# ∘ N_# = 0`, `N_# ∘ D_# = 0`, boundary-commutation (they are chain
  maps), and the homology-level versions `normHom`, `diffHom` with `D ∘ N = 0`, `N ∘ D = 0`, plus
  the covering relation `p_* ∘ τ_* = p_*` for any `p` with `p ∘ t = p`. Stated generically so the
  **same engine drives `H_*(Q)` from `H_*(T⁴°)` for `Q = T⁴°/τ`** (the planned downstream consumer).

* `§2` — the specialisation to the antipodal cover: the bundled maps `negS3C : C(S3, S3)`,
  `mkRP3C : C(S3, RP3)`; the involution/descent facts `negS3C ∘ negS3C = id`,
  `mkRP3C ∘ negS3C = mkRP3C`; the **freeness** fact `negS3 x ≠ x`; and the specialised homology
  operators on `Homology (TopCat.of S3) n` / `Homology (TopCat.of RP3) n`.

The remaining transfer input — chain-level exactness `ker(D_#) = range(N_#)` and
`ker(N_#) = range(D_#)` (the free-ℤ[ℤ/2]-module fact, whose geometric crux is that the antipodal
action on singular simplices is fixed-point-free), the two interlocking short exact sequences of
chain complexes, the resulting integral long exact sequence, and the low-degree solve — is left to
the follow-on brick(s).
-/

open CategoryTheory Opposite

namespace SKEFTHawking.KummerRP3Covering

open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt Homology.mapInt)
open SKEFTHawking.KummerResolutionPiece

noncomputable section

/-! ### §1. Generic ℤ/2 chain-transfer algebra for an involution `t : C(X, X)` -/

variable {X : TopCat}

/-- The chain-level **deck action** `τ_# = t_#` of a self-map `t : C(X, X)`. -/
def tauChain (t : C(X, X)) (n : ℕ) : SingularChainInt X n →ₗ[ℤ] SingularChainInt X n :=
  mapChainInt t n

/-- The chain-level **norm** operator `N_# = 1 + τ_#`. -/
def normChain (t : C(X, X)) (n : ℕ) : SingularChainInt X n →ₗ[ℤ] SingularChainInt X n :=
  LinearMap.id + mapChainInt t n

/-- The chain-level **difference** operator `D_# = 1 - τ_#`. -/
def diffChain (t : C(X, X)) (n : ℕ) : SingularChainInt X n →ₗ[ℤ] SingularChainInt X n :=
  LinearMap.id - mapChainInt t n

/-- `τ_#` is an involution when `t ∘ t = id`. -/
theorem tauChain_apply_apply {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ)
    (c : SingularChainInt X n) : mapChainInt t n (mapChainInt t n c) = c := by
  rw [← SingularFunctorialityInt.mapChainInt_comp, ht, SingularFunctorialityInt.mapChainInt_id]

/-- **Smith identity** `D_# ∘ N_# = 0`: `(1 - τ)(1 + τ) = 1 - τ² = 0`. -/
theorem diffChain_normChain {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ) :
    (diffChain t n).comp (normChain t n) = 0 := by
  ext c
  simp only [diffChain, normChain, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_add, LinearMap.zero_apply]
  rw [tauChain_apply_apply ht]
  abel_nf

/-- **Smith identity** `N_# ∘ D_# = 0`: `(1 + τ)(1 - τ) = 1 - τ² = 0`. -/
theorem normChain_diffChain {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ) :
    (normChain t n).comp (diffChain t n) = 0 := by
  ext c
  simp only [diffChain, normChain, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, LinearMap.zero_apply]
  rw [tauChain_apply_apply ht]
  abel_nf

/-- `τ_#` commutes with the singular boundary — it is a chain map. -/
theorem chainBoundary_tauChain (t : C(X, X)) (n : ℕ) (c : SingularChainInt X (n + 1)) :
    chainBoundary X n (mapChainInt t (n + 1) c) = mapChainInt t n (chainBoundary X n c) :=
  SingularFunctorialityInt.chainBoundary_mapChainInt t c

/-- `N_#` is a chain map: it commutes with the singular boundary. -/
theorem chainBoundary_normChain (t : C(X, X)) (n : ℕ) (c : SingularChainInt X (n + 1)) :
    chainBoundary X n (normChain t (n + 1) c) = normChain t n (chainBoundary X n c) := by
  simp only [normChain, LinearMap.add_apply, LinearMap.id_apply, map_add]
  rw [chainBoundary_tauChain]

/-- `D_#` is a chain map: it commutes with the singular boundary. -/
theorem chainBoundary_diffChain (t : C(X, X)) (n : ℕ) (c : SingularChainInt X (n + 1)) :
    chainBoundary X n (diffChain t (n + 1) c) = diffChain t n (chainBoundary X n c) := by
  simp only [diffChain, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [chainBoundary_tauChain]

/-! ### §1b. Homology-level transfer operators -/

/-- The homology-level **deck action** `τ_* = t_*`. -/
def tauHom (t : C(X, X)) (n : ℕ) : Homology X n →ₗ[ℤ] Homology X n := Homology.mapInt t n

/-- The homology-level **norm** operator `N_* = 1 + τ_*`. -/
def normHom (t : C(X, X)) (n : ℕ) : Homology X n →ₗ[ℤ] Homology X n :=
  LinearMap.id + Homology.mapInt t n

/-- The homology-level **difference** operator `D_* = 1 - τ_*`. -/
def diffHom (t : C(X, X)) (n : ℕ) : Homology X n →ₗ[ℤ] Homology X n :=
  LinearMap.id - Homology.mapInt t n

/-- `τ_*` is an involution on homology when `t ∘ t = id`. -/
theorem tauHom_apply_apply {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ)
    (h : Homology X n) : Homology.mapInt t n (Homology.mapInt t n h) = h := by
  rw [← LinearMap.comp_apply, ← SingularFunctorialityInt.Homology.mapInt_comp, ht,
    SingularFunctorialityInt.Homology.mapInt_id, LinearMap.id_apply]

/-- **Smith identity on homology** `D_* ∘ N_* = 0`. -/
theorem diffHom_normHom {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ) :
    (diffHom t n).comp (normHom t n) = 0 := by
  ext h
  simp only [diffHom, normHom, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_add, LinearMap.zero_apply]
  rw [tauHom_apply_apply ht]
  abel_nf

/-- **Smith identity on homology** `N_* ∘ D_* = 0`. -/
theorem normHom_diffHom {t : C(X, X)} (ht : t.comp t = ContinuousMap.id X) (n : ℕ) :
    (normHom t n).comp (diffHom t n) = 0 := by
  ext h
  simp only [diffHom, normHom, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, LinearMap.zero_apply]
  rw [tauHom_apply_apply ht]
  abel_nf

/-- **Covering relation** `p_* ∘ τ_* = p_*` for a map `p` that factors through the quotient
(`p ∘ t = p`). This is the homology shadow of `mkRP3 ∘ negS3 = mkRP3`; over a double cover it forces
`p_* ∘ tr = 2` on the base and drives the ℤ/2-torsion of the transfer. -/
theorem projHom_tauHom {Y : TopCat} {p : C(X, Y)} {t : C(X, X)} (hpt : p.comp t = p) (n : ℕ)
    (h : Homology X n) : Homology.mapInt p n (Homology.mapInt t n h) = Homology.mapInt p n h := by
  rw [← LinearMap.comp_apply, ← SingularFunctorialityInt.Homology.mapInt_comp, hpt]

/-! ### §2. The antipodal double cover `S³ → ℝP³` -/

/-- The 3-sphere as a `TopCat`. -/
def S3top : TopCat := TopCat.of S3

/-- Real projective 3-space `ℝP³ = S³/±` as a `TopCat` (the K7 seam's carrier). -/
def RP3top : TopCat := TopCat.of RP3

/-- The antipodal involution `(a, b) ↦ (−a, −b)` is continuous. -/
theorem continuous_negS3 : Continuous negS3 := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.fst.neg).prodMk (continuous_subtype_val.snd.neg)

/-- The antipodal involution as a bundled continuous self-map of `S³`. -/
def negS3C : C(S3top, S3top) := ⟨negS3, continuous_negS3⟩

/-- The double-cover projection `S³ → ℝP³` as a bundled continuous map. -/
def mkRP3C : C(S3top, RP3top) := ⟨mkRP3, continuous_mkRP3⟩

@[simp] theorem negS3C_apply (x : S3) : negS3C x = negS3 x := rfl

@[simp] theorem mkRP3C_apply (x : S3) : mkRP3C x = mkRP3 x := rfl

/-- `negS3` is an involution as a bundled map: `negS3C ∘ negS3C = id`. -/
theorem negS3C_comp_negS3C : negS3C.comp negS3C = ContinuousMap.id S3top := by
  ext x
  exact negS3_involutive x

/-- **Antipodal descent** as a bundled map: `mkRP3C ∘ negS3C = mkRP3C`. -/
theorem mkRP3C_comp_negS3C : mkRP3C.comp negS3C = mkRP3C := by
  ext x
  exact mkRP3_neg x

/-- **The antipodal action is free**: `negS3 x ≠ x` for every `x ∈ S³`. A fixed point would force
`x = (0, 0)`, contradicting `‖a‖² + ‖b‖² = 1`. This is the geometric crux input for the chain-level
exactness of the norm sequence (the follow-on brick). -/
theorem negS3_free (x : S3) : negS3 x ≠ x := by
  intro h
  have ha : -x.1.1 = x.1.1 := by
    have := congrArg (fun y : S3 => y.1.1) h
    simpa using this
  have hb : -x.1.2 = x.1.2 := by
    have := congrArg (fun y : S3 => y.1.2) h
    simpa using this
  have ha0 : x.1.1 = 0 := by linear_combination (-2⁻¹ : ℂ) * ha
  have hb0 : x.1.2 = 0 := by linear_combination (-2⁻¹ : ℂ) * hb
  have hx := x.2
  rw [ha0, hb0] at hx
  simp at hx

/-! ### §2b. The specialised transfer operators on `S³ → ℝP³` homology -/

/-- The deck action `τ_* = (−1)_*` on `Hₙ(S³; ℤ)`. -/
def tauHomS3 (n : ℕ) : Homology S3top n →ₗ[ℤ] Homology S3top n := tauHom negS3C n

/-- The projection `p_* : Hₙ(S³; ℤ) → Hₙ(ℝP³; ℤ)` — the seam consumer's target codomain. -/
def projHomRP3 (n : ℕ) : Homology S3top n →ₗ[ℤ] Homology RP3top n := Homology.mapInt mkRP3C n

/-- `τ_*` is an involution on `Hₙ(S³; ℤ)`. -/
theorem tauHomS3_apply_apply (n : ℕ) (h : Homology S3top n) :
    tauHomS3 n (tauHomS3 n h) = h :=
  tauHom_apply_apply negS3C_comp_negS3C n h

/-- **`p_* ∘ τ_* = p_*` on `S³ → ℝP³` homology** — the descent relation the transfer LES consumes. -/
theorem projHomRP3_tauHomS3 (n : ℕ) (h : Homology S3top n) :
    projHomRP3 n (tauHomS3 n h) = projHomRP3 n h :=
  projHom_tauHom mkRP3C_comp_negS3C n h

end

end SKEFTHawking.KummerRP3Covering
