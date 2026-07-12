/-
# Phase 5q.H (N5 witness tower) — the doubly-punctured sphere IS the punctured plane:
# `Sⁿ∖{v,−v} ≃ₜ ℝⁿ∖{0}`

The geometric bridge of the product-homology arc's H₂ slice: the S²×S² polar-cover intersection
carries the factor `S²∖{v,−v}`, and the `H_{≤2}(S²×S¹)`-grade Mayer–Vietoris that computes its
product homology runs over `ℝ²∖{0}` under the slit-plane cover (`SingularStarConvexSlit`). This
module supplies the transport: the stereographic projection from the `(−v)`-pole carries the
doubly-punctured sphere to the plane minus the image point of `v` (`image_restr_doubly_punctured`,
the φ-direction form of the in-tree `restr_doubly_punctured_pathConnected` image computation),
and the translation homeomorphism recenters that puncture at the origin.

* `vImage n v` — the stereographic image of the second puncture.
* `image_restr_doubly_punctured` — `φ '' (restr {v}ᶜ {−v}ᶜ) = {vImage}ᶜ`.
* `subRight_image_compl_singleton` — translation carries `{q}ᶜ` to `{0}ᶜ`.
* **`doublyPuncturedSphereHomeo : sub ({v}ᶜ ∩ {−v}ᶜ) ≃ₜ ↥({0}ᶜ : Set ℝⁿ)`** — the composite
  (seam reassociation → stereographic restriction → recentering translation).

Pure topology (coefficient-agnostic): both towers consume it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularMayerVietorisLES

open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularSphereAcyclic (Sph puncturedHomeo antipode ne_antipode)
open SKEFTHawking.SingularMayerVietorisLES (seamHomeo)

namespace SKEFTHawking.SphereDoublyPuncturedPlane

/-- The membership of the first puncture `v` in the `(−v)`-punctured sphere. -/
theorem v_mem_antipodeCompl (n : ℕ) (v : ↑(Sph n)) :
    v ∈ ({antipode v}ᶜ : Set ↑(Sph n)) := by
  simpa using ne_antipode v

/-- **The stereographic image of the second puncture**: where the `(−v)`-pole projection sends
`v`. The puncture of the plane the doubly-punctured sphere becomes. -/
noncomputable def vImage (n : ℕ) (v : ↑(Sph n)) : EuclideanSpace ℝ (Fin n) :=
  puncturedHomeo n (antipode v) ⟨v, v_mem_antipodeCompl n v⟩

/-- **The doubly-punctured sphere maps onto the punctured plane** (φ-direction image identity):
`φ '' (restr {v}ᶜ {−v}ᶜ) = {vImage}ᶜ`. The forward form of the image computation inside
`restr_doubly_punctured_pathConnected`. -/
theorem image_restr_doubly_punctured (n : ℕ) (v : ↑(Sph n)) :
    (puncturedHomeo n (antipode v)) '' (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
      = ({vImage n v}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  set φ := puncturedHomeo n (antipode v) with hφ
  have himg : (φ.symm '' ({vImage n v}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
      = (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, restr,
      Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ¬((↑(φ.symm y) : ↑(Sph n)) ∈ ({v} : Set ↑(Sph n)))
      rw [Set.mem_singleton_iff]
      intro hxv
      refine hy ?_
      have heq : φ.symm y = ⟨v, v_mem_antipodeCompl n v⟩ := Subtype.ext hxv
      rw [show y = φ (φ.symm y) from (φ.apply_symm_apply y).symm, heq]
      rfl
    · intro hx
      refine ⟨φ x, ?_, φ.symm_apply_apply x⟩
      intro hcontra
      have hxeq : x = ⟨v, v_mem_antipodeCompl n v⟩ := φ.injective (by rw [hcontra]; rfl)
      exact hx (by rw [hxeq])
  calc φ '' (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
      = φ '' (φ.symm '' ({vImage n v}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) := by rw [himg]
    _ = ({vImage n v}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
        rw [Homeomorph.image_symm, Homeomorph.image_preimage]

/-- **Translation recenters the puncture**: `(· − q) '' {q}ᶜ = {0}ᶜ`. -/
theorem subRight_image_compl_singleton {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) :
    (Homeomorph.subRight q) '' ({q}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
      = ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ := by
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ¬((Homeomorph.subRight q) y = 0)
    rw [show (Homeomorph.subRight q) y = y - q from rfl, sub_eq_zero]
    exact hy
  · intro hx
    refine ⟨x + q, ?_, ?_⟩
    · intro h
      refine hx ?_
      have h2 : x + q - q = q - q := by rw [h]
      rw [add_sub_cancel_right, sub_self] at h2
      exact h2
    · show x + q - q = x
      exact add_sub_cancel_right x q

/-- **The doubly-punctured sphere IS the punctured plane**:
`sub ({v}ᶜ ∩ {−v}ᶜ) ≃ₜ ↥({0}ᶜ : Set ℝⁿ)` — seam reassociation, then the stereographic
restriction, then the recentering translation. The H₂-slice bridge: homology of the S²×S²
polar-intersection factor computes over `ℝ²∖{0}`'s slit-plane cover. -/
noncomputable def doublyPuncturedSphereHomeo (n : ℕ) (v : ↑(Sph n)) :
    ↥(sub (({v}ᶜ : Set ↑(Sph n)) ∩ ({antipode v}ᶜ)))
      ≃ₜ ↥(({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ) :=
  ((seamHomeo ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)).symm.trans
    (((puncturedHomeo n (antipode v)).image
        (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))).trans
      (Homeomorph.setCongr (image_restr_doubly_punctured n v)))).trans
    (((Homeomorph.subRight (vImage n v)).image ({vImage n v}ᶜ)).trans
      (Homeomorph.setCongr (subRight_image_compl_singleton (vImage n v))))

end SKEFTHawking.SphereDoublyPuncturedPlane
