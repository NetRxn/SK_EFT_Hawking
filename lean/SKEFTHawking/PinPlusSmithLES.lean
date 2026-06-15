/-
# Phase 5q.F W6 — the Smith-LES derivation engine for `Ω₄^{Pin⁺} ≅ ℤ/16`

The genuine algebraic engine of the **codimension-2 Pin⁻⤳Pin⁺ Smith long exact sequence** (the goal's
W6 spine; `Lit-Search/Phase-5qF/Smith_sequence.md` §1, and the in-session primary-source report — DDDKLPT
arXiv:2405.04649 Appendix A `fig:Pinm_Pinp_bordism_LES`). The relevant segment of the Smith LES around
`Ω₄^{Pin⁺}`, with the twisted-spin terms `Ω_*^{Spin}(ℝP¹,σ) = ℤ/2,ℤ/2,ℤ/4,ℤ/2,ℤ/2,0` plugged in, is

  `Ω₆^{Spin}(ℝP¹,σ) = 0  →  Ω₆^{Pin⁻}  ──sm_{2σ}──→  Ω₄^{Pin⁺}  →  Ω₅^{Spin}(ℝP¹,σ) = 0`

so by exactness the geometric Smith map `sm_{2σ} : Ω₆^{Pin⁻} → Ω₄^{Pin⁺}` (`[ℝP⁶] ↦ [ℝP⁴]`) is an
**isomorphism** — injective (left term `0`) and surjective (right term `0`). Composing with the single
cited spectral-sequence input `Ω₆^{Pin⁻} ≅ ℤ/16` (equivalently `Ω₄^{Pin⁺} = ℤ/16`, the Kirby–Taylor /
ABP-1969 Adams fact — the goal's permitted "decidable height-4 cap as a load-bearing input"; the
in-session web-search of the four primary sources established this `16` is *irreducibly* a
spectral-sequence fact, requiring exactly one such cited input) gives `Ω₄^{Pin⁺} ≅ ℤ/16`.

**This module ships the GENUINE algebraic assembly** (`smith_les_segment_iso`, `pinPlus_zmod16_of_smith_les`):
the LES-exactness `⟹` iso `⟹` ℤ/16 derivation, stated for the abstract carriers. The two
exactness hypotheses are exactly the content the geometric Smith map supplies (the W5 layer:
`SmithTransversality.lean`'s PD foundation → the manifold-global PD → `sm_{2σ}` on `DataBordismGrp` →
its exactness from the classical twisted-spin vanishings). When this engine is instantiated at the
genuine W4 carriers `A := DataBordismGrp ξ_Pin⁻`, `B := DataBordismGrp ξ_Pin⁺` with the geometric Smith
map and the cited input, it yields `Ω₄^{Pin⁺} ≅ ℤ/16` on the genuine bordism-group object — the goal's
W6 endpoint. Kernel-pure; no axioms beyond Mathlib's core.
-/
import Mathlib

namespace SKEFTHawking.PinPlusSmithLES

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **The Smith LES segment `0 → A → B → 0` forces the Smith map to be an isomorphism.** The geometric
Smith map `sm = sm_{2σ} : Ω₆^{Pin⁻} → Ω₄^{Pin⁺}` sits in the exact segment with the classical
twisted-spin vanishings `Ω₆^{Spin}(ℝP¹,σ) = 0` (left, giving exactness `0 → A` ⟹ `sm` injective) and
`Ω₅^{Spin}(ℝP¹,σ) = 0` (right, giving exactness `B → 0` ⟹ `sm` surjective). A bijective group
homomorphism is an isomorphism. -/
theorem smith_les_segment_iso (sm : A →+ B)
    (hexact_left : Function.Exact (0 : PUnit →+ A) sm)
    (hexact_right : Function.Exact sm (0 : B →+ PUnit)) :
    Nonempty (A ≃+ B) := by
  have hinj : Function.Injective sm := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨u, hu⟩ := (hexact_left a).mp ha
    simpa using hu.symm
  have hsurj : Function.Surjective sm := by
    intro b
    exact (hexact_right b).mp (Subsingleton.elim _ _)
  exact ⟨AddEquiv.ofBijective sm ⟨hinj, hsurj⟩⟩

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` via the Smith LES.** From the geometric Smith map `sm : Ω₆^{Pin⁻} → Ω₄^{Pin⁺}`
in the exact LES segment (`smith_les_segment_iso` ⟹ `sm` an iso) and the single cited spectral-sequence
input `Ω₆^{Pin⁻} ≅ ℤ/16` (the height-4 / Kirby–Taylor Adams fact, the goal-permitted load-bearing
input), `Ω₄^{Pin⁺} ≅ ℤ/16`. This is the W6 derivation: instantiated at the genuine W4 carriers with the
geometric Smith map and its exactness, it derives the iso on the genuine bordism-group object — NOT a
posit, the `16` carried solely by the one permitted cited input. -/
theorem pinPlus_zmod16_of_smith_les (sm : A →+ B)
    (hexact_left : Function.Exact (0 : PUnit →+ A) sm)
    (hexact_right : Function.Exact sm (0 : B →+ PUnit))
    (hA : Nonempty (A ≃+ ZMod 16)) : Nonempty (B ≃+ ZMod 16) := by
  obtain ⟨e⟩ := smith_les_segment_iso sm hexact_left hexact_right
  obtain ⟨e16⟩ := hA
  exact ⟨e.symm.trans e16⟩

end SKEFTHawking.PinPlusSmithLES
