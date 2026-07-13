/-
# Phase 5q.H (N1 audit) — ⛔ STRUCTURAL NO-GO: the T2-less `Bordism` relation COLLAPSES

**Finding (kernel-checked).** The project's `Bordism` structure (`BordismGroup.lean`) does not
require the bordism manifold `W` to be Hausdorff. This module proves that omission is FATAL to the
geometric faithfulness of every carrier built on the relation:

* `tripleBordism` — for EVERY closed singular manifold `s` (at `k = 0`), the product of `s.M` with
  the bug-eyed interval (`NonHausdorffInterval.lean`) is a compact `Bordism` from `(s ⊔ s) ⊔ s` to
  `∅` (three boundary copies — an odd count, impossible for genuine/Hausdorff bordisms).
* `bordismGrp_mk_eq_zero` / `bordismGrp_subsingleton` — hence `3·[s] = 0`; with the in-tree
  2-torsion (`doublingBordism`) this forces `[s] = 0` for every `s`: **the plain `BordismGrp X 0 I`
  is the trivial group.** In particular `bordismGrp_rp4_eq_zero`: the in-tree relation null-bords
  ℝP⁴, whose genuine unoriented class is NONZERO (`w₁⁴[ℝP⁴] = 1`, in-tree `rp4_htie`). The
  relation is therefore PROVABLY NOT unoriented bordism.
* `dataBordismGMTied_mk_eq_iff_grade16_eq` — on the tied Guillou–Marin carrier the same
  construction collapses every pair of same-grade classes: **the carrier is exactly its `ZMod 16`
  grade**, i.e. the structured relation retains NO geometric content beyond the carried grade.
* Consequently the phase's gating completeness node `hbound` (`∀ x, abkGMTied16 x = 0 → x = 0`) is
  DISCHARGED AS STATED (`grade0_eq_zero_of_nonHausdorff`), and the σ-route door fires
  (`omega4PinPlusGMTied_equiv_zmod16_of_nonHausdorff_collapse`) — **but for the degenerate reason.**
  This is NOT the geometric completeness of `Ω₄^{Pin⁺} ≅ ℤ/16`; it is the demonstration that the
  current statement of the node is too weak to carry it. The genuine keystone must be restated on a
  Hausdorff-refined bordism relation (see `T2TiedBordism.lean`), where the collapse is blocked
  (the bug-eyed `W` is provably non-T2: `not_t2Space_bugInterval`).

Every declaration is kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry / axiom /
native_decide / maxHeartbeats. The bug-eyed charts are real-analytic (identity/affine transitions),
so NO smoothness upgrade of the `Bordism` structure alone can exclude this — only a `T2Space W`
field (compact + T2 + charted ⟹ metrizable ⟹ genuine bordism manifold) does.
-/
import Mathlib
import SKEFTHawking.BordismGroup
import SKEFTHawking.NonHausdorffInterval
import SKEFTHawking.PinPlusGMWitness

namespace SKEFTHawking.NonHausdorffBordismCollapse

open scoped Manifold
open SKEFTHawking.BordismTheory SKEFTHawking.NonHausdorffInterval
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusTiedData SKEFTHawking.PinPlusGMTiedData SKEFTHawking.PinPlusGMWitness

/-! ## §1. The odd-boundary bordism: `(s ⊔ s) ⊔ s` bounds `s.M × BugInterval` -/

variable {X : Type*} [TopologicalSpace X]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The triple-boundary bordism** — `W := s.M × BugInterval` is a compact (non-Hausdorff!) C⁰
bordism manifold whose boundary is THREE copies of `s.M` (the doubled origin + the top), so
`(s ⊔ s) ⊔ s` bounds. For genuine (Hausdorff) bordisms an odd boundary count is impossible; this
single object is what the missing `T2Space W` field lets through. -/
noncomputable def tripleBordism (s : SingularManifold X 0 I) :
    Bordism (I.prod (𝓡∂ 1)) ((s.sum s).sum s) emptySM where
  W := s.M × BugInterval
  e := Sum.elim
        (Sum.elim
          (Sum.elim (fun m => (m, origin false)) (fun m => (m, origin true)))
          (fun m => (m, btop)))
        (fun z => isEmptyElim z)
  he_smooth :=
    ContMDiff.sumElim
      (ContMDiff.sumElim
        (ContMDiff.sumElim (contMDiff_id.prodMk contMDiff_const)
          (contMDiff_id.prodMk contMDiff_const))
        (contMDiff_id.prodMk contMDiff_const))
      (fun z => isEmptyElim z)
  he_inj := by
    rintro (((a | a) | a) | z) (((b | b) | b) | w) hab
    all_goals first
      | exact isEmptyElim z
      | exact isEmptyElim w
      | (simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
         first
           | exact absurd hab.2 origin_ne
           | exact absurd hab.2.symm origin_ne
           | exact absurd hab.2 (origin_ne_btop false)
           | exact absurd hab.2 (origin_ne_btop true)
           | exact absurd hab.2.symm (origin_ne_btop false)
           | exact absurd hab.2.symm (origin_ne_btop true)
           | rw [hab.1])
  he_boundary := by
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_bugInterval]
    ext ⟨m, b⟩
    constructor
    · rintro ⟨(((a | a) | a) | z), hx⟩
      · simp only [Sum.elim_inl] at hx
        rw [← hx]
        exact Set.mk_mem_prod (Set.mem_univ _) (Set.mem_insert _ _)
      · simp only [Sum.elim_inl, Sum.elim_inr] at hx
        rw [← hx]
        exact Set.mk_mem_prod (Set.mem_univ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · simp only [Sum.elim_inl, Sum.elim_inr] at hx
        rw [← hx]
        exact Set.mk_mem_prod (Set.mem_univ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      · exact isEmptyElim z
    · intro hmem
      rcases hmem.2 with rfl | rfl | rfl
      · exact ⟨Sum.inl (Sum.inl (Sum.inl m)), rfl⟩
      · exact ⟨Sum.inl (Sum.inl (Sum.inr m)), rfl⟩
      · exact ⟨Sum.inl (Sum.inr m), rfl⟩
  g := fun p => s.f p.1
  hg := s.hf.comp continuous_fst
  hg_restrict := by
    funext x
    rcases x with (((a | a) | a) | z)
    · rfl
    · rfl
    · rfl
    · exact isEmptyElim z

/-! ## §2. The plain bordism group is TRIVIAL at `k = 0` -/

/-- **Every class of the plain `BordismGrp` vanishes.** The relation-level chain
`s ~ s ⊔ ∅ ~ s ⊔ (s ⊔ s) ~ (s ⊔ s) ⊔ s ~ ∅` — the middle step feeds the in-tree doubling
(`s ⊔ s ~ ∅`) through the disjoint-union congruence, and the last step is the non-Hausdorff triple
bordism. The T2-less relation identifies EVERYTHING with the empty manifold. -/
theorem bordismGrp_mk_eq_zero (s : SingularManifold X 0 I) :
    BordismGrp.mk s = BordismGrp.mk (emptySM : SingularManifold X 0 I) := by
  have h1 : BordismGrp.mk (s.sum emptySM) = BordismGrp.mk s :=
    BordismGrp.mk_eq_of_bordant (IsBordant.of_diffeo
      (Diffeomorph.sumEmpty I s.M 0 (M' := (emptySM : SingularManifold X 0 I).M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
  have h2 : BordismGrp.mk (s.sum emptySM) = BordismGrp.mk (s.sum (s.sum s)) :=
    BordismGrp.mk_eq_of_bordant
      ⟨Bordism.add (reflCylinder s) (doublingBordism s).symm⟩
  have h3 : BordismGrp.mk ((s.sum s).sum s) = BordismGrp.mk (s.sum (s.sum s)) :=
    BordismGrp.mk_eq_of_bordant (IsBordant.of_diffeo
      (Diffeomorph.sumAssoc I s.M 0 s.M s.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
  have h4 : BordismGrp.mk ((s.sum s).sum s) = BordismGrp.mk (emptySM : SingularManifold X 0 I) :=
    BordismGrp.mk_eq_of_bordant ⟨tripleBordism s⟩
  rw [← h1, h2, ← h3, h4]

/-- **The plain `k = 0` bordism group is the TRIVIAL group.** Mathematically `Ω₄^O ≅ (ℤ/2)²` is
nontrivial, so the T2-less relation is kernel-provably NOT unoriented bordism. -/
theorem bordismGrp_subsingleton : Subsingleton (BordismGrp X 0 I) := by
  constructor
  intro a b
  induction a using Quot.ind with | _ s =>
  induction b using Quot.ind with | _ t =>
  show BordismGrp.mk s = BordismGrp.mk t
  rw [bordismGrp_mk_eq_zero s, bordismGrp_mk_eq_zero t]

/-- **The falsifier witness: ℝP⁴ is null-bordant in the T2-less relation** — while its genuine
unoriented bordism class is the `w₁⁴`-generator of `Ω₄^O` (in-tree: `rp4_htie` computes
`w₁⁴[ℝP⁴] = 1`). This single theorem pins the infidelity of the current `Bordism` structure. -/
theorem bordismGrp_rp4_eq_zero :
    BordismGrp.mk SKEFTHawking.RP4Witness.rp4SM
      = BordismGrp.mk (emptySM : SingularManifold PUnit 0 (𝓡 4)) :=
  bordismGrp_mk_eq_zero _

/-! ## §3. The tied Guillou–Marin carrier collapses to its grade -/

universe u

/-- `3x = 0` for every grade-`0` class of the tied GM carrier — the triple bordism is admitted by
the tied `Bor` (which only checks grade equality: `0 + 0 + 0 = 0`). -/
theorem dataBordismGMTied_triple (s : SingularManifold.{0, u, 0, 0} PUnit.{u + 1} 0 (𝓡 4))
    (str : GMTiedStr (𝓡 4) s) (hg : str.grade16 = 0) :
    DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      + DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      + DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩ = 0 :=
  DataBordismGrp.mk_eq_of_bordant _ ⟨tripleBordism s, ⟨PLift.up (by
    show str.grade16 + str.grade16 + str.grade16 = (0 : ZMod 16)
    rw [hg, add_zero, add_zero])⟩⟩

/-- `-x = x` for every grade-`0` class (the reversed structure has grade `-0 = 0`, and the tied
`Bor` sees only the grade). -/
theorem dataBordismGMTied_neg_self (s : SingularManifold.{0, u, 0, 0} PUnit.{u + 1} 0 (𝓡 4))
    (str : GMTiedStr (𝓡 4) s) (hg : str.grade16 = 0) :
    -DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩ :=
  DataBordismGrp.mk_eq_of_bordant _ ⟨reflCylinder s, ⟨PLift.up (by
    show -str.grade16 = str.grade16
    rw [hg, neg_zero])⟩⟩

/-- **⛔ The phase's completeness node `hbound` is DISCHARGED AS STATED — by the collapse, not by
geometry.** Every grade-`0` class of the tied GM carrier is `0`: `3x = 0` (triple bordism through
the non-Hausdorff `W`) and `2x = 0` (`-x = x` + inverse law) force `x = 0`. This is exactly the
`hbound` binder of `SpinSigmaExactness` / the `D6` door — proven WITHOUT any geometric input, which
demonstrates the statement is too weak to carry the completeness content it was meant to name. -/
theorem grade0_eq_zero_of_nonHausdorff
    (x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hx : abkGMTied16 (k := 0) (I := 𝓡 4) x = 0) : x = 0 := by
  induction x using Quot.ind with | _ p =>
  obtain ⟨s, str⟩ := p
  have hg : str.grade16 = 0 := hx
  have h3 := dataBordismGMTied_triple s str hg
  have hneg := dataBordismGMTied_neg_self s str hg
  have h2 : DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      + DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩ = 0 := by
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel _
  rw [h2, zero_add] at h3
  exact h3

/-- **⛔ THE COLLAPSE, sharpest form: the tied GM carrier IS its grade.** Two structured manifolds
represent the same class **iff** their `ZMod 16` grades agree — the relation retains no geometric
information beyond the carried grade, so any "completeness" statement on this carrier is vacuously
about `ZMod 16` bookkeeping. This is the kernel-checked no-go against the T2-less substrate. -/
theorem dataBordismGMTied_mk_eq_iff_grade16_eq
    (p q : StrMfd (pinPlusGMTiedData (E := EuclideanSpace ℝ (Fin 4)) (k := 0) (𝓡 4))) :
    DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) p
      = DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) q
      ↔ p.2.grade16 = q.2.grade16 := by
  constructor
  · intro h
    exact congrArg (abkGMTied16 (k := 0) (I := 𝓡 4)) h
  · intro hgr
    have h0 : abkGMTied16 (k := 0) (I := 𝓡 4)
        (DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) p
          + -DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) q) = 0 := by
      rw [map_add, map_neg]
      have hp : abkGMTied16 (k := 0) (I := 𝓡 4)
          (DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) p) = p.2.grade16 := rfl
      have hq : abkGMTied16 (k := 0) (I := 𝓡 4)
          (DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) q) = q.2.grade16 := rfl
      rw [hp, hq, hgr, add_neg_cancel]
    have hz := grade0_eq_zero_of_nonHausdorff _ h0
    exact add_neg_eq_zero.mp hz

/-- **The σ-route door fires from the collapse** — `Nonempty (carrier ≃+ ZMod 16)` holds
unconditionally AS STATED. ⚠ This is NOT the phase's completeness achievement: the isomorphism is
the degenerate grade-bookkeeping one (`dataBordismGMTied_mk_eq_iff_grade16_eq`), obtained with zero
geometric input. It is recorded to make the vacuity of the current statement kernel-visible; the
genuine target must be restated on the T2-refined relation (`T2TiedBordism.lean`). -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_nonHausdorff_collapse :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_of_grade0_bounds
    (fun x hx => grade0_eq_zero_of_nonHausdorff x hx)

/-! ## §4. The hole is EXACTLY Hausdorff-ness: the collapsing `W` is provably non-T2 -/

/-- A product with the bug-eyed interval is never Hausdorff (slice inheritance). -/
theorem not_t2Space_prod_bugInterval {M : Type*} [TopologicalSpace M] (m₀ : M) :
    ¬T2Space (M × BugInterval) := by
  intro hT2
  apply not_t2Space_bugInterval
  constructor
  intro b₁ b₂ hb
  obtain ⟨U, V, hU, hV, hmU, hmV, hUV⟩ :=
    hT2.t2 (show (m₀, b₁) ≠ (m₀, b₂) from fun h => hb (congrArg Prod.snd h))
  refine ⟨_, _, hU.preimage (continuous_const.prodMk continuous_id),
    hV.preimage (continuous_const.prodMk continuous_id), hmU, hmV, ?_⟩
  exact Set.disjoint_left.mpr fun b hbU hbV => Set.disjoint_left.mp hUV hbU hbV

set_option linter.unusedSectionVars false in
/-- **The collapsing bordism manifold is provably non-Hausdorff** (for nonempty `s`): a `T2Space W`
field on `Bordism` excludes exactly this pathology — with compactness and charts, a T2 `W` is a
genuine (metrizable) bordism manifold, so the T2-refined relation (`T2TangentialBordism.lean`) is
honest bordism and the genuine completeness keystone survives there. -/
theorem tripleBordism_not_t2 (s : SingularManifold X 0 I) (m₀ : s.M) :
    ¬T2Space (tripleBordism s).W :=
  not_t2Space_prod_bugInterval m₀

end SKEFTHawking.NonHausdorffBordismCollapse
