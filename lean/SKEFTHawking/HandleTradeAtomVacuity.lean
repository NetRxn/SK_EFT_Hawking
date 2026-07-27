/-
# Phase 5q.H (N1a) — the Freeze-A handle-trade atom is ZERO-GEOMETRY SATISFIABLE

A **vacuity/degeneracy audit** of the Freeze-A geometric primitives the phase's E1 leaves terminate
at (`SpinSigmaRoute.lean` / `SphereProductRealization.lean` / `SphereProductRealizationAtoms.lean` /
`HandleTradeSurgery.lean`), run *before* any attempt to build one of them:

  (1) `SpinSigmaPresentation.HandleTradeCobordism` — the raw single-`S²×S²` handle-trace cobordism
      (Benedetti arXiv:1907.10297 Prop 20.16 / Lemma 20.17);
  (2) `SpinSigmaPresentation.HyperbolicBase` — the rank-0 nullbordism (Benedetti Thm 20.14).

**THE FINDING (both halves kernel-checked here).** Primitives (1) and (2) are each satisfiable, on
*any* tangential datum, with **no geometric input whatsoever** — no handle, no surgery, no embedded
sphere. The reason is structural: `SpinSigmaPresentation` carries `rank` and `form` as *free
disclosed data*, tied to the manifolds only through `sig_eq` (i.e. only through the signature). So a
presentation may choose `rank` to dodge whichever primitive it likes:

* **§3 — `collapsedPresentation`** puts `rank = 2` at the distinguished slot `p₀` and `rank = 0`
  everywhere else. Then the handle-trade hypothesis `Fin 2 ⊕ Fin m ≃ Fin (rank p)` can only fire at
  `p = p₀` with `m = 0`, and the demanded cobordism `p ↝ S²×S² ⊔ p'` is discharged by taking
  `p' = ∅` and the **unit cylinder** `(mapCylinder (sumEmpty …)).symm`
  (`collapsedPresentation_handleTradeCobordism`). No handle is attached anywhere.
* **§4 — `constRankTwoPresentation`** puts `rank ≡ 2`. Then primitive (2) is **vacuously** true: no
  structured manifold has rank `0` at all (`constRankTwoPresentation_rank_ne_zero`).

The two dodges are mutually exclusive (§4 refutes (1); §3 refutes (2) unless `Ω^ξ` collapses —
`collapsedPresentation_subsingleton_of_base_and_bounds`, which routes through the σ-route's own
`sig_injective`), so the *conjunction* of (1) and (2) still carries content. But **primitive (1)
carries none in isolation**: proving `HandleTradeCobordism` for *some* presentation is worth nothing,
and there is therefore nothing to gain by "building the handle-trade cobordism" at this grain. The
dodge propagates up the entire Freeze-A reduction chain (`HandleTradeSplit`, `HyperbolicPeel`), so no
statement layer above the primitive recovers the content either.

**THE REPAIR (§5).** What the two dodges exploit is that `SpinSigmaPresentation` never requires
`rank` to behave like `b₂`. `FaithfulRank` adds exactly the two literature-trivial facts that close
the hole — `b₂(∅) = 0` and additivity of `b₂` under disjoint union — and both degenerate
presentations are **refuted** by it (`constRankTwoPresentation_not_faithfulRank`,
`collapsedPresentation_not_faithfulRank`). Under `FaithfulRank` we then get the honest positive
statement `handleTradeConclusion_on_split`: primitive (1)'s conclusion is **free** on the split
locus `p = q ⊔ S²×S²` (the commutativity cylinder `commBor` is the required single cobordism), so the
irreducible geometric content of Benedetti Prop 20.16 is exactly *reduction to the split locus* —
not the cobordism, which the substrate already supplies there.

Additive module: modifies nothing upstream (imports `HandleTradeSurgery.lean`). Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HandleTradeSurgery

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open Matrix

universe u v

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {ξ : TangentialData.{u, v} X k I}

/-! ### §1. Cylinder cobordisms — the only structured cobordisms this module ever uses

Every "discharge" below is powered by one of these two: the unit cylinder and the commutativity
cylinder. Naming them separately is the point — it makes visible that no handle is ever attached. -/

/-- The **empty structured manifold** — the representative of `0 : DataBordismGrp ξ`. Every use of
the empty manifold below goes through this, so that its universe is pinned to `ξ`'s. -/
noncomputable def emptyStrMfd (ξ : TangentialData.{u, v} X k I) : StrMfd ξ := ⟨emptySM, ξ.emptyStr⟩

@[simp] theorem mk_emptyStrMfd (ξ : TangentialData.{u, v} X k I) :
    DataBordismGrp.mk ξ (emptyStrMfd ξ) = 0 := rfl

/-- **The unit cylinder as a SINGLE structured cobordism**: `p ↝ p ⊔ ∅`. The reverse of the
presentation-independent unit law `unitBor`; not a handle attachment. -/
theorem isDataBordant_sum_empty (p : StrMfd ξ) :
    IsDataBordant ξ p ⟨p.1.sum (emptyStrMfd ξ).1, ξ.sumStr p.2 (emptyStrMfd ξ).2⟩ :=
  ⟨_, ⟨ξ.symmBor (ξ.unitBor p.2)⟩⟩

/-- **The commutativity cylinder as a SINGLE structured cobordism**: `p ⊔ q ↝ q ⊔ p`. -/
theorem isDataBordant_sum_comm (p q : StrMfd ξ) :
    IsDataBordant ξ ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩ ⟨q.1.sum p.1, ξ.sumStr q.2 p.2⟩ :=
  ⟨_, ⟨ξ.commBor p.2 q.2⟩⟩

/-- The empty structured manifold is distinct from any structured manifold with a **nonempty**
underlying carrier — the only inhabitation input the §3 dodge needs (on the genuine slot it is
witnessed by `S²×S²` itself). -/
theorem emptyStrMfd_ne {p : StrMfd ξ} (hp : Nonempty p.1.M) : emptyStrMfd ξ ≠ p := by
  rintro rfl
  have he : IsEmpty (emptyStrMfd ξ).fst.M :=
    inferInstanceAs (IsEmpty (emptySM (X := X) (k := k) (I := I)).M)
  exact he.false hp.some

/-! ### §2. A rank-`{0,2}` form carried with no dependent casts

`offDiagOne n` is `0` on the diagonal and `1` off it: the empty matrix at `n = 0`, exactly `Hyp` at
`n = 2`. A single uniform formula lets a presentation whose `rank` takes only the values `0` and `2`
carry its `form` field without any transport along `rank`-equations. -/

/-- The `n × n` integer matrix with `0` on the diagonal and `1` off it. -/
def offDiagOne (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => if i = j then 0 else 1

@[simp] theorem offDiagOne_zero : offDiagOne 0 = 0 := by funext i; exact isEmptyElim i

@[simp] theorem offDiagOne_two : offDiagOne 2 = Hyp := by decide

/-- The one-block hyperbolic reindex is congruent to `Hyp` (the `s2s2_hyp`-shaped witness, named once
and reused). -/
theorem intCongr_hyp_block :
    IntCongr Hyp (Matrix.reindex (Equiv.sumEmpty (Fin 2) (Fin 0)) (Equiv.sumEmpty (Fin 2) (Fin 0))
      (Matrix.fromBlocks Hyp 0 0 (0 : Matrix (Fin 0) (Fin 0) ℤ))) := by
  rw [reindex_one_block_eq_hyp]
  exact IntCongr.rfl Hyp

theorem isEvenUnimodular_offDiagOne :
    ∀ {n : ℕ}, n = 0 ∨ n = 2 → IsEvenUnimodular (offDiagOne n) := by
  rintro n (rfl | rfl)
  · rw [offDiagOne_zero]; exact IsHyperbolicForm.empty.isEvenUnimodular
  · rw [offDiagOne_two]; exact ⟨hyp_symm, hyp_unimodular, hyp_even⟩

theorem latticeSig_offDiagOne : ∀ {n : ℕ}, n = 0 ∨ n = 2 → latticeSig (offDiagOne n) = 0 := by
  rintro n (rfl | rfl)
  · rw [offDiagOne_zero]; exact latticeSig_zero_matrix
  · rw [offDiagOne_two]; exact hyp_latticeSig

theorem exists_hyperbolic_offDiagOne : ∀ {n : ℕ}, n = 0 ∨ n = 2 →
    ∃ N : Matrix (Fin n) (Fin n) ℤ, IsHyperbolicForm N ∧ IntCongr (offDiagOne n) N := by
  rintro n (rfl | rfl)
  · exact ⟨0, IsHyperbolicForm.empty, by rw [offDiagOne_zero]; exact IntCongr.rfl 0⟩
  · refine ⟨_, IsHyperbolicForm.cons (Equiv.sumEmpty (Fin 2) (Fin 0)) IsHyperbolicForm.empty, ?_⟩
    rw [offDiagOne_two]
    exact intCongr_hyp_block

/-! ### §3. The rank-collapsed presentation — primitive (1) with ZERO geometry -/

/-- The **rank-collapsed rank function**: `2` at the distinguished slot `p₀`, `0` everywhere else.
Nothing in `SpinSigmaPresentation` forbids it. -/
noncomputable def collapsedRank (p₀ p : StrMfd ξ) : ℕ :=
  @ite ℕ (p = p₀) (Classical.propDecidable _) 2 0

theorem collapsedRank_self (p₀ : StrMfd ξ) : collapsedRank p₀ p₀ = 2 := if_pos rfl

theorem collapsedRank_of_ne {p₀ p : StrMfd ξ} (h : p ≠ p₀) : collapsedRank p₀ p = 0 := if_neg h

theorem collapsedRank_cases (p₀ p : StrMfd ξ) :
    collapsedRank p₀ p = 0 ∨ collapsedRank p₀ p = 2 := by
  by_cases h : p = p₀
  · exact Or.inr (h ▸ collapsedRank_self p₀)
  · exact Or.inl (collapsedRank_of_ne h)

theorem eq_of_collapsedRank_eq_two {p₀ p : StrMfd ξ} (h : collapsedRank p₀ p = 2) : p = p₀ := by
  by_contra hne
  rw [collapsedRank_of_ne hne] at h
  exact absurd h (by norm_num)

/-- **The rank-collapsed σ-presentation.** Every field of `SpinSigmaPresentation` is satisfied:
`sig = 0` (a legitimate bordism-invariant hom), `form = offDiagOne ∘ rank` (even unimodular of
signature `0` at both admissible ranks), and the distinguished slot `p₀` is pinned at rank `2` with
a hyperbolic form. It is not a "toy": `ξ` and `p₀` are arbitrary, so `p₀` may be the genuine
`S²×S²` spin element on the genuine spin datum. -/
noncomputable def collapsedPresentation (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ) :
    SpinSigmaPresentation ξ where
  sig := 0
  rank p := collapsedRank p₀ p
  form p := offDiagOne (collapsedRank p₀ p)
  even_unimod p := isEvenUnimodular_offDiagOne (collapsedRank_cases p₀ p)
  sig_eq p := by
    show (0 : ℤ) = _
    rw [latticeSig_offDiagOne (collapsedRank_cases p₀ p)]
  s2s2 := p₀
  s2s2_rank := collapsedRank_self p₀
  s2s2_hyp := exists_hyperbolic_offDiagOne (Or.inr (collapsedRank_self p₀))

@[simp] theorem collapsedPresentation_rank (ξ : TangentialData.{u, v} X k I) (p₀ p : StrMfd ξ) :
    (collapsedPresentation ξ p₀).rank p = collapsedRank p₀ p := rfl

@[simp] theorem collapsedPresentation_s2s2 (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ) :
    (collapsedPresentation ξ p₀).s2s2 = p₀ := rfl

/-- Rank-`2` supplies a witness of the handle-trade *hypothesis* (the one-block split with empty
complement). Stated over an abstract `n = 2` so it transports into the dependent `Fin (rank …)`
position with no cast. -/
theorem exists_oneBlock_split : ∀ {n : ℕ}, n = 2 →
    ∃ E : Fin 2 ⊕ Fin 0 ≃ Fin n, IntCongr (offDiagOne n)
      (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 (0 : Matrix (Fin 0) (Fin 0) ℤ))) := by
  rintro n rfl
  exact ⟨Equiv.sumEmpty (Fin 2) (Fin 0), by rw [offDiagOne_two]; exact intCongr_hyp_block⟩

/-- **The dodge is NOT itself ∀-vacuous.** The handle-trade hypothesis genuinely *fires* for the
collapsed presentation — at the distinguished slot, with `m = 0` and the empty complement. So
`collapsedPresentation_handleTradeCobordism` discharges a non-empty obligation with a cylinder; it is
not a statement whose antecedent is unsatisfiable. (This is the check the `sphereProdSM4` lesson
demands of any claimed discharge, applied here to the *counter*-claim.) -/
theorem collapsedPresentation_hypothesis_fires (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ) :
    ∃ E : Fin 2 ⊕ Fin 0 ≃ Fin ((collapsedPresentation ξ p₀).rank p₀),
      IntCongr ((collapsedPresentation ξ p₀).form p₀)
        (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 (0 : Matrix (Fin 0) (Fin 0) ℤ))) :=
  exists_oneBlock_split (collapsedRank_self p₀)

/-- **PRIMITIVE (1) IS SATISFIABLE WITH ZERO GEOMETRIC INPUT.** The raw handle-trace cobordism
`HandleTradeCobordism` — the phase's designated "one manifold-surgery primitive a future E1
foundation must build" — holds for the rank-collapsed presentation on **any** tangential datum, for
**any** distinguished slot with a nonempty carrier. The proof attaches no handle: the collapsed rank
forces the hypothesis to fire only at `p = p₀` with `m = 0`, and the demanded cobordism
`p₀ ↝ S²×S² ⊔ p'` is discharged with `p' = ∅` by the **unit cylinder** (`isDataBordant_sum_empty`).
Hence proving `HandleTradeCobordism` for *some* presentation establishes nothing about
handle-trading, and building it at this grain is not a route to Freeze A. -/
theorem collapsedPresentation_handleTradeCobordism (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) (hp₀ : Nonempty p₀.1.M) :
    SpinSigmaPresentation.HandleTradeCobordism.{_, _, _, u, u, v} (collapsedPresentation ξ p₀) := by
  intro p m e N' _ _
  have hcard : 2 + m = collapsedRank p₀ p := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    exact h
  have hrk2 : collapsedRank p₀ p = 2 := by
    rcases collapsedRank_cases p₀ p with h | h <;> omega
  obtain rfl : m = 0 := by omega
  obtain rfl : p = p₀ := eq_of_collapsedRank_eq_two hrk2
  exact ⟨emptyStrMfd ξ, collapsedRank_of_ne (emptyStrMfd_ne hp₀), isDataBordant_sum_empty p⟩

/-- The zero-geometry dodge propagates up the whole Freeze-A reduction chain: it also discharges the
form-free split atom `HandleTradeSplit` … -/
theorem collapsedPresentation_handleTradeSplit (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ)
    (hp₀ : Nonempty p₀.1.M) : (collapsedPresentation ξ p₀).HandleTradeSplit :=
  SpinSigmaPresentation.handleTradeSplit_of_cobordism _
    (collapsedPresentation_handleTradeCobordism ξ p₀ hp₀)

/-- … and the full single-handle-trade atom `HyperbolicPeel`. So none of the statement layers built
over primitive (1) recovers any geometric content the primitive itself lacks. -/
theorem collapsedPresentation_hyperbolicPeel (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ)
    (hp₀ : Nonempty p₀.1.M) : (collapsedPresentation ξ p₀).HyperbolicPeel :=
  SpinSigmaPresentation.hyperbolicPeel_of_handleTradeCobordism _
    (collapsedPresentation_handleTradeCobordism ξ p₀ hp₀)

/-- **Where the geometric weight actually sits.** The collapsed presentation cannot ALSO satisfy
primitive (2) and Freeze B without trivialising the bordism group: its signature homomorphism is the
zero map, so the σ-route's own `sig_injective` — fed the collapsed handle-trade via
`realizesSphereProducts_of_cobordism_and_base` — forces `Ω^ξ` to be a singleton. Since `Ω₄^{Spin}`
is not trivial, the pair (1) ∧ (2) is not jointly zero-geometry satisfiable this way: all of the
Freeze-A geometry that survives the audit lives in primitive (2) plus `rank`-faithfulness (§5). -/
theorem collapsedPresentation_subsingleton_of_base_and_bounds (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) (hp₀ : Nonempty p₀.1.M)
    (hBase : (collapsedPresentation ξ p₀).HyperbolicBase)
    (hB : (collapsedPresentation ξ p₀).SphereProductBounds) (x : DataBordismGrp ξ) : x = 0 :=
  (collapsedPresentation ξ p₀).sig_injective
      (SpinSigmaPresentation.realizesSphereProducts_of_cobordism_and_base _
        (collapsedPresentation_handleTradeCobordism ξ p₀ hp₀) hBase) hB
    (show (0 : DataBordismGrp ξ →+ ℤ) x = (0 : DataBordismGrp ξ →+ ℤ) 0 from rfl)

/-! ### §4. The constant-rank-2 presentation — primitive (2) VACUOUSLY -/

/-- **The constant-rank-2 σ-presentation**: every structured manifold is declared to have `b₂ = 2`
and hyperbolic form. Again every `SpinSigmaPresentation` field is satisfied. -/
noncomputable def constRankTwoPresentation (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ) :
    SpinSigmaPresentation ξ where
  sig := 0
  rank _ := 2
  form _ := Hyp
  even_unimod _ := ⟨hyp_symm, hyp_unimodular, hyp_even⟩
  sig_eq _ := by show (0 : ℤ) = _; rw [hyp_latticeSig]
  s2s2 := p₀
  s2s2_rank := rfl
  s2s2_hyp :=
    ⟨_, IsHyperbolicForm.cons (Equiv.sumEmpty (Fin 2) (Fin 0)) IsHyperbolicForm.empty,
      intCongr_hyp_block⟩

@[simp] theorem constRankTwoPresentation_rank (ξ : TangentialData.{u, v} X k I) (p₀ p : StrMfd ξ) :
    (constRankTwoPresentation ξ p₀).rank p = 2 := rfl

/-- The constant-rank-2 presentation has **no** rank-`0` structured manifold — the literal, checkable
form of the vacuity below. -/
theorem constRankTwoPresentation_rank_ne_zero (ξ : TangentialData.{u, v} X k I) (p₀ p : StrMfd ξ) :
    (constRankTwoPresentation ξ p₀).rank p ≠ 0 := two_ne_zero

/-- **PRIMITIVE (2) IS SATISFIABLE WITH ZERO GEOMETRIC INPUT — vacuously.** `HyperbolicBase` (the
rank-0 nullbordism, Benedetti Thm 20.14) holds for the constant-rank-2 presentation because its
antecedent `rank p = 0` is never satisfied (`constRankTwoPresentation_rank_ne_zero`). No manifold
bounds anything in this proof. -/
theorem constRankTwoPresentation_hyperbolicBase (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) : (constRankTwoPresentation ξ p₀).HyperbolicBase :=
  fun p hp => absurd hp (constRankTwoPresentation_rank_ne_zero ξ p₀ p)

/-- **The two dodges are mutually exclusive.** The constant-rank-2 presentation *refutes* primitive
(1): the handle-trade hypothesis fires at the slot itself (its form is `Hyp`), but the demanded
residual would need rank `0`, which no manifold has. So no single degenerate `rank` choice kills
both primitives at once — the conjunction retains content, the individual atoms do not. -/
theorem constRankTwoPresentation_not_handleTradeCobordism (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) :
    ¬ SpinSigmaPresentation.HandleTradeCobordism.{_, _, _, u, u, v} (constRankTwoPresentation ξ p₀) := by
  intro h
  obtain ⟨p', hrk, -⟩ :=
    h p₀ 0 (Equiv.sumEmpty (Fin 2) (Fin 0)) 0 IsHyperbolicForm.empty intCongr_hyp_block
  exact constRankTwoPresentation_rank_ne_zero ξ p₀ p' hrk

/-! ### §5. The repair — `rank` faithfulness, and what primitive (1) then costs -/

/-- **The faithfulness `SpinSigmaPresentation` never required.** Both fields are literature-trivial
facts about the second Betti number that any genuine E1 `interMatrix` presentation satisfies:
`b₂(∅) = 0`, and `b₂` is additive under disjoint union. `SpinSigmaPresentation` asks for neither —
which is exactly the room the §3 and §4 dodges exploit. -/
structure SpinSigmaPresentation.FaithfulRank (R : SpinSigmaPresentation ξ) : Prop where
  /-- The empty manifold has `b₂ = 0`. -/
  rank_empty : R.rank (emptyStrMfd ξ) = 0
  /-- `b₂` is additive under disjoint union. -/
  rank_sum : ∀ p q : StrMfd ξ,
    R.rank ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩ = R.rank p + R.rank q

/-- Faithfulness **refutes the §4 dodge**: a constant rank of `2` assigns `b₂ = 2` to the empty
manifold. -/
theorem constRankTwoPresentation_not_faithfulRank (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) : ¬ (constRankTwoPresentation ξ p₀).FaithfulRank :=
  fun h => two_ne_zero h.rank_empty

/-- Faithfulness **refutes the §3 dodge**: additivity forces `b₂(p₀ ⊔ p₀) = 4`, but the collapsed
rank only ever takes the values `0` and `2`. -/
theorem collapsedPresentation_not_faithfulRank (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) : ¬ (collapsedPresentation ξ p₀).FaithfulRank := by
  intro h
  have h1 := h.rank_sum p₀ p₀
  simp only [collapsedPresentation_rank, collapsedRank_self] at h1
  rcases collapsedRank_cases p₀ (⟨p₀.1.sum p₀.1, ξ.sumStr p₀.2 p₀.2⟩ : StrMfd ξ) with h2 | h2 <;>
    omega

/-- **The handle-trade atom's conclusion is FREE on the split locus.** For a manifold that is
*already* a disjoint union `q ⊔ S²×S²`, primitive (1)'s entire output — a residual of the
complementary rank (`rank p' + 2 = rank (q ⊔ S²×S²)`, by faithfulness) together with ONE structured
cobordism to `S²×S² ⊔ residual` — is supplied by the substrate's **commutativity cylinder**
(`isDataBordant_sum_comm`). No handle, no surgery, no embedded sphere.

So the irreducible geometric content of Benedetti Prop 20.16 / Lemma 20.17 is *not* "produce a
cobordism": it is precisely **reduction to the split locus** — showing that a `p` whose intersection
form splits off `H` is, up to one cobordism, already such a disjoint union. That, and not
`HandleTradeCobordism` as currently stated, is what a future E1 manifold-surgery foundation owes. -/
theorem handleTradeConclusion_on_split (R : SpinSigmaPresentation ξ) (hF : R.FaithfulRank)
    (q : StrMfd ξ) :
    ∃ p' : StrMfd ξ,
      R.rank p' + 2 = R.rank (⟨q.1.sum R.s2s2.1, ξ.sumStr q.2 R.s2s2.2⟩ : StrMfd ξ) ∧
      IsDataBordant ξ (⟨q.1.sum R.s2s2.1, ξ.sumStr q.2 R.s2s2.2⟩ : StrMfd ξ)
        (⟨R.s2s2.1.sum q.1, ξ.sumStr R.s2s2.2 q.2⟩ : StrMfd ξ) :=
  ⟨q, by rw [hF.rank_sum q R.s2s2, R.s2s2_rank], isDataBordant_sum_comm q R.s2s2⟩

end SKEFTHawking.SpinSigmaRoute
