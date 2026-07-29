/-
# Phase 5q.H (N1a) — Freeze A on a CONSTRAINED presentation: reduction to the split locus

The re-scoped successor to `HandleTradeAtomVacuity.lean`. That module's kernel-checked finding was
that the Freeze-A handle-trace primitive `SpinSigmaPresentation.HandleTradeCobordism` is satisfiable
with **zero geometric input** (a cylinder), because `SpinSigmaPresentation` carries `rank` as free
disclosed data tied to the manifolds only through `sig_eq`. Its §5 located the residue precisely:
primitive (1)'s *conclusion* is free on the **split locus** `q ⊔ S²×S²`, so the irreducible Benedetti
content (arXiv:1907.10297 Prop 20.16 / Lemma 20.17) is **REDUCTION TO THE SPLIT LOCUS**, not
production of a cobordism.

This module acts on that finding.

* **§2 the constraint.** `FaithfulSpinSigmaPresentation` — a `SpinSigmaPresentation` carrying two
  literature-trivial facts about `b₂` as *fields*: `b₂ = 0` on an **empty carrier**, and `b₂`
  additive under disjoint union. Both dodges of the vacuity audit are excluded, and — the point —
  §3 shows the exclusion is not case-by-case but **regional**: a faithful presentation has
  *unbounded* rank (`rank (n·S²×S²) = 2n`), so the whole `rank ≤ 2` region in which both dodges
  live, and which Sylvester's `|σ| ≤ b₂` already bars from carrying the route's `σ = −16` generator
  (`no_generator_of_rank_le_two`), contains **no faithful presentation at all**.
* **§5–§6 the reduction.** `BordantToSplitLocus` — the primitive that is NOT free: a manifold whose
  form splits off `H` is bordant to a manifold *literally* of the shape `q ⊔ S²×S²` **of the same
  rank**. Its conclusion at an already-split `p` is free (§6, disclosed), and that is the whole of
  what the audit found free; everything off the split locus is the geometry.
* **§7 the wiring.** `BordantToSplitLocus → HandleTradeSplit → HyperbolicPeel →
  RealizesSphereProducts` (kernel-pure), hence `sig_injective` and `Ω₄^{Spin} ≃+ ℤ`.
* **§8 falsifiability.** The new primitive is *refutable*: with the base + bounds freezes it forces
  `σ` injective, so a single nonzero `σ = 0` class kills it. This is the sharp contrast with the
  audited primitive — `HandleTradeCobordism` is satisfiable by a cylinder on **every** tangential
  datum (`collapsedPresentation_handleTradeCobordism`), whereas `BordantToSplitLocus` on a faithful
  presentation is outright FALSE on any carrier with a nonzero `σ = 0` class. It therefore cannot be
  a theorem of the substrate, and no presentation-level `rank` choice can make it free.

  *What is NOT proved here*: that the substrate's coherence cylinders fail to reach the conclusion at
  a specific non-split `p`. The substrate offers only `reflCylinder`, `mapCylinder`, `doublingBordism`
  and `Bordism.add` (there is no single-cobordism transitivity — that is what `Quot` is for), so no
  free cobordism out of an atomic `p` is apparent; but that is an observation about the available
  constructors, not a theorem, and it is not claimed as one.
* **§9 non-vacuity.** The constrained type is INHABITED, with **unbounded rank** — the gap
  `HandleTradeAtomVacuity` left open when it declined to claim an inhabitant for `FaithfulRank`. The
  witness is the rank-graded datum `rankGraded ξ₀` over an arbitrary base datum: the base's manifolds,
  structures and bordisms verbatim, decorated with an additive `b₂`-label forced to `0` on empty
  carriers. §9 also checks the witness against the new primitive: it cannot discharge it for free
  either — doing so would collapse `Ω^ξ`.

Universe hygiene (task #314): `SpinSigmaPresentation.HandleTradeCobordism` elaborates with **six**
universe parameters (`ξ : TangentialData.{max u₇ u₈, u₉, …}`), because the inline
`⟨R.s2s2.fst.sum p'.fst, …⟩` lets Lean generalize `SingularManifold.sum`'s two carrier universes
independently — so it cannot be mentioned from another file without hand-supplied levels. Everything
here goes through the universe-pinned `StrMfd.sum` (§1), whose signature keeps a single manifold
universe; no declaration in this module needs explicit level arguments.

Additive module (imports `HandleTradeAtomVacuity.lean`); modifies nothing upstream. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HandleTradeAtomVacuity

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open Matrix

universe u v

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {ξ : TangentialData.{u, v} X k I}

/-! ### §1. The universe-pinned disjoint union of structured manifolds

`SingularManifold.sum.{u₇,u₈} : SingularManifold.{u₈} → SingularManifold.{u₇} →
SingularManifold.{max u₇ u₈}` is polymorphic in the two carrier universes *independently*. Written
inline inside a statement (as `HandleTradeCobordism` does) Lean generalizes both, and the enclosing
declaration acquires a `max u₇ u₈` manifold universe — six universe parameters, unmentionable from
another file without hand-supplied levels. Routing every disjoint union through this definition, whose
binders force both arguments into `ξ`'s single manifold universe, keeps the level shape flat. -/

/-- Disjoint union of structured manifolds, `p ⊔ q`, with both carrier universes pinned to `ξ`'s. -/
noncomputable def StrMfd.sum (p q : StrMfd ξ) : StrMfd ξ := ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩

@[simp] theorem mk_strMfd_sum (p q : StrMfd ξ) :
    DataBordismGrp.mk ξ (StrMfd.sum p q) = DataBordismGrp.mk ξ p + DataBordismGrp.mk ξ q := rfl

/-- The `n`-fold disjoint union `n · p` (with `0 · p = ∅`). -/
noncomputable def StrMfd.nsum (p : StrMfd ξ) : ℕ → StrMfd ξ
  | 0 => emptyStrMfd ξ
  | n + 1 => StrMfd.sum (StrMfd.nsum p n) p

/-- The class of the `n`-fold disjoint union is `n • [p]` — the manifold-level realization of the
`(rank/2) • [S²×S²]` right-hand side of `RealizesSphereProducts`. -/
theorem mk_nsum (p : StrMfd ξ) (n : ℕ) :
    DataBordismGrp.mk ξ (StrMfd.nsum p n) = n • DataBordismGrp.mk ξ p := by
  induction n with
  | zero => rw [StrMfd.nsum, mk_emptyStrMfd, zero_nsmul]
  | succ n ih => rw [StrMfd.nsum, mk_strMfd_sum, ih, succ_nsmul]

/-- Reflexivity of the structured cobordism relation (the reflexive cylinder) — used only to make
visible, in §6, exactly where the new primitive's conclusion is free. -/
theorem isDataBordant_refl (p : StrMfd ξ) : IsDataBordant ξ p p :=
  ⟨reflCylinder p.1, ⟨ξ.cylBor p.2⟩⟩

/-! ### §2. The constraint — a presentation whose `rank` behaves like `b₂`

`HandleTradeAtomVacuity`'s root-cause diagnosis: `SpinSigmaPresentation` carries `rank` and `form` as
free disclosed data, tied to the manifolds only through `sig_eq`, so nothing forces `rank` to behave
like `b₂`. The two fields below are exactly the facts about the second Betti number that close the
hole, and nothing more:

* `rank_empty_carrier` — a manifold with **empty carrier** has `b₂ = 0`. This is deliberately stated
  on the carrier, not on the canonical `emptyStrMfd ξ`: the weaker `rank (emptyStrMfd ξ) = 0` leaves
  open a *phantom rank*, a different tangential structure on the same empty manifold declaring a
  nonzero `b₂`, which is enough to rebuild a cylinder dodge.
* `rank_sum` — `b₂` is additive under disjoint union.

Both are literature-trivial and hold for the genuine E1 `interMatrix` presentation by construction.
Their role is to make Freeze A a statement about handle-trading rather than about a cylinder; §3
measures how much they exclude. -/

/-- **The constrained σ-presentation**: a `SpinSigmaPresentation` whose declared `rank` satisfies the
two defining `b₂` facts (empty-carrier vanishing + additivity under disjoint union). -/
structure FaithfulSpinSigmaPresentation (ξ : TangentialData.{u, v} X k I) extends
    SpinSigmaPresentation ξ where
  /-- `b₂ = 0` on an empty carrier (stated on the carrier — see the section docstring). -/
  rank_empty_carrier : ∀ p : StrMfd ξ, IsEmpty p.1.M → rank p = 0
  /-- `b₂` is additive under disjoint union. -/
  rank_sum : ∀ p q : StrMfd ξ, rank (StrMfd.sum p q) = rank p + rank q

namespace FaithfulSpinSigmaPresentation

variable (R : FaithfulSpinSigmaPresentation ξ)

/-- The empty structured manifold has rank `0`. -/
theorem rank_emptyStrMfd : R.rank (emptyStrMfd ξ) = 0 :=
  R.rank_empty_carrier _ (inferInstanceAs (IsEmpty (emptySM (X := X) (k := k) (I := I)).M))

/-- The constraint implies the `FaithfulRank` soundness side-condition of `HandleTradeAtomVacuity`
§5 — so every refutation proved there against the two zero-geometry dodges transfers verbatim. -/
theorem faithfulRank : R.toSpinSigmaPresentation.FaithfulRank where
  rank_empty := R.rank_emptyStrMfd
  rank_sum := R.rank_sum

/-- **The distinguished `S²×S²` slot has a nonempty carrier — derived, not assumed.** This is the
concrete payoff of stating empty-carrier vanishing on the *carrier* rather than on the canonical
`emptyStrMfd ξ`: nothing in `SpinSigmaPresentation`, and nothing in the weaker `rank_empty` of
`FaithfulRank`, stops the `s2s2` slot from being the **empty manifold** under some non-canonical
structure with a declared `b₂ = 2` — an `S²×S²` that is not there. Under `rank_empty_carrier` that is
impossible, since `s2s2_rank = 2`.

Note what this converts: `Nonempty p₀.1.M` was a *hypothesis* of the audit's zero-geometry discharge
`collapsedPresentation_handleTradeCobordism`. On the constrained type it is a *theorem* about the
slot, so the split locus `q ⊔ S²×S²` is a genuine enlargement of `q` rather than possibly a unit
cylinder in disguise. -/
theorem s2s2_carrier_nonempty : Nonempty R.s2s2.1.M := by
  by_contra hne
  have : R.rank R.s2s2 = 0 := R.rank_empty_carrier _ (not_nonempty_iff.mp hne)
  rw [R.s2s2_rank] at this
  exact two_ne_zero this

/-! ### §3. What the constraint excludes — the whole rank-bounded region

Not "the two dodges are refuted case by case", but: a faithful presentation's rank is **unbounded**.
Both zero-geometry dodges are rank-`≤ 2`, and by `HandleTradeAtomVacuity`'s Sylvester bound
`abs_sig_le_rank` a rank-`≤ 2` presentation cannot carry the route's `σ = −16` generator at all
(`no_generator_of_rank_le_two`). §3 shows that region is not merely bad — it is **empty of faithful
presentations**. -/

/-- Rank of an `n`-fold disjoint union. -/
theorem rank_nsum (p : StrMfd ξ) (n : ℕ) : R.rank (StrMfd.nsum p n) = n * R.rank p := by
  induction n with
  | zero =>
    -- v4.32: simp no longer reduces `nsum p 0` to `emptyStrMfd`, and the RHS is `0 * rank p`.
    -- Unfold explicitly, exactly as the succ branch below already does.
    rw [StrMfd.nsum, Nat.zero_mul]; exact R.rank_emptyStrMfd
  | succ n ih => rw [StrMfd.nsum, R.rank_sum, ih, Nat.succ_mul]

/-- `n` copies of `S²×S²` have rank `2n` — the falsifiable numerical content of additivity, pinned
against the `s2s2_rank = 2` field. -/
theorem rank_nsum_s2s2 (n : ℕ) : R.rank (StrMfd.nsum R.s2s2 n) = 2 * n := by
  rw [rank_nsum, R.s2s2_rank, Nat.mul_comm]

/-- **A faithful presentation has unbounded rank.** -/
theorem exists_rank_gt (n : ℕ) : ∃ p : StrMfd ξ, n < R.rank p :=
  ⟨StrMfd.nsum R.s2s2 (n + 1), by rw [rank_nsum_s2s2]; omega⟩

/-- **The Sylvester-excluded region contains no faithful presentation.** `rank ≤ 2` is the shape of
*both* zero-geometry dodges of `HandleTradeAtomVacuity` (§3 `collapsedPresentation`, §4
`constRankTwoPresentation`) and, by `no_generator_of_rank_le_two`, exactly the region barred from
hosting the route's `σ = −16` generator. No faithful presentation lies in it: `S²×S² ⊔ S²×S²`
already has rank `4`. -/
theorem not_rank_le_two : ¬ ∀ p : StrMfd ξ, R.rank p ≤ 2 := by
  intro h
  have := h (StrMfd.nsum R.s2s2 2)
  rw [rank_nsum_s2s2] at this
  omega

end FaithfulSpinSigmaPresentation

/-! ### §4. Regression against the two zero-geometry dodges

The audit's dodges are not merely excluded as presentations — they cannot be the underlying
presentation of any faithful one. -/

/-- **The rank-collapsed dodge is not the shadow of any faithful presentation** (additivity forces
`b₂(p₀ ⊔ p₀) = 4`, which the collapsed rank cannot produce). -/
theorem no_faithful_over_collapsedPresentation (ξ : TangentialData.{u, v} X k I) (p₀ : StrMfd ξ) :
    ¬ ∃ R : FaithfulSpinSigmaPresentation ξ,
      R.toSpinSigmaPresentation = collapsedPresentation ξ p₀ := by
  rintro ⟨R, hR⟩
  exact collapsedPresentation_not_faithfulRank ξ p₀ (hR ▸ R.faithfulRank)

/-- **The constant-rank-2 dodge is not the shadow of any faithful presentation** (it assigns
`b₂ = 2` to the empty manifold). -/
theorem no_faithful_over_constRankTwoPresentation (ξ : TangentialData.{u, v} X k I)
    (p₀ : StrMfd ξ) :
    ¬ ∃ R : FaithfulSpinSigmaPresentation ξ,
      R.toSpinSigmaPresentation = constRankTwoPresentation ξ p₀ := by
  rintro ⟨R, hR⟩
  exact constRankTwoPresentation_not_faithfulRank ξ p₀ (hR ▸ R.faithfulRank)

/-! ### §5. The split locus, and the primitive that is NOT free -/

/-- **The split locus of `s`**: the structured manifolds that are *literally* a disjoint union with
`s`. For `s = S²×S²` this is where `HandleTradeAtomVacuity` §5 located the whole free part of the
Freeze-A handle-trade primitive. -/
def IsSplitOff (s p : StrMfd ξ) : Prop := ∃ q : StrMfd ξ, p = StrMfd.sum q s

namespace FaithfulSpinSigmaPresentation

variable (R : FaithfulSpinSigmaPresentation ξ)

/-- **The handle-trade conclusion, verbatim, on the split locus — for free.** For `p` already of the
shape `q ⊔ S²×S²`, the entire output of the Freeze-A primitive `HandleTradeCobordism` (a residual of
the complementary rank together with ONE structured cobordism to `S²×S² ⊔ residual`) is supplied by
the substrate's commutativity cylinder, with the rank bookkeeping supplied by `rank_sum`. No handle,
no surgery, no embedded sphere — and note this is now proved *under the constraint*, so it is not an
artefact of a degenerate `rank`. This is the sharpened form of `handleTradeConclusion_on_split`, and
it is what forces the residual geometric ask to be a *reduction to* this locus. -/
theorem handleTradeConclusion_of_isSplitOff {p : StrMfd ξ} (h : IsSplitOff R.s2s2 p) :
    ∃ p' : StrMfd ξ, R.rank p' + 2 = R.rank p ∧ IsDataBordant ξ p (StrMfd.sum R.s2s2 p') := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨q, by rw [R.rank_sum q R.s2s2, R.s2s2_rank], isDataBordant_sum_comm q R.s2s2⟩

/-- **The irreducible Benedetti content — reduction to the split locus.** Inputs identical to
`HyperbolicPeel` / `HandleTradeSplit` / `HandleTradeCobordism` (a structured manifold `p` whose form
splits off one hyperbolic plane `H` over a hyperbolic-standard complement `N'`); the output is
neither a bordism-group equation nor a bare cobordism, but the statement that `p` is bordant to a
manifold **lying in the split locus** `q ⊔ S²×S²`, **of the same rank**.

This is what the vacuity audit left: the cobordism *out of* the split locus is free
(`handleTradeConclusion_of_isSplitOff`), so all the geometry is in getting there. Rank preservation
is Benedetti's actual output — the handle trade replaces `p` by a bordant manifold with the same
`b₂ = 2 + m` — and it is what makes the residual's rank come out right (`m`) rather than being
declared, which is precisely the freedom the collapsed dodge exploited. -/
def BordantToSplitLocus : Prop :=
  ∀ (p : StrMfd ξ) (m : ℕ) (E : Fin 2 ⊕ Fin m ≃ Fin (R.rank p))
    (N' : Matrix (Fin m) (Fin m) ℤ), IsHyperbolicForm N' →
    IntCongr (R.form p) (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ p₀ : StrMfd ξ, IsSplitOff R.s2s2 p₀ ∧ R.rank p₀ = R.rank p ∧ IsDataBordant ξ p p₀

/-! ### §6. Where the new primitive is free — the honest disclosure

Any "reduction to `L`" statement is free *on* `L`; that is not a defect, it is the factorization. The
lemma below makes the free part explicit and kernel-checked, so the primitive's content is exactly
located: off the split locus. -/

/-- **The primitive's conclusion is free at an already-split `p`** (take `p₀ = p` and the reflexive
cylinder). So the content of `BordantToSplitLocus` is entirely at the `p` that are *not* disjoint
unions with `S²×S²` — which is the correct factorization of Benedetti Prop 20.16, not a residual
vacuity. -/
theorem bordantToSplitLocus_conclusion_free_on_split {p : StrMfd ξ} (h : IsSplitOff R.s2s2 p) :
    ∃ p₀ : StrMfd ξ, IsSplitOff R.s2s2 p₀ ∧ R.rank p₀ = R.rank p ∧ IsDataBordant ξ p p₀ :=
  ⟨p, h, rfl, isDataBordant_refl p⟩

/-! ### §7. The wiring — the reduction discharges Freeze A -/

/-- **Reduction to the split locus discharges the form-free handle-trade atom (kernel-pure).** Given
`BordantToSplitLocus`, the `HandleTradeSplit` output is pure bookkeeping: the split witness
`p₀ = q ⊔ S²×S²` has `rank q + 2 = rank p₀ = rank p = 2 + m` by `rank_sum` and the hypothesis
equivalence `E`, so `rank q = m`; and the single cobordism `p ↝ p₀` collapses under the quotient
(`Quot.sound`) to `[p] = [S²×S²] + [q]` via `mk_strMfd_sum` and commutativity.

Note where the constraint is load-bearing: `rank q = m` is *derived* from additivity here, whereas
`HandleTradeCobordism` had it *declared* — which is exactly what let `collapsedPresentation` meet it
with a cylinder. -/
theorem handleTradeSplit_of_bordantToSplitLocus (h : R.BordantToSplitLocus) :
    R.toSpinSigmaPresentation.HandleTradeSplit := by
  intro p m E N' hN' hcong
  obtain ⟨p₀, ⟨q, rfl⟩, hrank, hbord⟩ := h p m E N' hN' hcong
  have hcard : 2 + m = R.rank p := by
    have hc := Fintype.card_congr E
    simpa using hc
  have hq : R.rank q = m := by
    rw [R.rank_sum q R.s2s2, R.s2s2_rank] at hrank
    omega
  refine ⟨q, hq, ?_⟩
  rw [DataBordismGrp.mk_eq_of_bordant ξ hbord, mk_strMfd_sum, add_comm]

/-- **Freeze A from the reduction plus the rank-0 base (kernel-pure).** Composes
`handleTradeSplit_of_bordantToSplitLocus` with the in-tree chain
`hyperbolicPeel_of_handleTradeSplit` → `realizesSphereProducts_of_peel_and_base`. This is the
re-scoped Freeze-A discharge: the net geometric ask is now *reduction to the split locus* on a
presentation whose rank is `b₂`, and no cylinder meets it off that locus. -/
theorem realizesSphereProducts_of_bordantToSplitLocus_and_base (h : R.BordantToSplitLocus)
    (hBase : R.toSpinSigmaPresentation.HyperbolicBase) :
    R.toSpinSigmaPresentation.RealizesSphereProducts :=
  SpinSigmaPresentation.realizesSphereProducts_of_split_and_base _
    (handleTradeSplit_of_bordantToSplitLocus R h) hBase

/-- **`hA` for the σ-route's consumers.** The injective direction of `Ω₄^{Spin} ≅ ℤ`
(`SpinSigmaRoute.sig_injective`, the `hA` binder of `sig_injective` / `door_via_k3_generator` /
`door_via_k3_realization`) from the reduction, the rank-0 base and the `S²×S²` bounding freeze. -/
theorem sig_injective_of_bordantToSplitLocus (h : R.BordantToSplitLocus)
    (hBase : R.toSpinSigmaPresentation.HyperbolicBase)
    (hB : R.toSpinSigmaPresentation.SphereProductBounds) : Function.Injective R.sig :=
  R.toSpinSigmaPresentation.sig_injective
    (realizesSphereProducts_of_bordantToSplitLocus_and_base R h hBase) hB

/-- **`Ω₄^{Spin} ≃+ ℤ` from the reduction** (the `hyp:spin_bordism_iso_Z` consumer shape), with
Rokhlin `16 ∣ σ` and the `σ = −16` generator as the route's remaining binders. -/
theorem dataBordismGrp_equiv_int_of_bordantToSplitLocus (h : R.BordantToSplitLocus)
    (hBase : R.toSpinSigmaPresentation.HyperbolicBase)
    (hB : R.toSpinSigmaPresentation.SphereProductBounds) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) :
    ∃ e : DataBordismGrp ξ ≃+ ℤ,
      (∀ x, R.sig x = -16 * e x) ∧ e (DataBordismGrp.mk ξ g) = 1 :=
  R.toSpinSigmaPresentation.dataBordismGrp_equiv_int
    (realizesSphereProducts_of_bordantToSplitLocus_and_base R h hBase) hB g hg hdvd

/-- **The realization is by an actual manifold.** Under the reduction plus the base, every `σ = 0`
class is the class of an honest `q`-fold disjoint union of `S²×S²` — the `n(S²×S²)` statement of
Benedetti Prop 20.16 in manifold form rather than as a `•`-multiple of a class. -/
theorem exists_nsum_repr_of_bordantToSplitLocus (h : R.BordantToSplitLocus)
    (hBase : R.toSpinSigmaPresentation.HyperbolicBase) (p : StrMfd ξ)
    (hp : ∃ N, IsHyperbolicForm N ∧ IntCongr (R.form p) N) :
    DataBordismGrp.mk ξ p =
      DataBordismGrp.mk ξ (StrMfd.nsum R.s2s2 (R.rank p / 2)) := by
  rw [mk_nsum]
  exact realizesSphereProducts_of_bordantToSplitLocus_and_base R h hBase p hp

/-! ### §8. Falsifiability — the primitive is refutable, hence not a tautology -/

/-- **A single nonzero `σ = 0` class refutes the reduction.** With the two other freezes, the
reduction forces `σ` injective; so on any carrier possessing a nonzero class of signature `0`,
`BordantToSplitLocus` is FALSE.

This is the precise sense in which the re-scoped primitive has content that the audited one lacked:
`HandleTradeCobordism` is satisfiable — by a unit cylinder — on **every** tangential datum
(`collapsedPresentation_handleTradeCobordism`), so no instance of it can ever be refuted; whereas
`BordantToSplitLocus` has kernel-checkable refuting instances and hence cannot be a theorem of the
substrate. -/
theorem not_bordantToSplitLocus_of_sig_kernel
    (hBase : R.toSpinSigmaPresentation.HyperbolicBase)
    (hB : R.toSpinSigmaPresentation.SphereProductBounds) {x : DataBordismGrp ξ}
    (hx : R.sig x = 0) (hx0 : x ≠ 0) : ¬ R.BordantToSplitLocus := by
  intro h
  exact hx0 (sig_injective_of_bordantToSplitLocus R h hBase hB (by rw [hx]; simp))

/-- **A σ-blind faithful presentation cannot discharge the reduction without collapsing `Ω^ξ`.** The
σ-blindness test of `HandleTradeAtomVacuity` §2b, restated for the new primitive: if `R.sig = 0` then
the reduction plus the base and bounding freezes force the whole bordism group to be trivial. -/
theorem subsingleton_of_sig_eq_zero_of_bordantToSplitLocus (hsig : R.sig = 0)
    (h : R.BordantToSplitLocus) (hBase : R.toSpinSigmaPresentation.HyperbolicBase)
    (hB : R.toSpinSigmaPresentation.SphereProductBounds) (x : DataBordismGrp ξ) : x = 0 :=
  sig_injective_of_bordantToSplitLocus R h hBase hB (by rw [hsig]; rfl)

end FaithfulSpinSigmaPresentation

/-! ### §9. Non-vacuity — the constrained type is INHABITED, with unbounded rank

`HandleTradeAtomVacuity` §5 shipped `FaithfulRank` explicitly as a soundness side-condition with
**no abstract inhabitant**, disclosing that none was constructed and none claimed. That gap is closed
here: a conditional statement over `FaithfulSpinSigmaPresentation` would be worthless if the type were
empty, so §7's whole chain needs a witness.

The witness is the **rank-graded datum** `rankGraded ξ₀`: an arbitrary tangential datum `ξ₀` with its
manifolds, structures and bordisms taken verbatim, each structure decorated with an additive declared
`b₂`-label that the carrier constraint forces to `0` on the empty manifold. Two things make it a
*useful* witness rather than a toy:

* `rankGraded_equiv` — decoration changes nothing about the bordism group: `Ω^(rankGraded ξ₀) ≃+ Ω^ξ₀`.
  Applied to the in-tree `Ω₄^{Spin}` datum, the witness therefore lives over the genuine carrier.
* its rank is unbounded (`exists_rank_gt`), so unlike both zero-geometry dodges it is not confined to
  the Sylvester-excluded `rank ≤ 2` region.

**Honest scope.** The label is a *declared* `b₂`, not a computed one; the witness shows the two
faithfulness fields are jointly satisfiable and rank-unbounded, NOT that `rank` is pinned to `b₂`
(that is E1's `interMatrix` job at instantiation). And it does not dodge the new primitive:
`gradedPresentation_subsingleton_of_bordantToSplitLocus` shows that its discharging
`BordantToSplitLocus` (with the base and bounding freezes) would collapse `Ω^ξ₀` itself. -/

/-- A hyperbolic-standard integral form exists in every **even** rank (block-sum of `n` copies of
`H`, built by `IsHyperbolicForm.cons`). -/
theorem exists_isHyperbolicForm_two_mul (n : ℕ) :
    ∃ N : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ, IsHyperbolicForm N := by
  induction n with
  | zero => exact ⟨0, IsHyperbolicForm.empty⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨_, IsHyperbolicForm.cons
      ((finSumFinEquiv (m := 2) (n := 2 * n)).trans (finCongr (by omega))) hN⟩

/-- A chosen hyperbolic-standard form of rank `2n`. -/
noncomputable def hypStd (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ :=
  (exists_isHyperbolicForm_two_mul n).choose

theorem hypStd_isHyperbolicForm (n : ℕ) : IsHyperbolicForm (hypStd n) :=
  (exists_isHyperbolicForm_two_mul n).choose_spec

/-- A **declared `b₂` label** on a closed manifold, constrained to vanish on an empty carrier — the
propositional half of `rank_empty_carrier`, carried in the tangential structure so that additivity
and empty-carrier vanishing can hold simultaneously. -/
def RankLabel (s : SingularManifold.{u} X k I) : Type := {n : ℕ // IsEmpty s.M → n = 0}

/-- **The rank-graded tangential datum**: `ξ₀`'s manifolds, structures and bordisms verbatim, each
structure decorated with an additive `RankLabel`. Every closure field is `ξ₀`'s, the label riding
along additively; the bordism types ignore the label entirely (which is why `rankGraded_equiv`
below holds). -/
noncomputable def rankGraded (ξ₀ : TangentialData.{u, v} X k I) : TangentialData.{u, v} X k I where
  Mfd s := ξ₀.Mfd s × ULift.{v} (RankLabel s)
  Bor b σ τ := ξ₀.Bor b σ.1 τ.1
  emptyStr := (ξ₀.emptyStr, ⟨⟨0, fun _ => rfl⟩⟩)
  sumStr {s t} σ τ := (ξ₀.sumStr σ.1 τ.1, ⟨⟨σ.2.down.val + τ.2.down.val, fun h => by
    haveI : IsEmpty (s.M ⊕ t.M) := h
    rw [σ.2.down.property (Function.isEmpty (Sum.inl : s.M → s.M ⊕ t.M)),
      τ.2.down.property (Function.isEmpty (Sum.inr : t.M → s.M ⊕ t.M))]⟩⟩)
  cylBor σ := ξ₀.cylBor σ.1
  addBor h₁ h₂ := ξ₀.addBor h₁ h₂
  symmBor h := ξ₀.symmBor h
  commBor σ τ := ξ₀.commBor σ.1 τ.1
  assocBor σ τ ρ := ξ₀.assocBor σ.1 τ.1 ρ.1
  unitBor σ := ξ₀.unitBor σ.1
  revStr σ := (ξ₀.revStr σ.1, σ.2)
  revBor h := ξ₀.revBor h
  negBor σ := ξ₀.negBor σ.1

/-- **The witness: a faithful σ-presentation with unbounded rank.** Over the rank-graded datum, with
`rank = 2 ×` the declared label (so every rank is even and carries a hyperbolic-standard form of
signature `0`) and the distinguished `S²×S²` slot any nonempty manifold labelled `1`. Both
faithfulness fields hold by construction: additivity because the label is additive, empty-carrier
vanishing because the label type forces it. -/
noncomputable def gradedPresentation (ξ₀ : TangentialData.{u, v} X k I)
    (s₀ : SingularManifold.{u} X k I) (hs₀ : Nonempty s₀.M) (σ₀ : ξ₀.Mfd s₀) :
    FaithfulSpinSigmaPresentation (rankGraded ξ₀) where
  sig := 0
  rank p := 2 * p.2.2.down.val
  form p := hypStd p.2.2.down.val
  even_unimod p := (hypStd_isHyperbolicForm _).isEvenUnimodular
  sig_eq p := by
    show (0 : ℤ) = _
    rw [(hypStd_isHyperbolicForm p.2.2.down.val).latticeSig_eq_zero]
  s2s2 := ⟨s₀, (σ₀, ⟨⟨1, fun h => (h.false hs₀.some).elim⟩⟩)⟩
  s2s2_rank := rfl
  s2s2_hyp := ⟨_, hypStd_isHyperbolicForm 1, IntCongr.rfl _⟩
  rank_empty_carrier p h := by simp [p.2.2.down.property h]
  rank_sum p q := by
    show 2 * (p.2.2.down.val + q.2.2.down.val) = 2 * p.2.2.down.val + 2 * q.2.2.down.val
    omega

/-- **Relabelling is invisible to the bordism relation.** Any two labellings of the *same* underlying
structured manifold are `rankGraded ξ₀`-bordant, witnessed by the reflexive cylinder: `rankGraded`'s
`Bor` field ignores the label, so `ξ₀.cylBor σ` already bounds the pair.

This is the half of "decoration is invisible" that carries content. The other half — that
`IsDataBordant (rankGraded ξ₀) p q` *unfolds* to `IsDataBordant ξ₀ ⟨p.1, p.2.1⟩ ⟨q.1, q.2.1⟩` — is
definitional (`Iff.rfl`) and is deliberately NOT recorded as a theorem: a structurally-named
statement discharged by `Iff.rfl` asserts nothing, and the `rank` in its name would advertise a
quantitative result it does not have. What is actually needed downstream is the statement below, and
`rankGraded_equiv.left_inv` now calls it rather than re-deriving the cylinder inline. -/
theorem isDataBordant_relabel {ξ₀ : TangentialData.{u, v} X k I}
    (s : SingularManifold.{u} X k I) (σ : ξ₀.Mfd s) (ℓ ℓ' : ULift.{v} (RankLabel s)) :
    IsDataBordant (rankGraded ξ₀) ⟨s, (σ, ℓ)⟩ ⟨s, (σ, ℓ')⟩ :=
  ⟨reflCylinder s, ⟨ξ₀.cylBor σ⟩⟩

/-- **The rank-graded datum carries the same bordism group.** `Ω^(rankGraded ξ₀) ≃+ Ω^ξ₀`: the
forgetful map (drop the label) is an additive isomorphism, its inverse labelling everything `0` — a
class is unchanged by relabelling, since the reflexive cylinder is a `rankGraded`-bordism between any
two labellings of the same structured manifold. So the §9 witness is not a toy carrier: instantiated
at the in-tree `Ω₄^{Spin}` datum, it is a faithful presentation *over the genuine bordism group*. -/
noncomputable def rankGraded_equiv (ξ₀ : TangentialData.{u, v} X k I) :
    DataBordismGrp (rankGraded ξ₀) ≃+ DataBordismGrp ξ₀ where
  toFun := Quot.lift (fun p => DataBordismGrp.mk ξ₀ ⟨p.1, p.2.1⟩)
    (fun _ _ h => DataBordismGrp.mk_eq_of_bordant ξ₀ h)
  invFun := Quot.lift
    (fun p => DataBordismGrp.mk (rankGraded ξ₀) ⟨p.1, (p.2, ⟨⟨0, fun _ => rfl⟩⟩)⟩)
    (fun _ _ h => DataBordismGrp.mk_eq_of_bordant (rankGraded ξ₀) h)
  left_inv x := by
    induction x using Quot.ind with | _ p =>
    exact DataBordismGrp.mk_eq_of_bordant (rankGraded ξ₀)
      (isDataBordant_relabel p.1 p.2.1 _ _)
  right_inv x := by induction x using Quot.ind with | _ p => rfl
  map_add' x y := by
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    rfl

namespace FaithfulSpinSigmaPresentation

/-- **The new primitive is not ∀-vacuous on the witness — and it fires off the obvious free part.**
The antecedent of `BordantToSplitLocus` genuinely fires at a manifold whose carrier is the *atomic*
`s₀` (recorded by `p.1 = s₀`, so `p` is not presented as a disjoint union with the `s2s2` slot): its
declared `b₂` is `4`, and its form splits off one hyperbolic plane over a rank-`2` hyperbolic
complement. So `gradedPresentation_subsingleton_of_bordantToSplitLocus` below rules out a *live*
obligation, not an empty one — the discipline of `collapsedPresentation_hypothesis_fires`
(`HandleTradeAtomVacuity` §3) applied to the re-scoped primitive.

Disclosure: `p.1 = s₀` records that `p` is not *built* as a disjoint union with the slot; whether
`p` lies in the split locus is a question about equality of `SingularManifold`s that this level of
abstraction cannot decide either way, and no claim is made about it. -/
theorem gradedPresentation_hypothesis_fires (ξ₀ : TangentialData.{u, v} X k I)
    (s₀ : SingularManifold.{u} X k I) (hs₀ : Nonempty s₀.M) (σ₀ : ξ₀.Mfd s₀) :
    ∃ (p : StrMfd (rankGraded ξ₀))
      (E : Fin 2 ⊕ Fin 2 ≃ Fin ((gradedPresentation ξ₀ s₀ hs₀ σ₀).rank p)),
      p.1 = s₀ ∧ (gradedPresentation ξ₀ s₀ hs₀ σ₀).rank p = 4 ∧
      IsHyperbolicForm (Hyp : Matrix (Fin 2) (Fin 2) ℤ) ∧
      IntCongr ((gradedPresentation ξ₀ s₀ hs₀ σ₀).form p)
        (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 Hyp)) := by
  have hHyp : IsHyperbolicForm (Hyp : Matrix (Fin 2) (Fin 2) ℤ) :=
    reindex_one_block_eq_hyp ▸
      IsHyperbolicForm.cons (Equiv.sumEmpty (Fin 2) (Fin 0)) IsHyperbolicForm.empty
  refine ⟨⟨s₀, (σ₀, ⟨⟨2, fun h => (h.false hs₀.some).elim⟩⟩)⟩, finSumFinEquiv, rfl, rfl, hHyp,
    hyperbolicForm_intCongr (hypStd_isHyperbolicForm 2) ?_⟩
  exact IsHyperbolicForm.cons finSumFinEquiv hHyp

/-- **The witness does not dodge the new primitive.** Its signature hom is the zero map, so by §8's
σ-blindness test, discharging `BordantToSplitLocus` together with the base and bounding freezes would
force `Ω^(rankGraded ξ₀)` — hence, by `rankGraded_equiv`, `Ω^ξ₀` itself — to be trivial. So the §9
inhabitant establishes non-vacuity of the constrained type *without* re-opening the vacuity the audit
found: unlike `collapsedPresentation`, it cannot meet the primitive for free on a carrier with a
nontrivial bordism group. -/
theorem gradedPresentation_subsingleton_of_bordantToSplitLocus
    (ξ₀ : TangentialData.{u, v} X k I) (s₀ : SingularManifold.{u} X k I) (hs₀ : Nonempty s₀.M)
    (σ₀ : ξ₀.Mfd s₀)
    (h : (gradedPresentation ξ₀ s₀ hs₀ σ₀).BordantToSplitLocus)
    (hBase : (gradedPresentation ξ₀ s₀ hs₀ σ₀).toSpinSigmaPresentation.HyperbolicBase)
    (hB : (gradedPresentation ξ₀ s₀ hs₀ σ₀).toSpinSigmaPresentation.SphereProductBounds)
    (y : DataBordismGrp ξ₀) : y = 0 := by
  have hx := subsingleton_of_sig_eq_zero_of_bordantToSplitLocus
    (gradedPresentation ξ₀ s₀ hs₀ σ₀) rfl h hBase hB ((rankGraded_equiv ξ₀).symm y)
  have := congrArg (rankGraded_equiv ξ₀) hx
  rwa [AddEquiv.apply_symm_apply, map_zero] at this

end FaithfulSpinSigmaPresentation

end SKEFTHawking.SpinSigmaRoute
