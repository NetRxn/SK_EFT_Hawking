/-
# Phase 5q.H — bordism GLUING: the `hker` unlock, its exact cost, and how far it is buildable

`PinPlusKTDualSpinSubmanifold` names the wall of the `hker` lane verbatim: deriving the per-element
KT supply from PURE kernel membership `spinForgetPhi prov x = 0` needs a **single tethered
null-bordism witness** extracted from `T2DataBordismGrp.mk … = 0`; `Quot.eq` on
`Quot (IsT2DataBordant)` yields only `Relation.EqvGen (IsT2DataBordant) …`, and collapsing that to a
single `IsT2DataBordant` needs **transitivity**, i.e. bordism gluing — deliberately sidestepped by
`BordismGroup.lean` §4 ("`Quot (IsBordant)` — no transitivity/gluing needed").

This module does two things.

## §1–§2: the logical half — CLOSED, and shown to be exactly equivalent to the wall

* `IsT2DataBordant.refl` / `.symm` — the refined relation is reflexive and symmetric
  UNCONDITIONALLY (`reflCylinder` + `cylBor` + `t2Str`; `Bordism.symm` + `symmBor`, same `W`). So
  gluing is the *sole* missing equivalence law.
* `GluesT2 ξ` — the named geometric node (transitivity of the refined relation; `gluesT2_iff_isTrans`
  certifies it is Mathlib's transitivity on the nose, not a weakened stand-in).
* `T2DataBordismGrp.exact_of_gluesT2` — GIVEN gluing, `Quot.eq` collapses and the single witness
  is extracted.
* `nullBordism_of_class_eq_zero` — the extraction in exactly the shape `hker` consumes: from
  `T2DataBordismGrp.mk ξ p = 0`, a single `b` with `T2Space b.W` and `ξ.Bor b p.2 ξ.emptyStr`.
* **`gluesT2_iff_singleWitness`** — the sharp wall statement: transitivity of the refined bordism
  relation is *equivalent* to the single-witness extraction property, not merely sufficient for it.
  The `hker` lane therefore cannot be routed around the gluing content by any cleverer use of the
  quotient: the thing it wants IS gluing, on the nose. (A forcing theorem, not a refutation.)

## §3: the geometric half — how far generic gluing gets WITHOUT a collar

Given composable `b₁ : Bordism J p q`, `b₂ : Bordism J q r`, the seam pushout `b₁.W ⊔_q b₂.W`
(`glueCarrier`) is built here generically, and the `Bordism`-structure fields split cleanly:

| field | status |
|---|---|
| `W` | `glueCarrier` — the seam quotient of `b₁.W ⊕ b₂.W` |
| `topW` | the quotient topology |
| `compactW` | `compactSpace_glueCarrier` (unconditional) |
| (T2 of `W`) | `t2Space_glueCarrier` — needs both ends T2, which the REFINED relation supplies |
| `e` | `glueEnds` |
| `he_inj` | `glueEnds_injective` |
| `g` | `glueMap` |
| `hg` | `continuous_glueMap` |
| `hg_restrict` | `glueMap_comp_glueEnds` |
| `chartW` | ⛔ NOT constructible from `Bordism` data |
| `mfdW` | ⛔ NOT constructible from `Bordism` data |
| `he_smooth`, `he_boundary` | ⛔ depend on `chartW` |

`seam_notMem_range_glueEnds` adds the set-level shadow of `he_boundary`: the welded seam is disjoint
from the glued ends, i.e. the `q`-boundary really has been healed.

The "8 of 12" split is not prose: `SeamGlueChart` bundles exactly the four missing fields, and
`Bordism.ofSeamGlueChart` assembles the composite `Bordism p r` from it plus the eight constructed
pieces — so the reduction "manifold-level gluing ⟹ the collar content, and nothing else" is
kernel-checked.

The residue is therefore **exactly the charts at the seam** — the **collar neighbourhood theorem**.
A `Bordism` carries only `e : s.M ⊕ t.M → W`, smooth and injective with `Set.range e = J.boundary W`:
a set-level identification of the boundary, with no neighbourhood of it and no product structure
along it. No chart at a seam point can be produced from that. Mathlib names this same gap in its own
`Mathlib/Geometry/Manifold/Bordism.lean` ("transitivity follows from the collar neighbourhood
theorem") and supplies neither the collar theorem nor "the boundary is a submanifold".

## The two-arc verdict (the scope answer)

`GluesT2` is TRUE mathematically; formalizing it is **two sequential arcs**, not one:

* **ARC A — manifold gluing.** `SeamGlueChart` above. The blocker, and the collar theorem is a
  standing Mathlib TODO.
* **ARC B — the tethered structure across the seam.** `TangentialData` has fields `emptyStr`,
  `sumStr`, `cylBor`, `addBor`, `symmBor`, `commBor`, `assocBor`, `unitBor`, `revStr`, `revBor`,
  `negBor` — and **no composition field**. `Bor` is an arbitrary type family, so a glued structure
  cannot be derived; the structure needs a new `glueBor : Bor b₁ σ τ → Bor b₂ τ ρ → Bor (glue b₁ b₂) σ ρ`
  field, which every instance (`pinPlusGMTiedData`, `pinPlusCharPairData`, `spinEmptyData`, …) must
  then supply. Arc B **cannot even be typed** until arc A produces the glued bordism, so the arcs are
  strictly sequential — and adding the field is a breaking change to every `TangentialData` in tree.

`isT2DataBordant_of_seamGlue` records the one piece of good news across the two arcs: the Hausdorff
refinement costs nothing here — the glued carrier is automatically T2 when the ends are, so the
`NonHausdorffBordismCollapse` repair adds no new obstruction to gluing.

Everything here is stated **`k`-generically** — no `k = 0` specialization anywhere, per the
`k0-to-k1-transport-refuted` fence.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.T2TangentialBordism

namespace SKEFTHawking.T2BordismGluing

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.T2TangentialBordism

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ## §1. The refined relation is reflexive and symmetric — unconditionally -/

section Refined

variable [I.Boundaryless]

/-- **Reflexivity of the Hausdorff-refined structured relation.** The cylinder `p.M × [0,1]` is a
bordism from `p` to itself (`reflCylinder`), carries the product structure (`cylBor`), and is T2
because `ξ.t2Str` certifies the carrier is. -/
theorem IsT2DataBordant.refl (ξ : T2TangentialData X k I) (p : StrMfd ξ.toTangentialData) :
    IsT2DataBordant ξ p p := by
  refine ⟨reflCylinder p.1, ?_, ⟨ξ.cylBor p.2⟩⟩
  haveI := ξ.t2Str p.2
  exact inferInstanceAs (T2Space (p.1.M × Set.Icc (0 : ℝ) 1))

/-- **Symmetry of the Hausdorff-refined structured relation.** `Bordism.symm` reuses the SAME total
space `W` (only the boundary identification is precomposed with `Sum.swap`), so the `T2Space b.W`
certificate transports definitionally; `ξ.symmBor` reverses the tethered structure. -/
theorem IsT2DataBordant.symm {ξ : T2TangentialData X k I} {p q : StrMfd ξ.toTangentialData}
    (h : IsT2DataBordant ξ p q) : IsT2DataBordant ξ q p := by
  obtain ⟨b, hT2, ⟨str⟩⟩ := h
  exact ⟨b.symm, hT2, ⟨ξ.symmBor str⟩⟩

/-- **`GluesT2 ξ` — the named geometric node.** Composable Hausdorff-refined structured bordisms
compose: the bordism-GLUING supply. This is transitivity of `IsT2DataBordant ξ`; it is named so the
one remaining equivalence law can be tracked as a single open node (`gluesT2_iff_isTrans` certifies
it is exactly Mathlib's transitivity, so nothing has been weakened to make it reachable). -/
def GluesT2 (ξ : T2TangentialData X k I) : Prop :=
  ∀ ⦃p q r : StrMfd ξ.toTangentialData⦄,
    IsT2DataBordant ξ p q → IsT2DataBordant ξ q r → IsT2DataBordant ξ p r

/-- **Anti-weakening certificate**: `GluesT2` is Mathlib's transitivity of the refined relation on
the nose — the named node is the real law, not a stand-in for something easier. -/
theorem gluesT2_iff_isTrans (ξ : T2TangentialData X k I) :
    GluesT2 ξ ↔ IsTrans (StrMfd ξ.toTangentialData) (IsT2DataBordant ξ) :=
  ⟨fun h => ⟨fun _ _ _ hpq hqr => h hpq hqr⟩, fun h _ _ _ hpq hqr => h.trans _ _ _ hpq hqr⟩

/-- The refined relation is an equivalence **as soon as it glues** — reflexivity and symmetry are
already in hand, so gluing is the sole missing law. -/
theorem IsT2DataBordant.equivalence_of_gluesT2 (ξ : T2TangentialData X k I) (hglue : GluesT2 ξ) :
    Equivalence (IsT2DataBordant ξ) :=
  ⟨IsT2DataBordant.refl ξ, IsT2DataBordant.symm, fun h h' => hglue h h'⟩

/-! ## §2. The single-witness extraction, and its equivalence with gluing -/

/-- **The `Quot.eq` collapse.** Given gluing, equality of refined bordism classes yields a SINGLE
`IsT2DataBordant` witness — the step `PinPlusKTDualSpinSubmanifold`'s header names as walled. -/
theorem T2DataBordismGrp.exact_of_gluesT2 (ξ : T2TangentialData X k I) (hglue : GluesT2 ξ)
    {p q : StrMfd ξ.toTangentialData}
    (h : T2DataBordismGrp.mk ξ p = T2DataBordismGrp.mk ξ q) : IsT2DataBordant ξ p q :=
  ((IsT2DataBordant.equivalence_of_gluesT2 ξ hglue).eqvGen_iff).mp (Quot.eq.mp h)

/-- **The extraction in exactly the shape `hker` consumes**: from `[p] = 0` in the refined group, a
single tethered null-bordism witness `b` — its Hausdorff total space `b.W` is the ambient `W⁵` that
`PinPlusKTDualSpinSubmanifold.DualSpinFromW` is keyed on, and `ξ.Bor b p.2 ξ.emptyStr` is the
tethered structure along it. -/
theorem nullBordism_of_class_eq_zero (ξ : T2TangentialData X k I) (hglue : GluesT2 ξ)
    (p : StrMfd ξ.toTangentialData) (h : T2DataBordismGrp.mk ξ p = (0 : T2DataBordismGrp ξ)) :
    ∃ b : Bordism (I.prod (𝓡∂ 1)) p.1 emptySM,
      T2Space b.W ∧ Nonempty (ξ.Bor b p.2 ξ.emptyStr) :=
  T2DataBordismGrp.exact_of_gluesT2 ξ hglue (q := ⟨emptySM, ξ.emptyStr⟩) h

/-- **THE SHARP WALL STATEMENT (forcing theorem).** The single-witness extraction that the `hker`
lane needs is *equivalent* to gluing of the refined bordism relation — not merely implied by it. So
no cleverer use of the quotient, and no reformulation of the extraction, can dodge the geometric
gluing content: `←` recovers gluing from the extraction by routing the two hypotheses through
`Quot.sound` and back. -/
theorem gluesT2_iff_singleWitness (ξ : T2TangentialData X k I) :
    GluesT2 ξ ↔
      ∀ p q : StrMfd ξ.toTangentialData,
        T2DataBordismGrp.mk ξ p = T2DataBordismGrp.mk ξ q → IsT2DataBordant ξ p q := by
  refine ⟨fun hglue p q h => T2DataBordismGrp.exact_of_gluesT2 ξ hglue h, fun hex p q r hpq hqr => ?_⟩
  exact hex p r ((T2DataBordismGrp.mk_eq_of_bordant ξ hpq).trans
    (T2DataBordismGrp.mk_eq_of_bordant ξ hqr))

end Refined

/-! ## §3. The seam pushout `W₁ ⊔_q W₂` — the buildable part of gluing

Everything in this section is generic in `k` and in the composable pair; nothing is specialized to
`k = 0` and nothing assumes a collar. -/

section Glue

variable {p q r : SingularManifold X k I}
  (b₁ : Bordism (I.prod (𝓡∂ 1)) p q) (b₂ : Bordism (I.prod (𝓡∂ 1)) q r)

/-- **The seam join**: `x` is the `q`-end point of `b₁` at `m` and `y` is the `q`-end point of `b₂`
at the same `m`. These are the pairs the weld identifies, and nothing else. -/
def SeamJoin (x y : b₁.W ⊕ b₂.W) : Prop :=
  ∃ m : q.M, x = Sum.inl (b₁.e (Sum.inr m)) ∧ y = Sum.inr (b₂.e (Sum.inl m))

/-- **The seam relation**: equal, or joined across the seam in either direction. -/
def seamRel (x y : b₁.W ⊕ b₂.W) : Prop :=
  x = y ∨ SeamJoin b₁ b₂ x y ∨ SeamJoin b₁ b₂ y x

theorem seamRel_refl (x : b₁.W ⊕ b₂.W) : seamRel b₁ b₂ x x := Or.inl rfl

theorem seamRel_symm {x y : b₁.W ⊕ b₂.W} (h : seamRel b₁ b₂ x y) : seamRel b₁ b₂ y x := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- The seam relation is transitive: the two ends of a join sit in opposite summands, so no two
joins chain, and a shared endpoint forces a shared `q`-parameter by injectivity of `b₁.e` / `b₂.e`.
(This is transitivity of the *set-level weld*, which is free — it is emphatically NOT the manifold
gluing that `GluesT2` asks for.) -/
theorem seamRel_trans {x y z : b₁.W ⊕ b₂.W} (hxy : seamRel b₁ b₂ x y)
    (hyz : seamRel b₁ b₂ y z) : seamRel b₁ b₂ x z := by
  rcases hxy with rfl | hxy | hxy
  · exact hyz
  · obtain ⟨m, hx, hy⟩ := hxy
    rcases hyz with rfl | hyz | hyz
    · exact Or.inr (Or.inl ⟨m, hx, hy⟩)
    · obtain ⟨_, hy', _⟩ := hyz
      exact absurd (hy'.symm.trans hy) (by simp)
    · obtain ⟨m', hz, hy'⟩ := hyz
      have hm : m = m' := by
        have := Sum.inr.inj (hy.symm.trans hy')
        exact Sum.inl.inj (b₂.he_inj this)
      exact Or.inl (hx.trans (hm ▸ hz.symm))
  · obtain ⟨m, hy, hx⟩ := hxy
    rcases hyz with rfl | hyz | hyz
    · exact Or.inr (Or.inr ⟨m, hy, hx⟩)
    · obtain ⟨m', hy', hz⟩ := hyz
      have hm : m = m' := by
        have := Sum.inl.inj (hy.symm.trans hy')
        exact Sum.inr.inj (b₁.he_inj this)
      exact Or.inl (hx.trans (hm ▸ hz.symm))
    · obtain ⟨_, _, hy'⟩ := hyz
      exact absurd (hy.symm.trans hy') (by simp)

/-- The seam setoid. -/
def seamSetoid : Setoid (b₁.W ⊕ b₂.W) where
  r := seamRel b₁ b₂
  iseqv := ⟨seamRel_refl b₁ b₂, seamRel_symm b₁ b₂, seamRel_trans b₁ b₂⟩

/-- **The seam pushout `W₁ ⊔_q W₂`** — the carrier of the glued bordism, welded along the shared
`q`-end. Carries the quotient topology. -/
abbrev glueCarrier : Type _ := Quotient (seamSetoid b₁ b₂)

/-- The weld quotient map. -/
abbrev glueMk (x : b₁.W ⊕ b₂.W) : glueCarrier b₁ b₂ := Quotient.mk (seamSetoid b₁ b₂) x

theorem continuous_glueMk : Continuous (glueMk b₁ b₂) := continuous_quotient_mk'

theorem glueMk_surjective : Function.Surjective (glueMk b₁ b₂) := Quotient.mk_surjective

/-- **The weld**: the two `q`-end copies are identified point-for-point. -/
theorem glueMk_seam (m : q.M) :
    glueMk b₁ b₂ (Sum.inl (b₁.e (Sum.inr m))) = glueMk b₁ b₂ (Sum.inr (b₂.e (Sum.inl m))) :=
  Quotient.sound (Or.inr (Or.inl ⟨m, rfl, rfl⟩))

/-- **The glued carrier is compact** — the `compactW` field of the glued bordism, unconditionally. -/
theorem compactSpace_glueCarrier : CompactSpace (glueCarrier b₁ b₂) :=
  ⟨(glueMk_surjective b₁ b₂).range_eq ▸ isCompact_range (continuous_glueMk b₁ b₂)⟩

/-- The weld map is **closed**: the saturation of a closed `C` is `C` together with the two
seam-partner strata, each a continuous image of a closed — hence compact, since `q.M` is closed —
subset of `q.M`. -/
theorem isClosedMap_glueMk [T2Space b₁.W] [T2Space b₂.W] : IsClosedMap (glueMk b₁ b₂) := by
  have hce₁ : Continuous fun m : q.M => (Sum.inl (b₁.e (Sum.inr m)) : b₁.W ⊕ b₂.W) :=
    continuous_inl.comp (b₁.he_smooth.continuous.comp continuous_inr)
  have hce₂ : Continuous fun m : q.M => (Sum.inr (b₂.e (Sum.inl m)) : b₁.W ⊕ b₂.W) :=
    continuous_inr.comp (b₂.he_smooth.continuous.comp continuous_inl)
  intro C hC
  rw [← (isQuotientMap_quotient_mk' (s := seamSetoid b₁ b₂)).isClosed_preimage]
  have hsat : glueMk b₁ b₂ ⁻¹' (glueMk b₁ b₂ '' C) =
      C ∪ (fun m : q.M => (Sum.inr (b₂.e (Sum.inl m)) : b₁.W ⊕ b₂.W)) ''
            {m : q.M | (Sum.inl (b₁.e (Sum.inr m)) : b₁.W ⊕ b₂.W) ∈ C}
        ∪ (fun m : q.M => (Sum.inl (b₁.e (Sum.inr m)) : b₁.W ⊕ b₂.W)) ''
            {m : q.M | (Sum.inr (b₂.e (Sum.inl m)) : b₁.W ⊕ b₂.W) ∈ C} := by
    ext x
    constructor
    · rintro ⟨y, hyC, hxy⟩
      rcases Quotient.exact hxy with rfl | hsj | hsj
      · exact Or.inl (Or.inl hyC)
      · obtain ⟨m, hy, hx⟩ := hsj
        subst hy
        exact Or.inl (Or.inr ⟨m, hyC, hx.symm⟩)
      · obtain ⟨m, hx, hy⟩ := hsj
        subst hy
        exact Or.inr ⟨m, hyC, hx.symm⟩
    · rintro ((hxC | ⟨m, hm, rfl⟩) | ⟨m, hm, rfl⟩)
      · exact ⟨x, hxC, rfl⟩
      · exact ⟨_, hm, glueMk_seam b₁ b₂ m⟩
      · exact ⟨_, hm, (glueMk_seam b₁ b₂ m).symm⟩
  show IsClosed (glueMk b₁ b₂ ⁻¹' (glueMk b₁ b₂ '' C))
  rw [hsat]
  exact ((hC.union ((hC.preimage hce₁).isCompact.image hce₂).isClosed).union
    ((hC.preimage hce₂).isCompact.image hce₁).isClosed)

/-- Every weld fiber has **at most two points** (a point and its unique seam partner), hence is
finite. -/
theorem finite_glueFiber (y : glueCarrier b₁ b₂) : (glueMk b₁ b₂ ⁻¹' {y}).Finite := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  have hsub : glueMk b₁ b₂ ⁻¹' {glueMk b₁ b₂ x} ⊆
      ({x} ∪ {z | SeamJoin b₁ b₂ z x}) ∪ {z | SeamJoin b₁ b₂ x z} := by
    intro z hz
    rcases Quotient.exact hz with rfl | h | h
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  refine Set.Finite.subset (((Set.finite_singleton x).union ?_).union ?_) hsub
  · refine Set.Subsingleton.finite (fun u hu u' hu' => ?_)
    obtain ⟨m, hu1, hx⟩ := hu
    obtain ⟨m', hu1', hx'⟩ := hu'
    have hm : m = m' := Sum.inl.inj (b₂.he_inj (Sum.inr.inj (hx.symm.trans hx')))
    rw [hu1, hu1', hm]
  · refine Set.Subsingleton.finite (fun u hu u' hu' => ?_)
    obtain ⟨m, hx, hu1⟩ := hu
    obtain ⟨m', hx', hu1'⟩ := hu'
    have hm : m = m' := Sum.inr.inj (b₁.he_inj (Sum.inl.inj (hx.symm.trans hx')))
    rw [hu1, hu1', hm]

/-- **The glued carrier is Hausdorff.** The weld map is proper (continuous, closed, finite fibers),
so `glueMk × glueMk` is a closed map and the diagonal — the image of the closed diagonal of the
Hausdorff `b₁.W ⊕ b₂.W` — is closed. The T2 hypotheses on the two ends are exactly what the
Hausdorff-REFINED relation `IsT2DataBordant` supplies, which is why the repair of
`NonHausdorffBordismCollapse` also makes the weld well-behaved. -/
theorem t2Space_glueCarrier [T2Space b₁.W] [T2Space b₂.W] : T2Space (glueCarrier b₁ b₂) := by
  have hproper : IsProperMap (glueMk b₁ b₂) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨continuous_glueMk b₁ b₂, isClosedMap_glueMk b₁ b₂,
        fun y => (finite_glueFiber b₁ b₂ y).isCompact⟩
  rw [t2_iff_isClosed_diagonal]
  have hdiag : Set.diagonal (glueCarrier b₁ b₂) =
      Prod.map (glueMk b₁ b₂) (glueMk b₁ b₂) '' Set.diagonal (b₁.W ⊕ b₂.W) := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro ⟨y₁, y₂⟩ hy
      have hy' : y₁ = y₂ := hy
      subst hy'
      obtain ⟨x, rfl⟩ := Quotient.exists_rep y₁
      exact ⟨(x, x), rfl, rfl⟩
    · rintro ⟨y₁, y₂⟩ ⟨⟨u, v⟩, huv, heq⟩
      have huv' : u = v := huv
      have h1 : glueMk b₁ b₂ u = y₁ := congrArg Prod.fst heq
      have h2 : glueMk b₁ b₂ v = y₂ := congrArg Prod.snd heq
      show y₁ = y₂
      rw [← h1, ← h2, huv']
  rw [hdiag]
  exact (hproper.prodMap hproper).isClosedMap _ isClosed_diagonal

/-! ### §3b. The remaining constructible `Bordism` fields on the seam pushout -/

/-- The outer ends of the two pieces, as points of `b₁.W ⊕ b₂.W` (before welding). -/
def endRep : p.M ⊕ r.M → b₁.W ⊕ b₂.W :=
  Sum.elim (fun m => Sum.inl (b₁.e (Sum.inl m))) (fun m => Sum.inr (b₂.e (Sum.inr m)))

/-- **The glued boundary identification** `p.M ⊕ r.M → W₁ ⊔_q W₂` — the `e` field of the glued
bordism: the outer ends of the two pieces, pushed into the weld. -/
def glueEnds : p.M ⊕ r.M → glueCarrier b₁ b₂ := fun a => glueMk b₁ b₂ (endRep b₁ b₂ a)

theorem endRep_injective : Function.Injective (endRep b₁ b₂) := by
  rintro (a | a) (c | c) h <;> simp only [endRep, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Sum.inl.inj (b₁.he_inj (Sum.inl.inj h)))
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact congrArg Sum.inr (Sum.inr.inj (b₂.he_inj (Sum.inr.inj h)))

/-- **An outer end is never a `q`-end of `b₁`** — the injectivity of `b₁.e` separates the two ends of
`b₁`, and the `b₂` half sits in the other summand. -/
theorem endRep_ne_seamLeft (a : p.M ⊕ r.M) (m : q.M) :
    endRep b₁ b₂ a ≠ Sum.inl (b₁.e (Sum.inr m)) := by
  cases a with
  | inl n => intro h; exact absurd (b₁.he_inj (Sum.inl.inj h)) (by simp)
  | inr n => intro h; simp [endRep] at h

/-- **An outer end is never a `q`-end of `b₂`** — the mirror statement. -/
theorem endRep_ne_seamRight (a : p.M ⊕ r.M) (m : q.M) :
    endRep b₁ b₂ a ≠ Sum.inr (b₂.e (Sum.inl m)) := by
  cases a with
  | inl n => intro h; simp [endRep] at h
  | inr n => intro h; exact absurd (b₂.he_inj (Sum.inr.inj h)) (by simp)

theorem not_seamJoin_endRep_left (a : p.M ⊕ r.M) (y : b₁.W ⊕ b₂.W) :
    ¬ SeamJoin b₁ b₂ (endRep b₁ b₂ a) y := by
  rintro ⟨m, hx, -⟩; exact endRep_ne_seamLeft b₁ b₂ a m hx

theorem not_seamJoin_endRep_right (a : p.M ⊕ r.M) (x : b₁.W ⊕ b₂.W) :
    ¬ SeamJoin b₁ b₂ x (endRep b₁ b₂ a) := by
  rintro ⟨m, -, hy⟩; exact endRep_ne_seamRight b₁ b₂ a m hy

/-- **The welded seam is healed**: no seam point is an outer-end point. This is the set-level shadow
of the `he_boundary` field — the `q`-boundary has genuinely become interior, and only the *chart*
witness of that (`J.boundary` of the glued charted space) is missing. -/
theorem seam_notMem_range_glueEnds (m : q.M) :
    glueMk b₁ b₂ (Sum.inl (b₁.e (Sum.inr m))) ∉ Set.range (glueEnds b₁ b₂) := by
  rintro ⟨a, ha⟩
  rcases Quotient.exact ha with h | h | h
  · exact endRep_ne_seamLeft b₁ b₂ a m h
  · exact not_seamJoin_endRep_left b₁ b₂ a _ h
  · exact not_seamJoin_endRep_right b₁ b₂ a _ h

/-- **The glued boundary identification is injective** — the `he_inj` field. The weld only ever
identifies `q`-end points, and the outer ends are disjoint from those by injectivity of `b₁.e`,
`b₂.e`. -/
theorem glueEnds_injective : Function.Injective (glueEnds b₁ b₂) := by
  intro a c hac
  refine endRep_injective b₁ b₂ ?_
  rcases Quotient.exact hac with h | h | h
  · exact h
  · exact absurd h (not_seamJoin_endRep_left b₁ b₂ a _)
  · exact absurd h (not_seamJoin_endRep_left b₁ b₂ c _)

/-- **The glued map to `X`** — the `g` field. Well defined on the weld because both pieces restrict
to `q.f` along the shared end (`hg_restrict`). -/
def glueMap : glueCarrier b₁ b₂ → X :=
  Quotient.lift (Sum.elim b₁.g b₂.g) <| by
    rintro x y (rfl | ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩)
    · rfl
    · exact (congrFun b₁.hg_restrict (Sum.inr m)).trans
        (congrFun b₂.hg_restrict (Sum.inl m)).symm
    · exact (congrFun b₂.hg_restrict (Sum.inl m)).trans
        (congrFun b₁.hg_restrict (Sum.inr m)).symm

theorem continuous_glueMap : Continuous (glueMap b₁ b₂) :=
  continuous_quot_lift _ (b₁.hg.sumElim b₂.hg)

/-- **The glued map restricts to the two outer ends** — the `hg_restrict` field. -/
theorem glueMap_comp_glueEnds :
    glueMap b₁ b₂ ∘ glueEnds b₁ b₂ = Sum.elim p.f r.f := by
  funext x
  cases x with
  | inl m => exact congrFun b₁.hg_restrict (Sum.inl m)
  | inr m => exact congrFun b₂.hg_restrict (Sum.inr m)

/-! ### §3c. The residue, made kernel-checkable: `SeamGlueChart` -/

/-- **ARC A — the exact residual input of manifold-level bordism gluing.** A `C^k` charted structure
on the seam pushout `glueCarrier b₁ b₂` for which the *already-built* welded data is a bordism: the
charts, the manifold condition, smoothness of the welded end-map, and the boundary identity.

This is the **collar-neighbourhood content** and nothing else. Its four fields are precisely the four
`Bordism` fields §3 could not supply; `Bordism.ofSeamGlueChart` discharges the other eight from the
generic construction, so the claim "gluing reduces to the collar theorem" is kernel-checked rather
than asserted. Note that `smooth` and `boundary` are *about* the concrete `glueEnds` / `glueCarrier`
built above — this is not a restatement of "there exists a glued bordism". -/
structure SeamGlueChart where
  /-- charts on the seam pushout, modelled on the half-space model one dimension up. -/
  [chart : ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) (glueCarrier b₁ b₂)]
  /-- the charts are `C^k`-compatible. -/
  [mfd : IsManifold (I.prod (𝓡∂ 1)) k (glueCarrier b₁ b₂)]
  /-- the welded outer-end map is smooth for those charts. -/
  smooth : ContMDiff I (I.prod (𝓡∂ 1)) k (glueEnds b₁ b₂)
  /-- the welded outer ends are exactly the boundary — the seam has become interior. -/
  boundary : Set.range (glueEnds b₁ b₂) = (I.prod (𝓡∂ 1)).boundary (glueCarrier b₁ b₂)

/-- **The reduction, kernel-checked: a seam chart is all that manifold-level gluing lacks.** Given
`SeamGlueChart b₁ b₂` (and the T2 ends the REFINED relation supplies), the composite bordism
`p ⇝ r` is assembled entirely from §3's generic construction — carrier, compactness, end-map,
injectivity, map to `X`, and its restriction all come from there. -/
noncomputable def Bordism.ofSeamGlueChart [T2Space b₁.W] [T2Space b₂.W] (c : SeamGlueChart b₁ b₂) :
    Bordism (I.prod (𝓡∂ 1)) p r where
  W := glueCarrier b₁ b₂
  chartW := c.chart
  mfdW := c.mfd
  compactW := compactSpace_glueCarrier b₁ b₂
  e := glueEnds b₁ b₂
  he_smooth := c.smooth
  he_inj := glueEnds_injective b₁ b₂
  he_boundary := c.boundary
  g := glueMap b₁ b₂
  hg := continuous_glueMap b₁ b₂
  hg_restrict := glueMap_comp_glueEnds b₁ b₂

@[simp] theorem Bordism.ofSeamGlueChart_W [T2Space b₁.W] [T2Space b₂.W]
    (c : SeamGlueChart b₁ b₂) :
    (Bordism.ofSeamGlueChart b₁ b₂ c).W = glueCarrier b₁ b₂ := rfl

/-- **The Hausdorff refinement is FREE along the weld.** The glued total space is automatically T2
when the two pieces are, so the `NonHausdorffBordismCollapse` repair adds *no* new obstruction to
gluing: given arc A (`SeamGlueChart`) and arc B (a tethered structure `ξ.Bor` on the glued bordism),
the REFINED relation — not merely the degenerate one — holds. This is what makes `GluesT2` reachable
in principle from the two arcs. -/
theorem isT2DataBordant_of_seamGlue [I.Boundaryless] (ξ : T2TangentialData X k I)
    {σ : ξ.Mfd p} {τ : ξ.Mfd r} [T2Space b₁.W] [T2Space b₂.W] (c : SeamGlueChart b₁ b₂)
    (str : ξ.Bor (Bordism.ofSeamGlueChart b₁ b₂ c) σ τ) :
    IsT2DataBordant ξ ⟨p, σ⟩ ⟨r, τ⟩ :=
  ⟨Bordism.ofSeamGlueChart b₁ b₂ c, t2Space_glueCarrier b₁ b₂, ⟨str⟩⟩

end Glue

end SKEFTHawking.T2BordismGluing
