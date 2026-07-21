/-
# The 4-chart good-cover Mayer–Vietoris telescope: `Hₘ(ℝP³_𝔼;ℤ) = 0` for `m ≥ 4`

The geometric termination input for the `H_*(ℝP³;ℤ)` table, on the Euclidean carrier
`RP3E = S³_𝔼/±` of `KummerRP3EuclCharts`. The four central-projection charts
`UE 0, …, UE 3` cover `ℝP³`; every multi-intersection `UE i ∩ UE j ∩ ⋯` splits into
**disjoint signed lunes** based at its lowest chart, and each lune corresponds under the
central projection to a convex intersection of open coordinate half-spaces — so the banked
convex-chart acyclicity engine (`homology_chartConvexSub_eq_zeroInt`) gives every lune
`Hₖ = 0` for `k ≥ 1`, and the subset-level Mayer–Vietoris sandwich
(`subHom_exact_sumInt`) telescopes:

* every multi-intersection is `AcyclicPos` (positive-degree acyclic) — disjoint-lune splits;
* `VanishFrom 2 (UE 0 ∪ UE 1)`, `VanishFrom 2` of the two-chart seam unions;
* `VanishFrom 3 (UE 0 ∪ UE 1 ∪ UE 2)` and `VanishFrom 3` of the triple seam `V₃ ∩ UE 3`;
* **`rp3E_homology_high : Hₘ(ℝP³_𝔼;ℤ) = 0` for `m ≥ 4`** — the final ambient MV step
  (`mv_exact_ambientInt`) on the cover `(UE 0 ∪ UE 1 ∪ UE 2) ∪ UE 3 = univ`.

The `H₄`/`H₅` specializations transport to the pinned `ℂ²`-carrier `RP3top` in
`KummerRP3HomologyUnconditional`, discharging the two termination hypotheses of
`KummerRP3HomologyTop`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.KummerRP3EuclCharts
import SKEFTHawking.SingularSubHomologyMVInt
import SKEFTHawking.SingularConvexSubAcyclicInt
import SKEFTHawking.SingularCSCEmptyInt

open Metric Topology
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularOpenDualityMVSquareInt (subHomDiagInt subHomSumInt)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt subHom_exact_sumInt)
open SKEFTHawking.SingularCSCEmptyInt (homology_sub_empty_eq_zeroInt)
open SKEFTHawking.SingularConvexSubAcyclicInt (homology_chartConvexSub_eq_zeroInt)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvDeltaInt mv_exact_ambientInt)

namespace SKEFTHawking.KummerRP3GoodCoverTelescope

noncomputable section

/-! ## §0. Vanishing vocabulary and the Mayer–Vietoris sandwich -/

/-- Positive-degree acyclicity of a subspace of `ℝP³_𝔼`: `Hₖ(sub T;ℤ) = 0` for all `k ≥ 1`. -/
def AcyclicPos (T : Set ↑RP3Etop) : Prop :=
  ∀ (k : ℕ) (x : Homology (sub T) (k + 1)), x = 0

/-- `Hₘ(sub T;ℤ) = 0` for all `m ≥ d`. -/
def VanishFrom (d : ℕ) (T : Set ↑RP3Etop) : Prop :=
  ∀ m, d ≤ m → ∀ x : Homology (sub T) m, x = 0

theorem AcyclicPos.vanishFrom {T : Set ↑RP3Etop} (h : AcyclicPos T) : VanishFrom 1 T := by
  intro m hm x
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact h n x

/-- **The subset-level Mayer–Vietoris sandwich**: if both pieces vanish in degree `n + 1` and the
intersection vanishes in degree `n`, the union vanishes in degree `n + 1`. -/
theorem vanish_union {U V : Set ↑RP3Etop} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUv : ∀ x : Homology (sub U) (n + 1), x = 0)
    (hVv : ∀ x : Homology (sub V) (n + 1), x = 0)
    (hIv : ∀ x : Homology (sub (U ∩ V)) n, x = 0)
    (x : Homology (sub (U ∪ V)) (n + 1)) : x = 0 := by
  have h0 : subHomConnectingInt U V hU hV n x = 0 := hIv _
  obtain ⟨p, hp⟩ := (subHom_exact_sumInt U V hU hV x).mp h0
  have hp0 : p = 0 := Prod.ext_iff.mpr ⟨hUv p.1, hVv p.2⟩
  rw [← hp, hp0, map_zero]

/-- Disjoint open pieces: positive-degree acyclicity is preserved by disjoint unions (the
intersection is empty, whose homology vanishes in every degree). -/
theorem acyclicPos_union_disjoint {U V : Set ↑RP3Etop} (hU : IsOpen U) (hV : IsOpen V)
    (hd : U ∩ V = ∅) (hUv : AcyclicPos U) (hVv : AcyclicPos V) : AcyclicPos (U ∪ V) := by
  intro k x
  refine vanish_union hU hV (hUv k) (hVv k) ?_ x
  have h : ∀ w : Homology (sub (U ∩ V)) k, w = 0 := by
    rw [hd]
    exact homology_sub_empty_eq_zeroInt k
  exact h

/-- Degree-bookkeeping form of the sandwich. -/
theorem vanishFrom_union {U V : Set ↑RP3Etop} (hU : IsOpen U) (hV : IsOpen V) {dU dV dI d : ℕ}
    (hUv : VanishFrom dU U) (hVv : VanishFrom dV V) (hIv : VanishFrom dI (U ∩ V))
    (hdU : dU ≤ d) (hdV : dV ≤ d) (hdI : dI + 1 ≤ d) (hd : 1 ≤ d) :
    VanishFrom d (U ∪ V) := by
  intro m hm x
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact vanish_union hU hV (hUv (n + 1) (by omega)) (hVv (n + 1) (by omega))
    (hIv n (by omega)) x

/-! ## §1. Signed lunes and their chart-convex acyclicity -/

/-- The sign condition: `b = true` demands positivity, `b = false` negativity. -/
def signCond (b : Bool) (r : ℝ) : Prop := if b then 0 < r else r < 0

theorem signCond_ne_zero {b : Bool} {r : ℝ} (h : signCond b r) : r ≠ 0 := by
  cases b with
  | true => exact ne_of_gt h
  | false => exact ne_of_lt h

theorem signCond_incompatible {b b' : Bool} {r : ℝ} (h : signCond b r) (h' : signCond b' r)
    (hne : b ≠ b') : False := by
  cases b with
  | true => cases b' with
    | true => exact hne rfl
    | false => exact lt_irrefl r (lt_trans (show r < 0 from h') (show 0 < r from h))
  | false => cases b' with
    | true => exact lt_irrefl r (lt_trans (show r < 0 from h) (show 0 < r from h'))
    | false => exact hne rfl

/-- The signed-lune source on the sphere: `y i > 0`, and for `j ∈ s` the coordinate
`y (i.succAbove j)` carries the sign `ε j`. -/
def lumSet (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) : Set S3E :=
  {y : S3E | 0 < (y : EuclideanSpace ℝ (Fin 4)) i ∧
    ∀ j ∈ s, signCond (ε j) ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j))}

theorem isOpen_signSet (i : Fin 4) (j : Fin 3) (b : Bool) :
    IsOpen {y : S3E | signCond b ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j))} := by
  cases b with
  | true =>
      have hset : {y : S3E | signCond true ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j))}
          = {y : S3E | 0 < (y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j)} := by
        ext y; simp [signCond]
      rw [hset]
      exact isOpen_lt continuous_const (by fun_prop)
  | false =>
      have hset : {y : S3E | signCond false ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j))}
          = {y : S3E | (y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j) < 0} := by
        ext y; simp [signCond]
      rw [hset]
      exact isOpen_lt (by fun_prop) continuous_const

theorem lumSet_isOpen (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) :
    IsOpen (lumSet i s ε) := by
  have hrw : lumSet i s ε
      = hemiC i ∩ ⋂ j ∈ s, {y : S3E |
          signCond (ε j) ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j))} := by
    ext y
    simp only [lumSet, hemiC, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hrw]
  exact (hemiC_isOpen i).inter
    (Set.Finite.isOpen_biInter s.finite_toSet fun j _ => isOpen_signSet i j (ε j))

/-- **The signed lune** in `ℝP³_𝔼` — the image of the signed-lune source. -/
def lune (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) : Set ↑RP3Etop :=
  mkE '' lumSet i s ε

theorem lune_isOpen (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) :
    IsOpen (lune i s ε) :=
  isOpenMap_mkE _ (lumSet_isOpen i s ε)

/-- **Hemisphere-representative membership law for lunes**: for `x` with `x i > 0`,
`mkE x ∈ lune i s ε` iff `x` itself satisfies the sign conditions. -/
theorem mkE_mem_lune_iff {i : Fin 4} {s : Finset (Fin 3)} {ε : Fin 3 → Bool} {x : S3E}
    (hx : 0 < (x : EuclideanSpace ℝ (Fin 4)) i) :
    mkE x ∈ lune i s ε
      ↔ ∀ j ∈ s, signCond (ε j) ((x : EuclideanSpace ℝ (Fin 4)) (i.succAbove j)) := by
  constructor
  · rintro ⟨y, hy, hmk⟩
    rcases fiberE_pair hmk with heq | heq
    · rw [heq] at hy; exact hy.2
    · exfalso
      have hyi : (0 : ℝ) < (y : EuclideanSpace ℝ (Fin 4)) i := hy.1
      rw [heq, neg_one_smul_apply] at hyi
      exact absurd hx (not_lt.mpr (le_of_lt (neg_pos.mp hyi)))
  · intro hs
    exact ⟨x, ⟨hx, hs⟩, rfl⟩

/-- The chart-side convex model of a signed lune: the intersection of open half-spaces. -/
def chartC (s : Finset (Fin 3)) (ε : Fin 3 → Bool) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋂ j ∈ s, {z : EuclideanSpace ℝ (Fin 3) | signCond (ε j) (z j)}

theorem convex_signSet (j : Fin 3) (b : Bool) :
    Convex ℝ {z : EuclideanSpace ℝ (Fin 3) | signCond b (z j)} := by
  have hlin : IsLinearMap ℝ (fun z : EuclideanSpace ℝ (Fin 3) => z j) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  cases b with
  | true =>
      have hset : {z : EuclideanSpace ℝ (Fin 3) | signCond true (z j)}
          = {z : EuclideanSpace ℝ (Fin 3) | 0 < z j} := by
        ext z; simp [signCond]
      rw [hset]
      exact convex_halfSpace_gt hlin 0
  | false =>
      have hset : {z : EuclideanSpace ℝ (Fin 3) | signCond false (z j)}
          = {z : EuclideanSpace ℝ (Fin 3) | z j < 0} := by
        ext z; simp [signCond]
      rw [hset]
      exact convex_halfSpace_lt hlin 0

theorem chartC_convex (s : Finset (Fin 3)) (ε : Fin 3 → Bool) : Convex ℝ (chartC s ε) :=
  convex_iInter₂ fun j _ => convex_signSet j (ε j)

/-- The signed base point of the chart model. -/
def chartPt (ε : Fin 3 → Bool) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => if ε j then (1 : ℝ) else -1

theorem chartPt_mem (s : Finset (Fin 3)) (ε : Fin 3 → Bool) : chartPt ε ∈ chartC s ε := by
  refine Set.mem_iInter₂.mpr fun j _ => ?_
  show signCond (ε j) (chartPt ε j)
  have happ : chartPt ε j = if ε j then (1 : ℝ) else -1 := rfl
  cases hb : ε j with
  | true => rw [show signCond true (chartPt ε j) = (0 < chartPt ε j) from rfl, happ, hb]; norm_num
  | false =>
      rw [show signCond false (chartPt ε j) = (chartPt ε j < 0) from rfl, happ, hb]; norm_num

/-- Sign conditions transport through the central projection (positive denominator). -/
theorem signCond_div_iff {b : Bool} {a c : ℝ} (hc : 0 < c) :
    signCond b (a / c) ↔ signCond b a := by
  cases b with
  | true =>
      show 0 < a / c ↔ 0 < a
      constructor
      · intro h
        rcases div_pos_iff.mp h with ⟨ha, _⟩ | ⟨_, hc'⟩
        · exact ha
        · exact absurd hc (not_lt.mpr (le_of_lt hc'))
      · intro h; exact div_pos h hc
  | false =>
      show a / c < 0 ↔ a < 0
      constructor
      · intro h
        rcases div_neg_iff.mp h with ⟨_, hc'⟩ | ⟨ha, _⟩
        · exact absurd hc (not_lt.mpr (le_of_lt hc'))
        · exact ha
      · intro h; exact div_neg_of_neg_of_pos h hc

/-- **The lune ↔ chart-model membership correspondence** consumed by the acyclicity engine. -/
theorem lune_charted_mem (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool)
    (u : ↥(UE i)) :
    (u : ↑RP3Etop) ∈ lune i s ε
      ↔ ((charted i u : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) :
          EuclideanSpace ℝ (Fin 3)) ∈ chartC s ε := by
  obtain ⟨y, rfl⟩ := (hemiEquivUE i).surjective u
  have hyi : (0 : ℝ) < (y.1 : EuclideanSpace ℝ (Fin 4)) i := y.2
  rw [show ((hemiEquivUE i y : ↥(UE i)) : ↑RP3Etop) = mkE y.1 from hemiEquivUE_coe i y,
    charted_coe i y, mkE_mem_lune_iff hyi]
  constructor
  · intro hs
    refine Set.mem_iInter₂.mpr fun j hj => ?_
    show signCond (ε j) (centralProj i y j)
    rw [centralProj_apply, signCond_div_iff hyi]
    exact hs j hj
  · intro hC j hj
    have := Set.mem_iInter₂.mp hC j hj
    rw [show (centralProj i y ∈ {z : EuclideanSpace ℝ (Fin 3) | signCond (ε j) (z j)})
        = signCond (ε j) (centralProj i y j) from rfl, centralProj_apply,
      signCond_div_iff hyi] at this
    exact this

/-- **Every signed lune is positive-degree acyclic** — the convex-chart acyclicity engine applied
to the central-projection chart. -/
theorem acyclicPos_lune (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) :
    AcyclicPos (lune i s ε) := by
  intro k x
  refine homology_chartConvexSub_eq_zeroInt (M := RP3Etop) (m := 1) (U := UE i)
    (V := (Set.univ : Set ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 3))) (charted i)
    (chartC_convex s ε) (chartPt_mem s ε) (Set.subset_univ _) ?_ ?_ k x
  · rintro q ⟨y, hy, rfl⟩
    exact ⟨y, hy.1, rfl⟩
  · exact lune_charted_mem i s ε

/-! ## §2. Lune algebra: charts as lunes, sign splits, disjointness -/

/-- The chart `UE i` is the unconstrained lune. -/
theorem UE_eq_lune (i : Fin 4) : UE i = lune i ∅ (fun _ => true) := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hy, fun j hj => absurd hj (by simp)⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy.1, rfl⟩

theorem acyclicPos_UE (i : Fin 4) : AcyclicPos (UE i) := by
  rw [UE_eq_lune i]
  exact acyclicPos_lune i ∅ _

/-- **The sign split**: intersecting a lune with a fresh chart splits it into the two signed
refinements. -/
theorem lune_inter_UE (i : Fin 4) (s : Finset (Fin 3)) (ε : Fin 3 → Bool) {j : Fin 3}
    (hj : j ∉ s) :
    lune i s ε ∩ UE (i.succAbove j)
      = lune i (insert j s) (Function.update ε j true)
        ∪ lune i (insert j s) (Function.update ε j false) := by
  ext q
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hU⟩
    have hyi : (0 : ℝ) < (y : EuclideanSpace ℝ (Fin 4)) i := hy.1
    have hne : (y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j) ≠ 0 := mkE_mem_UE_iff.mp hU
    have hcond : ∀ (b : Bool),
        signCond b ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j)) →
        mkE y ∈ lune i (insert j s) (Function.update ε j b) := by
      intro b hb
      refine (mkE_mem_lune_iff hyi).mpr fun j' hj' => ?_
      rcases Finset.mem_insert.mp hj' with rfl | hj's
      · rwa [Function.update_self]
      · have hj'ne : j' ≠ j := fun h => hj (h ▸ hj's)
        rw [Function.update_of_ne hj'ne]
        exact hy.2 j' hj's
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr (hcond false hlt)
    · exact Or.inl (hcond true hgt)
  · intro hq
    have hcase : ∀ (b : Bool), q ∈ lune i (insert j s) (Function.update ε j b) →
        q ∈ lune i s ε ∩ UE (i.succAbove j) := by
      rintro b ⟨y, hy, rfl⟩
      have hyi : (0 : ℝ) < (y : EuclideanSpace ℝ (Fin 4)) i := hy.1
      have hsign : signCond b ((y : EuclideanSpace ℝ (Fin 4)) (i.succAbove j)) := by
        have := hy.2 j (Finset.mem_insert_self j s)
        rwa [Function.update_self] at this
      refine ⟨(mkE_mem_lune_iff hyi).mpr fun j' hj' => ?_, mkE_mem_UE_iff.mpr
        (signCond_ne_zero hsign)⟩
      have hj'ne : j' ≠ j := fun h => hj (h ▸ hj')
      have := hy.2 j' (Finset.mem_insert_of_mem hj')
      rwa [Function.update_of_ne hj'ne] at this
    rcases hq with h | h
    · exact hcase true h
    · exact hcase false h

/-- Lunes with an incompatible sign at a shared index are disjoint. -/
theorem lune_disjoint {i : Fin 4} {s : Finset (Fin 3)} {ε ε' : Fin 3 → Bool} {j : Fin 3}
    (hj : j ∈ s) (hne : ε j ≠ ε' j) : lune i s ε ∩ lune i s ε' = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun q ⟨h1, h2⟩ => ?_
  obtain ⟨y, hy, rfl⟩ := h1
  have hyi : (0 : ℝ) < (y : EuclideanSpace ℝ (Fin 4)) i := hy.1
  have hs' := (mkE_mem_lune_iff hyi).mp h2 j hj
  exact signCond_incompatible (hy.2 j hj) hs' hne

/-! ## §3. Every multi-intersection of charts is positive-degree acyclic -/

/-- **The disjoint-lune split engine**: a lune intersected with any set of fresh charts is
positive-degree acyclic — Finset induction, splitting off one chart per step into a disjoint
open pair. -/
theorem acyclicPos_lune_inter_biInter (i : Fin 4) (t : Finset (Fin 3)) :
    ∀ (s : Finset (Fin 3)) (ε : Fin 3 → Bool), Disjoint s t →
      AcyclicPos (lune i s ε ∩ ⋂ j ∈ t, UE (i.succAbove j)) := by
  induction t using Finset.induction_on with
  | empty =>
      intro s ε _
      have : lune i s ε ∩ ⋂ j ∈ (∅ : Finset (Fin 3)), UE (i.succAbove j) = lune i s ε := by
        simp
      rw [this]
      exact acyclicPos_lune i s ε
  | insert j t hjt ih =>
      intro s ε hst
      have hjs : j ∉ s := fun h =>
        (Finset.disjoint_left.mp hst h) (Finset.mem_insert_self j t)
      have hst' : ∀ b : Bool, Disjoint (insert j s) t := fun _ => by
        rw [Finset.disjoint_left]
        intro a ha hat
        rcases Finset.mem_insert.mp ha with rfl | has
        · exact hjt hat
        · exact (Finset.disjoint_left.mp hst has) (Finset.mem_insert_of_mem hat)
      have hrw : lune i s ε ∩ ⋂ j' ∈ insert j t, UE (i.succAbove j')
          = (lune i (insert j s) (Function.update ε j true) ∩ ⋂ j' ∈ t, UE (i.succAbove j'))
            ∪ (lune i (insert j s) (Function.update ε j false)
                ∩ ⋂ j' ∈ t, UE (i.succAbove j')) := by
        rw [Finset.set_biInter_insert, ← Set.inter_assoc, lune_inter_UE i s ε hjs,
          Set.union_inter_distrib_right]
      rw [hrw]
      refine acyclicPos_union_disjoint ?_ ?_ ?_ (ih _ _ (hst' true)) (ih _ _ (hst' false))
      · exact (lune_isOpen _ _ _).inter
          (Set.Finite.isOpen_biInter t.finite_toSet fun j' _ => UE_isOpen _)
      · exact (lune_isOpen _ _ _).inter
          (Set.Finite.isOpen_biInter t.finite_toSet fun j' _ => UE_isOpen _)
      · have hsub : (lune i (insert j s) (Function.update ε j true)
              ∩ ⋂ j' ∈ t, UE (i.succAbove j'))
            ∩ (lune i (insert j s) (Function.update ε j false)
              ∩ ⋂ j' ∈ t, UE (i.succAbove j'))
            ⊆ lune i (insert j s) (Function.update ε j true)
              ∩ lune i (insert j s) (Function.update ε j false) := by
          rintro q ⟨⟨hq1, _⟩, ⟨hq2, _⟩⟩
          exact ⟨hq1, hq2⟩
        refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
        have := hsub hq
        rw [lune_disjoint (Finset.mem_insert_self j s)
          (by rw [Function.update_self, Function.update_self]; decide)] at this
        exact this

/-- Positive-degree acyclicity of `UE i ∩ ⋂ j ∈ t, UE (i.succAbove j)` — every multi-intersection
of distinct charts, in based form. -/
theorem acyclicPos_inter_charts (i : Fin 4) (t : Finset (Fin 3)) :
    AcyclicPos (UE i ∩ ⋂ j ∈ t, UE (i.succAbove j)) := by
  rw [UE_eq_lune i]
  exact acyclicPos_lune_inter_biInter i t ∅ (fun _ => true) (Finset.disjoint_left.mpr
    fun a ha => absurd ha (by simp))

/-! ## §4. The concrete multi-intersections of the 4-chart cover -/

theorem acyclicPos_congr {S T : Set ↑RP3Etop} (h : S = T) (hS : AcyclicPos S) : AcyclicPos T :=
  h ▸ hS

theorem vanishFrom_congr {d : ℕ} {S T : Set ↑RP3Etop} (h : S = T) (hS : VanishFrom d S) :
    VanishFrom d T :=
  h ▸ hS

@[simp] theorem succAbove_0_0 : (0 : Fin 4).succAbove 0 = 1 := by decide
@[simp] theorem succAbove_0_1 : (0 : Fin 4).succAbove 1 = 2 := by decide
@[simp] theorem succAbove_0_2 : (0 : Fin 4).succAbove 2 = 3 := by decide
@[simp] theorem succAbove_1_1 : (1 : Fin 4).succAbove 1 = 2 := by decide
@[simp] theorem succAbove_1_2 : (1 : Fin 4).succAbove 2 = 3 := by decide
@[simp] theorem succAbove_2_2 : (2 : Fin 4).succAbove 2 = 3 := by decide

/-- The six pairwise intersections are positive-degree acyclic. -/
theorem acyclicPos_pair_01 : AcyclicPos (UE 0 ∩ UE 1) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {0})
  simp

theorem acyclicPos_pair_02 : AcyclicPos (UE 0 ∩ UE 2) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {1})
  simp

theorem acyclicPos_pair_12 : AcyclicPos (UE 1 ∩ UE 2) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 1 {1})
  simp

theorem acyclicPos_pair_03 : AcyclicPos (UE 0 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {2})
  simp

theorem acyclicPos_pair_13 : AcyclicPos (UE 1 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 1 {2})
  simp

theorem acyclicPos_pair_23 : AcyclicPos (UE 2 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 2 {2})
  simp

/-- The four triple intersections are positive-degree acyclic. -/
theorem acyclicPos_triple_012 : AcyclicPos (UE 0 ∩ UE 1 ∩ UE 2) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {0, 1})
  simp
  tauto

theorem acyclicPos_triple_013 : AcyclicPos (UE 0 ∩ UE 1 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {0, 2})
  simp
  tauto

theorem acyclicPos_triple_023 : AcyclicPos (UE 0 ∩ UE 2 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {1, 2})
  simp
  tauto

theorem acyclicPos_triple_123 : AcyclicPos (UE 1 ∩ UE 2 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 1 {1, 2})
  simp
  tauto

/-- The quadruple intersection is positive-degree acyclic. -/
theorem acyclicPos_quad : AcyclicPos (UE 0 ∩ UE 1 ∩ UE 2 ∩ UE 3) := by
  refine acyclicPos_congr (Set.ext fun q => ?_) (acyclicPos_inter_charts 0 {0, 1, 2})
  simp
  tauto

/-! ## §5. The telescope: `V₂ → V₃ → ℝP³` -/

/-- **Level 2**: `Hₘ(UE 0 ∪ UE 1; ℤ) = 0` for `m ≥ 2`. -/
theorem vanishFrom_V2 : VanishFrom 2 (UE 0 ∪ UE 1) :=
  vanishFrom_union (UE_isOpen 0) (UE_isOpen 1) (acyclicPos_UE 0).vanishFrom
    (acyclicPos_UE 1).vanishFrom acyclicPos_pair_01.vanishFrom
    (by omega) (by omega) (by omega) (by omega)

/-- **Level 2, seam of step 3**: `Hₘ((UE 0 ∩ UE 2) ∪ (UE 1 ∩ UE 2); ℤ) = 0` for `m ≥ 2`. -/
theorem vanishFrom_I3 : VanishFrom 2 ((UE 0 ∩ UE 2) ∪ (UE 1 ∩ UE 2)) := by
  refine vanishFrom_union ((UE_isOpen 0).inter (UE_isOpen 2)) ((UE_isOpen 1).inter (UE_isOpen 2))
    acyclicPos_pair_02.vanishFrom acyclicPos_pair_12.vanishFrom
    (vanishFrom_congr ?_ acyclicPos_triple_012.vanishFrom)
    (by omega) (by omega) (by omega) (by omega)
  ext q
  simp only [Set.mem_inter_iff]
  tauto

/-- **Level 3**: `Hₘ(UE 0 ∪ UE 1 ∪ UE 2; ℤ) = 0` for `m ≥ 3`. -/
theorem vanishFrom_V3 : VanishFrom 3 (UE 0 ∪ UE 1 ∪ UE 2) :=
  vanishFrom_union ((UE_isOpen 0).union (UE_isOpen 1)) (UE_isOpen 2) vanishFrom_V2
    (acyclicPos_UE 2).vanishFrom
    (vanishFrom_congr (Set.union_inter_distrib_right _ _ _).symm vanishFrom_I3)
    (by omega) (by omega) (by omega) (by omega)

/-- **Level 2, first half of the step-4 seam**: `(UE 0 ∩ UE 3) ∪ (UE 1 ∩ UE 3)`. -/
theorem vanishFrom_W24 : VanishFrom 2 ((UE 0 ∩ UE 3) ∪ (UE 1 ∩ UE 3)) := by
  refine vanishFrom_union ((UE_isOpen 0).inter (UE_isOpen 3)) ((UE_isOpen 1).inter (UE_isOpen 3))
    acyclicPos_pair_03.vanishFrom acyclicPos_pair_13.vanishFrom
    (vanishFrom_congr ?_ acyclicPos_triple_013.vanishFrom)
    (by omega) (by omega) (by omega) (by omega)
  ext q
  simp only [Set.mem_inter_iff]
  tauto

/-- **Level 2, refined step-4 seam**: `(UE 0 ∩ UE 2 ∩ UE 3) ∪ (UE 1 ∩ UE 2 ∩ UE 3)`. -/
theorem vanishFrom_W' : VanishFrom 2 ((UE 0 ∩ UE 2 ∩ UE 3) ∪ (UE 1 ∩ UE 2 ∩ UE 3)) := by
  refine vanishFrom_union (((UE_isOpen 0).inter (UE_isOpen 2)).inter (UE_isOpen 3))
    (((UE_isOpen 1).inter (UE_isOpen 2)).inter (UE_isOpen 3))
    acyclicPos_triple_023.vanishFrom acyclicPos_triple_123.vanishFrom
    (vanishFrom_congr ?_ acyclicPos_quad.vanishFrom)
    (by omega) (by omega) (by omega) (by omega)
  ext q
  simp only [Set.mem_inter_iff]
  tauto

/-- **Level 3, the full step-4 seam** `V₃ ∩ UE 3 = (UE 0 ∩ UE 3) ∪ (UE 1 ∩ UE 3) ∪ (UE 2 ∩ UE 3)`:
`Hₘ = 0` for `m ≥ 3`. -/
theorem vanishFrom_I4 : VanishFrom 3 ((UE 0 ∩ UE 3) ∪ (UE 1 ∩ UE 3) ∪ (UE 2 ∩ UE 3)) := by
  refine vanishFrom_union
    (((UE_isOpen 0).inter (UE_isOpen 3)).union ((UE_isOpen 1).inter (UE_isOpen 3)))
    ((UE_isOpen 2).inter (UE_isOpen 3)) vanishFrom_W24 acyclicPos_pair_23.vanishFrom
    (vanishFrom_congr ?_ vanishFrom_W')
    (by omega) (by omega) (by omega) (by omega)
  ext q
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-! ## §6. The final ambient Mayer–Vietoris step: `Hₘ(ℝP³_𝔼;ℤ) = 0` for `m ≥ 4` -/

/-- **The termination theorem on the Euclidean carrier** — `Hₘ(ℝP³_𝔼;ℤ) = 0` for every `m ≥ 4`,
by the ambient Mayer–Vietoris LES of the open cover `(UE 0 ∪ UE 1 ∪ UE 2) ∪ UE 3 = univ`:
the connecting map lands in `Hₘ₋₁` of the triple seam (`vanishFrom_I4`, `m - 1 ≥ 3`), and the
`Σ`-preimage lives on `Hₘ(V₃) ⊕ Hₘ(UE 3)` (`vanishFrom_V3`, `m ≥ 3` and chart acyclicity). -/
theorem rp3E_homology_high (m : ℕ) (hm : 4 ≤ m) (x : Homology RP3Etop m) : x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hA : IsOpen (UE 0 ∪ UE 1 ∪ UE 2) :=
    ((UE_isOpen 0).union (UE_isOpen 1)).union (UE_isOpen 2)
  have hcov : (⋃ W ∈ ({UE 0 ∪ UE 1 ∪ UE 2, UE 3} : Set (Set ↑RP3Etop)), interior W)
      = Set.univ := by
    rw [Set.biUnion_pair, hA.interior_eq, (UE_isOpen 3).interior_eq]
    exact UE_cover
  have h0 : mvDeltaInt (X := RP3Etop) (UE 0 ∪ UE 1 ∪ UE 2) (UE 3) n hcov x = 0 := by
    have hseam : ((UE 0 ∪ UE 1 ∪ UE 2) ∩ UE 3 : Set ↑RP3Etop)
        = (UE 0 ∩ UE 3) ∪ (UE 1 ∩ UE 3) ∪ (UE 2 ∩ UE 3) := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_union]
      tauto
    have hvan : ∀ w : Homology
        (sub (((UE 0 ∪ UE 1 ∪ UE 2) ∩ UE 3 : Set ↑RP3Etop))) n, w = 0 := by
      rw [hseam]
      exact fun w => vanishFrom_I4 n (by omega) w
    exact hvan _
  obtain ⟨p, hp⟩ :=
    (mv_exact_ambientInt (X := RP3Etop) (UE 0 ∪ UE 1 ∪ UE 2) (UE 3) n hcov x).mp h0
  have hp0 : p = 0 := Prod.ext_iff.mpr
    ⟨vanishFrom_V3 (n + 1) (by omega) p.1, (acyclicPos_UE 3).vanishFrom (n + 1) (by omega) p.2⟩
  rw [← hp, hp0, map_zero]

/-- **`H₄(ℝP³_𝔼;ℤ) = 0`** — the first geometric termination input. -/
theorem rp3E_homology_four_eq_zero (x : Homology RP3Etop 4) : x = 0 :=
  rp3E_homology_high 4 (le_refl 4) x

/-- **`H₅(ℝP³_𝔼;ℤ) = 0`** — the second geometric termination input. -/
theorem rp3E_homology_five_eq_zero (x : Homology RP3Etop 5) : x = 0 :=
  rp3E_homology_high 5 (by omega) x

end

end SKEFTHawking.KummerRP3GoodCoverTelescope
