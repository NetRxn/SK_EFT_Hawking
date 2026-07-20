/-
# Phase 5q.H — the Kummer K3 generator, K5′ (Route B): the free quotient `Q := T⁴°/τ`

Continues `KummerPuncturedTorus.lean` (K4′ = the punctured torus `T⁴°`, `τ` free on it, the 16
`τ`-invariant boundary spheres `∂B_i = sphere c (1/2)` in the pinned `S³/±1` antipodal
presentation). Read the **binding Route-B design doc**
`docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md` (K5′ row) first: the singular orbifold quotient
is NEVER formed — we quotient the FREE locus `T⁴°` and get an honest smooth
manifold-with-boundary `Q` with `∂Q = 16 × ℝP³`.

**The load-bearing reuse — the `ℝP⁴ = S⁴/±1` hand-chart template (`RP4PointSet`/`RP4Manifold`,
the #44 arc).** `ℝP⁴` was built as the orbit space of the antipodal `ℤˣ`-action on `S⁴`:
`Quotient (MulAction.orbitRel ℤˣ S4)`, with `T2`/`CompactSpace`/open-quotient-map ALL from the
finite-group properly-discontinuous machinery, and descended charts on "hemispheres" where the
quotient map is injective. We mirror this **verbatim** one dimension up, with `τ(w) = w⁻¹`
playing the role of the antipodal map: `τ` restricts to a **free** `ℤ/2 = ℤˣ`-action on the
subtype `↥T⁴°` (the generator `-1 : ℤˣ` acts by `τ`), so:

- **§1 — the action.** `SMul`/`MulAction`/`ContinuousConstSMul`/`ProperlyDiscontinuousSMul`
  `ℤˣ ↥T⁴°`, exactly the `RP4PointSet` §1 stack.
- **§2 — the carrier.** `FreeQuotient := Quotient (MulAction.orbitRel ℤˣ ↥T⁴°)`, with
  `TopologicalSpace`/`CompactSpace`/`T2Space` inherited (compact because `T⁴°` is closed in the
  compact `T⁴`; Hausdorff by the properly-discontinuous quotient theorem). The falsifiable pin:
  `Q` is genuinely a 2-to-1 quotient — the free orbit `{x, τx}` (distinct by freeness) is glued
  (`freeQuotient_identifies_distinct`), so `Q` is NOT the punctured torus.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedTorus

namespace SKEFTHawking.KummerFreeQuotient

open Metric Set
open scoped Manifold
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus

/-! ## §0. `T⁴°` is a compact (closed-in-`T⁴`) Hausdorff subtype -/

/-- The excised region is open (a finite union of open balls). -/
theorem isOpen_excisedBalls : IsOpen excisedBalls := by
  refine isOpen_biUnion ?_
  intro c _
  exact Metric.isOpen_ball

/-- **`T⁴°` is closed** (complement of the open excised region). -/
theorem isClosed_puncturedTorus : IsClosed puncturedTorus := by
  rw [puncturedTorus]
  exact isOpen_excisedBalls.isClosed_compl

/-- **`T⁴°` is compact** — a closed subset of the compact `T⁴`. -/
theorem isCompact_puncturedTorus : IsCompact puncturedTorus :=
  isClosed_puncturedTorus.isCompact

/-- **`↥T⁴°` is a compact space.** -/
instance : CompactSpace (↥puncturedTorus) :=
  isCompact_iff_compactSpace.mp isCompact_puncturedTorus

/-! ## §1. The free `ℤ/2 = ℤˣ`-action of `τ` on `↥T⁴°` (the `RP4PointSet` §1 stack) -/

/-- **The `τ`-action of `ℤˣ` on the punctured torus**: the generator `-1 : ℤˣ` acts by `τ`
(`τ² = id`, `τ` maps `T⁴°` into itself). The one-dimension-up analogue of the antipodal
`ℤˣ`-action on `S⁴` (`RP4PointSet`). -/
noncomputable instance instSMul : SMul ℤˣ (↥puncturedTorus) where
  smul u x := if u = 1 then x else ⟨torusFourInvolution x.1, involution_mapsTo_puncturedTorus x.2⟩

/-- The value of `1 • x` is `x` (the identity deck element). -/
@[simp] theorem one_smul_eq (x : ↥puncturedTorus) : (1 : ℤˣ) • x = x := by
  show (if (1 : ℤˣ) = 1 then x else _) = x
  rw [if_pos rfl]

/-- The underlying point of `(-1) • x` is `τ x` (the nontrivial deck element acts by `τ`). -/
@[simp] theorem neg_one_smul_val (x : ↥puncturedTorus) :
    (((-1 : ℤˣ) • x : ↥puncturedTorus) : TorusFour) = torusFourInvolution x.1 := by
  show (↑(if (-1 : ℤˣ) = 1 then x
      else (⟨torusFourInvolution x.1, involution_mapsTo_puncturedTorus x.2⟩ : ↥puncturedTorus)) :
    TorusFour) = _
  rw [if_neg (by decide)]

/-- The underlying-point form of the action (case split on the two deck elements). -/
theorem smul_val (u : ℤˣ) (x : ↥puncturedTorus) :
    ((u • x : ↥puncturedTorus) : TorusFour)
      = if u = 1 then (x : TorusFour) else torusFourInvolution x.1 := by
  show (↑(if u = 1 then x
      else (⟨torusFourInvolution x.1, involution_mapsTo_puncturedTorus x.2⟩ : ↥puncturedTorus)) :
    TorusFour) = _
  split <;> rfl

/-- **`ℤˣ` acts on `↥T⁴°`** — the `MulAction` laws from `τ² = id`. -/
noncomputable instance instMulAction : MulAction ℤˣ (↥puncturedTorus) where
  one_smul x := one_smul_eq x
  mul_smul u v x := by
    apply Subtype.ext
    rw [smul_val, smul_val, smul_val]
    rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv <;>
      subst hu <;> subst hv <;>
      simp only [mul_one, one_mul, if_neg (show (-1 : ℤˣ) ≠ 1 by decide),
        torusFourInvolution_involutive x.1] <;> rfl

/-- **The action is continuous** (each deck element acts by a homeomorphism: `id` or `τ`). -/
noncomputable instance instContinuousConstSMul : ContinuousConstSMul ℤˣ (↥puncturedTorus) := by
  refine ⟨fun u => ?_⟩
  rcases Int.units_eq_one_or u with hu | hu <;> subst hu
  · simpa only [one_smul_eq] using continuous_id
  · refine Continuous.subtype_mk ?_ _
    exact (torusFourInvolution_continuous.comp continuous_subtype_val)

/-- **The action is properly discontinuous** (`ℤˣ` is finite) — the engine for the Hausdorff
quotient, exactly as `RP4PointSet`. -/
instance instProperlyDiscontinuousSMul : ProperlyDiscontinuousSMul ℤˣ (↥puncturedTorus) :=
  ⟨fun _ _ => Set.toFinite _⟩

/-! ## §2. The carrier `Q := T⁴°/τ` -/

/-- **`Q := T⁴°/τ` — the free quotient**, mirroring `RP4 = S⁴/±1`. -/
def FreeQuotient : Type := Quotient (MulAction.orbitRel ℤˣ (↥puncturedTorus))

instance : TopologicalSpace FreeQuotient :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ (↥puncturedTorus))))

/-- **`Q` is compact** — a quotient of the compact `↥T⁴°`. -/
instance : CompactSpace FreeQuotient :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel ℤˣ (↥puncturedTorus))))

/-- **`Q` is Hausdorff** — the properly-discontinuous quotient theorem (the free `ℤˣ`-action on the
`T2` `↥T⁴°`), the one-dimension-up analogue of `RP4`'s `T2Space`. -/
instance : T2Space FreeQuotient :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel ℤˣ (↥puncturedTorus))))

/-- The quotient map `T⁴° ↠ Q`. -/
noncomputable def qmk (x : ↥puncturedTorus) : FreeQuotient :=
  Quotient.mk (MulAction.orbitRel ℤˣ (↥puncturedTorus)) x

/-! ## §2b. Falsifiable pins — `Q` is a genuine 2-to-1 quotient, NOT the punctured torus -/

/-- **The nontrivial deck element glues** `x` and `τ x` in `Q` (they lie in one orbit). -/
theorem qmk_neg_one_smul (x : ↥puncturedTorus) : qmk ((-1 : ℤˣ) • x) = qmk x := by
  apply Quotient.sound
  exact ⟨-1, rfl⟩

/-- **Freeness at the type level**: `(-1) • x ≠ x` for every `x ∈ T⁴°` (no fixed point survives
excision — `involution_free_on_puncturedTorus`). -/
theorem neg_one_smul_ne (x : ↥puncturedTorus) : (-1 : ℤˣ) • x ≠ x := by
  intro h
  have hval : torusFourInvolution x.1 = x.1 := by
    rw [← neg_one_smul_val x, h]
  exact involution_free_on_puncturedTorus x.1 x.2 hval

/-- **Falsifiable pin — `Q` is a genuine 2-to-1 quotient (NOT the punctured torus).** For every
`x ∈ T⁴°` the free orbit `{x, τx}` consists of two DISTINCT points (`neg_one_smul_ne`) that `Q`
identifies (`qmk_neg_one_smul`). So `qmk` is 2-to-1 on every orbit; `Q` is not the injective image
of `T⁴°`. (Non-vacuous once `T⁴°` is inhabited — see §2c.) -/
theorem freeQuotient_identifies_distinct (x : ↥puncturedTorus) :
    (-1 : ℤˣ) • x ≠ x ∧ qmk ((-1 : ℤˣ) • x) = qmk x :=
  ⟨neg_one_smul_ne x, qmk_neg_one_smul x⟩

/-! ## §2c. `T⁴°` is inhabited — the pins are non-vacuous -/

/-- The circle element `i` (`↑ = Complex.I`, norm `1`). -/
noncomputable def circleI : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

@[simp] theorem coe_circleI : ((circleI : Circle) : ℂ) = Complex.I := rfl

/-- **`i` is at distance `≥ 1/2` from each square-root of unity** (`1` and `negOne`): in fact the
distance is `≥ 1` (the imaginary part of `i − (±1)` is `1`, and `|im| ≤ ‖·‖`). -/
theorem half_le_dist_circleI {z : Circle} (hz : z = 1 ∨ z = negOne) :
    (1 : ℝ) / 2 ≤ dist circleI z := by
  have h1 : (1 : ℝ) ≤ dist circleI z := by
    show (1 : ℝ) ≤ dist ((circleI : Circle) : ℂ) ((z : Circle) : ℂ)
    rw [coe_circleI, Complex.dist_eq]
    rcases hz with rfl | rfl
    · rw [Circle.coe_one]
      calc (1 : ℝ) = |(Complex.I - 1).im| := by simp
        _ ≤ ‖Complex.I - 1‖ := Complex.abs_im_le_norm _
    · rw [coe_negOne]
      calc (1 : ℝ) = |(Complex.I - (-1)).im| := by simp
        _ ≤ ‖Complex.I - (-1)‖ := Complex.abs_im_le_norm _
  linarith

/-- **A concrete point of `T⁴°`**: `(i, 1, 1, 1)`. Its first coordinate `i` is `≥ 1/2` from both
`1` and `negOne`, so `(i, 1, 1, 1)` is outside every excised ball (each centred at a point of
`{±1}⁴`, whose first coordinate is `1` or `negOne`). -/
noncomputable def witnessPoint : TorusFour := (circleI, 1, 1, 1)

/-- The witness point lies in `T⁴°`. -/
theorem witnessPoint_mem : witnessPoint ∈ puncturedTorus := by
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c, hc, hmem⟩
  rw [Metric.mem_ball] at hmem
  have hc1 : c.1 = 1 ∨ c.1 = negOne := ((mem_fixedSet_iff c).mp hc).1
  have hbound : (1 : ℝ) / 2 ≤ dist witnessPoint.1 c.1 := half_le_dist_circleI hc1
  have hle : dist witnessPoint.1 c.1 ≤ dist witnessPoint c := le_dist_c1 witnessPoint c
  rw [show excisionRadius = (1 : ℝ) / 2 from rfl] at hmem
  linarith

/-- **`T⁴°` is inhabited** — the free orbit at `witnessPoint` witnesses that `Q` genuinely glues a
distinct pair (`freeQuotient_identifies_distinct` is non-vacuous). -/
instance : Nonempty (↥puncturedTorus) := ⟨⟨witnessPoint, witnessPoint_mem⟩⟩

/-- **`Q` is inhabited.** -/
instance : Nonempty FreeQuotient := ⟨qmk ⟨witnessPoint, witnessPoint_mem⟩⟩

/-! ## §3. The interior open-embedding engine — the `RP4PointSet` §2 pattern

Away from the boundary the free `ℤ/2`-action gives, around each `x`, a metric ball on which the
quotient map is **injective** (no orbit `{y, τy}` fits inside), hence an **open embedding** — the
one-dimension-up analogue of `RP4PointSet`'s hemisphere open embedding (`isOpenEmbedding_mk_hemi`),
and the descent engine for the interior charts. The separating ball has radius `dist(x, τx)/4 > 0`
(positive precisely by freeness). -/

/-- **The quotient map is open** (the group-orbit map), exactly as `RP4PointSet.isOpenMap_mk`. -/
theorem isOpenMap_qmk :
    IsOpenMap (Quotient.mk (MulAction.orbitRel ℤˣ (↥puncturedTorus))) :=
  isOpenMap_quotient_mk'_mul (Γ := ℤˣ) (T := ↥puncturedTorus)

/-- **Separating radius** at `x`: a quarter of `dist(x, τx)`, positive by freeness. -/
noncomputable def sepRadius (x : ↥puncturedTorus) : ℝ :=
  dist x.1 (torusFourInvolution x.1) / 4

/-- The separating radius is positive (freeness: `τx ≠ x`, so `dist(x, τx) > 0`). -/
theorem sepRadius_pos (x : ↥puncturedTorus) : 0 < sepRadius x := by
  have hne : torusFourInvolution x.1 ≠ x.1 := involution_free_on_puncturedTorus x.1 x.2
  have hd : 0 < dist x.1 (torusFourInvolution x.1) := dist_pos.mpr (fun h => hne h.symm)
  rw [sepRadius]; linarith

/-- **`Quotient.mk` is injective on the separating ball** — no orbit pair `{y, τy}` fits inside a
ball of radius `dist(x, τx)/4` (the `mk_injOn_hemi` analogue). -/
theorem qmk_injOn_sepBall (x : ↥puncturedTorus) :
    Set.InjOn (Quotient.mk (MulAction.orbitRel ℤˣ (↥puncturedTorus)))
      (Metric.ball x (sepRadius x)) := by
  intro y hy y' hy' hmk
  obtain ⟨u, hu⟩ : y ∈ MulAction.orbit ℤˣ y' := Quotient.eq''.mp hmk
  have hu' : u • y' = y := hu
  rcases Int.units_eq_one_or u with h1 | h1
  · rw [h1, one_smul] at hu'; exact hu'.symm
  · exfalso
    rw [h1] at hu'
    have hyval : (y : TorusFour) = torusFourInvolution y'.1 := by rw [← hu', neg_one_smul_val]
    have hyd : dist y.1 x.1 < sepRadius x := by rw [← Subtype.dist_eq]; exact Metric.mem_ball.mp hy
    have hy'd : dist y'.1 x.1 < sepRadius x := by
      rw [← Subtype.dist_eq]; exact Metric.mem_ball.mp hy'
    have hs : sepRadius x = dist x.1 (torusFourInvolution x.1) / 4 := rfl
    have hlow : dist x.1 (torusFourInvolution x.1)
        ≤ dist x.1 y'.1 + (dist y'.1 (torusFourInvolution y'.1)
            + dist (torusFourInvolution y'.1) (torusFourInvolution x.1)) :=
      calc dist x.1 (torusFourInvolution x.1)
          ≤ dist x.1 y'.1 + dist y'.1 (torusFourInvolution x.1) := dist_triangle _ _ _
        _ ≤ dist x.1 y'.1 + (dist y'.1 (torusFourInvolution y'.1)
              + dist (torusFourInvolution y'.1) (torusFourInvolution x.1)) := by
            gcongr; exact dist_triangle _ _ _
    have hiso : dist (torusFourInvolution y'.1) (torusFourInvolution x.1) = dist y'.1 x.1 :=
      torusFourInvolution_dist _ _
    have hup : dist y'.1 (torusFourInvolution y'.1) ≤ dist y'.1 x.1 + dist x.1 y.1 := by
      rw [hyval]; exact dist_triangle _ _ _
    rw [dist_comm x.1 y'.1] at hlow
    rw [dist_comm x.1 y.1] at hup
    rw [hiso] at hlow
    rw [hs] at hyd hy'd
    linarith

/-- **The separating-ball-restricted quotient map is an open embedding** — continuous + injective +
open (the interior descent engine; the `isOpenEmbedding_mk_hemi` analogue). -/
theorem isOpenEmbedding_qmk_sepBall (x : ↥puncturedTorus) :
    Topology.IsOpenEmbedding
      (fun y : ↥(Metric.ball x (sepRadius x)) =>
        Quotient.mk (MulAction.orbitRel ℤˣ (↥puncturedTorus)) y.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (qmk_injOn_sepBall x a.2 b.2 hab)
  · exact isOpenMap_qmk.comp (Metric.isOpen_ball.isOpenMap_subtype_val)

/-- **Fiber characterization** — the fibers of `qmk` are exactly the free `ℤ/2`-orbits `{x, τx}`:
`qmk x = qmk x' ↔ x = x' ∨ x = τ x'`. The structural fact that `Q` is the free 2-to-1 quotient. -/
theorem qmk_eq_iff (x x' : ↥puncturedTorus) :
    qmk x = qmk x' ↔ x = x' ∨ x = (-1 : ℤˣ) • x' := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ : x ∈ MulAction.orbit ℤˣ x' := Quotient.eq''.mp h
    have hu' : u • x' = x := hu
    rcases Int.units_eq_one_or u with h1 | h1
    · left; rw [h1, one_smul] at hu'; exact hu'.symm
    · right; rw [h1] at hu'; exact hu'.symm
  · rintro (rfl | rfl)
    · rfl
    · exact qmk_neg_one_smul x'

/-! ## §4. The boundary `∂Q = 16 × ℝP³` — the S³/±1 antipodal presentation (Design Risk #2)

The 16 boundary 3-spheres `∂B_i = sphere c (1/2)` (`c ∈ Fix(τ) = {±1}⁴`) are `τ`-invariant with `τ`
free on each (`KummerPuncturedTorus`), so their `qmk`-images are the antipodal quotients
`S³/±1 = ℝP³` (Design Risk #2 — the pinned presentation K6′a's `∂E ≅ ℝP³` welds against). The 16
components are pairwise disjoint (the fixed points are `≥ 2` apart, the spheres `≤ 1` across). -/

/-- The `i`-th **boundary 3-sphere** inside `T⁴°`: `∂B_i = {x | dist(x, c) = 1/2}` (`c` a fixed
point). Lies in `T⁴°` and is `τ`-invariant (`KummerPuncturedTorus`). -/
def boundarySphere (c : TorusFour) : Set (↥puncturedTorus) :=
  {x : ↥puncturedTorus | dist x.1 c = excisionRadius}

/-- The `i`-th **boundary component of `Q`**: `qmk '' ∂B_i` — the 3-sphere's antipodal quotient
`S³/±1 = ℝP³`, the pinned boundary presentation (Design Risk #2). -/
noncomputable def boundaryComponent (c : TorusFour) : Set FreeQuotient :=
  qmk '' boundarySphere c

/-- **The whole boundary `∂Q`** — the union of the 16 components (indexed by `Fix(τ) = {±1}⁴`). -/
noncomputable def boundaryQ : Set FreeQuotient := ⋃ c ∈ fixedSet, boundaryComponent c

/-- **`τ`-invariance of a boundary 3-sphere** at a fixed centre: `τ x ∈ ∂B_i ↔ x ∈ ∂B_i`. -/
theorem boundarySphere_smul_mem {c : TorusFour} (hc : torusFourInvolution c = c)
    (x : ↥puncturedTorus) : (-1 : ℤˣ) • x ∈ boundarySphere c ↔ x ∈ boundarySphere c := by
  simp only [boundarySphere, Set.mem_setOf_eq, neg_one_smul_val, dist_involution_fixed hc]

/-- **The S³/±1 antipodal presentation (Design Risk #2)**: on each boundary 3-sphere `∂B_i`
(`c ∈ Fix(τ)`), the antipode `τ x` also lies on `∂B_i`, is DISTINCT from `x` (freeness), and is
GLUED to `x` in `Q`. So `qmk` restricts to the free 2-to-1 antipodal quotient `∂B_i ↠ ℝP³ =
S³/±1` — the pinned presentation the resolution bundle `E` welds against. -/
theorem boundaryComponent_antipodal {c : TorusFour} (hc : torusFourInvolution c = c)
    (x : ↥puncturedTorus) (hx : x ∈ boundarySphere c) :
    (-1 : ℤˣ) • x ∈ boundarySphere c ∧ (-1 : ℤˣ) • x ≠ x ∧ qmk ((-1 : ℤˣ) • x) = qmk x :=
  ⟨(boundarySphere_smul_mem hc x).mpr hx, neg_one_smul_ne x, qmk_neg_one_smul x⟩

/-- **The 16 boundary components are pairwise disjoint** — the fixed points `{±1}⁴` are `≥ 2` apart
(`fixedSet_dist_ge`) while the boundary spheres are `≤ 1` in diameter across a shared image point.
So `∂Q` is genuinely `16 ×` disjoint copies of `ℝP³`, not fewer. -/
theorem boundaryComponent_disjoint {c1 c2 : TorusFour} (h1 : c1 ∈ fixedSet) (h2 : c2 ∈ fixedSet)
    (hne : c1 ≠ c2) : Disjoint (boundaryComponent c1) (boundaryComponent c2) := by
  rw [Set.disjoint_left]
  rintro z ⟨x1, hx1, rfl⟩ ⟨x2, hx2, hz⟩
  have hr1 : dist x1.1 c1 = excisionRadius := hx1
  have hr2 : dist x2.1 c2 = excisionRadius := hx2
  have hsep : (2 : ℝ) ≤ dist c1 c2 := fixedSet_dist_ge h1 h2 hne
  have hx1c2 : dist x1.1 c2 = excisionRadius := by
    rcases (qmk_eq_iff x2 x1).mp hz with rfl | hτ
    · exact hr2
    · rw [hτ, neg_one_smul_val, dist_involution_fixed h2] at hr2; exact hr2
  have htri : dist c1 c2 ≤ dist c1 x1.1 + dist x1.1 c2 := dist_triangle c1 x1.1 c2
  rw [dist_comm c1 x1.1, hr1, hx1c2, show excisionRadius = (1 : ℝ) / 2 from rfl] at htri
  linarith

/-- `∂Q` re-indexed over the explicit 16-element `Finset` of fixed points. -/
theorem boundaryQ_eq_biUnion_fixedFinset :
    boundaryQ = ⋃ c ∈ fixedFinset, boundaryComponent c := by
  ext z
  simp only [boundaryQ, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, hz⟩; exact ⟨c, (mem_fixedFinset c).mpr hc, hz⟩
  · rintro ⟨c, hc, hz⟩; exact ⟨c, (mem_fixedFinset c).mp hc, hz⟩

/-- **The `16` of `∂Q = 16 × ℝP³`**: the boundary components are indexed by the 16-element fixed
`Finset` (`fixedFinset_card`). -/
theorem boundaryQ_component_count : fixedFinset.card = 16 := fixedFinset_card

end SKEFTHawking.KummerFreeQuotient
