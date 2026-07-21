/-
# Phase 5q.H — K6′b Leg 7: THE SEAM DOUBLE COLLAR — `ℝP³ × [−1/8, 1/2] ↪ K3`

The glue. Legs 5 and 6 built the two halves of the seam collar as explicit products over the SAME
`ℝP³` factor:

* `KummerSeamCollarE.eCollarHomeo : ℝP³ × [1/2, 1] ≃ₜ {x : E ∣ 1/2 ≤ fiberNorm x}` (E side, radial
  parameter = fiber radius, `t = 1` face = `bdryMapRP3`);
* `KummerSeamCollarQ.qCollarHomeo : ℝP³ × [1/2, 5/8] ≃ₜ qCollarSet c` (Q side, radial parameter =
  chart radius, `s = 1/2` face = `qBdryMap c`).

This module welds them into ONE collar of the seam **inside `K3`**, on the signed parameter

    v ∈ [−1/8, 1/2],   v ≥ 0 ↦ the E side at fiber radius `1 − v`,
                       v ≤ 0 ↦ the Q side at chart radius `1/2 − v`,

so that `v = 0` is the seam itself — and the two branches AGREE there precisely because the weld
identifies `qBdryMap c r` with `bdryMapRP3 r` (`KummerWeld.weldMk_seam`). That single identity is
what makes the piecewise map continuous (`Continuous.if_le`), and it is the set-level shadow of the
smooth compatibility `KummerSeamSmooth.contMDiff_bdryMapRP3`.

**The result (§3).** `dblCollarHomeo c : ℝP³ × [−1/8, 1/2] ≃ₜ range (dblCollar c)` — the seam
component `∂Q_c = ∂E_c` sits inside `K3` with a genuine **two-sided** collar, crossing from the `Q`
piece into the `E` piece. `dblCollar_mem_seamComponent_iff` pins that the collar meets the seam
EXACTLY in its `v = 0` slice, so the collar is transverse, not tangential: the former boundary is an
interior hypersurface of the welded carrier. That is the set-theoretic content of "the 16-fold weld
closes both boundaries".

**Residual (sharply named).** Chart family 3/3 needs, beyond this collar, (i) that the collar's
interior `v ∈ (−1/8, 1/2)` is OPEN in `K3` — the saturation argument of `KummerWeldOpenPieces` /
`KummerWeldQInterior` run on a set that straddles the seam — and (ii) the transport of the `ℝP³`
atlas (`KummerRP3Smooth.isManifold_rp3`) across it into `𝓡 4`, together with the transition classes
against chart families 1 and 2. Neither is built here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamCollarQ

namespace SKEFTHawking.KummerSeamDoubleCollar

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamCollarE (eCollar continuous_eCollar fiberNorm_eCollar eCollar_one
  eCollar_injOn)
open SKEFTHawking.KummerSeamCollarQ (qParam qCollar continuous_qCollar qCollar_half
  qCollar_injective)

noncomputable section

open scoped Classical

/-! ## §1. The signed collar parameter and the two clamped branches -/

/-- **The signed double-collar parameter** `v ∈ [−1/8, 1/2]`: `v ≥ 0` is the `E` side (fiber radius
`1 − v`), `v ≤ 0` is the `Q` side (chart radius `1/2 − v`), `v = 0` is the seam. -/
def dblParam : Set ℝ := Set.Icc (-(1 / 8) : ℝ) (1 / 2)

instance instCompactSpaceDblParam : CompactSpace ↥dblParam :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- The E-branch radial parameter `1 − max v 0` — clamped so it is total on `dblParam` and equals
`1` (the seam) on the whole `Q` half. -/
def clampE (v : ↥dblParam) : unitInterval :=
  ⟨1 - max (v : ℝ) 0, by
    constructor
    · have h : max (v : ℝ) 0 ≤ 1 / 2 := max_le v.2.2 (by norm_num)
      linarith
    · have h : (0 : ℝ) ≤ max (v : ℝ) 0 := le_max_right _ _
      linarith⟩

/-- The Q-branch radial parameter `1/2 − min v 0` — clamped so it is total on `dblParam` and equals
`1/2` (the seam) on the whole `E` half. -/
def clampQ (v : ↥dblParam) : ↥qParam :=
  ⟨1 / 2 - min (v : ℝ) 0, by
    constructor
    · have h : min (v : ℝ) 0 ≤ 0 := min_le_right _ _
      show 1 / 2 ≤ 1 / 2 - min (v : ℝ) 0; linarith
    · have h : -(1 / 8 : ℝ) ≤ min (v : ℝ) 0 := le_min v.2.1 (by norm_num)
      show 1 / 2 - min (v : ℝ) 0 ≤ 5 / 8; linarith⟩

@[simp] theorem clampE_coe (v : ↥dblParam) : (clampE v : ℝ) = 1 - max (v : ℝ) 0 := rfl

@[simp] theorem clampQ_coe (v : ↥dblParam) : (clampQ v : ℝ) = 1 / 2 - min (v : ℝ) 0 := rfl

theorem continuous_clampE : Continuous clampE :=
  Continuous.subtype_mk (continuous_const.sub (continuous_subtype_val.max continuous_const)) _

theorem continuous_clampQ : Continuous clampQ :=
  Continuous.subtype_mk (continuous_const.sub (continuous_subtype_val.min continuous_const)) _

/-- The E-side branch of the double collar. -/
def eBranch (c : EIndex) (p : RP3 × ↥dblParam) : KummerK3 :=
  weldMk (Sum.inr (c, eCollar (p.1, clampE p.2)))

/-- The Q-side branch of the double collar. -/
def qBranch (c : EIndex) (p : RP3 × ↥dblParam) : KummerK3 :=
  weldMk (Sum.inl (qCollar c (p.1, clampQ p.2)))

theorem continuous_eBranch (c : EIndex) : Continuous (eBranch c) :=
  continuous_weldMk.comp (continuous_inr.comp (continuous_const.prodMk
    (continuous_eCollar.comp (continuous_fst.prodMk (continuous_clampE.comp continuous_snd)))))

theorem continuous_qBranch (c : EIndex) : Continuous (qBranch c) :=
  continuous_weldMk.comp (continuous_inl.comp
    ((continuous_qCollar c).comp (continuous_fst.prodMk (continuous_clampQ.comp continuous_snd))))

/-- **The two branches agree on the seam slice** — this is exactly `weldMk_seam`, the 16-fold weld
identity `qBdryMap c r ~ bdryMapRP3 r`. It is the single fact that makes the piecewise collar
continuous, and it is the set-level shadow of `KummerSeamSmooth.contMDiff_bdryMapRP3`. -/
theorem eBranch_eq_qBranch_of_zero (c : EIndex) {p : RP3 × ↥dblParam} (h : (0 : ℝ) = (p.2 : ℝ)) :
    eBranch c p = qBranch c p := by
  have hE : clampE p.2 = 1 := by
    apply Subtype.ext
    rw [clampE_coe, ← h]
    show 1 - max (0 : ℝ) 0 = 1
    rw [max_self]; ring
  have hQ : (clampQ p.2 : ℝ) = 1 / 2 := by
    rw [clampQ_coe, ← h]
    show 1 / 2 - min (0 : ℝ) 0 = 1 / 2
    rw [min_self]; ring
  have hQ' : clampQ p.2 = ⟨1 / 2, by constructor <;> norm_num⟩ := Subtype.ext hQ
  rw [eBranch, qBranch, hE, hQ', eCollar_one, qCollar_half]
  exact (weldMk_seam c p.1).symm

/-! ## §2. The double collar map -/

/-- **THE SEAM DOUBLE COLLAR MAP** `ℝP³ × [−1/8, 1/2] → K3`: the `E` collar for `v ≥ 0`, the `Q`
collar for `v ≤ 0`, glued along the weld at `v = 0`. -/
def dblCollar (c : EIndex) (p : RP3 × ↥dblParam) : KummerK3 :=
  if (0 : ℝ) ≤ ((p.2 : ℝ)) then eBranch c p else qBranch c p

theorem continuous_dblCollar (c : EIndex) : Continuous (dblCollar c) :=
  Continuous.if_le (continuous_eBranch c) (continuous_qBranch c) continuous_const
    (continuous_subtype_val.comp continuous_snd) (fun _ h => eBranch_eq_qBranch_of_zero c h)

theorem dblCollar_of_nonneg (c : EIndex) {p : RP3 × ↥dblParam} (h : (0 : ℝ) ≤ (p.2 : ℝ)) :
    dblCollar c p = eBranch c p := if_pos h

theorem dblCollar_of_neg (c : EIndex) {p : RP3 × ↥dblParam} (h : ¬ (0 : ℝ) ≤ (p.2 : ℝ)) :
    dblCollar c p = qBranch c p := if_neg h

/-- **The `v = 0` slice of the double collar is the seam** — `dblCollar c (r, 0) = the seam point of
`r` in the `c`-th copy. -/
@[simp] theorem dblCollar_zero (c : EIndex) (r : RP3) :
    dblCollar c (r, ⟨0, by constructor <;> norm_num⟩) = weldMk (Sum.inr (c, bdryMapRP3 r)) := by
  rw [dblCollar_of_nonneg c (le_refl (0 : ℝ))]
  have hE : clampE (⟨0, by constructor <;> norm_num⟩ : ↥dblParam) = 1 := by
    apply Subtype.ext
    show 1 - max (0 : ℝ) 0 = 1
    rw [max_self]; ring
  show weldMk (Sum.inr (c, eCollar (r, clampE ⟨0, _⟩))) = _
  rw [hE, eCollar_one]

/-- **The E-branch fiber radius** — `1 − v` on the `E` half. -/
theorem fiberNorm_eBranch_arg (p : RP3 × ↥dblParam) (h : (0 : ℝ) ≤ (p.2 : ℝ)) :
    fiberNorm (eCollar (p.1, clampE p.2)) = 1 - (p.2 : ℝ) := by
  rw [fiberNorm_eCollar, clampE_coe, max_eq_left h]

/-! ## §3. The double collar is injective — the seam is TWO-SIDED in `K3` -/

/-- **THE SEAM DOUBLE COLLAR IS INJECTIVE.** Both same-side cases reduce to the corresponding
half-collar injectivity (`eCollar_injOn` / `qCollar_injective`) through the piece embeddings
(`weldMk_inr_injective` / `weldMk_inl_injective`). The cross-side case is the interesting one: a
`Q`-side point and an `E`-side point can only be welded *on the seam*, which forces both parameters
to be `0` — impossible when one of them is strictly negative. So the collar genuinely crosses from
one piece to the other, meeting each side only in its own half. -/
theorem dblCollar_injective (c : EIndex) : Function.Injective (dblCollar c) := by
  have hEE : ∀ p q : RP3 × ↥dblParam, (0 : ℝ) ≤ (p.2 : ℝ) → (0 : ℝ) ≤ (q.2 : ℝ) →
      eBranch c p = eBranch c q → p = q := by
    intro p q hp hq h
    have h' : eCollar (p.1, clampE p.2) = eCollar (q.1, clampE q.2) :=
      congrArg Prod.snd (weldMk_inr_injective h)
    have hne : ((clampE p.2 : unitInterval) : ℝ) ≠ 0 := by
      rw [clampE_coe, max_eq_left hp]
      have := p.2.2.2; intro hc; linarith
    have hpair := eCollar_injOn (p := (p.1, clampE p.2)) (q := (q.1, clampE q.2)) hne h'
    have h1 : p.1 = q.1 := (Prod.ext_iff.mp hpair).1
    have h2 : (clampE p.2 : ℝ) = (clampE q.2 : ℝ) :=
      congrArg (fun t : unitInterval => (t : ℝ)) (Prod.ext_iff.mp hpair).2
    rw [clampE_coe, clampE_coe, max_eq_left hp, max_eq_left hq] at h2
    exact Prod.ext h1 (Subtype.ext (by linarith))
  have hQQ : ∀ p q : RP3 × ↥dblParam, ¬ (0 : ℝ) ≤ (p.2 : ℝ) → ¬ (0 : ℝ) ≤ (q.2 : ℝ) →
      qBranch c p = qBranch c q → p = q := by
    intro p q hp hq h
    have h' : qCollar c (p.1, clampQ p.2) = qCollar c (q.1, clampQ q.2) := weldMk_inl_injective h
    have hpair := qCollar_injective c h'
    have h1 : p.1 = q.1 := (Prod.ext_iff.mp hpair).1
    have h2 : (clampQ p.2 : ℝ) = (clampQ q.2 : ℝ) :=
      congrArg (fun t : ↥qParam => (t : ℝ)) (Prod.ext_iff.mp hpair).2
    rw [clampQ_coe, clampQ_coe, min_eq_left (le_of_not_ge hp), min_eq_left (le_of_not_ge hq)] at h2
    exact Prod.ext h1 (Subtype.ext (by linarith))
  -- the cross-side case: the weld forces both parameters to vanish
  have hcross : ∀ p q : RP3 × ↥dblParam, (0 : ℝ) ≤ (p.2 : ℝ) → ¬ (0 : ℝ) ≤ (q.2 : ℝ) →
      eBranch c p ≠ qBranch c q := by
    intro p q _ hq h
    rcases Quotient.exact h with he | ⟨c₀, r₀, h1, _⟩ | ⟨c₀, r₀, h1, h2⟩
    · exact absurd he (by simp)
    · exact absurd h1 (by simp)
    · -- `h1 : inl (qCollar c (q.1, clampQ q.2)) = inl (qBdryMap c₀ r₀)`
      have hq1 : qCollar c (q.1, clampQ q.2) = qBdryMap c₀ r₀ := Sum.inl.inj h1
      have hc0 : c = c₀ := congrArg Prod.fst (Sum.inr.inj h2)
      subst hc0
      rw [← qCollar_half c r₀] at hq1
      have hpair := qCollar_injective c hq1
      have h2' : (clampQ q.2 : ℝ) = 1 / 2 :=
        congrArg (fun t : ↥qParam => (t : ℝ)) (Prod.ext_iff.mp hpair).2
      rw [clampQ_coe, min_eq_left (le_of_not_ge hq)] at h2'
      exact hq (by linarith)
  intro p q h
  by_cases hp : (0 : ℝ) ≤ (p.2 : ℝ) <;> by_cases hq : (0 : ℝ) ≤ (q.2 : ℝ)
  · exact hEE p q hp hq (by rwa [dblCollar_of_nonneg c hp, dblCollar_of_nonneg c hq] at h)
  · exact absurd (by rwa [dblCollar_of_nonneg c hp, dblCollar_of_neg c hq] at h) (hcross p q hp hq)
  · refine absurd ?_ (hcross q p hq hp)
    rw [dblCollar_of_neg c hp, dblCollar_of_nonneg c hq] at h
    exact h.symm
  · exact hQQ p q hp hq (by rwa [dblCollar_of_neg c hp, dblCollar_of_neg c hq] at h)

/-! ## §4. The collar homeomorphism and the transversality pin -/

/-- The double collar map onto its range. -/
def dblCollarRestrict (c : EIndex) (p : RP3 × ↥dblParam) : ↥(Set.range (dblCollar c)) :=
  ⟨dblCollar c p, Set.mem_range_self p⟩

theorem continuous_dblCollarRestrict (c : EIndex) : Continuous (dblCollarRestrict c) :=
  Continuous.subtype_mk (continuous_dblCollar c) _

theorem bijective_dblCollarRestrict (c : EIndex) : Function.Bijective (dblCollarRestrict c) :=
  ⟨fun _ _ h => dblCollar_injective c (congrArg Subtype.val h),
   fun y => by obtain ⟨p, hp⟩ := y.2; exact ⟨p, Subtype.ext hp⟩⟩

/-- **THE SEAM HAS A TWO-SIDED COLLAR IN `K3`**: `ℝP³ × [−1/8, 1/2] ≃ₜ` a neighbourhood-sized
subspace of the welded carrier containing the `c`-th seam component, with the `Q` piece on one side
of `v = 0` and the `E` piece on the other. Continuous bijection from a compact space to the
Hausdorff `K3` (`KummerWeld.instT2SpaceKummerK3`).

This is the topological form of chart family 3/3 — the double collar the smooth seam chart is built
on, and the reason the welded `K3` is boundaryless where the two pieces used to end. -/
def dblCollarHomeo (c : EIndex) : (RP3 × ↥dblParam) ≃ₜ ↥(Set.range (dblCollar c)) :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (bijective_dblCollarRestrict c))
    (continuous_dblCollarRestrict c)

/-- **The `c`-th seam component sits inside the collar.** -/
theorem seamComponent_subset_range (c : EIndex) :
    Set.range (fun r : RP3 => weldMk (Sum.inr (c, bdryMapRP3 r))) ⊆ Set.range (dblCollar c) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨(r, ⟨0, by constructor <;> norm_num⟩), dblCollar_zero c r⟩

/-- **TRANSVERSALITY PIN — the collar meets the seam EXACTLY in its `v = 0` slice.** So the collar
is not tangential to the seam: every `v ≠ 0` collar point is off the seam, on one definite side.
Together with `dblCollarHomeo` this says the seam is a two-sided hypersurface of `K3`, which is the
set-level content of "the 16-fold weld closes both boundaries". -/
theorem dblCollar_mem_seamComponent_iff (c : EIndex) (p : RP3 × ↥dblParam) :
    dblCollar c p ∈ Set.range (fun r : RP3 => weldMk (Sum.inr (c, bdryMapRP3 r)))
      ↔ (p.2 : ℝ) = 0 := by
  constructor
  · rintro ⟨r₀, hr₀⟩
    have h : dblCollar c p = dblCollar c (r₀, ⟨0, by constructor <;> norm_num⟩) := by
      rw [dblCollar_zero]; exact hr₀.symm
    have := dblCollar_injective c h
    exact congrArg (fun q : RP3 × ↥dblParam => (q.2 : ℝ)) this
  · intro h
    have hp : p = (p.1, ⟨0, by constructor <;> norm_num⟩) :=
      Prod.ext rfl (Subtype.ext h)
    rw [hp, dblCollar_zero]
    exact Set.mem_range_self p.1

end

end SKEFTHawking.KummerSeamDoubleCollar
