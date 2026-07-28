import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import SKEFTHawking.GrapheneNoiseFormula

/-!
# Phase 6EB Wave 1 — ENBW and the matched-boxcar realizability floor

**Publication target: bundle D12** (*Kernel-Verified Detector & Readout Metrology*).

Between the detection statistics of Phase 6EA and any physical detector sits the
*signal-processing layer*: a linear filter of equivalent noise bandwidth (ENBW) integrating
over a single-shot window `[0, T]`. This file builds that layer's first exact floor.

## The result

For any filter `h` that is interval-integrable on `[0,T]` together with its square, and whose
**DC gain** `∫₀ᵀ h` is non-zero,

    ENBW(h) · T ≥ 1/2                    (`enbw_mul_window_ge_half`)

with equality **iff** `h` is almost-everywhere a scalar multiple of the boxcar on the window
(`enbw_eq_half_iff_boxcar`), and the boxcar attaining it exactly (`enbw_boxcar`). The two
combine into the sharp form: `1/2` is the *least* attainable value of `ENBW · T`
(`enbw_mul_window_isLeast`) — so the floor is tight, not merely true.

## Convention — ONE-SIDED, and it is carried in the statements

The repo's PSD convention is fixed by `SKEFTHawking.GrapheneNoiseFormula`:
`johnsonNyquistPSD kB_T σ_Q = 4·kB_T·σ_Q` and
`hawkingNoisePSD ℏω σ_Q Γ n_H = 2·ℏω·σ_Q·Γ·n_H` — both **one-sided** forms (a two-sided
convention halves each). Phase 6EA Wave 3 inherits the same convention, and so does this file.

The matching one-sided ENBW normalization puts a `2` in the denominator:

    ENBW(h) := (∫₀ᵀ h²) / (2 · (∫₀ᵀ h)²)

and that factor is **numerically load-bearing, not cosmetic**. Five statements below carry the
convention rather than merely documenting it:

* `enbw_boxcar` — the boxcar's ENBW is `1/(2T)`; the two-sided convention would give `1/T`.
* `enbw_mul_window_ge_half` — the floor constant is `1/2`; two-sided it would be `1`.
* `enbw_oneSided_ne_twoSided` — the two normalizations **provably disagree** at every `T > 0`,
  so a convention-ambiguous downstream statement is detectably wrong, not just differently
  phrased (roadmap guardrail: "a convention-ambiguous theorem is a defect").
* `variance_eq_psd_mul_enbw` — the definitional raison d'être: a *white* source of **one-sided**
  PSD `S₀` produces DC-normalized output variance `S₀ · ENBW(h)` (no stray factor of 2).
* `johnsonNyquist_filteredVariance_floor` — the composed physical floor
  `σ² ≥ 2·kB_T·σ_Q/T`, whose `2` is `4 × (1/2)`: the one-sided Johnson–Nyquist PSD
  `4·kB_T·σ_Q` times the one-sided minimum bandwidth `1/(2T)`. Note the *product*
  `S₀ · ENBW` is convention-invariant (as a physical variance must be) — which is precisely
  why the two factors must be taken in the **same** convention: pairing a one-sided PSD with a
  two-sided ENBW (or vice versa) is a silent factor-of-2 error in either direction.

The `(∫₀ᵀ h)²` denominator is the **normalized-DC-gain** convention: ENBW is a property of the
filter *shape*, not of its gain. `enbw_const_mul` proves exactly that (invariance under
`h ↦ c·h` for `c ≠ 0`), which is what licenses stating floors without a normalization
hypothesis on `h`.

## Two-layer honesty

The *mathematics* here (an interval-form Cauchy–Schwarz with its equality case, and the
resulting bandwidth floor) is Lean-verified. The identification of a physical instrument's
impulse response with an admissible `h`, and of a physical noise source with the whiteness
hypothesis `IsWhiteFilteredVariance`, is the **consumer's declared hypothesis** — never
smuggled into these statements. No claim is made about any instrument's implementation.

## Non-vacuity

* The floor is **attained** (`enbw_boxcar`, `enbw_mul_window_isLeast`) — it is not a loose
  bound.
* The floor is **not an equality in disguise**: a linear-ramp weighting on `[0,1]` has
  `ENBW·T = 2/3 > 1/2` (`enbw_ramp_gt_half`), so the bound is a genuine screen with slack.
* The `∫₀ᵀ h ≠ 0` hypothesis is **load-bearing and non-droppable**: an integrable filter with
  zero DC gain satisfies every other hypothesis and *violates* the conclusion
  (`enbw_dcGain_hypothesis_load_bearing`), because Lean's total division sends the undefined
  ratio to `0` (`enbw_of_dcGain_eq_zero`). Physically a zero-DC-gain filter has no signal path,
  so it has no equivalent noise bandwidth at all.

## Route note (UNKNOWN-1 of `docs/roadmaps/Phase6EB_Roadmap.md`, resolved here)

The roadmap posed the Cauchy–Schwarz brick as a choice between `norm_inner_le_norm` (the L² inner-product route) on
`L²(volume.restrict (Set.Icc 0 T))` and `MeasureTheory.integral_mul_le_Lp_mul_Lq`. Neither is
used. The bound `(∫₀ᵀ h)² ≤ T·∫₀ᵀ h²` is proved from **non-negativity of a variance**: with
`c := (∫₀ᵀ h)/T`,

    0 ≤ ∫₀ᵀ (h − c)² = ∫₀ᵀ h² − 2c·∫₀ᵀ h + c²·T = ∫₀ᵀ h² − (∫₀ᵀ h)²/T,

which needs only `intervalIntegral.integral_nonneg`, linearity, and the stated integrability —
no Hölder, no `rpow`, no L² inner-product structure, no `MemLp` plumbing. The same expansion
(`integral_sub_const_sq`) *also* delivers the equality case for free: `ENBW·T = 1/2` iff that
variance integral vanishes iff `h` is a.e. constant on the window.

## References

- `docs/roadmaps/Phase6EB_Roadmap.md` — Wave 1 acceptance criteria.
- `docs/dev-loops/Phase6EA/Phase6EA_Wave3_StatementFreeze.md` §1 — the frozen PSD convention.
- `SKEFTHawking.GrapheneNoiseFormula` — the convention anchor, consumed by
  `johnsonNyquist_filteredVariance_floor`.
-/

namespace SKEFTHawking.Detection

open MeasureTheory

/-! ## Definitions -/

/-- **One-sided equivalent noise bandwidth of an interval-supported filter.**

    `ENBW(h) = (∫₀ᵀ h²) / (2 · (∫₀ᵀ h)²)`

The denominator carries **both** conventions of this file simultaneously:

* the factor `2` is the **one-sided** normalization, matching
  `GrapheneNoiseFormula.johnsonNyquistPSD = 4·kB_T·σ_Q` and
  `GrapheneNoiseFormula.hawkingNoisePSD`'s leading `2` (a two-sided convention drops it);
* the `(∫₀ᵀ h)²` is the **normalized-DC-gain** convention — `|H(0)|²` for the filter's transfer
  function — which makes `enbw` a function of the filter *shape* only (`enbw_const_mul`).

Physically: white noise of one-sided PSD `S₀` filtered by `h` and referred back to the filter's
DC gain has output variance exactly `S₀ · ENBW(h)` (`variance_eq_psd_mul_enbw`).

**Degenerate branch, disclosed.** When `∫₀ᵀ h = 0` the ratio is undefined and Lean's total
division returns `0` (`enbw_of_dcGain_eq_zero`). Every floor below therefore carries the DC-gain
hypothesis explicitly; it is not removable (`enbw_dcGain_hypothesis_load_bearing`). -/
noncomputable def enbw (h : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ x in (0:ℝ)..T, h x ^ 2) / (2 * (∫ x in (0:ℝ)..T, h x) ^ 2)

/-- **The unit boxcar (matched single-shot integrator) on `[0, T]`.** Genuinely
interval-supported: it is the indicator of `Set.Icc 0 T`, so it vanishes outside the window
rather than being the constant `1` in disguise. This is the filter that saturates the
realizability floor (`enbw_boxcar`, `enbw_mul_window_isLeast`). -/
noncomputable def boxcar (T : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc 0 T) (fun _ => (1 : ℝ))

/-! ## The variance identity and the interval Cauchy–Schwarz bound -/

/-- **The variance expansion** — the single engine behind both the floor and its equality case.

    ∫₀ᵀ (h − c)² = ∫₀ᵀ h² − 2c·∫₀ᵀ h + c²·T

Elementary linearity of the interval integral, but stated separately because *both*
`sq_integral_le` (via non-negativity of the left side) and `enbw_eq_half_iff_boxcar` (via
vanishing of the left side) consume it. -/
theorem integral_sub_const_sq (h : ℝ → ℝ) (T c : ℝ)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T) :
    (∫ x in (0:ℝ)..T, (h x - c) ^ 2)
      = (∫ x in (0:ℝ)..T, h x ^ 2) - 2 * c * (∫ x in (0:ℝ)..T, h x) + c ^ 2 * T := by
  have e1 : (fun x => (h x - c) ^ 2) = fun x => (h x ^ 2 - 2 * c * h x) + c ^ 2 := by
    funext x; ring
  have hi1 : IntervalIntegrable (fun x => h x ^ 2 - 2 * c * h x) volume 0 T :=
    hsq.sub (hint.const_mul _)
  have hi2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 T := intervalIntegrable_const
  rw [e1, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_sub hsq (hint.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp [mul_comm]

/-- **Cauchy–Schwarz on the window, in the form the floor needs:** `(∫₀ᵀ h)² ≤ T · ∫₀ᵀ h²`.

This is the continuous analogue of Mathlib's `sq_sum_le_card_mul_sum_sq`
(`Mathlib.Algebra.Order.Chebyshev`); Mathlib carries the discrete form and the abstract `L²`
inner-product form, but not this interval-integral shape.
Proved from non-negativity of `∫₀ᵀ (h − c)²` at `c = (∫₀ᵀ h)/T` — no Hölder, no `rpow`, no
`MemLp`. See the module docstring's route note (UNKNOWN-1). -/
theorem sq_integral_le (h : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T) :
    (∫ x in (0:ℝ)..T, h x) ^ 2 ≤ T * ∫ x in (0:ℝ)..T, h x ^ 2 := by
  set I := ∫ x in (0:ℝ)..T, h x with hI
  have h0 : 0 ≤ ∫ x in (0:ℝ)..T, (h x - I / T) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun u _ => sq_nonneg _)
  rw [integral_sub_const_sq h T (I / T) hint hsq] at h0
  have hTne : T ≠ 0 := ne_of_gt hT
  have e1 : 2 * (I / T) * I = 2 * (I ^ 2 / T) := by field_simp
  have e2 : (I / T) ^ 2 * T = I ^ 2 / T := by field_simp
  rw [e1, e2] at h0
  have hkey : I ^ 2 / T ≤ ∫ x in (0:ℝ)..T, h x ^ 2 := by linarith
  have hfin := (div_le_iff₀ hT).mp hkey
  linarith [hfin]

/-! ## The single-shot realizability floor -/

/-- **THE FLOOR — `ENBW · T ≥ 1/2` for any admissible single-shot filter.**

No linear filter integrating over a window of length `T` can have a one-sided equivalent noise
bandwidth below `1/(2T)`. Any claimed noise bandwidth below that in a single-shot measurement is
unphysical — this is the hand-checkable screen the phase exists to provide.

**Hypotheses are all load-bearing.** `hT : 0 < T` (a zero-length window integrates nothing);
`hint`/`hsq` (the filter and its square must actually be integrable on the window — the
physical filter class); and critically `hDC : ∫₀ᵀ h ≠ 0`, whose non-droppability is witnessed
by `enbw_dcGain_hypothesis_load_bearing`.

**Non-vacuous and tight.** The constant `1/2` is attained (`enbw_boxcar`) and is the *least*
attainable value (`enbw_mul_window_isLeast`); it is not tight for every filter
(`enbw_ramp_gt_half`). The constant is convention-pinned: under a two-sided PSD normalization
the same theorem would read `≥ 1`. -/
theorem enbw_mul_window_ge_half (h : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    1 / 2 ≤ enbw h T * T := by
  have hpos : 0 < (∫ x in (0:ℝ)..T, h x) ^ 2 := by positivity
  have hle := sq_integral_le h T hT hint hsq
  unfold enbw
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hle]

/-- **The equality case: the floor is saturated exactly by the boxcar (a.e.).**

`ENBW(h)·T = 1/2` **iff** `h` agrees almost everywhere on the window with the scaled boxcar
whose level is `h`'s own DC average `(∫₀ᵀ h)/T`. In words: the matched single-shot integrator
is the *unique* (up to a.e. equality and gain) minimizer, which is what makes the floor a
characterization rather than an inequality.

Routed through the same variance integral as the floor: equality holds iff
`∫₀ᵀ (h − c)² = 0`, which by `intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae` forces
`h =ᵐ c`. (A Hölder route would have had to reconstruct the equality case separately.) -/
theorem enbw_eq_half_iff_boxcar (h : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    enbw h T * T = 1 / 2 ↔
      h =ᵐ[volume.restrict (Set.Ioc 0 T)]
        fun x => ((∫ y in (0:ℝ)..T, h y) / T) * boxcar T x := by
  have hTne : T ≠ 0 := ne_of_gt hT
  set I := ∫ x in (0:ℝ)..T, h x with hI
  set A := ∫ x in (0:ℝ)..T, h x ^ 2 with hA
  have hIpos : 0 < I ^ 2 := by positivity
  have hvar : (∫ x in (0:ℝ)..T, (h x - I / T) ^ 2) = A - I ^ 2 / T := by
    rw [integral_sub_const_sq h T (I / T) hint hsq]; field_simp; ring
  have hsub : IntervalIntegrable (fun x => (h x - I / T) ^ 2) volume 0 T := by
    have hrw : (fun x => (h x - I / T) ^ 2)
        = fun x => (h x ^ 2 - 2 * (I / T) * h x) + (I / T) ^ 2 := by funext x; ring
    rw [hrw]
    exact (hsq.sub (hint.const_mul _)).add intervalIntegrable_const
  have halg : enbw h T * T = 1 / 2 ↔ (∫ x in (0:ℝ)..T, (h x - I / T) ^ 2) = 0 := by
    rw [hvar]
    unfold enbw
    rw [← hA, ← hI, div_mul_eq_mul_div, sub_eq_zero]
    rw [div_eq_div_iff (by positivity) (two_ne_zero), eq_div_iff hTne]
    constructor <;> intro hh <;> linarith
  have hzero := intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
    (Filter.Eventually.of_forall (fun x => sq_nonneg (h x - I / T))) hsub
  have hbox : (fun x => (I / T) * boxcar T x)
      =ᵐ[volume.restrict (Set.Ioc 0 T)] fun _ => I / T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hb : boxcar T x = 1 := by
      unfold boxcar; rw [Set.indicator_of_mem (Set.Ioc_subset_Icc_self hx)]
    rw [hb, mul_one]
  rw [halg, hzero]
  constructor
  · intro hh
    refine Filter.EventuallyEq.trans ?_ hbox.symm
    filter_upwards [hh] with x hx
    have hx0 : (h x - I / T) ^ 2 = 0 := hx
    have hsq0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  · intro hh
    have hh' : h =ᵐ[volume.restrict (Set.Ioc 0 T)] fun _ => I / T := hh.trans hbox
    filter_upwards [hh'] with x hx
    simp [hx]

/-! ## The saturating witness: the boxcar -/

/-- The boxcar is identically `1` on the closed window (used to evaluate its integrals). -/
theorem boxcar_eqOn (T : ℝ) (hT : 0 ≤ T) :
    Set.EqOn (boxcar T) (fun _ => (1:ℝ)) (Set.uIcc 0 T) := by
  intro x hx
  rw [Set.uIcc_of_le hT] at hx
  exact Set.indicator_of_mem hx _

/-- The boxcar's DC gain: `∫₀ᵀ boxcar = T`. -/
theorem integral_boxcar (T : ℝ) (hT : 0 ≤ T) : (∫ x in (0:ℝ)..T, boxcar T x) = T := by
  rw [intervalIntegral.integral_congr (boxcar_eqOn T hT)]; simp

/-- The boxcar's energy: `∫₀ᵀ boxcar² = T`. -/
theorem integral_boxcar_sq (T : ℝ) (hT : 0 ≤ T) : (∫ x in (0:ℝ)..T, boxcar T x ^ 2) = T := by
  have hEq : Set.EqOn (fun x => boxcar T x ^ 2) (fun _ => (1:ℝ)) (Set.uIcc 0 T) := by
    intro x hx; simp [boxcar_eqOn T hT hx]
  rw [intervalIntegral.integral_congr hEq]; simp

/-- The boxcar is `1` on the half-open window (the integrability carrier). -/
theorem boxcar_eqOn_uIoc (T : ℝ) (hT : 0 ≤ T) :
    Set.EqOn (fun _ : ℝ => (1:ℝ)) (boxcar T) (Set.uIoc 0 T) := by
  intro x hx
  rw [Set.uIoc_of_le hT] at hx
  exact (Set.indicator_of_mem (Set.Ioc_subset_Icc_self hx) (fun _ => (1:ℝ))).symm

/-- The boxcar is an admissible filter. -/
theorem intervalIntegrable_boxcar (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (boxcar T) volume 0 T :=
  (intervalIntegrable_const (c := (1:ℝ))).congr (boxcar_eqOn_uIoc T hT)

/-- The boxcar's square is an admissible filter energy. -/
theorem intervalIntegrable_boxcar_sq (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun x => boxcar T x ^ 2) volume 0 T :=
  (intervalIntegrable_const (c := (1:ℝ))).congr
    (fun x hx => by simp [← boxcar_eqOn_uIoc T hT hx])

/-- **The saturating witness:** the matched single-shot integrator has `ENBW = 1/(2T)`, i.e. it
attains the floor `ENBW·T = 1/2` of `enbw_mul_window_ge_half` exactly.

This is not a decorative arithmetic evaluation: it is the membership half of
`enbw_mul_window_isLeast`, which is what upgrades the floor from "true" to "sharp". The value
`1/(2T)` is also the file's cleanest **convention check** — a two-sided normalization would give
`1/T` (`enbw_oneSided_ne_twoSided`). -/
theorem enbw_boxcar (T : ℝ) (hT : 0 < T) : enbw (boxcar T) T = 1 / (2 * T) := by
  unfold enbw
  rw [integral_boxcar_sq T hT.le, integral_boxcar T hT.le]
  have hTne : T ≠ 0 := ne_of_gt hT
  field_simp

/-- The set of `ENBW · T` products realizable by the admissible single-shot filter class on
`[0,T]`: interval-integrable `h` with interval-integrable square and non-zero DC gain. The class
is stated explicitly (roadmap guardrail: "bounds over admissible filter classes with the class
stated explicitly"). -/
def enbwWindowProducts (T : ℝ) : Set ℝ :=
  {y | ∃ h : ℝ → ℝ, IntervalIntegrable h volume 0 T ∧
    IntervalIntegrable (fun x => h x ^ 2) volume 0 T ∧
    (∫ x in (0:ℝ)..T, h x) ≠ 0 ∧ y = enbw h T * T}

/-- **The sharp form: `1/2` is the LEAST realizable value of `ENBW · T`.**

Strictly stronger than `enbw_mul_window_ge_half` alone: `IsLeast` asserts both that `1/2` lower-
bounds the realizable set *and* that it belongs to it. So no better constant exists — the floor
cannot be improved, and it is not an artefact of a lossy inequality. The membership half is
carried by `enbw_boxcar`, which is why that evaluation is load-bearing rather than decorative. -/
theorem enbw_mul_window_isLeast (T : ℝ) (hT : 0 < T) :
    IsLeast (enbwWindowProducts T) (1 / 2) := by
  constructor
  · refine ⟨boxcar T, intervalIntegrable_boxcar T hT.le,
      intervalIntegrable_boxcar_sq T hT.le, ?_, ?_⟩
    · rw [integral_boxcar T hT.le]; exact ne_of_gt hT
    · rw [enbw_boxcar T hT]
      field_simp
  · rintro y ⟨h, hint, hsq, hDC, rfl⟩
    exact enbw_mul_window_ge_half h T hT hint hsq hDC

/-! ## Convention discipline -/

/-- **The one-sided convention is numerically detectable, not cosmetic.**

The two-sided normalization `(∫₀ᵀ h²)/(∫₀ᵀ h)²` — this file's `enbw` without its factor `2` —
disagrees with the one-sided `enbw` on the boxcar at **every** positive window length (`1/T` vs
`1/(2T)`). Hence a downstream statement that silently switches convention is *wrong*, not merely
differently phrased: this is the Phase-6EB guardrail ("a convention-ambiguous theorem is a
defect, not a simplification") discharged as a theorem rather than left as prose. -/
theorem enbw_oneSided_ne_twoSided (T : ℝ) (hT : 0 < T) :
    enbw (boxcar T) T
      ≠ (∫ x in (0:ℝ)..T, boxcar T x ^ 2) / (∫ x in (0:ℝ)..T, boxcar T x) ^ 2 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  rw [enbw_boxcar T hT, integral_boxcar_sq T hT.le, integral_boxcar T hT.le]
  intro hcontra
  rw [div_eq_div_iff (by positivity) (by positivity)] at hcontra
  nlinarith [hcontra, hT]

/-- **ENBW is a bandwidth, not a gain.** Scaling a filter by any non-zero constant leaves its
equivalent noise bandwidth unchanged — the content of the normalized-DC-gain convention, and
what licenses every floor above being stated without a normalization hypothesis on `h`.

`hc : c ≠ 0` is load-bearing: at `c = 0` the left side collapses to the degenerate branch
`enbw_of_dcGain_eq_zero` (value `0`) while the right side need not vanish. -/
theorem enbw_const_mul (c : ℝ) (hc : c ≠ 0) (h : ℝ → ℝ) (T : ℝ) :
    enbw (fun x => c * h x) T = enbw h T := by
  unfold enbw
  have e1 : (∫ x in (0:ℝ)..T, (c * h x) ^ 2) = c ^ 2 * ∫ x in (0:ℝ)..T, h x ^ 2 := by
    simp_rw [mul_pow]
    exact intervalIntegral.integral_const_mul _ _
  have e2 : (∫ x in (0:ℝ)..T, c * h x) = c * ∫ x in (0:ℝ)..T, h x :=
    intervalIntegral.integral_const_mul _ _
  rw [e1, e2, mul_pow]
  rcases eq_or_ne (∫ x in (0:ℝ)..T, h x) 0 with hI | hI
  · rw [hI]; simp
  · field_simp

/-! ## The PSD bridge — why ENBW is defined this way -/

/-- **Whiteness, declared as an explicit hypothesis** (Phase 6EB UNKNOWN-2, resolved here in
favour of the roadmap's preferred option).

`V` is the *output second-moment functional* of a noise source read out through a filter: `V h`
is the variance of the filtered output before DC-gain normalization. The source is **white with
one-sided PSD `S₀`** exactly when that variance is proportional to the filter's energy over the
window with the one-sided constant `S₀/2`:

    V h = (S₀ / 2) · ∫₀ᵀ h²

*Why a `Prop` parameter and not a derived object.* The repo models no stochastic processes, and
Mathlib's `ProbabilityTheory` carries no stationary-process spectral theory (no
Wiener–Khinchin, no spectral measure for a second-order process) at the pinned version — so an
"abstract white-noise second-moment functional" would have to be built from scratch to state a
fact that is, physically, a *modelling assumption* about the source. Carrying it as a declared
hypothesis is the honest encoding: `V` is supplied by the consumer, the whiteness assumption is
visible in every consuming statement's binder list, and nothing about a physical noise source is
smuggled into a definition.

*Substantive load, disclosed (checklist Q5).* The physics content of the relation
`V h = (S₀/2)·∫h²` — Parseval plus flatness of the PSD — lives in this definition, not in
`variance_eq_psd_mul_enbw`, which is the algebra converting it into the bandwidth form. -/
def IsWhiteFilteredVariance (V : (ℝ → ℝ) → ℝ) (S₀ T : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, V h = S₀ / 2 * ∫ x in (0:ℝ)..T, h x ^ 2

/-- **The definitional raison d'être of ENBW.** For white noise of one-sided PSD `S₀` read out
through filter `h`, the **DC-gain-normalized** output variance is exactly `S₀ · ENBW(h)`:

    Var(output / H(0)) = S₀ · ENBW(h)

i.e. ENBW is precisely the number that converts a one-sided PSD into a variance. Whiteness is an
explicit hypothesis (`hwhite`), and the DC-gain hypothesis (`hDC`) is required because the
normalization divides by `H(0)² = (∫₀ᵀ h)²`.

Combining this with `enbw_mul_window_ge_half` gives the physical floor
`johnsonNyquist_filteredVariance_floor`. -/
theorem variance_eq_psd_mul_enbw {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (h : ℝ → ℝ)
    (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    V h / (∫ x in (0:ℝ)..T, h x) ^ 2 = S₀ * enbw h T := by
  rw [hwhite h]
  unfold enbw
  field_simp

/-- **The composed physical floor — thermal noise through ANY admissible single-shot filter.**

For Johnson–Nyquist white noise, whose one-sided PSD is the repo-canonical
`GrapheneNoiseFormula.johnsonNyquistPSD kB_T σ_Q = 4·kB_T·σ_Q`, no linear filter integrating
over a window of length `T` can achieve a DC-normalized output variance below

    σ² ≥ 2·kB_T·σ_Q / T.

This is a genuine cross-module bridge, not a docstring reference: the body **calls**
`GrapheneNoiseFormula.johnsonNyquistPSD` (in the hypothesis) and
`GrapheneNoiseFormula.johnsonNyquistPSD_pos` (in the proof), and composes them with
`enbw_mul_window_ge_half`.

The prefactor `2` is convention-pinned end-to-end: it is `4 × (1/2)` — the one-sided
Johnson–Nyquist PSD `4·kB_T·σ_Q` times the one-sided minimum bandwidth `1/(2T)`. The *product*
`S₀ · ENBW` is itself convention-invariant, as a physical variance must be; the danger is
**mixing** conventions, which changes the answer by exactly a factor of 2 in one direction or
the other. That is what `enbw_oneSided_ne_twoSided` makes non-negotiable. -/
theorem johnsonNyquist_filteredVariance_floor {V : (ℝ → ℝ) → ℝ} {kB_T sigma_Q T : ℝ}
    (hkT : 0 < kB_T) (hsQ : 0 < sigma_Q) (hT : 0 < T)
    (hwhite : IsWhiteFilteredVariance V
      (GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q) T)
    (h : ℝ → ℝ) (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    2 * kB_T * sigma_Q / T ≤ V h / (∫ x in (0:ℝ)..T, h x) ^ 2 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  rw [variance_eq_psd_mul_enbw hwhite h hDC]
  have hS : 0 < GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q :=
    GrapheneNoiseFormula.johnsonNyquistPSD_pos kB_T sigma_Q hkT hsQ
  have hfloor := enbw_mul_window_ge_half h T hT hint hsq hDC
  have hE : 1 / (2 * T) ≤ enbw h T := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hfloor]
  have hmul := mul_le_mul_of_nonneg_left hE hS.le
  calc 2 * kB_T * sigma_Q / T
      = GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q * (1 / (2 * T)) := by
        unfold GrapheneNoiseFormula.johnsonNyquistPSD
        field_simp
        ring
    _ ≤ _ := hmul

/-! ## Non-vacuity: the hypothesis is load-bearing, the floor has slack -/

/-- **The degenerate branch, disclosed.** A filter with zero DC gain has no equivalent noise
bandwidth; Lean's total division sends the undefined ratio to `0`. Stated so that consumers
cannot mistake the junk value for a physical bandwidth. -/
theorem enbw_of_dcGain_eq_zero (h : ℝ → ℝ) (T : ℝ) (hDC : (∫ x in (0:ℝ)..T, h x) = 0) :
    enbw h T = 0 := by
  unfold enbw; rw [hDC]; simp

/-- **The `∫₀ᵀ h ≠ 0` hypothesis of `enbw_mul_window_ge_half` CANNOT be dropped.**

Exhibits a filter satisfying *every other* hypothesis of the floor — interval-integrable on
`[0, 2]`, with interval-integrable square, on a positive window — that nonetheless **violates**
the conclusion `1/2 ≤ enbw h T * T`. The witness is the zero-mean ramp `h(y) = y − 1` on
`[0, 2]`, whose DC gain `∫₀² (y − 1) dy = 0` vanishes, so `enbw h 2 = 0` by
`enbw_of_dcGain_eq_zero` and `enbw h 2 * 2 = 0 < 1/2`.

Physically this is not a Lean artefact: a zero-DC-gain filter rejects the signal entirely, so
there is no "bandwidth per unit gain" to bound. Same shape as Phase 6EA's
`darkBaseline_zeroFalseAlarm_load_bearing`. -/
theorem enbw_dcGain_hypothesis_load_bearing :
    ∃ h : ℝ → ℝ, IntervalIntegrable h volume 0 2 ∧
      IntervalIntegrable (fun x => h x ^ 2) volume 0 2 ∧
      enbw h 2 * 2 < 1 / 2 := by
  refine ⟨fun y => y - 1, ?_, ?_, ?_⟩
  · exact (continuous_id.sub continuous_const).intervalIntegrable 0 2
  · exact ((continuous_id.sub continuous_const).pow 2).intervalIntegrable 0 2
  · have hz : (∫ y in (0:ℝ)..2, (y - 1)) = 0 := by
      rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const]
      simp
      norm_num
    rw [enbw_of_dcGain_eq_zero _ _ hz]
    norm_num

/-- **The floor is not an equality in disguise.** A linear-ramp weighting `h(x) = x` on `[0, 1]`
has `ENBW · T = (1/3)/(2·(1/2)²) = 2/3`, strictly above the `1/2` floor — so the bound is a
genuine screen with slack for non-boxcar filters, not a restatement of a definition. (Consistent
with `enbw_eq_half_iff_boxcar`: the ramp is not a.e. constant on the window.) -/
theorem enbw_ramp_gt_half : 1 / 2 < enbw (fun x => x) 1 * 1 := by
  have h1 : (∫ x in (0:ℝ)..1, x ^ 2) = 1 / 3 := by
    simp [integral_pow]
    norm_num
  have h2 : (∫ x in (0:ℝ)..1, x) = 1 / 2 := by
    simp [integral_id]
  unfold enbw
  rw [h1, h2]
  norm_num

end SKEFTHawking.Detection
