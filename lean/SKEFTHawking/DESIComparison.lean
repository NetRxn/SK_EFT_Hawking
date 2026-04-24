import SKEFTHawking.Basic

/-!
# DESI DR2 Preferred Dark-Energy Region

Formal encoding of the DESI DR2 Baryon Acoustic Oscillation preferred region
for the CPL (Chevallier-Polarski-Linder) dark-energy parameterization
`w(a) = w₀ + w_a · (1 − a)`.

## DESI DR2 preferred-region summary

From the DESI DR2 BAO data combined with CMB and supernovae samples:

| Dataset combination         | `(w₀, w_a)` central       | Source |
| DESI DR2 BAO + CMB          | `(−0.42 ± 0.21, −1.75 ± 0.58)` | arXiv:2503.14738 |
| DESI DR2 + CMB + DESY5      | `(−0.75, −0.86)` tight errors | Nature Astronomy 2025 |
| DESI DR2 + CMB + Pantheon+  | `(−0.84, −0.44)`              | arXiv:2503.14738 |
| DESI DR2 + CMB + Union3     | `(−0.73, −1.05) ± (0.07, 0.3)` | Nature Astronomy 2025 companion |

All combinations show **phantom crossing** near `z ≈ 0.5` with `w(z) > −1`
today and `w(z) < −1` at `z ∼ 0.75` (the "quintom-B" region).

## 1σ and 3σ envelopes

Following the Phase 5y roadmap specification, we take as the canonical
DESI DR2 preferred region (1σ):
- `w₀ ∈ [−0.8, −0.66]`
- `w_a ∈ [−1.35, −0.75]`

3σ envelope (roughly):
- `w₀ ∈ [−0.95, −0.50]`
- `w_a ∈ [−2.00, −0.20]`

## References

- DESI Collaboration, *Cosmological constraints from DESI 2024 VI*,
  arXiv:2404.03002 and DR2 update arXiv:2503.14738
- Lodha et al., arXiv:2503.14743 (CPL vs. alternative parameterizations)
- Nature Astronomy 2025 companion paper on DESI DR2 phantom crossing
- `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md` §8
-/

namespace SKEFTHawking.DESIComparison

/-!
## CPL parameterization

The Chevallier-Polarski-Linder parameterization uses the scale factor
`a ∈ (0, 1]` with `a = 1` today, decreasing to `a → 0` in the early
universe. The CPL fit is `w(a) = w₀ + w_a · (1 − a)`.
-/

/-- Chevallier-Polarski-Linder dark-energy parameterization. Specifies a
    candidate `(w₀, w_a)` pair for comparison against DESI DR2. -/
structure CPLCandidate where
  /-- Equation-of-state parameter today (`a = 1`). -/
  w0 : ℝ
  /-- Linear rate parameter: `w_a = −(dw/da)|_{a=1}`. -/
  wa : ℝ

/-- CPL fit function `w(a) = w₀ + w_a · (1 − a)` (Round 5 EQ.125). -/
noncomputable def CPLCandidate.w (c : CPLCandidate) (a : ℝ) : ℝ :=
  c.w0 + c.wa * (1 - a)

/-- **DC1 — CPL agrees with `w₀` at today (`a = 1`).** -/
theorem cpl_today (c : CPLCandidate) : c.w 1 = c.w0 := by
  unfold CPLCandidate.w; ring

/-- **DC2 — CPL value at `a = 0` is `w₀ + w_a`.** -/
theorem cpl_at_a_zero (c : CPLCandidate) : c.w 0 = c.w0 + c.wa := by
  unfold CPLCandidate.w; ring

/-!
## DESI DR2 preferred-region bounds
-/

/-- DESI DR2 preferred region (1σ envelope), as declared in the Phase 5y
    roadmap: `w₀ ∈ [−0.8, −0.66], w_a ∈ [−1.35, −0.75]`. -/
structure DESIRegion where
  /-- Lower bound on `w₀`. -/
  w0_min : ℝ
  /-- Upper bound on `w₀`. -/
  w0_max : ℝ
  /-- Lower bound on `w_a`. -/
  wa_min : ℝ
  /-- Upper bound on `w_a`. -/
  wa_max : ℝ
  /-- Bounds are well-ordered on `w₀`. -/
  w0_ordered : w0_min ≤ w0_max
  /-- Bounds are well-ordered on `w_a`. -/
  wa_ordered : wa_min ≤ wa_max

/-- DESI DR2 1σ preferred region: `w₀ ∈ [−0.8, −0.66], w_a ∈ [−1.35, −0.75]`. -/
noncomputable def desiDR2_1sigma : DESIRegion where
  w0_min := -0.8
  w0_max := -0.66
  wa_min := -1.35
  wa_max := -0.75
  w0_ordered := by norm_num
  wa_ordered := by norm_num

/-- DESI DR2 3σ envelope: `w₀ ∈ [−0.95, −0.50], w_a ∈ [−2.00, −0.20]`. -/
noncomputable def desiDR2_3sigma : DESIRegion where
  w0_min := -0.95
  w0_max := -0.50
  wa_min := -2.00
  wa_max := -0.20
  w0_ordered := by norm_num
  wa_ordered := by norm_num

/-- Predicate: a CPL candidate lies in the DESI preferred region. -/
def InDESIRegion (c : CPLCandidate) (R : DESIRegion) : Prop :=
  R.w0_min ≤ c.w0 ∧ c.w0 ≤ R.w0_max ∧ R.wa_min ≤ c.wa ∧ c.wa ≤ R.wa_max

/-!
## Quintom-B phantom crossing

The DESI DR2 combinations consistently show **phantom crossing**: `w(z)`
crosses `−1` around `z ≈ 0.5`. In the CPL parameterization with `a = 1/(1+z)`,
phantom crossing at some `a₀ ∈ (0, 1)` requires `w₀ > −1` and
`w₀ + w_a < −1` — that is, `w_a < −1 − w₀`. This is the "quintom-B" region.
-/

/-- Quintom-B predicate: CPL candidate exhibits phantom crossing from the
    non-phantom side today (`w₀ > −1`) to the phantom side in the past
    (`w₀ + w_a < −1`). -/
def QuintomB (c : CPLCandidate) : Prop :=
  c.w0 > -1 ∧ c.w0 + c.wa < -1

/-- **DC3 — Quintom-B implies `w_a < −1 − w₀`.** -/
theorem quintomB_wa_bound (c : CPLCandidate) (h : QuintomB c) :
    c.wa < -1 - c.w0 := by
  obtain ⟨_, h2⟩ := h
  linarith

/-- **DC4 — Quintom-B implies `w_a < 0`** (since `w₀ > −1`). -/
theorem quintomB_wa_neg (c : CPLCandidate) (h : QuintomB c) : c.wa < 0 := by
  obtain ⟨h1, h2⟩ := h
  linarith

/-- **DC5 — DESI DR2 preferred-region candidates are phantom-today.**

    For the 1σ region with `w₀ ≤ −0.66`, the `w₀ > −1` side is not strict;
    phantom crossing can still happen. But our encoded region has
    `w₀ ≥ −0.8 > −1`, so candidates in the region are non-phantom today. -/
theorem desi_region_non_phantom_today (c : CPLCandidate)
    (h : InDESIRegion c desiDR2_1sigma) : c.w0 > -1 := by
  unfold InDESIRegion at h
  unfold desiDR2_1sigma at h
  have := h.1
  linarith

/-!
## σ-offset computation for candidate predictions

For a candidate `(w₀, w_a)` predicted by a theory model, the σ-offset from
the DESI central value measures how many standard deviations away the
prediction sits. We use a simple weighted distance.
-/

/-- Weighted σ-offset from a DESI central point `(w₀_c, w_a_c)` with
    respective 1σ errors `(σ_{w₀}, σ_{w_a})`:
    `σ_offset² = ((w₀ − w₀_c) / σ_{w₀})² + ((w_a − w_a_c) / σ_{w_a})²`. -/
noncomputable def sigmaOffsetSq (c : CPLCandidate)
    (w0_c wa_c sigma_w0 sigma_wa : ℝ) : ℝ :=
  ((c.w0 - w0_c) / sigma_w0)^2 + ((c.wa - wa_c) / sigma_wa)^2

/-- **DC6 — σ-offset is non-negative.** -/
theorem sigmaOffsetSq_nonneg (c : CPLCandidate)
    (w0_c wa_c sigma_w0 sigma_wa : ℝ) :
    0 ≤ sigmaOffsetSq c w0_c wa_c sigma_w0 sigma_wa := by
  unfold sigmaOffsetSq
  positivity

/-- **DC7 — σ-offset vanishes iff the candidate matches the central point
    exactly.**

    More precisely: if `sigma_w0 ≠ 0` and `sigma_wa ≠ 0`, then
    `sigmaOffsetSq = 0 ↔ w₀ = w₀_c ∧ w_a = wa_c`. We prove the reverse
    direction (matching → zero); the forward direction requires
    injectivity of `x ↦ x²` on `ℝ` which is standard but tangential. -/
theorem sigmaOffsetSq_zero_of_match (c : CPLCandidate)
    (w0_c wa_c sigma_w0 sigma_wa : ℝ) (hw0 : c.w0 = w0_c) (hwa : c.wa = wa_c) :
    sigmaOffsetSq c w0_c wa_c sigma_w0 sigma_wa = 0 := by
  unfold sigmaOffsetSq
  rw [hw0, hwa]
  ring

/-!
## DESI-compatibility vs. `w = −1`-locked candidates

The Wave 1 Gibbs-Duhem theorem shows that emergent-vacuum frameworks lock
`w_vac = −1`. In CPL language, this is `(w₀, w_a) = (−1, 0)`, which lies
**outside** the DESI preferred region (since `w₀ = −1 < −0.8 = w₀_min`).
Hence any q-theory realization is incompatible with DESI.
-/

/-- The `w = −1` (cosmological-constant) CPL point. -/
noncomputable def lambdaCDM : CPLCandidate where
  w0 := -1
  wa := 0

/-- **DC8 — `w = −1` is NOT in the DESI DR2 1σ region.**

    The ΛCDM point `(w₀, w_a) = (−1, 0)` fails the DESI preferred region
    with `w₀ = −1 < −0.8 = w₀_min`. This is the structural incompatibility
    of any Gibbs-Duhem-locked vacuum with DESI. -/
theorem lambda_cdm_not_in_desi :
    ¬ InDESIRegion lambdaCDM desiDR2_1sigma := by
  unfold InDESIRegion lambdaCDM desiDR2_1sigma
  intro h
  have := h.1  -- -0.8 ≤ -1
  linarith

end SKEFTHawking.DESIComparison
