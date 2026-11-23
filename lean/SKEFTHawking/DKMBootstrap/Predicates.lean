/-
# DKM modeled response and legacy predicate interfaces

The signed modeled spectrum below is CHHK arXiv:2509.18255v2 §3 Eq. (4).
Its positivity input is restricted to nonnegative frequency (§7.1 after Eq. (24)).
The algebraic model is defined globally, but identifying it with a microscopic response
requires a finite effective frequency/momentum window (§3). Model sign, symmetry and
holomorphy do not establish the weighted thermal microscopic bounds, a physical transport
realization, or uniqueness. The F1/F2/F5 interfaces retained here have the limitations
specified on their definitions. Standalone F3 and its APIs are independent of those repairs.

Source: held canonical `Lit-Search/Phase-1-and-Background/primary-sources/
CHHK2025DKMTransport.pdf`, v2 dated 14 May 2026, Eqs. (4), (5), (14), (22)-(25).
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.SKDoubling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.GloriosoLiu SKEFTHawking.SKDoubling

/-! ## §1. The `DKMParameters` 5-real positivity capsule.

Per Wave 2a.1 DR §3 Option-A/Option-B hybrid: minimal typed capsule for
the 5-real positivity tuple `(τ, D, χ, a, ε)`, with everything else
operationalized at predicate-substrate level (Option B primary). This
preserves the FreeAlgebra/RingQuot zero-sorry pattern that the rest of
the project uses while giving the bootstrap-bound proofs a clean small
data type to consume.

The five reals:
- `τ` current relaxation time;
- `D` charge diffusivity;
- `χ` charge compressibility;
- `a` microscopic length scale (e.g., lattice spacing — graphene a ≈
  0.246 nm per Castro Neto et al. RMP 81, 109);
- `ε` CHHK microscopic energy scale `ε = 2·h · b_d · (2R)^d / ν`
  (CHHK eq. 12 just before).
-/

/-- **CHHK 5-real positivity capsule.** Pre-positivity-witnessed
parameters of the Drude–Kadanoff–Martin model that the CHHK bootstrap
constrains. All fields are physically required to be strictly positive. -/
structure DKMParameters where
  /-- Current relaxation time τ (units of time). -/
  τ : ℝ
  /-- Charge diffusivity D (units of length²/time). -/
  D : ℝ
  /-- Charge compressibility χ. -/
  χ : ℝ
  /-- Microscopic length scale a (e.g., lattice spacing). -/
  a : ℝ
  /-- CHHK microscopic energy scale ε = 2·h·b_d·(2R)^d/ν. -/
  ε : ℝ
  /-- Physical positivity: τ > 0. -/
  τ_pos : 0 < τ
  /-- Physical positivity: D > 0. -/
  D_pos : 0 < D
  /-- Physical positivity: χ > 0. -/
  χ_pos : 0 < χ
  /-- Physical positivity: a > 0. -/
  a_pos : 0 < a
  /-- Physical positivity: ε > 0. -/
  ε_pos : 0 < ε

namespace DKMParameters

/-- The collective mean free path `ℓ := √(τ·D)`. CHHK eq. (9) v2 [= eq. (26) v1] MIR-style
master bound is phrased in terms of `ℓ/a`. -/
noncomputable def collectiveMeanFreePath (p : DKMParameters) : ℝ :=
  Real.sqrt (p.τ * p.D)

/-- The mean free path is strictly positive (from τ_pos and D_pos). -/
theorem collectiveMeanFreePath_pos (p : DKMParameters) :
    0 < p.collectiveMeanFreePath := by
  unfold collectiveMeanFreePath
  exact Real.sqrt_pos.mpr (mul_pos p.τ_pos p.D_pos)

end DKMParameters

/-! ## §2. Signed effective DKM spectrum (CHHK v2 Eq. (4)).

`Correlator` stores Im G^R itself, without division by frequency.
Lean division is total: its value at the origin is zero. This is not a statement about
static compressibility, which involves a different order of limits.
-/

/-- Signed real-frequency imaginary response, as a function of frequency and momentum. -/
abbrev Correlator : Type := ℝ → ℝ → ℝ

/-- CHHK v2 Eq. (4), multiplied by Ω. The denominator is
`Ω² + (D k² - τ Ω²)²`, including the mixed diffusion/relaxation term. -/
noncomputable def dkmImGRetarded (p : DKMParameters) : Correlator :=
  fun Ω k ↦ p.χ * p.D * k^2 * Ω / (Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2)

/-- The source denominator is nonnegative everywhere. -/
theorem dkm_denom_nonneg (p : DKMParameters) (Ω k : ℝ) :
    0 ≤ Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The source denominator is strictly positive away from the origin. -/
theorem dkm_denom_pos (p : DKMParameters) (Ω k : ℝ) (h : Ω ≠ 0 ∨ k ≠ 0) :
    0 < Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2 := by
  by_cases hΩ : Ω = 0
  · subst Ω
    have hk : k ≠ 0 := h.resolve_left (by simp)
    simpa using sq_pos_of_pos (mul_pos p.D_pos (sq_pos_of_ne_zero hk))
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hΩ) (sq_nonneg _)

/-- No real pole except the excluded origin of the displayed source quotient. -/
theorem dkm_denom_ne_zero (p : DKMParameters) (Ω k : ℝ) (h : Ω ≠ 0 ∨ k ≠ 0) :
    Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2 ≠ 0 :=
  ne_of_gt (dkm_denom_pos p Ω k h)

/-- Signed oddness in frequency of the model; physical responses need their own symmetry. -/
theorem dkmImGRetarded_odd (p : DKMParameters) (Ω k : ℝ) :
    dkmImGRetarded p (-Ω) k = -dkmImGRetarded p Ω k := by
  simp [dkmImGRetarded, neg_div]

/-- Evenness in momentum of this isotropic model. -/
theorem dkmImGRetarded_even_k (p : DKMParameters) (Ω k : ℝ) :
    dkmImGRetarded p Ω (-k) = dkmImGRetarded p Ω k := by
  simp [dkmImGRetarded]

/-- Conservation gives zero spectral response on the whole k=0 slice, including the origin
under Lean's total division convention. This does not evaluate the static limit. -/
theorem dkmImGRetarded_zero_k (p : DKMParameters) (Ω : ℝ) :
    dkmImGRetarded p Ω 0 = 0 := by
  simp [dkmImGRetarded]

/-- Strict positive-frequency response at every nonzero momentum. -/
theorem dkmImGRetarded_pos (p : DKMParameters) (Ω k : ℝ) (hΩ : 0 < Ω) (hk : k ≠ 0) :
    0 < dkmImGRetarded p Ω k := by
  exact div_pos (mul_pos (mul_pos (mul_pos p.χ_pos p.D_pos)
    (sq_pos_of_ne_zero hk)) hΩ) (dkm_denom_pos p Ω k (Or.inl (ne_of_gt hΩ)))

/-- A genuinely nonzero slice, for every allowed parameter tuple. -/
theorem dkmImGRetarded_one_pos (p : DKMParameters) : 0 < dkmImGRetarded p 1 1 :=
  dkmImGRetarded_pos p 1 1 zero_lt_one one_ne_zero

/-- The negative-frequency control rules out the obsolete global positivity requirement. -/
theorem dkmImGRetarded_neg_one (p : DKMParameters) : dkmImGRetarded p (-1) 1 < 0 := by
  rw [dkmImGRetarded_odd]
  exact neg_neg_of_pos (dkmImGRetarded_one_pos p)

/-- Source regression: τ=χ=1, D=2 gives 1, whereas the old denominator gives 1/2. -/
theorem dkmImGRetarded_source_regression :
    let p : DKMParameters := ⟨1, 2, 1, 1, 1, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩
    dkmImGRetarded p 1 1 = 1 ∧
      (p.χ * p.D * (1 : ℝ)^2 * 1 /
        ((1 : ℝ)^2 * (1 - p.τ * (1 : ℝ)^2)^2 + (p.D * (1 : ℝ)^2)^2)) = 1 / 2 := by
  norm_num [dkmImGRetarded]

/-- The displayed Eq. (4) ratio is recovered at nonzero frequency. -/
theorem dkmImGRetarded_div_frequency (p : DKMParameters) (Ω k : ℝ) (hΩ : Ω ≠ 0) :
    dkmImGRetarded p Ω k / Ω =
      p.χ * p.D * k^2 / (Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2) := by
  unfold dkmImGRetarded
  field_simp

/-! ### Conductivity limit (CHHK v2 Eq. (5)). -/

/-- Cancelling k² is valid only at nonzero momentum; the original quotient is zero at k=0. -/
theorem dkm_scaled_spectrum (p : DKMParameters) (Ω k : ℝ) (hk : k ≠ 0) :
    Ω * dkmImGRetarded p Ω k / k^2 =
      p.χ * p.D * Ω^2 / (Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2) := by
  unfold dkmImGRetarded
  field_simp

/-- Actual punctured k→0 limit of the scaled signed spectrum at fixed Ω≠0.
This is Eq. (5); it does not assign this value to the k=0 total quotient. -/
theorem dkm_conductivity_limit (p : DKMParameters) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    Filter.Tendsto (fun k : ℝ ↦ Ω * dkmImGRetarded p Ω k / k^2)
      (nhdsWithin 0 {0}ᶜ) (nhds (p.χ * p.D / (1 + p.τ^2 * Ω^2))) := by
  have hd : (0 : ℝ) < Ω^2 + (p.D * 0^2 - p.τ * Ω^2)^2 :=
    dkm_denom_pos p Ω 0 (Or.inl hΩ)
  have hc : ContinuousAt
      (fun k : ℝ ↦ p.χ * p.D * Ω^2 / (Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt hd
  have hv : p.χ * p.D * Ω^2 / (Ω^2 + (p.D * 0^2 - p.τ * Ω^2)^2) =
      p.χ * p.D / (1 + p.τ^2 * Ω^2) := by
    have hp : 0 < 1 + p.τ^2 * Ω^2 := by positivity
    field_simp
    ring
  have ht := hc.tendsto
  rw [hv] at ht
  apply ht.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact (dkm_scaled_spectrum p Ω k (by simpa using hk)).symm

/-! ### An actual complex effective model, separate from legacy F5. -/

/-- Denominator of `χDk²/(Dk²-τz²-iz)`. -/
noncomputable def dkmRetardedDenom (p : DKMParameters) (z : ℂ) (k : ℝ) : ℂ :=
  (p.D : ℂ) * (k : ℂ)^2 - (p.τ : ℂ) * z^2 - Complex.I * z

/-- Complex retarded effective model, with the same total-division convention. -/
noncomputable def dkmGRetarded (p : DKMParameters) (z : ℂ) (k : ℝ) : ℂ :=
  ((p.χ * p.D * k^2 : ℝ) : ℂ) / dkmRetardedDenom p z k

/-- Explicit imaginary part of the denominator in the upper half-plane. -/
theorem dkmRetardedDenom_im (p : DKMParameters) (z : ℂ) (k : ℝ) :
    (dkmRetardedDenom p z k).im = -z.re * (2 * p.τ * z.im + 1) := by
  simp [dkmRetardedDenom, Complex.mul_im, Complex.mul_re, pow_two]
  ring

/-- Real part of the same denominator. -/
theorem dkmRetardedDenom_re (p : DKMParameters) (z : ℂ) (k : ℝ) :
    (dkmRetardedDenom p z k).re =
      p.D * k^2 - p.τ * (z.re^2 - z.im^2) + z.im := by
  simp [dkmRetardedDenom, Complex.mul_re, Complex.mul_im, pow_two]

/-- No poles on Im z>0: the imaginary equation forces Re z=0, where the real part is positive. -/
theorem dkmRetardedDenom_ne_zero_uhp (p : DKMParameters) (z : ℂ) (k : ℝ)
    (hz : 0 < z.im) : dkmRetardedDenom p z k ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  rw [dkmRetardedDenom_im] at hi
  have hfactor : 0 < 2 * p.τ * z.im + 1 :=
    add_pos (mul_pos (mul_pos (by norm_num) p.τ_pos) hz) zero_lt_one
  have hx : z.re = 0 := by
    have hm : -z.re = 0 := (mul_eq_zero.mp hi).resolve_right (ne_of_gt hfactor)
    linarith
  have hr := congrArg Complex.re h
  rw [dkmRetardedDenom_re, hx] at hr
  have hD : 0 ≤ p.D * k^2 := mul_nonneg p.D_pos.le (sq_nonneg k)
  have ht : 0 ≤ p.τ * z.im^2 := mul_nonneg p.τ_pos.le (sq_nonneg z.im)
  simp only [Complex.zero_re, sq, zero_mul, zero_sub, mul_neg, sub_neg_eq_add] at hr
  nlinarith

/-- Complex differentiability of the actual model at every upper-half-plane point. -/
theorem dkmGRetarded_differentiableAt (p : DKMParameters) (z : ℂ) (k : ℝ)
    (hz : 0 < z.im) : DifferentiableAt ℂ (fun w ↦ dkmGRetarded p w k) z := by
  apply DifferentiableAt.div
  · exact differentiableAt_const _
  · unfold dkmRetardedDenom
    fun_prop
  · exact dkmRetardedDenom_ne_zero_uhp p z k hz

/-- Holomorphy of the modeled response on the open upper half-plane. This provides
no microscopic spectral representation or contour identity for a physical response. -/
theorem dkmGRetarded_differentiableOn (p : DKMParameters) (k : ℝ) :
    DifferentiableOn ℂ (fun z ↦ dkmGRetarded p z k) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (dkmGRetarded_differentiableAt p z k hz).differentiableWithinAt

/-- The real-axis denominator has precisely the source denominator as squared modulus. -/
theorem dkmRetardedDenom_normSq_real (p : DKMParameters) (Ω k : ℝ) :
    Complex.normSq (dkmRetardedDenom p (Ω : ℂ) k) =
      Ω^2 + (p.D * k^2 - p.τ * Ω^2)^2 := by
  rw [Complex.normSq_apply, dkmRetardedDenom_re, dkmRetardedDenom_im]
  simp
  ring

/-- Real-axis poles are excluded away from the origin. -/
theorem dkmRetardedDenom_ne_zero_real (p : DKMParameters) (Ω k : ℝ)
    (h : Ω ≠ 0 ∨ k ≠ 0) : dkmRetardedDenom p (Ω : ℂ) k ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [dkmRetardedDenom_normSq_real]
  exact dkm_denom_pos p Ω k h

/-- The complex model's signed imaginary part agrees with Eq. (4).
The identity even holds at the origin under total division; the nonzero real-axis domain
is qualified separately by `dkmRetardedDenom_ne_zero_real`. -/
theorem dkmGRetarded_im_real (p : DKMParameters) (Ω k : ℝ) :
    (dkmGRetarded p (Ω : ℂ) k).im = dkmImGRetarded p Ω k := by
  unfold dkmGRetarded
  rw [Complex.div_im, dkmRetardedDenom_normSq_real, dkmRetardedDenom_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, mul_one,
    zero_mul, zero_div, zero_sub, mul_neg, neg_div, neg_neg, dkmImGRetarded]

/-! ## §3. The six DKM axiom-family predicates.

Each Prop carries only its displayed type. In particular, the legacy F1/F2/F5
interfaces below do not encode the full source contract. -/

/-- **Legacy global F1 model identity.** This equates the response to Eq. (4) on all
real frequencies and momenta. CHHK assumes this form only on an effective finite window.
This interface is not microscopic applicability; in particular it must not be combined
with pointwise F2 as a claimed physical witness. -/
def IsDKMTransportCorrelator (G : Correlator) (p : DKMParameters) : Prop :=
  ∀ Ω k, G Ω k = dkmImGRetarded p Ω k

/-- **Legacy pointwise F2.** This is one uniform pointwise bound for every window,
not CHHK v2 Eq. (2)/(25)'s weighted frequency/momentum integral in a thermal state.
Global F1 with this predicate remains incompatible with diffusion scaling near the origin:
`G(D k²,k)/(D k²)` diverges as k→0. Correcting F4 does not populate the full bundle.
This module supplies no weighted microscopic spectral inequality. The previously
promised `SpectralWeightBound.lean` module is absent. -/
def HasFSumRule (G : Correlator) (boundData : ℝ) : Prop :=
  ∀ ω Λ : ℝ, 0 < ω → ω ≤ Λ →
    ∀ Ω k : ℝ, ω ≤ Ω → Ω ≤ Λ → 0 < Ω →
      G Ω k / Ω ≤ boundData

/-- **F3 — High-frequency operator-growth bound.** This predicate encodes
the factorial-times-exponential bound from CHHK arXiv:2509.18255v2 Eq. (31)
for a supplied real sequence. In CHHK, bounded local Hamiltonian terms and
a local observable yield that estimate; Eq. (32) then optimizes the
spectral bound in Eq. (33). The factor of e concerns the exponential
falloff of the spectral bound relative to the earlier heating estimate.
A physical use of this predicate must identify and bound the actual
nested commutator norms on its chosen carrier. -/
def HasOperatorGrowthBound
    (commutatorNorm : ℕ → ℝ) (ε n0Norm : ℝ) : Prop :=
  ∀ κ : ℕ, commutatorNorm κ ≤ (Nat.factorial κ : ℝ) * ε^κ * n0Norm

/-- **F4: positive-frequency cone.** CHHK v2 §7.1 after Eq. (24) requires
`0 ≤ Im G^R(Ω,k)` for `0 ≤ Ω`. Negative frequencies retain their signed response. -/
def IsImGRetardedNonneg (G : Correlator) : Prop :=
  ∀ Ω k, 0 ≤ Ω → 0 ≤ G Ω k

/-- **Legacy real F5.** The existential is satisfied by choosing `G α k` itself.
It asserts neither a complex extension nor holomorphy, a contour identity, decay, or
causality. Consumers projecting this field inherit only that real-valued tautology.
The actual complex model proved above is separate from microscopic causal matching. -/
def IsUpperHalfPlaneAnalytic (G : Correlator) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ k : ℝ, ∃ value : ℝ, G α k = value

/-- **F6 — Parity / time-reversal symmetry.** Time-reversal with `k → -k`
gives `Im G^R(Ω, k) = -Im G^R(-Ω, k)` (CHHK; consistent with the
project's `SKEFTAxiomsExt_yields_parity_alternation`). -/
def HasParityTimeReversal (G : Correlator) : Prop :=
  ∀ Ω k, G Ω k = -(G (-Ω) k)

/-- The corrected model belongs to the positive-frequency cone. -/
theorem dkmImGRetarded_nonneg (p : DKMParameters) :
    IsImGRetardedNonneg (dkmImGRetarded p) := by
  intro Ω k hΩ
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p.χ_pos.le p.D_pos.le)
    (sq_nonneg k)) hΩ) (dkm_denom_nonneg p Ω k)

/-- The modeled signed response satisfies F6 by algebra; identifying a physical response
with it requires an independently justified symmetry and effective window. -/
theorem dkmImGRetarded_hasParityTimeReversal (p : DKMParameters) :
    HasParityTimeReversal (dkmImGRetarded p) := by
  intro Ω k
  rw [dkmImGRetarded_odd, neg_neg]

/-! ## §4. The bundled `IsDKMAxiomSet` predicate.

Legacy bundle of six interfaces, without a claim that they are jointly inhabited.
The `commutatorNorm`, `ε`, `n0Norm`, and `boundData` fields enter as parameters that
downstream consumers supply as hypothesis parameters. No parameter choice here
establishes a microscopic realization of this legacy bundle. -/

/-- **Legacy six-interface bundle on a transport correlator.** A
correlator `G` satisfies the DKM axiom set if it (F1) matches the
explicit DKM form globally, (F2) has the legacy uniform pointwise bound, (F3) the
underlying nested-commutator norms have the κ!·ε^κ growth bound, (F4) is
nonnegative at nonnegative frequency, (F5) has the trivial real existential, and (F6) is
P/T-odd. This does not certify the weighted microscopic or causal CHHK contract. -/
structure IsDKMAxiomSet
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) : Prop where
  /-- F1 — `G = dkmImGRetarded p`. -/
  dkm_form : IsDKMTransportCorrelator G p
  /-- F2 — legacy uniform pointwise bound, not a weighted integral. -/
  f_sum_rule : HasFSumRule G boundData
  /-- F3 — nested-commutator operator-growth bound at scale `p.ε`. -/
  operator_growth : HasOperatorGrowthBound commutatorNorm p.ε n0Norm
  /-- F4 — positivity. -/
  positivity : IsImGRetardedNonneg G
  /-- F5 — legacy real existential, not complex analyticity. -/
  uhp_analytic : IsUpperHalfPlaneAnalytic G
  /-- F6 — parity / time-reversal. -/
  pt_symmetry : HasParityTimeReversal G

/-! ## §5. Drude diffusion benchmark and individual API witnesses.

The τ=0 algebraic benchmark below is separate from the strictly positive-τ parameter
capsule. Its zero-momentum theorem alone is not a nonzero F4 witness; the actual modeled
positive-frequency nonzero witness is `dkmImGRetarded_one_pos` above.
-/

/-- The pure-diffusion (τ=0) benchmark spectrum. -/
noncomputable def drudeCorrelator (p : DKMParameters) : Correlator :=
  fun Ω k =>
    let denom := Ω^2 + (p.D * k^2)^2
    p.χ * p.D * k^2 * Ω / denom

/-- The Drude denominator is strictly positive when `(Ω, k)` is not the
origin, and nonneg always. -/
theorem drude_denom_nonneg (p : DKMParameters) (Ω k : ℝ) :
    0 ≤ Ω^2 + (p.D * k^2)^2 := by
  have h1 : 0 ≤ Ω^2 := sq_nonneg Ω
  have h2 : 0 ≤ (p.D * k^2)^2 := sq_nonneg _
  linarith

/-- The zero-momentum Drude slice vanishes and is therefore nonnegative. -/
theorem drude_positivity_at_zero_k (p : DKMParameters) :
    ∀ Ω, 0 ≤ drudeCorrelator p Ω 0 := by
  intro Ω
  unfold drudeCorrelator
  simp

/-! **Individual substrate-API witnesses.**

The zero correlator supplies individual F4, legacy F5, F6, and nonnegative-bound
pointwise F2 witnesses, and the zero commutator sequence supplies F3. They do not
satisfy global F1 for positive parameters and cannot populate `IsDKMAxiomSet`.
CGL/KMS link projections and LDP consumers of these predicates inherit exactly their
stated premises; a projection or a zero witness does not upgrade F2 to a weighted
microscopic integral or F5 to a complex causal response. Standalone F3 growth and BEC
obstruction theorems retain their separate hypotheses.

- `becBogoliubovCommutatorNorm` (`BECBogoliubovBosonicGrowth.lean`) is the
  prescribed sequence (2κ)!, used to test the abstract sharpened no-go.
  It does not compute a commutator norm of a BEC Hamiltonian.
- `grapheneDKMParameters` (`E1E2CrossBridge.lean`) gives a normalized
  parameter record. The calculation in `src/dkm_bootstrap/graphene_mir.py`
  separately evaluates the scalar (2·β_2/(4π))^(1/3) ≈ 0.0756. Neither
  identifies an actual graphene transport tuple or establishes DKM
  applicability for a measured sample.
-/

/-- **The constantly-zero correlator.** -/
def zeroCorrelator : Correlator := fun _ _ => 0

/-- The zero correlator is nonneg. -/
theorem zeroCorrelator_isImGRetardedNonneg :
    IsImGRetardedNonneg zeroCorrelator := by
  intro _ _ _
  exact le_refl 0

/-- The zero correlator satisfies the legacy real F5 existential with `value = 0`. -/
theorem zeroCorrelator_isUpperHalfPlaneAnalytic :
    IsUpperHalfPlaneAnalytic zeroCorrelator := by
  intro α _ k
  exact ⟨0, rfl⟩

/-- The zero correlator is P/T-odd (trivially: `0 = -0`). -/
theorem zeroCorrelator_hasParityTimeReversal :
    HasParityTimeReversal zeroCorrelator := by
  intro Ω k
  simp [zeroCorrelator]

/-- The zero correlator satisfies the f-sum rule for any nonneg bound. -/
theorem zeroCorrelator_hasFSumRule (boundData : ℝ) (h : 0 ≤ boundData) :
    HasFSumRule zeroCorrelator boundData := by
  intro ω Λ _hω _hωΛ Ω k _hωΩ _hΩΛ hΩpos
  simp [zeroCorrelator]
  exact h

/-- The constantly-zero commutator-norm sequence satisfies the operator-
growth bound for any positive ε and n0Norm. -/
theorem zeroCommutatorNorm_hasOperatorGrowthBound
    (ε n0Norm : ℝ) (hε : 0 < ε) (h0 : 0 ≤ n0Norm) :
    HasOperatorGrowthBound (fun _ => 0) ε n0Norm := by
  intro κ
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact pow_nonneg hε.le κ
  · exact h0

/-! ## §6. Scope of downstream bridges.

`AxiomSet.lean` and `KMSConsistency.lean` consume spectral-link hypotheses; their
projections preserve the corrected positive-frequency F4 premise. `NoCrossing.lean`
and `SDPStructure.lean` rearrange assumed bundle fields. `LDPBridge.lean` and
`SKEFTSpecialization.lean` retain their stated direction and hypotheses. None of these
uses by itself supplies a microscopic F1 window, weighted thermal F2, causal F5,
transport realization, or uniqueness. The nonzero modeled response and its holomorphy
proved here are independent of those unfulfilled physical matching obligations.
-/

end SKEFTHawking.DKMBootstrap
