/-
# Phase 6q Wave 1c.3 — DKM Transport Bootstrap: LDP cross-bridge

Wave 2a.1 DR §6 motivates relating the DKM response to fluctuations.
Connects three substantive pieces of the program's substrate:
1. The Phase 6q DKM transport-bootstrap framework (`DKMBootstrap.*`).
2. The Phase 6n Wave 2c+ `IsLDPRateFunction` class (`CrooksAnalogHawking.LDPLinearResponse`).
3. The modeled variance parameter `χ·D` for the centered
   linear-response rate function.

The class witness follows from positivity of the DKM parameters and the
existing W-form Gallavotti–Cohen result. The forward compatibility
statement carries an unused F4 premise. The reverse existential uses
the zero correlator. The microscopic identification remains open.

**Wave 1c.3 deliverables:**
1. **`DKMToLDPData`** — substantive construction: given a DKM parameter
   capsule + a positive inverse temperature β, build an
   `LDPLinearResponseData` with variance parameter `σ² := p.χ · p.D`.
2. **`dkm_rate_function`** — the LDP rate function naturally associated
   with `p` at temperature β (the centered linear-response Gaussian
   with variance `p.χ · p.D`).
3. **`dkm_rate_function_is_LDPRateFunction`** — the load-bearing
   substantive theorem: `dkm_rate_function β p` satisfies
   `IsLDPRateFunction β`. Discharged via the existing `Fact`-based
   instance in `LDPLinearResponse.lean` lifted to the DKM substrate.
4. **`chhk_positivity_yields_LDP_rate_function`** — compatibility
   interface retaining the historical forward declaration signature.

References:
- Wave 2a.1 DR §6: cross-bridge to IsLDPRateFunction (load-bearing
  LDP cross-bridge of Phase 6q per DR §6 framing)
- Wave 1a.1 DR §3 (LB4): IsLDPRateFunction instantiation, ~60 LOC
- `SKEFTHawking.CrooksAnalogHawking.LDPLinearResponse`:
  `IsLDPRateFunction`, `linearResponseRateFunctionCentered`
- CHHK arXiv:2509.18255v2 Eq. (5): effective conductivity limit
-/
import SKEFTHawking.DKMBootstrap.LinearFunctionals
import SKEFTHawking.CrooksAnalogHawking.LDPLinearResponse

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.CrooksAnalogHawking

/-! ## §1. DKM → LDP data construction.

Given a DKM parameter capsule `p` (with positive `χ, D` etc.) and an
inverse temperature `β > 0`, we construct an `LDPLinearResponseData`
witness with the modeled variance parameter `σ² := p.χ · p.D`.
Establishing a physical fluctuation-dissipation relation for a state
requires evidence beyond the effective conductivity limit. -/

/-- **DKM → LDP linear-response data construction.** Maps a DKM
parameter capsule `p` and a positive inverse temperature `β` to an
`LDPLinearResponseData` witness with `σ² := p.χ · p.D`. -/
noncomputable def DKMToLDPData (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    LDPLinearResponseData where
  β := β
  σ_sq := p.χ * p.D
  β_pos := hβ
  σ_sq_pos := mul_pos p.χ_pos p.D_pos

/-- The DKM-LDP variance is strictly positive. -/
theorem DKMToLDPData.σ_sq_pos (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    0 < (DKMToLDPData β hβ p).σ_sq := by
  unfold DKMToLDPData
  exact mul_pos p.χ_pos p.D_pos

/-- The DKM-LDP variance is nonzero. -/
theorem DKMToLDPData.σ_sq_ne_zero (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    (DKMToLDPData β hβ p).σ_sq ≠ 0 :=
  (DKMToLDPData.σ_sq_pos β hβ p).ne'

/-! ## §2. The DKM rate function and its LDP witness. -/

/-- **The DKM rate function** naturally associated with `(β, p)`: the
centered linear-response Gaussian with variance `p.χ · p.D`. -/
noncomputable def dkm_rate_function (β : ℝ) (p : DKMParameters) :
    ℝ → ℝ :=
  linearResponseRateFunctionCentered β (p.χ * p.D)

/-- **The DKM rate function vanishes at the no-work event.** -/
@[simp]
theorem dkm_rate_function_zero (β : ℝ) (p : DKMParameters) :
    dkm_rate_function β p 0 = 0 :=
  linearResponseRateFunctionCentered_zero β (p.χ * p.D)

/-- **The DKM rate function satisfies W-form Gallavotti–Cohen at β.** -/
theorem dkm_rate_function_satisfies_WFormGC
    (β : ℝ) (p : DKMParameters) :
    WFormGallavottiCohen β (dkm_rate_function β p) := by
  unfold dkm_rate_function
  exact linearResponseRateFunctionCentered_satisfies_WFormGC β (p.χ * p.D)
    (mul_pos p.χ_pos p.D_pos).ne'

/-! ## §3. The substantive `IsLDPRateFunction` instance. -/

/-- **The DKM rate function is an `IsLDPRateFunction` witness at β.**
The constructed rate function carries the abstract LDP class.

The two class fields:
- `zero_at_zero` — `dkm_rate_function β p 0 = 0` (by construction).
- `wForm_gc` — W-form GC at β (substantively, via the existing
  `linearResponseRateFunctionCentered_satisfies_WFormGC`). -/
theorem dkm_rate_function_is_LDPRateFunction
    (β : ℝ) (p : DKMParameters) :
    IsLDPRateFunction β (dkm_rate_function β p) where
  zero_at_zero := dkm_rate_function_zero β p
  wForm_gc := dkm_rate_function_satisfies_WFormGC β p

/-! ## §4. Forward compatibility interface from Wave 2a.1 DR §6. -/

/-- The parameterized function is an `IsLDPRateFunction` witness.
The supplied F4 premise and temperature sign are unused. -/
theorem chhk_positivity_yields_LDP_rate_function
    {G : Correlator} (_h_pos : IsImGRetardedNonneg G)
    (β : ℝ) (_hβ : 0 < β) (p : DKMParameters) :
    IsLDPRateFunction β (dkm_rate_function β p) :=
  dkm_rate_function_is_LDPRateFunction β p

/-! ## §4.5. Reverse direction (Wave 2b.2 per DR §6).

The original Wave 2a.1 DR §6 task proposed this implication for
a specified correlator:

    `IsLDPRateFunction (dkm_rate_function β p) → IsImGRetardedNonneg G`
    *under action-correlator link.*

The "under action-correlator link" qualifier means: `G` is the spectral
function of the SK-EFT effective action whose Wilson coefficients live
in `DKMParameters`. The substantive D1-paper SK-Green's-function link is
**deferred** to the D1 lift-to-Lean wave (out of Phase 6q scope per Wave
2a.1 DR §4 PARTIAL-VIABLE alignment-only verdict).

The implemented existence interface uses the zero correlator
independently of the supplied rate-function witness. -/

/-- **Reverse direction (substrate-level existence form).** Wave 2b.2 per
Wave 2a.1 DR §6 — IsLDPRateFunction → ∃ F4-compatible correlator.

For any DKM substrate `(β, p)` where the natural rate function is an
LDP rate function, there exists an F4-compatible correlator on the same
substrate. Witnessed by the zero correlator (via
`zeroCorrelator_isImGRetardedNonneg`).

This is the substrate-level reverse direction of the Wave 2a.1 DR §6
biconditional. The substantive "under action-correlator link" form is
deferred to the D1 lift-to-Lean wave (out of Phase 6q scope). -/
theorem LDP_rate_function_yields_F4_compatible_correlator_existence
    (β : ℝ) (_hβ : 0 < β) (p : DKMParameters)
    (_h_ldp : IsLDPRateFunction β (dkm_rate_function β p)) :
    ∃ G : Correlator, IsImGRetardedNonneg G :=
  ⟨zeroCorrelator, zeroCorrelator_isImGRetardedNonneg⟩

/-- **Wave 2b.2 equivalence of independently available witnesses.**

⚠️ **SUBSTRATE LEVEL ONLY** — both sides of this biconditional hold
unconditionally on every well-formed DKM substrate (the forward direction
via the constructed Gaussian rate function, the reverse direction via the
ever-available zero-correlator witness). The biconditional therefore
asserts an *architectural* equivalence at the substrate-existence level,
NOT a substantive content-bearing biconditional on a specific correlator.
The substantive "under action-correlator link" biconditional — pinning a
specific `G` to the SK-EFT effective action's spectral function — is the
D1-deferred follow-on (`feedback`: a future biconditional name should make
the substrate vs action-link distinction explicit; current name retained
for downstream-API stability).

For any DKM substrate `(β, p)`:
    (∃ G : Correlator, IsImGRetardedNonneg G)  ↔  IsLDPRateFunction β (dkm_rate_function β p) -/
theorem chhk_F4_existence_iff_LDP_rate_function_holds
    (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    (∃ G : Correlator, IsImGRetardedNonneg G) ↔
      IsLDPRateFunction β (dkm_rate_function β p) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨G, h_F4⟩
    exact chhk_positivity_yields_LDP_rate_function h_F4 β hβ p
  · intro h_ldp
    exact LDP_rate_function_yields_F4_compatible_correlator_existence β hβ p h_ldp

/-! ## §5. Zero-correlator control and parameter-only class witness. -/

/-- Instantiate the compatibility interface at the zero correlator. -/
theorem zero_correlator_yields_LDP_rate_function
    (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    IsLDPRateFunction β (dkm_rate_function β p) :=
  chhk_positivity_yields_LDP_rate_function
    zeroCorrelator_isImGRetardedNonneg β hβ p

/-- The historical name refers to the proposed CGL connection. The
proof uses the parameters and the existing rate-function witness. -/
theorem skeft_axioms_yields_LDP_rate_function
    (β : ℝ) (_hβ : 0 < β) (p : DKMParameters) :
    IsLDPRateFunction β (dkm_rate_function β p) := by
  exact dkm_rate_function_is_LDPRateFunction β p

/-! ## §6. Closure summary — Wave 1c.3 LDP cross-bridge.

This module ships:
- **`DKMToLDPData`** — substantive construction of LDP linear-response
  data from DKM parameters + positive inverse temperature, with
  the modeled variance parameter `σ² := p.χ · p.D`.
- **`dkm_rate_function`** — the centered linear-response Gaussian on
  the DKM substrate.
- **`dkm_rate_function_is_LDPRateFunction`** — the load-bearing
  substantive theorem: DKM rate function is an `IsLDPRateFunction`
  witness at the corresponding β (Phase 6n abstract LDP class
  instantiated on Phase 6q DKM substrate).
- **`chhk_positivity_yields_LDP_rate_function`** — compatibility
  interface for the parameter-only class witness.
- **Zero-correlator and existence controls** use independent witnesses.
  The link to a specific action and its microscopic fluctuations remains
  open.

Track 2 (SK-EFT-Hawking specialization) opens next — Wave 2a.2
`SKEFTSpecialization.lean` + Wave 2a.3 platform cross-bridge. -/

end SKEFTHawking.DKMBootstrap
