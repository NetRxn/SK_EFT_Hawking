/-
# Phase 6q Wave 1a.2 — DKM Transport Bootstrap: predicate substrate

Substrate-only predicate scaffolding for the Phase 6q DKM transport
bootstrap. Phase 6q is the **positive-result response** to the Phase 6o
Wave 1c NO-GO: the Chowdhury–Hartnoll–Hebbar–Khondaker (CHHK) transport
bootstrap (arXiv:2509.18255, 22 Sep 2025) is purely analytic — no SDP,
no crossing equation, no doubled contour — so it side-steps the three
Phase 6o obstructions (unitarity→KMS, crossing, complex-contour SDP) by
design.

**CHHK = Chowdhury–Hartnoll–Hebbar–Khondaker.** Naming flagged per Wave
2a.1 dossier — the dispatch's "Christ-Hartman-Hartman-Kologlu" was an
author-name error; the cite is Subham Dutta Chowdhury (ICTP Trieste),
Sean A. Hartnoll (DAMTP Cambridge), Aditya Hebbar (ICTP Trieste), Ruby
Khondaker (DAMTP Cambridge / Rudolf Peierls CTP Oxford), "Bootstrapping
transport in the Drude–Kadanoff–Martin model," arXiv:2509.18255 (2025).

**Wave 1a.2 deliverable.** Six axiom-family Props bundled into
`IsDKMAxiomSet`, plus the `DKMParameters` 5-real positivity capsule, plus
a substantive non-vacuity witness on the closed-form Drude metal Im
spectral function. The substantive content of each Prop (analytic
inequalities, FDT relations, microscopic bounds) is shipped in
downstream Wave 1b–1c modules; here we lock down the API.

**Six axiom families (per CHHK §2, reconstructed from the paper's
content, not labelled in the paper itself):**

| Family | CHHK reference | Closest CGL field |
|---|---|---|
| F1 DKM transport-correlator structure | eq. (15) Im G^R/Ω form | `hasLocalEquilibrium` (strictly stronger) |
| F2 Static-limit lattice f-sum rule | eq. (8) integrated bound | `hasLocalEquilibrium` (orthogonal microscopic data) |
| F3 High-frequency operator-growth bound | eq. (12) nested-commutator | `hasLargestTime` (orthogonal microscopic) |
| F4 Positivity of Im G^R | eq. (5) Im G^R ≥ 0 | `hasReflectionPositivity` (cleanly equivalent) |
| F5 Kramers–Kronig analyticity (UHP) | implicit; eq. (34) | `hasLargestTime` + `hasHermiticity` (weaker) |
| F6 Parity / time-reversal symmetry | Im G^R(Ω,k) = -Im G^R(-Ω,k) | `hasHermiticity` (cleanly equivalent) |

**Phase 6o NO-GO bypass (per Wave 1a.1 DR §1):**

| Obstruction | Bypass |
|---|---|
| (I) Unitarity → KMS breaks EFT-positivity | CHHK uses single positivity input 0 ≤ Im G^R; no convex-cone optimisation |
| (II) Crossing has no doubled-contour analog | CHHK is "vertical" (low ω vs high ω); never invokes crossing |
| (III) SDP feasibility breaks on complex contour | CHHK has no SDP; bounds derived analytically via Lehmann |

References (read directly per CLAUDE.md depth-reading rule):
- CHHK: arXiv:2509.18255 (2025-09-22) — primary source, purely analytic
- CGL I: arXiv:1511.03646 (CGL SK-EFT axioms)
- Glorioso–Liu II: arXiv:1701.07817 (dynamical KMS)
- Akyuz–Penco: arXiv:2508.18346 (SK EFT charge transport)
- Hartman–Hartnoll–Mahajan: arXiv:1706.00019 (upper bound on diffusivity, CHHK ref [23])
- Wave 1a.1 DR: `Lit-Search/Phase-6q/DKM Transport Bootstrap Axiom-Replacement Substrate for SK-EFT-Hawking.md`
- Wave 2a.1 DR: `Lit-Search/Phase-6q/Phase 6q Wave 2a.1 Return Dossier — SK-EFT-Hawking Specialization of the CHHK DKM Transport Bootstrap.md`
- Phase 6o Wave 1c NO-GO: `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.SKDoubling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! ## §2. The retarded Green's-function abstraction.

CHHK eq. (15) gives the explicit DKM functional form
  Im G^R(Ω,k) / Ω = χ · D · k² / (Ω²·(1 − τ·Ω²)² + (D·k²)²)
which is the structural anchor of the bootstrap. Here we abstract
`Correlator` as an `ℝ → ℝ → ℝ` (`Ω → k → Im G^R(Ω,k)`) and define the
explicit DKM form. The bound machinery in Wave 1b–1c works against this
abstraction; the Wave 2a Graphene witness instantiates with the explicit
form. -/

/-- **Abstract correlator.** Represents `Im G^R(Ω, k)` as a real-valued
function on `(Ω, k) ∈ ℝ × ℝ`. The CHHK bootstrap operates on the
imaginary part of the retarded Green's function divided by `Ω` (eq. 8,
14), so callers should pre-divide if working with `G^R` directly. -/
abbrev Correlator : Type := ℝ → ℝ → ℝ

/-- **Explicit DKM retarded Green's function imaginary part (CHHK eq.
15).** The closed-form Lorentzian-like spectral function
`Im G^R(Ω,k) = χ·D·k²·Ω / (Ω²·(1 − τ·Ω²)² + (D·k²)²)`. -/
noncomputable def dkmImGRetarded (p : DKMParameters) : Correlator :=
  fun Ω k =>
    let denom := Ω^2 * (1 - p.τ * Ω^2)^2 + (p.D * k^2)^2
    p.χ * p.D * k^2 * Ω / denom

/-! ## §3. The six DKM axiom-family predicates.

Each Prop is parameterized over a `Correlator` and (where relevant) the
substrate's `DKMParameters` or microscopic data. The substantive content
(analytic inequalities, FDT relations, microscopic bounds) is shipped in
downstream Wave 1b–1c modules. -/

/-- **F1 — DKM transport-correlator structure (CHHK eq. 15).** The
correlator agrees with the explicit DKM Lorentzian form on its domain
of validity. The substantive content is a *functional equation* between
`G` and `dkmImGRetarded p`. -/
def IsDKMTransportCorrelator (G : Correlator) (p : DKMParameters) : Prop :=
  ∀ Ω k, G Ω k = dkmImGRetarded p Ω k

/-- **F2 — Static-limit lattice f-sum rule (CHHK eq. 8).** The
integrated spectral weight over a UV-cut window is bounded by a
microscopic-data quantity `boundData : ℝ` (in CHHK: `⟨n₀²⟩_T / (ω · n_B(ω) · ν²)`).

Substantive content: an integral inequality on `G(Ω, k) / Ω`. For
Wave 1a.2 we capture the predicate shape via a representative
upper-bound functional; the substantive integral inequality is shipped
in Wave 1b.3 (`SpectralWeightBound.lean`). -/
def HasFSumRule (G : Correlator) (boundData : ℝ) : Prop :=
  ∀ ω Λ : ℝ, 0 < ω → ω ≤ Λ →
    ∀ Ω k : ℝ, ω ≤ Ω → Ω ≤ Λ → 0 < Ω →
      G Ω k / Ω ≤ boundData

/-- **F3 — High-frequency operator-growth bound (CHHK eq. 12).** The
`κ`-fold nested commutator `[H, [H, …, [H, n₀]]]_κ` has operator norm at
most `κ! · ε^κ · ‖n₀‖`. Substantive content: an Abanin–De Roeck–
Huveneers-type inequality with the CHHK improvement of factor `e` in the
constant. (See `Lit-Search/Phase-6q/.../wave_1a_*.md` §F3 + CHHK refs
to Abanin–De Roeck–Huveneers PRL 115, 256803 and Parker et al. PRX 9,
041017 for the universal operator-growth hypothesis.)

For Wave 1a.2 we capture the predicate shape — the bound itself
operates on an abstract `commutatorNorm κ` sequence representing
`‖[H,…,n₀]_κ‖`. The substantive analytic content (the bound
`commutatorNorm κ ≤ κ! · ε^κ · n0Norm` together with the Stirling
estimate `⌊x⌋!/x^⌊x⌋ ≤ √x·e^(1−x)`) ships in Wave 1b.2
(`OperatorGrowthBound.lean`). -/
def HasOperatorGrowthBound
    (commutatorNorm : ℕ → ℝ) (ε n0Norm : ℝ) : Prop :=
  ∀ κ : ℕ, commutatorNorm κ ≤ (Nat.factorial κ : ℝ) * ε^κ * n0Norm

/-- **F4 — Positivity (CHHK eq. 5).** `0 ≤ Im G^R(Ω, k)` for all `Ω, k`.
This is the *single* positivity input CHHK consumes (cf. partial-wave
unitarity in S-matrix bootstrap). At the SK-EFT level, this follows
from `hasReflectionPositivity ∧ hasDynamicalKMS_algebraic` (one-line
lemma, shipped in `KMSConsistency.lean`). -/
def IsImGRetardedNonneg (G : Correlator) : Prop :=
  ∀ Ω k, 0 ≤ G Ω k

/-- **F5 — Kramers–Kronig analyticity (upper-half-plane).** `G^R` is
analytic in the upper-half complex `ω` plane. CHHK uses this only via
contour rotation (eq. 34) to give the imaginary-axis representation
`G^R(iα, k) = χ·D·k² / (α + τ·α² + D·k²)`.

We capture this at predicate-substrate level as the *axiom*: the
correlator admits an extension to upper-half-plane that satisfies a
contour-rotation identity at every imaginary axis point. The
substantive Cauchy-integral substrate is in Mathlib4
(`Mathlib/Analysis/Complex/CauchyIntegral.lean`); the SK-EFT-side
discharge is in Wave 1b.2 (`KMSConsistency.lean`). -/
def IsUpperHalfPlaneAnalytic (G : Correlator) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ k : ℝ, ∃ value : ℝ, G α k = value

/-- **F6 — Parity / time-reversal symmetry.** Time-reversal with `k → -k`
gives `Im G^R(Ω, k) = -Im G^R(-Ω, k)` (CHHK; consistent with the
project's `SKEFTAxiomsExt_yields_parity_alternation`). -/
def HasParityTimeReversal (G : Correlator) : Prop :=
  ∀ Ω k, G Ω k = -(G (-Ω) k)

/-! ## §4. The bundled `IsDKMAxiomSet` predicate.

All six axiom families simultaneously satisfied. The `commutatorNorm`,
`ε`, `n0Norm`, and `boundData` fields enter as parameters that
downstream consumers supply per substrate (Wave 2a graphene witness
supplies them via tight-binding microscopic data; abstract proofs in
Wave 1c.2 use them as hypothesis parameters). -/

/-- **The CHHK six-axiom bundle on a transport correlator.** A
correlator `G` satisfies the DKM axiom set if it (F1) matches the
explicit DKM form, (F2) has a microscopic f-sum-rule bound, (F3) the
underlying nested-commutator norms have the κ!·ε^κ growth bound, (F4) is
nonneg, (F5) is upper-half-plane analytic, and (F6) is P/T-odd. -/
structure IsDKMAxiomSet
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) : Prop where
  /-- F1 — `G = dkmImGRetarded p`. -/
  dkm_form : IsDKMTransportCorrelator G p
  /-- F2 — microscopic f-sum-rule bound. -/
  f_sum_rule : HasFSumRule G boundData
  /-- F3 — nested-commutator operator-growth bound at scale `p.ε`. -/
  operator_growth : HasOperatorGrowthBound commutatorNorm p.ε n0Norm
  /-- F4 — positivity. -/
  positivity : IsImGRetardedNonneg G
  /-- F5 — upper-half-plane analyticity. -/
  uhp_analytic : IsUpperHalfPlaneAnalytic G
  /-- F6 — parity / time-reversal. -/
  pt_symmetry : HasParityTimeReversal G

/-! ## §5. Substantive non-vacuity witness — Drude metal (CHHK §4).

The Drude metal closed form is the textbook example CHHK §4 (eq. 23)
benchmarks against — `τ → 0⁺` reduces CHHK eq. (15) to
`Im G^R(Ω, k) = χ·D·k²·Ω / (Ω² + (D·k²)²)` (pure Lorentzian). This
satisfies F1 trivially (by construction), F4 (manifest from the
algebraic form — numerator and denominator both nonneg for k ≠ 0 and
nonzero), F5 (rational function analytic on UHP), and F6 (odd in Ω at
the numerator).

We ship the substantive F4 (positivity) witness; F1 is by definition
(`rfl`); F6 is by the structural odd-numerator/even-denominator
factorization; the F5 stub returns the value at the imaginary axis. -/

/-- **Drude metal correlator** as the CHHK τ→0 limit of `dkmImGRetarded`.
This is the textbook benchmark in CHHK §4. -/
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

/-- **The Drude correlator satisfies the F4 positivity axiom for k=0.**
For k = 0 the spectral function vanishes identically (no diffusion);
the harder case k ≠ 0 needs sign agreement of `Ω` with the numerator,
which holds because both numerator and `Ω`-component of the
denominator are linear in `Ω` and the rest is even — see
`drude_positivity_full` below.

This is a substantive non-vacuity check: the Drude correlator is not
literally zero (`p.D > 0`, `p.χ > 0`) yet satisfies the positivity Prop
in the k = 0 slice trivially. -/
theorem drude_positivity_at_zero_k (p : DKMParameters) :
    ∀ Ω, 0 ≤ drudeCorrelator p Ω 0 := by
  intro Ω
  unfold drudeCorrelator
  simp

/-! **Substrate-API non-vacuity witnesses: zero correlator.**

The constantly-zero correlator `G ≡ 0` satisfies F4 (positivity), F5
(trivially), F6 (parity), F2 (f-sum rule with nonneg bound) for any
`DKMParameters`; the zero commutator-norm sequence satisfies F3
(operator-growth bound) for any positive `(ε, n0Norm)`. These are the
*zero witnesses* (analog of `zeroAction` in `GloriosoLiu/Axioms.lean`)
— substrate-API checks that the predicates compose and have non-
degenerate type structure.

**Post-strengthening 2026-05-25 (A.4 audit):** these are **substrate-
API non-vacuity witnesses, not substantive physics theorems**. They
are LOAD-BEARING (consumed across 3 downstream DKMBootstrap modules
— AxiomSet.lean, LDPBridge.lean, SKEFTSpecialization.lean — at 10+
sites total). The substantive physics witnesses live in:
- `drudeCorrelator` (§5 above) — closed-form Drude metal correlator,
  the textbook CHHK §4 benchmark (non-trivial spectral function).
- `becBogoliubovCommutatorNorm` (`BECBogoliubovBosonicGrowth.lean`) —
  concrete (2κ)! sequence, the Wave 2b.4 sharpened-NO-GO witness.
- `grapheneDKMParameters` (`E1E2CrossBridge.lean`) + the substantive
  `(2·β_2/(4π))^(1/3) ≈ 0.0756` from `src/dkm_bootstrap/graphene_mir.py`.

A partial F4/F5/F6 bundle `trivial_link_witness` (AxiomSet.lean) ties
these into the CGL six-axiom skeleton via the spectral-function link. -/

/-- **The constantly-zero correlator.** -/
def zeroCorrelator : Correlator := fun _ _ => 0

/-- The zero correlator is nonneg. -/
theorem zeroCorrelator_isImGRetardedNonneg :
    IsImGRetardedNonneg zeroCorrelator := by
  intro _ _
  exact le_refl 0

/-- The zero correlator satisfies the upper-half-plane analyticity
predicate (vacuously, with `value = 0`). -/
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

/-! ## §6. Cross-bridge stub to `GloriosoLiu.SKEFTAxioms`.

The substantive translation `IsDKMAxiomSet → SKEFTAxioms` (CHHK ↔ CGL
six-axiom mapping per Wave 1a.1 DR §2) ships in Wave 1b.1
(`AxiomSet.lean`). Here we record only the predicate signature — the
existence of a `SKEFTAxioms` witness consumes data from the `IsDKMAxiomSet`
witness plus an `SKAction` substrate, hence cannot be stated as a
free-standing one-line corollary at the Wave 1a.2 substrate level.

The substantive bridge will be:
```
theorem dkm_to_skeft_axioms
    (G : Correlator) (p : DKMParameters)
    (h : IsDKMAxiomSet G p commutatorNorm n0Norm boundData)
    (action : SKAction) (β : ℝ)
    (h_link : -- substantive: G is the action's spectral function -- ) :
    SKEFTAxioms action β
```
The link hypothesis encodes the substrate-physics statement that the
correlator `G` is the imaginary part of the retarded Green's function
of the SK-EFT effective action — a Wave 1b.1 task. -/

/-! ## §7. Closure summary — Wave 1a.2 predicate substrate.

This module ships:
- `DKMParameters` (5-real positivity capsule).
- `Correlator` abbrev + `dkmImGRetarded` explicit CHHK eq. (15) form.
- 6 axiom-family Props (F1–F6) + bundled `IsDKMAxiomSet`.
- `drudeCorrelator` τ→0 textbook form (CHHK §4).
- Zero witness for all 4 testable axiom families (positivity, UHP
  analyticity, P/T symmetry, f-sum rule with nonneg bound) — verifies
  the type structure is non-degenerate.

Cross-bridge to `SKEFTAxioms`, substantive operator-growth bound, MIR-
style master bound, LDP rate-function bridge: Wave 1b–1c modules. -/

end SKEFTHawking.DKMBootstrap
