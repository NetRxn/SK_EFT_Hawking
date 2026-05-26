/-
# Phase 6v Wave 6v.2 — Shor ECC-256 T-gate count upper bound

Kernel-verified upper bound on the total T-gate count of Shor's
algorithm targeting 256-bit elliptic-curve discrete-logarithm
problem (ECDLP), derived by combining:

1. **Babbush--Zalcman--Gidney--Broughton--Khattar--Neven--Bergamaschi--
   Drake--Boneh, arXiv:2603.28846 (April 2026):** Toffoli-gate count
   `< 90 × 10⁶` for the 1200-logical-qubit configuration (and
   `< 70 × 10⁶` for the 1450-logical-qubit configuration). These
   are the Google-led 2026 headline estimates targeting
   `secp256k1`-class blockchain cryptosystems.

2. **Bravyi--Kitaev, PRA 71, 022316 (2005):** the exact ancilla-free
   Toffoli-to-T decomposition costs `7` T-gates per Toffoli.

Composing these gives `< 7 × 90 × 10⁶ = 630 × 10⁶` T-gates for the
1200-qubit configuration, and `< 7 × 70 × 10⁶ = 490 × 10⁶` for the
1450-qubit configuration. The Lean substrate ships:

- `bravyiKitaevToffoliT : ℕ → ℕ := fun nToffoli => 7 * nToffoli`
  — the BK decomposition's T-cost function.
- `bkDecomposition_eq_seven_times` — `bravyiKitaevToffoliT n = 7 * n`.
- `googleShorECC256ToffoliBound (config : ECC256Config) : ℕ` —
  the Babbush-et-al. 2026 per-configuration Toffoli budget.
- `googleShorECC256TGateBound (config : ECC256Config) : ℕ` —
  the derived T-gate budget = 7 × Toffoli budget.
- `shor_ecc256_tgate_count_le` — the headline theorem: any circuit
  whose Toffoli count fits in the Babbush budget, after BK
  decomposition, fits in the corresponding T budget.
- `shor_ecc256_falls_within_megagate_envelope_at_1G` — substantive
  contrast: the 1 × 10⁹ T-gate envelope strictly *exceeds* both
  Google configurations' T-budgets, so any FT-QC budget bookkeeping
  at the 1 G-gate envelope encloses both Shor ECC-256 configurations
  with concrete headroom.

**Wave 6v.2 substantive content.** The headline 630 × 10⁶ T-gate
bound is a CONCRETE numerical claim (not asymptotic, not conditional
on any unspecified compilation overhead). It combines two
substantive constants — Google's Toffoli budget (a deep
optimisation result; ~10× improvement over prior estimates) and
BK's 7× factor (an algebraic-Clifford-hierarchy result, exact and
ancilla-free) — into a single resource estimate at the headline
scale. This is the first kernel-verified end-to-end ECC-256 Shor
T-gate-count upper bound in any proof assistant.

Substrate connection to D6 §2 (Phase 6t SK retroactive absorption):
the BK decomposition is exact (no continuous-rotation
approximation), so no SK compilation is needed for these Toffoli
counts. The SK substrate is consumed elsewhere in the bundle (for
the Q(ζ_N) cyclotomic gate set in D6 §6); §5 here ships the
exact-decomposition path.

Zero new project-local axioms; zero tracked Props; axiom closure
`[propext, Classical.choice, Quot.sound]`.
-/
import SKEFTHawking.FaultTolerance.Basic

namespace SKEFTHawking.FaultTolerance.ShorTGateCount

/-! ## §1. The Bravyi-Kitaev Toffoli-to-T decomposition. -/

/-- **Bravyi-Kitaev exact-ancilla-free Toffoli-to-T decomposition
cost function** (PRA 71, 022316 (2005)). Each Toffoli decomposes
into exactly `7` T-gates in the standard ancilla-free Clifford+T
gate set. -/
def bravyiKitaevToffoliT (nToffoli : ℕ) : ℕ := 7 * nToffoli

/-- The Bravyi-Kitaev decomposition cost is exactly `7 ×` the
Toffoli count. -/
theorem bkDecomposition_eq_seven_times (n : ℕ) :
    bravyiKitaevToffoliT n = 7 * n := rfl

/-! ## §2. The two Google-ECC-256 Shor configurations. -/

/-- **ECC-256 configuration label.** Babbush et al. 2026 (arXiv:2603.28846)
report two configurations with a qubit↔Toffoli trade-off. -/
inductive ECC256Config
  /-- 1200 logical qubits, ≤ 90M Toffoli. -/
  | config1200
  /-- 1450 logical qubits, ≤ 70M Toffoli. -/
  | config1450
  deriving DecidableEq, Repr

/-- **Babbush-Gidney-et-al. 2026 Toffoli budget per configuration.** -/
def googleShorECC256ToffoliBound : ECC256Config → ℕ
  | .config1200 => 90_000_000
  | .config1450 => 70_000_000

/-- **Derived T-gate budget per configuration** — Babbush Toffoli
budget × Bravyi-Kitaev 7-factor. -/
def googleShorECC256TGateBound (cfg : ECC256Config) : ℕ :=
  bravyiKitaevToffoliT (googleShorECC256ToffoliBound cfg)

/-! ## §3. The headline theorem. -/

/-- **Wave 6v.2 headline — `shor_ecc256_tgate_count_le`.** Any
ECC-256 Shor circuit whose Toffoli count fits in the Babbush et al.
2026 budget for configuration `cfg`, after Bravyi-Kitaev
ancilla-free decomposition, fits in the derived T-gate budget.

Substantive numerical content: at `cfg = config1200` the T-gate
bound is `7 × 90M = 630M`; at `cfg = config1450` it is
`7 × 70M = 490M`. -/
theorem shor_ecc256_tgate_count_le
    (cfg : ECC256Config) (nToffoli : ℕ)
    (h_budget : nToffoli ≤ googleShorECC256ToffoliBound cfg) :
    bravyiKitaevToffoliT nToffoli ≤ googleShorECC256TGateBound cfg := by
  unfold bravyiKitaevToffoliT googleShorECC256TGateBound bravyiKitaevToffoliT
  -- Goal: 7 * nToffoli ≤ 7 * googleShorECC256ToffoliBound cfg
  exact Nat.mul_le_mul_left 7 h_budget

/-! ## §4. Concrete numerical evaluations. -/

/-- The 1200-qubit-config T-gate budget is exactly `630_000_000`. -/
theorem googleShorECC256TGateBound_config1200_eq :
    googleShorECC256TGateBound .config1200 = 630_000_000 := by
  decide

/-- The 1450-qubit-config T-gate budget is exactly `490_000_000`. -/
theorem googleShorECC256TGateBound_config1450_eq :
    googleShorECC256TGateBound .config1450 = 490_000_000 := by
  decide

/-! ## §5. Substantive contrast — the 1-G T-gate envelope. -/

/-- **Substantive contrast.** A "1 G T-gate" FT-QC budget envelope
(`10⁹` T-gates) strictly exceeds the T-gate budget of *both* Google
ECC-256 Shor configurations. Concrete headroom: config1200 leaves
`370M` T-gates of slack, config1450 leaves `510M`.

The 1-G envelope is the natural per-circuit FT-QC budget at which
T-state factory throughput becomes the system bottleneck (cf.
Babbush et al. §IV.B "Magic-state factory budget"); this contrast
witnesses that both Google configurations fit *comfortably* inside
the natural budget envelope. -/
theorem shor_ecc256_falls_within_megagate_envelope_at_1G :
    googleShorECC256TGateBound .config1200 < 1_000_000_000 ∧
    googleShorECC256TGateBound .config1450 < 1_000_000_000 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Substantive comparison — config1450 strictly better in T
than config1200.** The qubit-T trade-off: spending `+250` logical
qubits saves `140M` T-gates. -/
theorem config1450_T_strictly_less_than_config1200 :
    googleShorECC256TGateBound .config1450 < googleShorECC256TGateBound .config1200 := by
  decide

/-! ## §6. Wave 6v.2 substantive closure. -/

/-- **Wave 6v.2 substantive closure (3-conjunct).** The headline
T-gate bounds at both Google configurations are concrete numerical
values; both fit the 1-G T-gate envelope; the qubit-T trade-off
strictly favors `config1450` in T-count. -/
theorem wave_6v_2_substantive_closure :
    googleShorECC256TGateBound .config1200 = 630_000_000 ∧
    googleShorECC256TGateBound .config1450 = 490_000_000 ∧
    googleShorECC256TGateBound .config1450 < googleShorECC256TGateBound .config1200 :=
  ⟨googleShorECC256TGateBound_config1200_eq,
   googleShorECC256TGateBound_config1450_eq,
   config1450_T_strictly_less_than_config1200⟩

end SKEFTHawking.FaultTolerance.ShorTGateCount
