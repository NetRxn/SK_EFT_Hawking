# Phase 6AH — Operational-layer strengthening & consolidation (public)

**Status:** ACTIVE (opened 2026-06-02). Public-only (`SKEFTHawking.QuantumNetwork.*`). Follows the
6AA→6AG QuantumNetwork certification arc. This phase ships high-certainty *additive* channel-distance
and fidelity substrate and closes the two rigor gaps surfaced by the cross-phase adversarial Stage-13
sweep. The two deeper analytic frontiers (constructive diamond-SDP optimal witness; fidelity-domain
data processing) are their own full phases **6AI** and **6AJ**.

**Hygiene / leak-discipline:** this is pure QI / measure-theory substrate. All theorems are neutral
mathematical objects (channel-distance bounds, fidelity identities, duality). Docstrings and naming
stay neutral pure-math — no product/positioning prose. Downstream consumers reference results by FQN;
the public side does not name or describe any downstream application.

**Invariants (hard):** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local
axiom (user sign-off required for any); no `sorry`/`maxHeartbeats`/`native_decide`. Each wave's
headline committed on main (not pushed); counts regenerated; D6/preprint prose kept in sync;
preemptive-strengthening checklist applied per theorem.

**Sequencing** (value × certainty, hardening the operational substrate earliest):
6AH.1 RB→diamond compose → 6AH.2 general-Pauli diamond → 6AH.3 diamond error budget →
6AH.4 amp-damp exact → 6AH.5 two-sided RB→diamond → 6AH.6 DEJMPS witness → 6AH.7 GHZ baseline.

---

## Wave 6AH.1 — average-fidelity → entanglement-fidelity → diamond bound (compose) 🎯

**Goal:** compose three separately-shipped pieces into ONE public theorem: an average gate fidelity
`F_avg` (an averaged benchmark — e.g. a randomized-benchmarking fidelity) bounds the worst-case
diamond distance of a channel to the ideal. Pure-math composition of Horodecki (`avgGateFidelity_eq`)
+ Fuchs–van de Graaf (`GateFidelityBridge`) + the maximally-entangled overlap.

**Chain:** invert `avgGateFidelity_eq` to `F_e = ((d+1)·F_avg − 1)/d`; identify
`entanglementFidelity K = ⟨Ω̂|(Φ⊗id)Ω|Ω̂⟩ = sqrtFidelity((Φ⊗id)Ω, Ω)²` (pure target); the bridge
`one_sub_sqrtFidelity_output_le_diamondDist` at `ρ = maxEntangled` gives `1 − √F_e ≤ diamondDist(Φ,id)`.

**Status / bricks:**
- ✅ **FOUNDATION SHIPPED** (`RBCertificate.lean`, commit `4530baa5`, kernel-pure, not root-imported
  yet): `omega_ricochet` (`⟨Ω|(A⊗1)|Ω⟩=(tr A)·1`), `kron_one_conjTranspose`, `omega_overlap_krausMap`
  (`⟨Ω|(K⊗id)Ω|Ω⟩=(n⁻¹∑ₖ tr Kₖ·tr Kₖᴴ)·1`), `omega_overlap_scalar` (`= n⁻¹∑ₖ|tr Kₖ|²`).
- 🔜 **fidelity-at-pure-state** `sqrtFidelity(ρ, maxEntangled n) = √⟨Ω̂|ρ|Ω̂⟩` — the deep brick (needs
  rank-1 trace norm `‖|u⟩⟨v|‖₁=‖u‖‖v‖` + `√(pure projector)=itself`; no reusable lemma exists).
- 🔜 `entanglementFidelity K = ⟨Ω̂|(K⊗id)Ω|Ω̂⟩` (from `omega_overlap_scalar`, `n=d`); `(id⊗id)Ω=Ω`;
  inversion algebra; HEADLINE `avgGateFidelity_diamondDist_bound`; root-import; D6/preprint; Stage-13.
**Risk:** LOW–MED (only the rank-1 trace-norm lemma is real work).

## Wave 6AH.2 — general single-qubit Pauli-channel diamond distance (NEW, Tier 1) ⭐ value/risk

**Goal:** `diamondDist(PauliChannel p, id) = 1 − p_I` (total error probability) for a Pauli channel
`Φ(ρ)=∑ᵢ pᵢ σᵢ ρ σᵢᴴ`. The Choi is Bell-diagonal, so by the same covariance argument as the named
channels the diamond distance to identity is exact. **Subsumes** dephasing (`1−(1−γ)=γ`) and
depolarizing (`1−(1−p)=p`) as special cases, covering essentially all single-qubit Pauli noise in one
exact theorem.

**Bricks:** `pauliChannel : (Fin 4 → ℝ) → Kraus tuple` (weights `p`, operators `{I,X,Y,Z}`,
`∑pᵢ=1`); `IsKrausChannel`; Choi Bell-diagonality; optimal dual witness on the `+`-eigenspace +
matching primal lower bound; `diamondDist_pauliChannel_eq` via `le_antisymm`
(`diamondDist_le_dual_witness` + a max-entangled/primal lower bound). Re-derive dephasing/depolarizing
exacts as corollaries. **Templates:** `NamedChannelDiamondExact.lean` (witnesses `γ·vvᵀ`, `(2p/3)P₊`).
**Risk:** LOW (same machinery as the shipped named-channel exacts, general weights).

## Wave 6AH.3 — diamond-norm network error budget (NEW) 🌐

**Goal:** the worst-case (diamond) analogue of the shipped trace-distance chain bound. Sub-additivity
under composition `‖Φ₁∘Φ₂ − Ψ₁∘Ψ₂‖_◇ ≤ ‖Φ₁−Ψ₁‖_◇ + ‖Φ₂−Ψ₂‖_◇`, plus diamond data-processing,
telescoping to an **N-segment budget: total worst-case error ≤ ∑ per-segment diamond errors** — the
end-to-end worst-case guarantee for a composed channel network.

**Bricks:** diamond composition sub-additivity (scout the triangle/DP primitives — `diamondDist`
metric + `le_diamondDist` + `tensorKraus` are present); `diamondDist_applyChain_le` mirroring
`traceDist_applyChain_le`. **Risk:** MED (needs a diamond-level data-processing step; interactive
lean4 scout for the composition primitive first).

## Wave 6AH.4 — amplitude-damping exact diamond distance

Upgrade `diamondDist_ampDamp` from the bracket `γ/2 ≤ ◇ ≤ γ+1−√(1−γ)` to an EXACT closed form
(optimal `γ`-dependent input + `√(1−γ)`-dependent witness; amp-damp is non-Pauli-covariant so the
max-entangled input is not optimal). If exact resists, ship a strictly-tighter bracket + document.
**Risk:** MED.

## Wave 6AH.5 — two-sided RB→diamond (NEW, completes 6AH.1)

Pair 6AH.1 with the opposite-direction bound (via `diamondDist_ge_maxEntangled` composed with the
`F_e` relation) so the average-fidelity→diamond certificate is **two-sided** — catching both ends of
the average↔worst-case relationship, not only one. **Risk:** LOW (reuses 6AH.1 + 6AH.5 scaffolding).

## Wave 6AH.6 — DEJMPS asymmetric-input pairing witness (rigor)

Close the adversarial-review gap: the only shipped DEJMPS theorem uses the symmetric Werner input
where the corrected diagonal `A²+D²` pairing COINCIDES with the naive `A²+B²`, so no theorem witnesses
the correction. `dejmps_diagonal_pairing_distinguishes` — a concrete asymmetric Bell-diagonal input
(`B ≠ D`) on which they differ and the diagonal one is correct (`norm_num`). Defensive/credibility
value. **Risk:** LOW.

## Wave 6AH.7 — GHZ randomization baseline, two-sided (rigor)

Close the 6AC defining-the-conclusion gap: derive the GHZ₃ randomization advantage `= 0` from an
explicit local-randomization model so `w3_beats_ghz_randomization_advantage` is genuinely two-sided,
or document a precise honest cited-input. Defensive/credibility value. **Risk:** LOW–MED.

---

## Phase exit
All waves shipped (or honestly documented where a sub-item is a genuine cited input), counts
regenerated, D6 §6 + preprint §3e synced, memory + Inventory updated, fresh-context Stage-13 GREEN.
Then proceed to 6AI (constructive diamond-SDP witness) and 6AJ (fidelity-domain DP).
