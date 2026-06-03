# Phase 6AH — Operational-layer strengthening & consolidation (public)

**Status:** ACTIVE (opened 2026-06-02). Public-only (`SKEFTHawking.QuantumNetwork.*`). Follows the
6AA→6AG QuantumNetwork certification arc. This phase ships the high-certainty *additive* value and
closes the two rigor gaps surfaced by the cross-phase adversarial Stage-13 sweep. The two genuine
analytic frontiers (strong-duality SDP equality; fidelity-domain data processing) are scoped as their
own full phases **6AI** and **6AJ**.

**IP boundary:** everything here is public substrate. Where a result is meant for a downstream
private consumer (Vector M certification oracle), we ship it public and *recommend* the private side
consume it by FQN — we never scope private dev into this phase.

**Invariants (hard):** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local
axiom (user sign-off required for any); no `sorry`/`maxHeartbeats`/`native_decide`. Each wave's
headline committed on main (not pushed); counts regenerated; D6/preprint prose kept in sync;
preemptive-strengthening checklist applied per theorem.

---

## Wave 6AH.1 — RB-fidelity → entanglement-fidelity → diamond certificate (item A) 🎯 HIGHEST VALUE

**Goal:** compose the three separately-shipped pieces into ONE public theorem: *a measured average
gate fidelity (e.g. from randomized benchmarking) certifies a worst-case diamond distance to the
ideal channel.* This is the bench-data→worst-case bridge as a single object — the piece the private
Vector M oracle is about to build around; shipping it public lets the private side consume it by FQN.

**Chain:** `avgGateFidelity_eq` (6AG) ⟹ invert to `F_e = ((d+1)·F_avg − 1)/d`; then
`entanglementFidelity` (Kraus-trace form) = the maximally-entangled overlap `⟨Ω|(Φ⊗id)Ω|Ω⟩`
= `sqrtFidelity((Φ⊗id)Ω, Ω)²` (since `Ω` is pure); then the bridge
`one_sub_sqrtFidelity_output_le_diamondDist` at `ρ = maxEntangled` gives
`1 − √F_e ≤ diamondDist(Φ, id)`. Substituting F_e yields the certificate.

**Bricks (each kernel-pure, committed, root-imported):**
1. **`entanglementFidelity_eq_maxEntangled_overlap`** — `entanglementFidelity K = ⟨Ω|(Φ⊗id)Ω|Ω⟩`
   (the Kraus-trace `(1/d²)∑|tr Kₖ|²` equals the maximally-entangled Choi overlap). Uses the noted-but-
   unshipped identity `(Φ⊗id)Ω = (1/n)·choiMatrix(Φ)` (`DiamondNorm.lean:135`) + `tensorKraus`.
2. **`maxEntangled_overlap_eq_sqrtFidelity_sq`** — fidelity at a pure target: `⟨Ω|ρ|Ω⟩ = sqrtFidelity(ρ,Ω)²`
   for pure `Ω` (Mathlib `Matrix`/spectral; `√(√Ω ρ √Ω)` collapses when `Ω = |ω⟩⟨ω|`).
3. **`entanglementFidelity_inverts_avgGateFidelity`** — `F_e = ((d+1)·F_avg − 1)/d` from `avgGateFidelity_eq`
   (pure algebra; `field_simp`).
4. **HEADLINE `avgGateFidelity_certifies_diamondDist`** — for a CPTP `Φ` on `d` dims,
   `diamondDist(Φ, id) ≥ 1 − √(((d+1)·avgGateFidelity Φ − 1)/d)`. Compose bricks 1–3 with the bridge.
5. Optional contrapositive (`avgGateFidelity` lower bound from a diamond upper bound) for symmetry.

**Risk:** LOW. All inputs shipped; brick 1 is the only real work (the Choi-overlap identity).
**Done:** headline proven kernel-pure; D6 §6 + preprint §3e note the composed certificate; Stage-13.

---

## Wave 6AH.2 — Amplitude-damping exact diamond distance (item C)

**Goal:** upgrade `diamondDist_ampDamp` from the bracket `γ/2 ≤ ◇ ≤ γ+1−√(1−γ)` to an EXACT closed
form, removing the lone non-exact named channel. (Recommendation to private side: bind the exact
value, not the bracket.)

**Approach:** amplitude damping is non-Pauli-covariant, so the maximally-entangled input is NOT
optimal — the optimal input is a `γ`-dependent state and the optimal dual witness is
`√(1−γ)`-dependent. Determine the exact `diamondDist(ampDamp_γ, id)` (literature value), then prove it
two-sided: lower via an explicit optimal *input* in the `sSup`, upper via the matching optimal
*dual witness* (`diamondDist_le_dual_witness`). Mathlib scouting (interactive lean4 skill) for any
needed `2×2`/`4×4` eigenvalue closed forms.

**Risk:** MEDIUM (the optimal pair is fiddly; may need a `Real.sqrt` enclosure). If the exact value
resists, ship the *tightened* bracket and document. **Done:** `diamondDist_ampDamp_eq` (or a strictly
tighter two-sided bracket), kernel-pure; D6/preprint updated; Stage-13.

---

## Wave 6AH.3 — DEJMPS asymmetric-input pairing witness (item B, rigor)

**Goal:** close the adversarial-review gap — the roadmap markets the corrected diagonal `A²+D²` DEJMPS
pairing, but the only shipped theorem uses the symmetric Werner input where the diagonal and naive
`A²+B²` pairings COINCIDE, so no theorem witnesses the correction.

**Brick:** `dejmps_diagonal_pairing_distinguishes` — exhibit a concrete *asymmetric* Bell-diagonal
input `(A,B,C,D)` with `B ≠ D` on which the diagonal-pairing output `dejmpsOutA` differs from the
naive-adjacent-pairing output, and the diagonal one is the correct/fidelity-increasing one
(`norm_num`/`nlinarith` on the explicit rationals). Makes the convention correction a *theorem*, not
just a definition.

**Risk:** LOW. **Done:** witness theorem kernel-pure; soften/ground the 6AA roadmap DEJMPS wording.

---

## Wave 6AH.4 — GHZ randomization baseline, two-sided (item F, rigor)

**Goal:** close the 6AC defining-the-conclusion gap — `ghz3RandomizationAdvantage := 0` is asserted
as a cited modeling input, making `w3_beats_ghz_randomization_advantage` one-sided.

**Brick:** derive the GHZ₃ randomization advantage `= 0` from an explicit GHZ-state local-randomization
model (the GHZ measurement statistics are randomization-invariant), so that
`w3_beats_ghz_randomization_advantage` becomes a genuine two-sided comparison `(W₃ adv > 0) ∧ (GHZ adv = 0)`
with BOTH sides derived. If the model genuinely reduces to a cited Fortescue–Lo input that cannot be
derived in-substrate, document precisely and leave as honest cited-input (no false strengthening).

**Risk:** LOW–MED. **Done:** two-sided theorem OR a precise honest-input note; Stage-13.

---

## Phase exit
All four waves shipped (or honestly documented where a sub-item is a genuine cited input), counts
regenerated, D6 §6 + preprint §3e synced, memory + Inventory updated, fresh-context Stage-13 GREEN.
Then proceed to the moonshot phases 6AI (strong-duality SDP) and 6AJ (fidelity-domain DP).
