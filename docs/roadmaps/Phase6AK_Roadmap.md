# Phase 6AK — Physical-limit & impossibility substrate (public)

**Status:** ✅ COMPLETE (2026-06-03). All 6 waves shipped kernel-pure, Stage-13 GREEN, NO fences,
NO new axioms. Final counts 10721 thm / 0 axiom / 0 sorry / 814 mod. Commits on `main` (not pushed):
6AK.1 `fb8a77f4` (CoherenceFidelity — coherence-limited avgGateFidelity = ½+⅙e^{−t/T1}+⅓e^{−t/(2T1)−t/T2},
antitone ceiling) · 6AK.3 `5d893c61` (ErrorBasisDiamond — dimension-general unitary-error-basis exact
diamond distance 1−p₀; instances: single-qubit Pauli re-derived as n=2, two-qubit Pauli n=4) ·
6AK.6 `4d0fa74b` (SpamProcessFidelity — SPAM bit-flip diamond=q, process=entanglement fidelity bridge) ·
6AK.5 `cc29f5d8` (QECSuppression — abstract code-distance threshold theorem, IP-clean) ·
6AK.2 `da8f6470` (PLOBRateBound — repeaterless rate-bound function + loss-penalty properties, honestly
labeled surrogate) · 6AK.4 `e70dc6ea` (GeneralizedAmpDamp — thermal GAD two-sided bracket
(1−N)γ ≤ ◇ ≤ 1, lower exact-achievable). Leakage (qutrit) noted as a natural extension via the GAD
technique (deferred). D6 §6 + preprint §3g synced (D6 LaTeX compile-clean) for every wave.

**Precision notes (delivery boundaries — exactly what is and is not Lean-verified):**
- *6AK.1 is an equality, not a physical-gate ceiling.* `avgGateFidelity_coherenceChannel = …` is exact
  for the model channel `𝒜_γ∘𝒟_p`. Treating it as an upper bound on a real gate's `F_avg` is a
  modelling assumption (coherence-limited noise = best case), NOT in the theorem. Docstrings + D6/
  preprint prose now state this explicitly.
- *6AK.4's `◇ ≤ 1` upper is the trivial CPTP cap* (`diamondDist_le_one`), carrying no GAD-specific
  information; the substantive verified content is the exact-achievable lower `(1−N)γ`. A tight GAD
  upper is intentionally left to the dual-witness route (`diamondDist_le_dual_witness`, Phase 6AI) — the
  eigenvector-witness exact (à la the amp-damp exact in `NamedChannelDiamondExact`) is deliberately not
  pursued here.

**Original plan (DRAFT, opened 2026-06-03):** Public-only (`SKEFTHawking.QuantumNetwork.*`). Follows the
6AA→6AJ QuantumNetwork certification arc. Where 6AA–6AH shipped *consistency* substrate (bounds a
quantity must satisfy), this phase ships **physical-limit substrate**: closed-form ceilings/floors
that an achievable quantity provably *cannot cross*. Downstream these enable "a claim that beats this
limit is physically impossible" certificates — but, per leak-discipline, the public side states only
the neutral mathematical bound.

**Hygiene / leak-discipline (hard):** pure QI / measure-theory / QEC math. All theorems are neutral
objects (fidelity ceilings, channel-distance values, rate bounds, code-distance error relations).
Docstrings/naming stay neutral pure-math — **no product/positioning/"impossibility-certificate"
prose, no downstream-application naming.** Downstream consumers reference results by FQN only.

**Invariants (hard):** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local
axiom without explicit user sign-off** (Pipeline Invariant #15); no `sorry`/`maxHeartbeats`/
`native_decide`. Each wave headline committed on `main` (not pushed); counts regenerated
(`scripts/update_counts.py`); D6/preprint prose synced; preemptive-strengthening checklist per theorem.
Mathlib scouting via the **interactive lean4 MCP loop** (`lean_leansearch`/`lean_loogle`/`lean_goal`/
`lean_multi_attempt`), NOT deep research. Fence only with a grep-verified written blocker + a 2–4
agent fan-out (FENCE-DISCIPLINE), never a hand-wave.

**Sequencing (value × certainty, lowest-risk first):**
6AK.1 coherence-limited fidelity ceiling → 6AK.3 two-qubit/crosstalk diamond → 6AK.4 thermal/leakage
channels → 6AK.5 code-distance error relation (QEC, IP-bounded) → 6AK.2 repeaterless rate bound
(moonshot) → 6AK.6 SPAM / process-fidelity completeness.

---

## Wave 6AK.1 — coherence-limited average-gate-fidelity ceiling 🎯 (LOW risk, do first)

**Goal:** a public closed-form **upper bound on `avgGateFidelity`** for a gate of duration `t` on a
qubit with relaxation/dephasing characterized by `T1`, `T2` (i.e. the best fidelity physics permits
given decoherence). Concretely, for the coherence-limited channel `Φ_{t}` (amplitude damping with
`γ = 1 − e^{−t/T1}` composed with dephasing `p = (1 − e^{−t/T2})/2`, both already defined in
`NamedChannels`/6AH), prove

  `avgGateFidelity (Φ_t) = (d·F_e + 1)/(d+1)`  with `F_e` the (computable) entanglement fidelity of
  `Φ_t`,  hence  `avgGateFidelity (Φ_t) ≤ G(t, T1, T2)` for an explicit decreasing `G`.

**Chain:** `Φ_t` is a fixed Kraus channel → its `entanglementFidelity` is a closed form in the Kraus
traces (`avgGateFidelity_eq` / `kraus_normSq_sum`, both shipped 6AG) → bound below by monotonicity in
`γ, p`. The simplest shippable form: `avgGateFidelity (ampDampKraus γ) ≤ 1 − γ/(something)`; generalize
to the composed coherence channel. Reuse `GateFidelity.lean`, `NamedChannels.lean`.
**Acceptance:** a kernel-pure theorem giving an explicit `avgGateFidelity ≤ G(t,T1,T2)` (or the
exact `avgGateFidelity` of the coherence channel as a closed form, from which the ceiling follows by
`exp` monotonicity); D6/preprint note. **Risk:** LOW (all machinery shipped in 6AG/6AH).

---

## Wave 6AK.3 — two-qubit / general n-qubit Pauli-channel diamond distance 🎯 (LOW–MED risk)

**Goal:** generalize 6AH.2 (`diamondDist_pauliKraus_eq = 1 − p₀`, single-qubit) to the **two-qubit
Pauli channel** (16 Pauli weights), proving `diamondDist (twoQubitPauliKraus p) id = 1 − p₀₀` (total
error probability). This covers the dominant real-device error (two-qubit gate / crosstalk).
**Chain:** the single-qubit proof in `PauliChannel.lean` is weight-general over the 4 Bell blocks via
orthogonality `BᵢBⱼ = 2δᵢⱼBᵢ`; the two-qubit case is the Kronecker square — 16 Bell blocks, same
orthogonality + positive-part dual witness. Reuse `PauliChannel.lean` machinery; index `Fin 4 × Fin 4`.
**Acceptance:** kernel-pure `diamondDist (twoQubitPauliKraus p) (idKrausPad 15 4) = 1 − p 0`; the
single-qubit result re-derived as the `d=2` factor. **Risk:** LOW–MED (16-way orthogonality bookkeeping;
the `2d` Kronecker-of-Bell-blocks structure is mechanical but larger).

---

## Wave 6AK.4 — thermal (generalized amplitude damping) + leakage channels (MED risk)

**Goal:** exact or two-sided-bracket diamond distances for two more physically-important named
channels: **generalized amplitude damping** (finite-temperature relaxation, params `γ, N`) and a
**leakage channel** (qubit → a third level; qutrit Kraus). Each `diamondDist(·, id)` as a closed form.
**Chain:** GAD is the amp-damp template (`NamedChannelDiamondExact.lean`) with a thermal mixing weight;
leakage needs a `Fin 3` carrier + an `idKrausPad`-style embedding. **Acceptance:** kernel-pure exact
value or honest two-sided bracket per channel + docstring hedge if bracket. **Risk:** MED (leakage
qutrit Choi/witness is new; GAD is close to amp-damp).

---

## Wave 6AK.5 — code-distance physical→logical error relation (QEC; IP-BOUNDED) (MED risk)

**Goal:** a public, **general** stabilizer-QEC relation between physical error rate `p` and logical
error rate `p_L` for a distance-`d` code — the standard suppression form
`p_L ≤ A·(p/p_th)^{⌊(d+1)/2⌋}` (or the threshold-existence statement), as neutral QEC math.
**⚠️ IP boundary (critical):** keep this **general code-capacity / threshold-form math only**. Do NOT
import, restate, or mirror any compiler/accuracy-threshold-specific result that lives in a downstream
private project — scope this wave to the textbook code-distance suppression bound and STOP. If it would
overlap existing non-public substrate, **shrink the wave to just the combinatorial suppression
inequality** (a `norm_num`/`Nat`-power statement) and flag it.
**Acceptance:** a kernel-pure suppression/threshold inequality for an abstract `(p, p_th, d)`; no
device/compiler-specific content. **Risk:** MED (and bounded deliberately to stay general + IP-clean).

---

## Wave 6AK.2 — repeaterless secret-key / entanglement rate bound (PLOB-type) 🌙 (HIGH risk, moonshot)

**Goal:** a public upper bound on the two-way-assisted secret-key/entanglement rate of a lossy channel
of transmissivity `η` — the repeaterless (PLOB-type) limit `rate ≤ −log₂(1 − η)`, or a tractable
formalizable surrogate.
**Wave 6AK.2.0 = interactive lean4 Mathlib scout** (bosonic channels? relative-entropy of
entanglement? channel capacity? log-negativity? — almost certainly absent). Decide route:
(a) a **discrete/finite** no-go surrogate (e.g. a data-processing/no-signaling rate inequality that
captures the loss penalty) that IS formalizable, or (b) the relative-entropy-of-entanglement upper
bound restricted to a tractable family, or (c) **FENCE** with a grep-verified written blocker + fan-out.
**Acceptance:** EITHER a kernel-pure rate bound (even a restricted/surrogate form, honestly labeled) OR
a fenced, documented blocker (no axiom without sign-off). **Risk:** HIGH (continuous-variable capacity
theory is far from Mathlib; treat as a genuine research wave, scout before committing time).

---

## Wave 6AK.6 — SPAM / measurement-error & process-fidelity completeness (LOW–MED risk)

**Goal:** round out the device-claim substrate: (a) a **measurement (SPAM) error** channel-distance
bound, and (b) confirm/expose `process fidelity = entanglement fidelity` as a named lemma so process-
fidelity claims bind directly. **Chain:** SPAM as a classical-ish bit-flip POVM distance; process-
fidelity is definitional from `entanglementFidelity` (6AG). **Acceptance:** kernel-pure bounds/lemmas.
**Risk:** LOW–MED.

---

## Follow-on backlog (post-6AK; opened 2026-06-03, NOT yet built)

Two genuine new-theorem items deferred from the main phase. Neither blocks anything; both are honest
extensions, not fence-repairs. Tracked here so they are explicit rather than implicit "deferreds".

### FU-1 — Qutrit Weyl-Heisenberg leakage channel: exact diamond distance ✅ COMPLETE 2026-06-03

**Status: SHIPPED, kernel-pure, NO new axioms, Stage-13 GREEN.** New module `QutritWeyl.lean`
(`SKEFTHawking.QuantumNetwork`). Headline `diamondDist_weylKraus_eq : diamondDist (weylKraus p)
(idKrausPad 8 3) = 1 − p 0` (the `n = 3` instance of `diamondDist_errorBasisKraus_eq`, dropped out free
once the `weyl3UEB : UnitaryErrorBasis 3 8` instance was built). Named instance
`diamondDist_shiftLeakage_eq : diamondDist (weylKraus (shiftLeakageWeights q)) (idKrausPad 8 3) = q`
(pure cyclic-shift `X = W_{1,0}` leakage, diamond distance = leakage probability `q`). Both verified
`{propext, Classical.choice, Quot.sound}` only. The entry-formula `weylOp a b = Matrix.of (fun i j =>
if i = j + a then ω^(b·j) else 0)` de-risked it exactly as planned: the only real proof was
`weyl_trace_orthonormal` via the cube-root sum `weyl_phase_sum` (`∑_x conj(ω^{bx})·ω^{dx} = 3·⟦b=d⟧`,
reduced to `ω^{(2b+d)x}` + `3∣(2b+d) ⟺ b=d` by `omega`). Reusable bricks: `omega3_conj`
(`conj ω = ω²` via `RCLike.mul_conj` + `ω³=1` cancellation), `cube_geom_zero` (any `ζ³=1, ζ≠1 ⟹
1+ζ+ζ²=0`). D6 §6 + preprint §3g prose added; D6 LaTeX compile-clean (11 pp). Counts/validate
(axiom_closure_allowlist + graph_integrity) GREEN.

**Original goal (for reference).** Instantiate the 6AK.3 `UnitaryErrorBasis` framework at `n = 3` with the 9 qutrit
Weyl–Heisenberg (clock–shift) operators, yielding `diamondDist (weylKraus p) (idKrausPad 8 3) = 1 − p₀`
**for free** from `diamondDist_errorBasisKraus_eq`. A qutrit **leakage** channel (population escaping the
qubit `{0,1}` subspace into level `2`) is then a specific weight choice, with diamond distance = total
leakage probability. This is the "leakage" half of Wave 6AK.4, delivered exactly (not bracketed).

**Key simplification (de-risks the whole thing).** Define the basis operators by their **entry formula**
— `weylOp a b = Matrix.of (fun i j => if i = j + a then ω^(b·j) else 0)`, `ω = e^{2πi/3}` — so the three
`UnitaryErrorBasis` fields reduce to direct `∑`-over-`Fin 3` computations with **no matrix powers** and
no heavy `IsPrimitiveRoot` machinery. `op_zero` = `1` (a=b=0). `op_unitary` uses `|ω|=1`. `op_orthonormal`
`tr((weylOp a b)ᴴ (weylOp c d)) = 3·δ_{ac}δ_{bd}` reduces to `δ_{ac} · ∑_{i:Fin 3} ω^{(d−b)i}`, and the
**only nontrivial fact** is the cube-root geometric sum `∑_{i<3} ω^{ki} = 3·⟦3∣k⟧` (from `ω³=1`,
`1+ω+ω²=0`). **Acceptance:** kernel-pure `diamondDist_weylKraus_eq = 1 − p₀` + a named leakage instance.
**Risk:** MED (the ω-sum + the `i = j + a` cyclic-`Fin 3` bookkeeping; everything downstream is free).

### FU-2 — entanglement negativity + PPT criterion (Bell-diagonal / Werner) ✅ SHIPPED 2026-06-03 (scout-corrected)

**Status: SHIPPED, kernel-pure, NO new axioms.** New module `BellNegativity.lean`. The original PLOB
*rate-inequality* target stays genuinely blocked (CV Gaussian-capacity theory + LOCC-monotonicity
`E_D ≤ E_N`, unformalizable without an axiom) — BUT a first deeper scout had wrongly called the whole
area "no substrate / unformalizable." A **thorough re-search (Mathlib MCP + Explore fan-out over the
full Lean tree, `Lit-Search`, docs)** corrected that: the honest, buildable target is the **entanglement
measure itself** (negativity + the PPT criterion), with the operational rate reading left as a citation
— exactly the project's standard posture (compute the measure; cite its meaning). And the substrate was
*already present*: `PauliChannel.lean` ships the Bell projectors `bellBlock i` (`BᵢBⱼ=2δᵢⱼBᵢ`, `trBᵢ=2`)
and the combination trace norm `traceNorm_bellCombo` (`‖∑cᵢBᵢ‖₁=2∑|cᵢ|`). Shipped:
- `pt2` partial transpose (second-factor index swap) + `pt2_bellBlock`: `Tᵦ(Bᵢ)=Bᵢ−½yᵢ∑ⱼyⱼBⱼ`
  (`y=(−1,1,−1,1)` the `Y⊗Y` parity — the **only real proof**, a 64-case `fin_cases`+`ring`; the
  `½−pᵢ` first guess was a convention error, corrected to `pt2(B₀)=SWAP=½(B₀+B₁−B₂+B₃)`).
- `pt2_bellCombo` / `pt2_bellDiagState`: PT eigenvalues `μⱼ(p)=pⱼ−½yⱼ∑ᵢyᵢpᵢ`.
- `traceNorm_pt2_bellDiagState`: `‖ρ(p)^Γ‖₁=∑ⱼ|μⱼ|`; `negativityBellDiag_eq`: `N=½(∑|μⱼ|−1)`;
  `negativityBellDiag_nonneg`; **`ppt_bellDiagState_iff`** (`N=0 ↔ ∀j μⱼ≥0` — the PPT criterion).
- Werner: `negativityBellDiag_werner = (2F−1)/2` (F≥½) and `ppt_werner_iff` (PPT ⟺ `F≤½`) — the same
  `½` threshold as the BBPSSW/DEJMPS distillability cutoff. All `{propext,Classical.choice,Quot.sound}`.

**Lesson (logged): a repo `grep` is NOT a substrate search.** The first defer rested on a couple of
`grep`s of `lean/SKEFTHawking/QuantumNetwork/` only; "negativity" matched `nonnegativity` substrings and
the real Bell-block tooling in `PauliChannel.lean` was missed. Always run the goal's intractability
protocol (Mathlib MCP + Explore fan-out over ALL prior work product) before declaring infeasibility.

**Note on the genuinely-blocked piece.** A literal `rate ≤ f(η)` quantum inequality still needs
LOCC-monotonicity (axiom-only in current Mathlib); option (a)'s elementary core is the classical
triviality `E[Binomial(N,η)]=Nη`. So the PLOB *function* surrogate (6AK.2) remains the honest form of
that specific claim; FU-2's shipped negativity/PPT result is the substantive entanglement-measure win.
If a future wave builds a kernel-provable distillability bound on a finite family,
FU-2 becomes a genuine target then. Until then 6AK.2 (rate-bound *function* properties) is the honest
formalization.

### FU-2 (original spec, for reference) — PLOB as a genuine discrete-family rate inequality (EXPLORATORY, scout-first)

**Goal.** Upgrade 6AK.2 from "properties of the bound *function*" to a theorem that actually bounds a
*rate quantity* — i.e. `someRate(model) ≤ f(η)` rather than facts about `f` alone. **Scout decides the
target** (genuinely open):
- (a) **classical erasure-link bound:** an elementary finite/expectation bound — the expected number of
  symbols transmitted through `N` uses of an erasure channel (parameter `η`) is `η·N`, so any extracted
  message/key rate `≤ η` (linear loss penalty). Formalizable, honest, but weak.
- (b) **log-negativity on a Bell-diagonal family:** `E_N(ρ) = log₂‖ρ^{Γ}‖₁` using the **already-shipped**
  partial-transpose + trace-norm substrate (6AE/6AF) — prove the distillable bound on a tractable finite
  family. Stronger and reuses substrate, but the LOCC-monotonicity step may be absent from Mathlib.
**Acceptance:** EITHER a kernel-pure rate inequality (honestly labelled) OR a documented scout finding
that no clean non-trivial target is reachable without new substrate. **Risk:** HIGH/uncertain — and the
6AK.2 surrogate already stands on its own, so this is genuinely optional. Do FU-1 first.

### FU-3 — negativity is an entanglement monotone under local operations ✅ SHIPPED 2026-06-04

**Status: SHIPPED, kernel-pure, NO new axioms.** New module `NegativityMonotone.lean`. Promotes the
FU-2 negativity from a *computed number* to a proven **entanglement monotone**, and ships a one-shot
distillation no-go — the first two rungs of the decomposition of the Vidal–Werner `E_D ≤ E_N` bound
that AVOIDS formalising full LOCC theory. The only new ingredient is `pt2_conj_kronOne`: the
second-qubit partial transpose commutes with a local `A`-channel (`M⊗1`), since `M` touches only the
`A` indices and `T_B` only the `B` indices (a 64-case entrywise `fin_cases`). Composed with the
*already-shipped* CPTP trace-norm contractivity (`traceNorm_krausMap_le`, 6AF-4), this gives:
- `traceNorm_pt2_localKraus_le`: `‖((Φ_A⊗id)ρ)^Γ‖₁ ≤ ‖ρ^Γ‖₁` — negativity is non-increasing under a
  local operation on one party (the monotone property);
- `no_local_distillation_to_bellPair`: `‖ρ^Γ‖₁ < 2 ⟹` no local `A`-op converts `ρ` to a Bell pair —
  a genuine one-shot no-go (axiom-free; no LOCC abstraction, no asymptotics).

All `{propext, Classical.choice, Quot.sound}`. D6 §6 + preprint §3g prose; D6 compiles (11pp);
axiom_closure GREEN; fresh-context Stage-13 GREEN.

**Decomposition lesson (logged):** my first read called the `E_D ≤ E_N` monotonicity "needs the whole
LOCC theory" — wrong (the assert-a-wall reflex). It decomposes into P5a (CPTP trace-norm contractivity,
already shipped) + P5b (the partial-transpose/local-op commutation, one elementary lemma) + convexity +
local-unitary invariance. The genuinely-hard residual shrinks to a single Fannes-type continuity lemma
(rung 4) for the asymptotic `E_D ≤ E_N`; even that has a one-shot rung below it that needs none of it.
**Open ladder (all public-disposition, textbook):** rung 3 tensor additivity `N(ρ⊗σ)=N(ρ)+N(σ)`;
rung 4 asymptotic continuity of log-negativity; rung 5 regularized-rate corollary; and the genuinely-new
target — a finite-dim repeaterless ENTANGLEMENT-distribution bound via Choi-state log-negativity +
a finite channel-simulation layer (the bricks public; any productized certification is a separate
private-side concern). NB the *secret-key* `−log₂(1−η)` value stays doubly-gapped (von Neumann
entropy/REE absent even finite-dim, AND Gaussian/CV machinery absent) — 6AK.2 remains its honest form.

### Remaining follow-on ladder (open TODOs) — all PUBLIC disposition (textbook, §101-non-patentable)

The `E_D ≤ E_N` decomposition + the negativity/entanglement programme leave these open, in build order.
All are textbook/published math → **public** (defensive-pub; any productized certification is a separate
private-side concern that consumes these by FQN). Disposition rule: math public; the "if-in-doubt-private"
tiebreaker does NOT fire on already-textbook substrate.

- **FU-4 — log-negativity additivity** ✅ SHIPPED 2026-06-04 (`LogNegativity.lean`). Correction: the
  *negativity* `N` is NOT additive — *log-negativity* `E_N = log₂‖ρ^Γ‖₁` is. Substantive core =
  dimension-general **`traceNorm_kronecker : ‖A⊗B‖₁ = ‖A‖₁·‖B‖₁`** (reusable; via `absOp_kronecker`
  `|A⊗B|=|A|⊗|B|` from PSD-sqrt uniqueness + `tr(P⊗Q)=trP·trQ`). Then `logNegativity_add`
  (`E_N(ρ⊗σ)=E_N(ρ)+E_N(σ)`) + Bell-diagonal corollary `logNegativity_bellDiag_add` (`‖ρ^Γ‖₁≥1` kills
  the side condition). Kernel-pure, NO axioms; D6/preprint prose; Stage-13 GREEN.
- **FU-5 — negativity continuity** ✅ SHIPPED 2026-06-04 (`NegativityContinuity.lean`). Scout corrected
  the "genuinely-hard analytic nub" label: the negativity is **2-Lipschitz in trace distance** and the
  crux `traceNorm_pt2_le : ‖X^Γ‖₁ ≤ 2‖X‖₁` decomposes into *existing* bounds + ONE elementary lemma
  `norm_pt2` (pt2 preserves the Frobenius norm — it permutes entries; brute-force trace-equality `ring`).
  Then `‖X^Γ‖₁ ≤ √card·‖X^Γ‖_F = 2‖X‖_F ≤ 2‖X‖₁` (`traceNorm_le_sqrt_card_mul_norm` +
  `frobenius_le_traceNorm`, card=4) + reverse-triangle ⟹ `abs_traceNorm_pt2_sub_le_traceDist`
  (`|‖ρ^Γ‖₁−‖σ^Γ‖₁| ≤ 4·D(ρ,σ)`). Kernel-pure, NO axioms. NB: `open scoped Matrix.Norms.Frobenius` (the
  Frobenius `‖·‖` is a LOCAL instance, NOT the `L2Operator`/`Matrix` scope). D6/preprint prose; Stage-13.
  (The full *log*-negativity Fannes continuity — log-Lipschitz away from 0 — is a thin add-on for
  density ops where `‖ρ^Γ‖₁ ≥ 1`; the trace-norm/negativity version above is the substantive content.)
- **FU-6 — regularized-rate corollary** ✅ COMPLETE 2026-06-04 (autonomous /goal, scope kept). Shipped as
  bricks 3–6b: `KroneckerPower.lean` (n-fold via representative, `22bc522b`), `MaxEntNegativity.lean`
  (`E_N(Φ_d)=log₂d`, `b06edc70`), `DistillationRateBound.lean` (single-copy `log₂k≤E_N(ρ)`, `45577262`),
  **party-generalization** of the ptB/monotone/logNegB layer to arbitrary `{A B : Type*}` (`4b670324`),
  and `NCopyRateBound.lean` (`2f2c88c7`): cross-type reindex `traceNorm_reindex_cross`, grouped tensor
  `gtensor`/`ptB_gtensor`, the grouped n-copy `ncopy`, **`logNegB_ncopy : E_N(ρ^⊗n)=n·E_N(ρ)` on the
  actual grouped state**, and the **regularized rate bound `logNegB_ncopy_localKraus_le :
  E_N(Λ(ρ^⊗n)) ≤ n·E_N(ρ)`** (Λ = first-party A-side Kraus channel; with `E_N(Φ_k)=log₂k` this is the
  per-n reading `log₂k ≤ n·E_N(ρ)` of `E_D ≤ E_N`). All kernel-pure, no new axioms; prose `c0b2f777`
  (D6 §6 + preprint §3g, D6 LaTeX clean) + Stage-13 GREEN-after-remediation `73b89a32`.
- **FU-7 — finite-dim repeaterless ENTANGLEMENT-distribution bound** (MED) — 📋 SCOUT-DOCUMENTED 2026-06-04.
  Substrate now present: Choi state `Ω` (`DiamondNormChoi.lean`), general `ptB`/`logNegB`/monotone on any
  bipartite party (`4b670324`), grouped tensor + `ncopy` (`2f2c88c7`). **What is reachable kernel-pure
  decompose-first):** the repeaterless bound's textbook proof (Pirandola teleportation-stretching) has
  two ingredients — (a) **local-operation monotonicity of negativity, iterated/`n`-link additive** —
  *already shipped* (brick-1 `traceNorm_ptB_localKraus_le` / brick-2 monotone + `logNegB_ncopy`); and (b)
  the **teleportation-simulation identity** `Φ(ρ) = Λ(ρ ⊗ Ω_Φ)` rewriting a channel as a Bell-measurement-
  plus-correction **LOCC** on its Choi state. Ingredient (b) is the genuinely-new content AND the **genuine
  wall**: the Bell-measurement / classical-communication / conditional-correction LOCC is exactly the LOCC
  framework Mathlib lacks (verified) — the *same* gap that fences the PLOB secret-key rate (6AK.2). Even the
  "teleportation-simulable class" (Pauli/erasure/dephasing) still needs that Bell-measurement LOCC to realize
  the simulation, so it does NOT route around (b) (my first scout note overstated this — corrected). **What
  is GAPPED (do NOT claim):** the channel→Choi *rate-ceiling* `E_N(output) ≤ E_N(Ω_Φ)` for any channel.
  **Conclusion:** the honest kernel-pure content of FU-7 (negativity monotone under a repeaterless line of
  local operations, `n`-link additive) is already delivered by FU-3/FU-6; the channel→Choi ceiling is
  LOCC-gapped (Mathlib-upstream-grade, not in 6AK scope, no axiom to paper over it). Productized repeaterless
  cert = private FQN-consumer over the shipped monotone/additive bricks.
  **REACHABLE-NEXT (toe-hold hunt 2026-06-04, NOT a wall — only the rate-*ceiling* above is):** the
  *channel entanglement MEASURE* — the Choi state of a Pauli channel is Bell-diagonal (`pauli_choiMatrix`
  `J(Φ_p)=∑ᵢ pᵢ Bᵢ`), so its negativity/log-negativity is computable in closed form from the existing
  `negativityBellDiag_eq` / `traceNorm_bellCombo` bricks. This gives `E_N(Ω_Φ)` explicitly for the
  teleportation-covariant class — a real shippable FU-7 brick (the channel's entanglement-generating
  capacity), distinct from (and not requiring) the LOCC-gapped output≤Choi ceiling. Buildable next.
- **FU-8 — von Neumann entropy / quantum relative entropy / REE** (HIGH/large, foundational) —
  ⚠️ EARLIER "GENUINE WALL" SCOUT NOTE WAS WRONG (assert-a-wall reflex; user-flagged). After Explore
  fan-out + Mathlib MCP the toe-holds were rich and **substantial content SHIPPED 2026-06-04**:
  - **`VonNeumannEntropy.lean` `9be3dd0e`** — `S(ρ)=∑ᵢ negMulLog(λᵢ)` via the eigenvalue spectrum (NO
    matrix log needed — that was the key misframe; entropy is an eigenvalue sum). `vonNeumannEntropy`,
    `sum_eigenvalues_density`, `eigenvalue_mem_Icc`, **`vonNeumannEntropy_nonneg` (S≥0)**, and
    **`vonNeumannEntropy_le_log_card` (S ≤ log d, max-entropy)** via `concaveOn_negMulLog` + Jensen
    `ConcaveOn.le_map_sum`. 🔑 reusable: `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, `Real.negMulLog`
    + `negMulLog_nonneg` + `concaveOn_negMulLog`, `PosSemidef.eigenvalues_nonneg`.
  - **`QuantumRelativeEntropy.lean` `be11fc23`+`2ef4a622`** — `matrixLog` (`cfc Real.log`),
    `mul_matrixLog` (ρ·log ρ = cfc(x·log x)ρ via `cfc_mul`+`cfc_id`), **`re_trace_mul_matrixLog`
    (Re tr(ρ log ρ) = −S(ρ))**, `relativeEntropy` def + `relativeEntropy_self`=0, and **`classical_gibbs`
    (0 ≤ ∑ pᵢ(log pᵢ−log qᵢ), classical KL≥0)** via `Real.log_le_sub_one_of_pos` — the math core of Klein.
  REACHABLE-NEXT (decomposed, NOT walls): (a) **full quantum Klein `S(ρ‖σ)≥0`** = `classical_gibbs`
  applied to ρ's spectrum + the doubly-stochastic image `rᵢ=∑ⱼ|⟨eᵢ|fⱼ⟩|²qⱼ`; the one remaining crux is
  the **two-eigenbasis spectral expansion** `tr(ρ log σ)=∑ᵢⱼ pᵢ|⟨eᵢ|fⱼ⟩|² log qⱼ` (uses both
  `eigenvectorUnitary`s + `|⟨eᵢ|fⱼ⟩|²` doubly-stochastic) + Jensen per row — sizeable but reachable.
  (b) **additivity `S(ρ⊗σ)=S(ρ)+S(σ)`** via `log(ρ⊗σ)=log ρ⊗1+1⊗log σ` (kronecker-eigenvalue product →
  log distributes) — moderate. IRREDUCIBLE RESIDUAL (genuine wall, no axiom): **REE
  `E_R(ρ)=inf_{σ∈SEP} S(ρ‖σ)`** needs the separable-set/convex-optimization infimum framework Mathlib
  lacks; and the secret-key `−log₂(1−η)` additionally needs Gaussian/CV (Gap #2). The entropy/rel-entropy
  track is now a SHIPPED companion to the negativity ladder; only the REE optimization is genuinely out
  of reach.

---

## Out of scope (keeps 6AK closeable)
- Any downstream-application naming or product/positioning prose.
- Any device/compiler-specific accuracy-threshold result that belongs to a non-public project (6AK.5
  stays general QEC math only).
- New project-local axioms without explicit user sign-off.

## Notes for the executing agent
Read the Mandatory References + the 6AG/6AH/6AI/6AJ roadmaps for the shipped substrate this builds on
(`avgGateFidelity_eq`, `kraus_normSq_sum`, `diamondDist_pauliKraus_eq`, `NamedChannelDiamondExact`,
`diamondDist_ampDamp_eq`, the dual-witness `diamondDist_le_dual_witness`). The coherence ceiling (6AK.1)
and two-qubit Pauli (6AK.3) are the highest value-per-effort and should go first; PLOB (6AK.2) is a
scout-first moonshot.
