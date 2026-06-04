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

### FU-2 — PLOB as a genuine discrete-family rate inequality 🔭 SCOUTED 2026-06-03 → DEFER (no clean target)

**Scout outcome (2026-06-03): no clean non-trivial kernel-pure *quantum* rate inequality is reachable
without major new substrate whose load-bearing step is unformalizable in current Mathlib. FU-2 stays
deferred; the 6AK.2 surrogate stands on its own.** Findings:

- **Roadmap premise was wrong.** This section assumed a "partial-transpose + trace-norm substrate
  already shipped in 6AE/6AF." A full-tree scan finds **no `partialTranspose` / `negativity` /
  `logNegativity` / distillable-entanglement / Bell-diagonal *density-matrix* definition anywhere** in
  the Lean codebase. `traceNorm` exists (`MixedState.lean`); `BellDiagonalSwap.lean` is **pure
  `(a,b,c,d)`-coefficient real algebra with no density operators**. So option (b) would have to build,
  from scratch: a `4×4` Bell-diagonal density matrix in the Pauli basis, the partial-transpose
  operation, its eigenvalues, and the trace-norm of the partial transpose.
- **Option (b) is blocked at the monotonicity step.** Even after building the negativity machinery, a
  genuine *rate* bound needs LOCC-monotonicity `E_D ≤ E_N` (log-negativity an upper bound on
  distillable entanglement) — a deep result absent from Mathlib that would require a project-local
  **axiom** (disallowed without sign-off, Invariant #15). Without it, the strongest honest deliverable
  is a *surrogate* "`negativity(ρ(p)) = f(p)`" trace-norm computation — no better in kind than 6AK.2,
  at a large substrate cost.
- **Option (a) collapses to a classical triviality.** The only *elementary, axiom-free* content of the
  erasure-link bound is `E[Binomial(N, η)] = N·η` (linearity of expectation) — a classical fact, not a
  quantum-network rate bound. The genuine quantum `rate ≤ η` reading needs the same missing
  entanglement-monotone machinery as (b).

**Decision:** document and stop (the handoff's second acceptance branch). If a future wave builds a real
negativity substrate (partial transpose + a kernel-provable distillability bound on a finite family),
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
