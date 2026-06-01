# Phase 6AA — Verified Quantum-Network Substrate

**Status:** OPEN (seeded 2026-06-01). Bundle-target: **D6** ("Formally Verified Fault-Tolerant Quantum Computation Substrate"; extends D6 §6 where `WStateQFT`/Wave 6v.6 already lives — the sibling-bundle-vs-extend-D6 question is a Stage-1 call).

**Trigger.** The Kyoto/Hiroshima 2025-09 single-shot projective W-state measurement (cyclic-shift symmetry → QFT on `Z_N`) is already formalized as a `Q(ζ_N)` cyclotomic decomposition in `SKEFTHawking.FaultTolerance.WStateQFT` (Wave 6v.6, D6 §6). Phase 6AA extends that point result to a **protocol-level verified-envelope substrate** for entanglement-based quantum networks: machine-checked bounds on the metrics network operators care about (entanglement-swapping fidelity, distillation yield, end-to-end fidelity under loss + decoherence).

**Headline goal.** Ship kernel-pure, parameterized **"metric ∈ [lo, hi]" envelope theorems**: given channel/protocol parameters, the end-to-end network metric provably lies in a certified interval. These are the first verified quantum-network-protocol bounds in any prover.

## Architectural decisions (pinned at phase open; do not re-litigate)

- **Toolchain/pin:** `leanprover/lean4:v4.29.1`, Mathlib `5e932f97`. Fixed; load-bearing for the existing library.
- **No external QI dependency.** Mathlib-at-pin provides the substrate (`Matrix.PosSemidef`, `Matrix.PosSemidef.kronecker` in `Mathlib.Analysis.Matrix.Order`, `Matrix.kroneckerMap`, Loewner order, C*-`cfc`) but **lacks** `traceNorm`, `partialTrace`, fidelity, trace distance, CPTP/Kraus, entropy, diamond norm (verified absent by direct `lean_loogle` probe 2026-06-01). The Lean-QuantumInfo library has these but pins v4.28.0 — two minors behind, and this repo is deliberately zero-extra-deps. **Native-build the focused primitives we need; borrow Lean-QuantumInfo's conventions only as reference.**
- **Bell-diagonal / Werner parameterization.** Repeater-network metrics (swapping fidelity, DEJMPS/BBPSSW purification, end-to-end fidelity under loss/decoherence) are, in the standard Briegel-Dür model, explicit polynomial/rational/transcendental expressions in a few real parameters — **not** general density matrices. So the envelope substrate is real-analysis on explicit expressions (`norm_num` + transcendental interval bounds + `PolyQuotQ`/`QCyc` for algebraic pieces). General density-matrix fidelity / trace distance / diamond norm are **out of scope** (return only for arbitrary-state certification, post-phase).
- **Pauli-error Bell-basis convention (DR-FORM).** Adopt `(a,b,c,d) ↔ (I,Z,X,Y)`. The DEJMPS squared-and-added pair is the *diagonal* (00,11)=(I,Y) pair — the naive "adjacent" pairing is wrong and will not compose. Translate all literature formulas to this convention at parse time.
- **Envelope target = model-independent FIDELITY, not time (DR-SIM).** The simulator disagreement motivating the work (Chung/Hajdušek/Van Meter et al., arXiv 2504.01290 — *not* Coopmans; benchmarks QuISP + SeQUeNCe only, *not* NetSquid) is on elementary-link entanglement-*generation time*, a **connection/handshake-model artifact** (ratio ~4.16–4.33, not 2×) that is **Tier-3: genuinely model-dependent, NOT cleanly envelope-able.** The simulators *agree* on fidelity. ⟹ envelope the **fidelity + model-independent quantities**; flag handshake-inclusive times as model-dependent, do not bound them.
- **Attenuation convention (DR-SIM, resolved).** `0.046` is **Np/km (= 0.2 dB/km)**; "0.046 dB/km" is wrong by ~4.343×. Adopt **dB as primitive, Np derived**; the first Tier-1 theorem is the dB↔Np consistency identity `(10:ℝ)^(−α_dB·L/10) = Real.exp(−α_Np·L)`, `α_Np = α_dB·ln 10/10`. Never write "0.046 dB/km".
- **W2 numerics = kernel-only manual Taylor-squeeze (DR-INT).** Build `SKEFTHawking.NumericalBounds` (~80–120 LoC) over the existing `Real.exp_bound`/`Real.expNear`/`Real.exp_approx_*`/`ExponentialBounds.lean`; 3–5 LoC per bound. **No `native_decide`, no LeanCert** (LeanCert is now version-compatible at v4.29.1/5e932f97 but defaults to `Lean.trustCompiler`; kernel-purity + zero-dep wins).

## Wave catalog

| Wave | Content | DR input | Module |
|---|---|---|---|
| **W0** | This roadmap + substrate root module (skeleton, builds clean) | — | `QuantumNetwork/Basic.lean` |
| **W1** | Channel models: fiber loss `exp(−αL)`, memory decoherence `e^{−t/T₂}`, heralding success; composition + monotone fidelity-decay lemmas | DR-SIM, DR-FORM | `QuantumNetwork/Channels.lean` |
| **W2** | Transcendental interval bounds: two-sided `norm_num`-checkable bounds on `Real.exp(−x)` / `Real.log` at device parameters | DR-INT | `QuantumNetwork/IntervalBounds.lean` |
| **W1′ Tier-1** | The three model-independent anchors: **dB↔Np attenuation identity** (first theorem), **BSM linear-optics 50% bound** (Calsamiglia-Lütkenhaus), **physics-only link rate** `τ = L/(c·p_link)` (geometric expectation) | DR-SIM | `QuantumNetwork/Channels.lean`, `Rate.lean` |
| **W3** | **Fidelity-composition core** (Tier-2, all `ring`/`nlinarith`): Werner swap `F_out=F₁F₂+(1−F₁)(1−F₂)/3` + Bell-diagonal Klein-4 swap map + monotonicity; **BBPSSW** flagship `(1−F)(2F−1)(4F−1)>0 ⟺ F'>F` (one cubic); **DEJMPS** (Pauli-error pairing); **W-state** Fortescue-Lo **lower bound `≥1` + finite-round `D/(D+1)` ONLY** (NOT the open `=1` equality), composing with `WStateQFT` | DR-FORM | `QuantumNetwork/{Swapping,Distillation,WStateRate}.lean` |
| **W4** | Memory-decoherence fidelity **parameterized by model** (depolarising / dephasing / QuISP-discrete — state model as hypothesis, pick no default) + end-to-end via the **Werner-iterated closed form** `F_e2e^(k)=(1+3·((4F−1)/3)^k)/4` (induction; **avoids** trace-distance/Fuchs-van-de-Graaf, which need the absent `traceNorm`) | DR-FORM | `QuantumNetwork/Fidelity.lean` |
| **W5** | General parameterized **fidelity** envelope theorems (metric ∈ [lo,hi]) + D6 §6 absorption + Stage-13 + bridging arXiv preprint | all | `QuantumNetwork/Envelope.lean` |
| **W6 (optional/deferred)** | Horodecki teleportation fidelity `(2F+1)/3` — the **one analytic exception**: needs a Haar-integral lemma `∫_{S²}(⟨ψ|σ_k|ψ⟩)²dμ=1/3` (may be absent in Mathlib). Factor as (i) Haar lemma + (ii) algebra. **Off the core critical path.** | DR-FORM | `QuantumNetwork/Teleportation.lean` |

**Tier discipline (DR-SIM §6).** Tier-1 = clean & model-independent (W1′). Tier-2 = closed-form *under an explicit model hypothesis* (W3/W4). **Tier-3 = AVOID:** handshake-inclusive link/swap *times* (model-dependent, ~4.16–4.33× simulator split — document in prose, never bound). **Do NOT formalize:** the W-state `=1` asymptotic equality (open conjecture); general trace-distance / diamond-norm / `partialTrace` machinery.

**Sequencing.** W0 → W1/W1′ → W2 → W3 → W4 → W5 (W6 optional, anytime after W2). Ship per-wave: `lake build` clean, zero sorry, kernel-pure `{propext, Classical.choice, Quot.sound}`, no `maxHeartbeats`, no new project-local axioms. Preemptive-strengthening checklist before each theorem. The four Phase-6AA dossiers in `../../Lit-Search/Phase-6AA/` are advisory — **verify every Mathlib lemma directly via lean-lsp before trusting a DR version-claim** (the DRs were authored against a stale `8850ed93` assumption; our pin is `5e932f97`/v4.29.1).

**Stage-13.** Bundle-level adversarial review runs after W5 (last D6-contributing wave); precedes any D6 preprint refresh.

## Invariants (Phase 6AA)
- Kernel-pure; zero sorry; zero new project-local axioms; no `maxHeartbeats` in proof bodies (decompose instead).
- All metrics carry explicit physical units; every numerical bound is `norm_num`-backed and falsifiable.
- Substrate is self-contained under `SKEFTHawking.QuantumNetwork.*`; no external QI dependency.
