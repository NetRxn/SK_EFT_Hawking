# Phase 6AO — Fully Strengthen 6AL, 6AM, 6AN

**Status: REVISED 2026-06-09 — scope expanded. (a) Adopt PhysLib for the entropy/capacity cluster
(was the 2026-06-04 revision); (b) ADD waves closing the Phase-6AN residuals — the quantum-FDT
(Callen–Welton) amplifier/detector floor (W4) and the Ross–Selinger O(log 1/ε) optimal Clifford+T
synthesis (W5); (c) ADD the 6AL Gap-1 cleanup — the sharp Fannes–Audenaert `log(d−1)` constant (W6),
discharging `hAud`. Do NOT hand-roll DPI / Lieb concavity / SSA / REE.
**Full-strength budget: ~50k LoC for the whole phase** (W2–W7, all cleanup included) — generous
**by design** to remove LOE/budget guesswork; build every wave at full strength now, in-context.**

> **⚠️ AGENTS IN FLIGHT — READ THIS FIRST.** An earlier draft of this phase planned to build the
> data-processing inequality (DPI) from scratch (vendor-in operator concavity of log → construct the
> relative modular operator → discharge joint convexity → REE). **That plan is SUPERSEDED.** The entire
> cluster is already proven, complete and kernel-clean, in **PhysLib** (`leanprover-community/physlib`,
> arXiv:2510.08672), which is pinned to **Mathlib v4.29.1 / 5e932f97 — our exact toolchain pin**. Do not
> reinvent any of it. This phase is now: *adopt PhysLib and bridge to it* (W1–W3), *close the 6AN
> residuals* (W4 quantum-FDT floor, W5 Ross–Selinger), and *optionally migrate* (W6).

## Gate-strength discipline + no-effort-based deferral (READ BEFORE EVERY WAVE — 2026-06-09)

This phase was hardened after a review found two recurring failure modes. Both are **forbidden here:**

1. **No weak-form / vacuous / definitional-only deliverable.** Every gate below specifies the
   *strength* of what ships, not just its shape. A bridge that round-trips only on a trivial channel
   class, a corollary stated so weakly it is `True`-adjacent, an FQN **cited in a docstring but never
   invoked in the proof body** (the CLAUDE.md **P6** anti-pattern), or a "REE" that delivers only the
   *definition* and not an *operational bound on a concrete channel* — all FAIL the gate. Apply the
   five preemptive-strengthening questions (CLAUDE.md) to every theorem statement before writing it.
2. **Effort/LoC is NEVER a reason to defer, ask, down-scope, OR gate.** The project ships ~15k LoC/day;
   this phase has a deliberately generous **~50k LoC full-strength budget** (covers W2–W7 including all
   cleanup), set high precisely to **remove LOE/budget guesswork** — which in a long auto-dev session is
   far more expensive than building at full strength from the start. **Do NOT introduce LoC thresholds
   or "stop if > N lines" gates anywhere** (e.g. build the W6 finite-Fano scaffolding to whatever size
   it takes). The ONLY legitimate pause is a **genuine wall** (axiom-needing, or machinery that truly
   cannot be built — established by decompose → Mathlib-MCP/PhysLib-search → Explore-fan-out) or a true
   product tradeoff only the user can make. **"Absent from Mathlib" is a BUILD instruction, not a wall.**
   A "documented-gap / awaiting-sign-off / stop-at-N-LoC" note whose only blocker is effort is the
   antipattern (it silently makes the user the bottleneck). **Do the work now, in context — do not ship
   loose ends to circle back to.** Each wave states its real-world reason so it can't be re-deferred.
   See memory `feedback-no-hypothesis-based-descope`.

## ✅ PHASE 6AO CLOSED (2026-06-10)

Value-bearing work complete and gate-met (W2, W3, W4 per their original gates; **W6** fully — sharp
Fannes–Audenaert `log(d−1)`, `hAud` discharged, unconditional, kernel-pure; **W5** per the amended gate —
O(log 1/ε) efficiency + axiom-free §6-gate `Prop`). All kernel-pure `{propext, Classical.choice, Quot.sound}`
where claimed (independently `#print axioms`-verified by the closure adversarial review); lib + ExtractDeps
green (9204); axiom_closure_allowlist + graph_integrity + counts_fresh pass; counts refreshed. Commits
(NOT pushed): `599c3be9` `c7fc6863` `b0bd8a8b` `846f2ccf` `f16c3f81` `be40ce07`. W7 (migration) was optional,
not required — not done.

### → Next `/goal`: the W5-residual program (DR-sharpened 2026-06-09; see goal statement below)
The DR (`Lit-Search/Phase-6AM/Is the Ross–Selinger O(log 1:ε) existence…md`) sharpened the three strands.
Treat the DR as suggestion, not fact (the requesting side has the Mathlib/Lean access it lacked).

- **Track 2 — KMM-ancilla UNCONDITIONAL O(log 1/ε) Clifford+T (THE PRIZE; genuinely removes the wall).**
  KMM (arXiv:1212.0822, PRL 110:190502) gives unconditional O(log 1/ε) Clifford+T with ≤2 ancillas;
  mechanism = ancillas add variables ⟹ the norm/Diophantine equation is *always* solvable (Lagrange
  four-squares, `Nat.sum_four_squares`, IS in Mathlib). Map the exact KMM rounding+ancilla construction
  onto the shipped KMM exact-synthesis substrate (`KMMCompleteness`); ship the unconditional headline.
  This is NOT the BRS/RUS protocols (those keep a runtime hypothesis) — KMM specifically.
- **Track 1 — unconditional scaffolding + thin the bare-CT `Prop`.** (a) ℤ[√2] norm-Euclidean — ALREADY
  shipped (`Zsqrt2EuclideanDomain`; the DR listed it as a missing build — we're ahead). (b) finish
  ℤ[ω]=ℤ[√2][i] relative norm (`GaussInt2` + `RelativeNorm`). (c) the **even-power relative-norm criterion**
  (β a relative norm ⟺ every inert ℤ[√2]-prime to even power) — lift Mathlib `Nat.eq_sq_add_sq_iff`
  (ℤ template, PRESENT) over `Zsqrt2EuclideanDomain`; splitting law = `x²+1` mod π (split/inert ⟺ −1 is a
  square/non-square; ramified ⟺ residue char 2, π~√2 — DR-corrected). (d) §5 grid existence (Ross
  Lemma 4.4 / Thm 5.18 — paper numbering DR-confirmed). The terminal ancilla-free existence stays a tracked
  `Prop`: *"∃ k=log₂(1/ε)+O(loglog) with a relative-norm-solvable residual in R_ε"* — **strictly weaker
  than RS Hypothesis 29** (relative-norm, not primality), plausibly unconditional but its lower bound is a
  Friedlander–Iwaniec/half-dimensional-sieve statement (Landau–Ramanujan absent from Mathlib; Selberg sieve
  is upper-bound-only) → tracked `Prop`, NEVER an axiom.
- **Track 3 — structural-KMM `native_decide` elimination** (4 sites; project-tolerated meanwhile). Per-site:
  `cliffordBase_box_core` (Clifford ≤6-word coverage), `bridge_box_core` (Giles–Selinger sde↔kSO3 + column
  bounds), `kmm_lemma3_alg2` (mod-8 algebra — research-flavoured), `maStep_exists_core` (MA-step
  orthogonality-class orbit-closure — mechanical-tedious, ~809k triples). NO trusted-oracle/checksum fallback
  (= `native_decide` by another name). Benefits all KMM consumers.

## Phase 6AO execution log (the W5-residual `/goal`, started 2026-06-09)

### Track 2 — KMM ancilla (PRIORITIZED). Increments 1–2 shipped (kernel-pure, green).

- **Increment 1 ✅ — the unconditional number-theoretic keystone (`a8cf2f3d`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaCompletion.lean`:
  - `exists_two_relativeNorms_of_nat (r : ℕ) : ∃ t₁ t₂, normSq t₁ + normSq t₂ = (r:ZOmega)` — **every
    `r:ℕ` is a sum of two ℤ[ω] relative norms**, via Lagrange `Nat.sum_four_squares` (`r=a²+b²+c²+d²` →
    `t₁=a+bω²`, `t₂=c+dω²`, `normSq_real_sumSq`). **This is the wall-removing core**: the ancilla turns
    the single-relative-norm condition (sum of 2 squares over ℤ[√2], conditional/prime-density) into a
    sum-of-4-integer-squares condition — ALWAYS solvable. No Hypothesis 29, no prime density.
  - `ancilla_completion_of_nat_residual` — for an approximant `u` with integer `normSq u = m ≤ 2^k`,
    `∃ t₁ t₂, normSq u + normSq t₁ + normSq t₂ = 2^k` UNCONDITIONALLY (the (1+ancilla)-qubit unit column
    closes), vs the ancilla-free `rossSelinger_synth_of_residual` which REQUIRES a single relative norm.
  - `conj_intCast`/`conj_natCast` — rational integers are `conj`-fixed (real in ℤ[ω]).
  - Both headlines `#print axioms`-clean `{propext, Classical.choice, Quot.sound}`.
- **Increment 2 ✅ — two-qubit Clifford+T gate semantics (circuit-layer foundation) (`c787a24b`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/CliffordTGate2.lean` (`Matrix (Fin 2 × Fin 2)`, kronecker-native):
  `Gate2` ADT (onFst/onSnd single-qubit + cx01/cx10 cnots), `gateMatrix2`/`interp2`, `embedFst`/`embedSnd`
  (proven monoid homs via `Matrix.mul_kronecker_mul`), **`embedFst_interp`/`embedSnd_interp` — the
  load-bearing realizability transport** (single-qubit Clifford+T word → 2-qubit word, SAME length;
  so the shipped single-qubit `kmmReduce` transports onto the system/ancilla line at no length cost),
  `interp2_append`, `cnot{01,10}_mul_cnot{01,10}` involutions (kernel `decide`). Kernel-pure; cnot
  `decide` is KERNEL `decide` (native_decide count unchanged at 592).
- **Increment 3 ✅ — unconditional normalized ancilla state column (`3757096f`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaState.lean`: lifts the inc-1 integer identity to the
  ℤ[ω][1/√2] amplitude level. `ZOmegaSqrt2.mk_add_same`; `ancillaColNormSq` (3-entry extension of the
  shipped `KMM.colNormSq`); **`exists_ancilla_normalized_column`** — for an integer-residual approximant
  `u` (`normSq u = m ≤ 2^k`), the cleared column `(u,t₁,t₂)/√2^k` is a UNIT vector UNCONDITIONALLY (the
  KMM-ancilla existence, DR rec. #3, at the amplitude level — no relative-norm hypothesis). Kernel-pure.
- **Increment 4 ✅ — system-line synthesis on the two-qubit register (`bd6fd333`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/AncillaSynthesisBridge.lean`: `embedFst_kmmReduce_interp`
  (`interp2 ((kmmReduce M).map onFst) = embedFst M` — the shipped single-qubit KMM synthesis realizes
  `M⊗I` on the system line) + `embedFst_kmmReduce_length` (same `N₃+4·denExp` bound, no length cost).
  Connects inc-2 semantics to the verified `kmmReduce`; consumes the 4 TOLERATED native_decide
  (Track-3 targets), no new project-local axiom (native_decide decl-count 592→594, as any kmmReduce
  consumer). The building block for the ancilla circuit's system-line ops.
- **Increment 5 ✅ — two-qubit Clifford+T realizable class + closure (`0086d83f`).** `Gate2.IsRealizable`
  (`∃ w, interp2 w = M`) + `.one`/`.mul` (monoid closure)/`gateMatrix2_isRealizable`/cnot realizability;
  `embedFst_isRealizable` (single→2-qubit transport). The codomain 2-qubit synthesis targets.
- **Increment 6 ✅ — length-tracked realizability, the O(log 1/ε) composition law (`b3babeec`).**
  `Gate2.IsRealizableWithin M L` + **`IsRealizableWithin.mul` (budgets ADD under product)** + `.mono`/
  `.isRealizable`/`gateMatrix2_realizableWithin_one`; `embedFst_kmmReduce_realizableWithin` (system-line
  `M⊗I` within `N₃+4·denExp` = O(log 1/ε)). **This is the precise abstraction the headline needs**: a
  circuit assembled from O(log)-length pieces is O(log) overall.
- **✅ Construction RESOLVED via web search (2026-06-09; DR delayed, user-directed) —
  `Lit-Search/Phase-6AO/KMM-1212.0822-ancilla-construction-websearch.md`.** The KMM §2.1 Diophantine
  `a²+b²+c²+d² = 4^k − ⌊2^k cos φ⌋² − ⌊2^k sin φ⌋²` with `|v⟩ = (1/2^k)(⌊2^k cosφ⌋+i⌊2^k sinφ⌋, 0, a+ib,
  c+id)` **IS EXACTLY** the Phase-6AO keystone (inc 1) + normalized state (inc 3) at `K=2k`: `a+ib`,
  `c+id` = our `t₁=a+bω²`, `t₂=c+dω²`; `u=⌊2^k cosφ⌋+⌊2^k sinφ⌋i ∈ ℤ[i]`; residual `4^k−|u|² = 2^K−normSq u`.
  **Inc 1–6 confirmed faithful to the primary source — no correction.** **CRUX resolved:** *deterministic*
  unitary (no measurement/post-selection); the ancilla-|1⟩ leakage `|g⟩` is *bounded and folded into the
  ε error* `O(2^{−0.5k})` — so the headline is `‖W − Λ(e^{iφ})⊗I‖ ≤ ε` for a deterministic Clifford+T `W`
  (the naive-column "post-selection" worry is settled). **2 ancillas.** **Brick B (now unblocked)** =
  circuit C preparing `|v⟩` via O(k) Clifford+T (= 2-qubit exact synthesis of a ℤ[ω][1/√2] unit column,
  the Giles–Selinger/KMM-1206.5236 Column-Lemma at dim 4) + controlled-C (Column Lemma, no extra ancilla)
  + the leakage error bound. ~~Rounding-into-disk (`|u|²≤4^k`) stays the §5-style tracked hypothesis.~~
  **[UPDATED inc 8] The rounding is NO LONGER a hypothesis — inc 8 `exists_round_toward_zero` +
  `kmm_amplitude_approx` PROVE it unconditionally (∀φ,k ∃ disk-bounded `m₁,m₂` with `‖u/2^k − e^{iφ}‖ ≤
  √2/2^k`). So the z-rotation headline carries NO rounding hypothesis — stronger than this inc-6-era plan.**
- **Increment 7 ✅ — the KMM z-rotation ancilla state exists unconditionally (`21804cab`).**
  `AncillaState.lean`: `kmm_ancilla_state_exists (m₁ m₂ : ℤ) (k) (h : m₁²+m₂² ≤ 4^k) : ∃ t₁ t₂,
  Σ normSq((m₁+m₂ω², t₁, t₂)/√2^{2k}) = 1` — the exact KMM target column `|v⟩` is a UNIT vector for the
  Gaussian approximant `u = m₁+m₂i` in the disk, completion `t₁,t₂` by Lagrange four-squares (keystone).
- **Increment 8 ✅ — the unconditional amplitude approximation (rounding → ε) (`33f4700b`).**
  `AmplitudeApprox.lean`: `exists_round_toward_zero` (∃ m, m²≤x² ∧ |x−m|≤1 — disk-preserving rounding);
  `toComplex_gaussian_approx` (the shipped `ZOmegaSqrt2 →+* ℂ` embedding sends `mk (m₁+m₂ω²) (2k)` to its
  analytic amplitude `(m₁+m₂i)/2^k` via `s2C²=2`, `ω²↦i`); **`kmm_amplitude_approx`** (∀φ,k a disk-bounded
  approximant with `‖u/2^k − e^{iφ}‖ ≤ √2/2^k`, UNCONDITIONAL); **`kmm_ancilla_state_approx`** (milestone:
  inc-7 state + this amplitude bound). Kernel-pure; native_decide unchanged 596.
- **Increment 9 ✅ — the KMM leakage bound, the dominant `O(2^{−0.5k})` error (`38126592`).**
  `AncillaLeakage.lean`: `toComplex_normSq` (ring norm → complex squared modulus, `toComplex` is a *-hom);
  **`kmm_ancilla_state_full`** (∀φ,k: normalized + `|00⟩`-amplitude within √2/2^k of `e^{iφ}` + total
  ancilla-|1⟩ leakage `≤ 2·√2/2^k`, UNCONDITIONAL — leakage² = 1−|amp|², bounded via inc-8 + reverse
  triangle, `‖e^{iφ}‖=1`). **This completes the ERROR-BUDGET half of `‖W − Λ(e^{iφ})⊗I‖ ≤ ε`** (both the
  amplitude error and the leakage are now quantitative + unconditional). Kernel-pure; native_decide 596.

**REMAINING Track-2 brick = the CIRCUIT SYNTHESIS only** (multi-increment sub-program, NOT de-scoped):
the `O(k)` Clifford+T word that realizes a unitary preparing `|v⟩`, + its assembly into the operator-norm
headline + the length-`O(log 1/ε)` corollary (inc 6's composition law makes length automatic once the
synthesis is O(k)-piece-assembled). Per the websearch resolution, KMM §2.2 does NOT give a new explicit
circuit — it *invokes* the Giles–Selinger/KMM-1206.5236 **Column Lemma at dim 4** (no shortcut via a
guessable §2.2 gate sequence; the faithful route is the correct-by-construction exact synthesis). Structure
(reuse the dim-2 `KMMReduce`/`MAStep`/`*Column` machinery at dim 4 on the shipped `Gate2`/`Mat4` semantics):
(1) `colDenExp` of a 4-column; (2) base case `colDenExp v = 0` ∧ unit ⟹ `v = ωʲ·eᵢ` realizable by Clifford
`Gate2`; (3) reduction step `colDenExp = k+1 ⟹ ∃ O(1) Gate2 word g, colDenExp (g·v) ≤ k` (the residue/
syndrome lemma at dim 4 — the hard core); (4) induct ⟹ any unit column realizable in `O(colDenExp)` =
`O(k)` = `O(log 1/ε)` `Gate2` gates. Then controlled-C + operator-norm assembly on inc-8/9's error budget.

**Circuit-synthesis progress (inc 10–13, all kernel-pure, native_decide stays 596):**
- inc 10 (`77a3b91a`, `ColumnSynthesis.lean`): `IsColRealizableWithin` (column = `M·e₀` of a `Gate2`
  word ≤ L) + **`smul_left`** (the induction backbone: `G` realizable + `v` col-realizable ⟹ `G·v`
  col-realizable, budgets add) + base anchor `e₀`. inc 10b (`ad051faa`): all basis states `|a,b⟩`
  realizable within 2 (X-permutation, kernel `decide`).
- inc 11 (`55679480`, `ColumnBaseCase.lean`): `normSq_eq_one_iff_omega_pow` (`|z|²=1 ⟺ z=ωᵏ`) +
  `normSq_eq_zero_iff`. **Key simplification: the base case needs NO total-positivity / Galois /
  Kronecker** — `normSq` lands in ℤ[ω] with `(|z|²).d = a²+b²+c²+d²`, so `|z|²=1` ⟹ elementary
  sum-of-four-squares =1.
- inc 12 (`b0e7a345`): `unit_col_zero_denExp_structure` (`Σ|vᵢ|²=1 ⟹` one unit entry, rest 0) +
  `normSq_d_eq_zero_imp`. inc 13 (`3ebe0904`): `isColRealizableWithin_omega_pow_basis` (`ωᵏ·eᵢ`
  realizable within `k+2`, via `smul_omega`/`smul_omega_pow`). **⟹ base case (step 2) essentially
  DONE** — remaining = the `of`/`normSq` bridge (denExp-0 ⟹ ℤ[ω] entries via `denExp_le_iff` k=0;
  `normSq(of z)=of(normSq z)`) assembling `base_case : denExp-0 unit column ⟹ IsColRealizableWithin`.

**🔑 KEY DEPENDENCY (decomposition-backed, surfaced inc-reduction-step depth-read):** the reduction
step (3) reuses the dim-2 `reduceStep` (`H·Tᵏ`, col → `(z+ωᵏw)/√2`) + **`kmm_lemma3_column`**, whose
existence-of-reducing-`k` is the `native_decide` `kmm_lemma3_alg2` (KMM Algorithm 2; **no published
closed-form proof** — `(ZMod 8)⁴×(ZMod 8)⁴` computer check). So a **fully kernel-pure** Track-2 synthesis
shares its hardest dependency with **Track 3's hardest site** (`kmm_lemma3_alg2`). Efficient architecture
(matches "build on KMMCompleteness substrate"): **ship the synthesis reusing the tolerated-native_decide
dim-2 reduction** (exactly as inc-4 `AncillaSynthesisBridge` already consumes the 4 sites), then **Track 3
eliminates `kmm_lemma3_alg2`** (structural mod-8 / symmetry-reduced kernel-decide) ⟹ retroactively
kernel-pure. NOT a wall (provable, not axiom-needing) — sequencing, not de-scope.

**↑ inc 15 + inc 16 (the latter's framing CORRECTED — `kmm_lemma3` IS needed; see ⚠ below):**
- inc 15 (`ad3d7c77`): `colDenExp` measure + `ReductionStep C` predicate + **`colLemma_of_reductionStep`**
  (the column lemma by strong induction on `colDenExp`, reduced to `ReductionStep` alone — base case at 0,
  else `v=g·v'` climbs via `smul_left`). The ENTIRE remaining circuit-`C` synthesis is now the single
  `ReductionStep` brick (then controlled-C + operator-norm assembly).
- inc 16 (`6b7e337d`, `MatchingResidue.lean`): `dividesSqrt2_add_of_dividesSqrt2_sub` + `denExp_mk_succ_
  le_of_dividesSqrt2` — CORRECT facts, part of the elementary residue toolkit.

**✅ DEFINITIVE (web-verified 2026-06-09, `Lit-Search/Phase-6AO/GilesSelinger-1212.0506-column-lemma-
mechanism-websearch.md`): the `ReductionStep` is the GILES–SELINGER column lemma — ELEMENTARY, kernel-
pure, optimal O(lde), and INDEPENDENT of `kmm_lemma3`/Track 3.** This supersedes the inc-16 back-and-
forth below (both the v1 "elementary mod-√2" mechanism AND the v2 "kmm_lemma3 needed" walk-back were
off; the v2 conflated `kmm_lemma3` with the column lemma).
  - **Two ar5iv fetches settle it.** KMM 1212.0822: circuit C = "Lemma 20 (Column lemma) from [8]",
    [8] = **Giles–Selinger 1212.0506** "Exact synthesis of multiqubit Clifford+T circuits". Giles–Selinger
    reduction = **purely elementary**: Lemma 5 parity (`Σ xⱼ†xⱼ = 0000` over residues in `𝔽₂[x]/(x⁴+1)`;
    each summand ∈ {`0000`,`0001`,`1010`}; EVEN count of `0001` ⟹ a matching-residue-norm pair exists)
    + Lemma 4 row operation (3 explicit cases by residue norm, H/T 2-level word, denExp drops by 1).
    **"No algebraic number theory, class field theory, or number-theoretic decision procedures." NO
    `native_decide`.**
  - **`kmm_lemma3` is a DIFFERENT result** (KMM Algorithm 2: the SO(3)/`|·|²`-valuation optimal-T-count
    for ANCILLA-FREE single-qubit synthesis) — NOT what circuit C uses. The project's dim-2 column
    reduction happens to use it (a choice for the finer SO(3) optimality); the dim-4 KMM-ancilla circuit C
    does NOT. So the dim-4 `ReductionStep` neither needs nor reuses `kmm_lemma3`.
  - **Optimal T-count preserved**: Giles–Selinger gives O(lde) = O(log 1/ε) gates (exponent 1) — the
    headline's asymptotic optimality (saturates the constant-ancilla lower bound, per KMM). The finer
    kmm_lemma3/SO(3) optimality is ancilla-free-only and not required.
  - **⟹ kernel-pure `ReductionStep` is achievable via Giles–Selinger, independent of Track 3.** Build
    plan (elementary): (i) residue map `ZOmega → ℤ[ω]/√2 ≅ 𝔽₂[x]/(x⁴+1)` + residue-norm `x†x ∈
    {0000,0001,1010}`; (ii) Lemma-4 3-case row operation (matching pair → H/T word via `onFst`/`onSnd`/
    CNOT + the inc-17 block-action + inc-16 `√2`-clearing; denExp drops by 1); (iii) Lemma-5 parity
    (even count of `0001` ⟹ matching pair) ⟹ `ReductionStep`; (iv) inc-15 `colLemma_of_reductionStep`
    ⟹ unconditional column lemma. All kernel-pure. THIS is the next build (elementary, NOT research-grade).

**Giles–Selinger build PROGRESS (inc 18–21, `GilesSelingerResidue.lean`, ALL kernel `decide` only —
native_decide held at 596, confirming Track-3 independence):**
- inc 18 (`47c2a5fd`): `normSq_cd_not_both_odd` — residue-norm classification (`{0000,0001,1010}`, never
  `1011`: `(|z|²).c`,`(|z|²).d` never both odd; `Q≡(a+c)(b+d)`, `P≡(a+c)+(b+d)`).
- inc 19 (`ba635d43`): `cHom`/`dHom`+`sum_c`/`sum_d` (coord sums distribute) + `dividesSqrt2_iff_normSq_
  cd_even` (active = not-√2-divisible ⟺ residue norm ≠ 0000).
- inc 20 (`0e200ed6`): parity engine — `emod_two_eq_zero_iff_zmod`, `intCast_zmod2_eq_ite`,
  **`even_card_filter_of_sum_even`** (even ℤ-sum ⟹ even count of odd summands).
- inc 21 (`0552a469`): **`exists_matching_residue_pair` = GILES–SELINGER LEMMA 5 DONE** — unit column +
  active entry ⟹ two distinct entries with matching residue norm mod 2, both active.
- **inc 22 (`GilesSelingerRowOp.lean`): LEMMA-4 CORE STEP + kernel-confirmed 3-case structure.** Settled
  via `#eval` over `ℤ[ω]/2` (`ω`-action `(a,b,c,d)↦(b,c,d,a)`, period 4): the active residues split by
  residue norm — `(P,Q)=(0,1)` ["1010"] = the SINGLE `ω`-orbit `{3,6,9,12}`; `(P,Q)=(1,0)` ["0001"] =
  TWO orbits `O₁={1,2,4,8}`, `O₂={7,11,13,14}=O₁⊕1111` (exactly Giles–Selinger's Case-3 sets). So Lemma 4
  is: **same-orbit (`x≡ωᵐy mod 2`) ⟹ single `H·Tᵐ`** (`core_step`: drops BOTH entries one denExp level,
  `(x±ωᵐy)/√2` at `denExp≤t` from level `t+1`, via `2 ∣ x±ωᵐy` ⟹ `√2²`-clear); **cross-orbit `0001` ⟹
  2-step `1111`-bridge** (follow-on). `core_step`+`denExp_mk_le_of_two_dvd`+`two_dvd_add_of_two_dvd_sub`+
  `mk_sub_same` all kernel-pure `{propext,Quot.sound}`; native_decide held at 596; lib+ExtractDeps green
  (9218). **CONFIRMS the settled plan** — "mechanical-concrete, NOT research-grade" = elementary multi-case
  (incl. the 2-step), exactly as designed; the single-`H·Tᵐ` insufficiency was always known (inc-16). Also
  corrected the stale inc-16 `MatchingResidue` docstring (the v2 "`kmm_lemma3` IS needed" conflation).
- **VALIDATED Lemma-4 construction (kernel `#eval` over `{-1,0,1}⁴`, 0 failures — the recipe for the next
  increment).** The UNIFORM 2-step handles BOTH same- and cross-orbit matched-active pairs:
  - **(A) √2-match always exists:** every matched-active pair has `∃m∈{0,1}, √2 ∣ (w_p − ωᵐw_q)`. **Clean
    proof (no big decide):** the mod-`√2` residue `r(z) := (a+c, b+d) mod 2 ∈ (ZMod 2)²` (so `√2∣z ⟺ r(z)=0`)
    is *determined by the norm class* — `1010` `(P,Q)=(0,1)` ⟹ `r=(1,1)`; `0001` `(1,0)` ⟹ `r∈{(0,1),(1,0)}`
    (since `P≡u+v`, `Q≡uv` with `u=a+c=r.1`, `v=b+d=r.2`). And `ω` acts on `r` by SWAPPING its two components
    (`r(ωz)=(b+d,a+c)=swap r(z)`, so `ω²` fixes `r`). Swap-orbits: `{(1,1)}`, `{(0,1),(1,0)}` — so matched-norm
    ⟹ same swap-orbit ⟹ `r(w_p)=r(ω^m w_q)` for `m=0` (if `r` equal) or `m=1` (if swapped). Step1 = `H·Tᵐ`
    keeps both entries at level `k` (`√2 ∣ w_p ± ωᵐw_q`), giving `(u₁,u₂)=(divSqrt2(w_p+ωᵐw_q),divSqrt2(w_p−ωᵐw_q))`.
    (Corollary: `1010` pairs have `r=(1,1)` always ⟹ √2-matched at `m=0`; consistent with `1010` = single ω-orbit.)
  - **(B) post-step1 is mod-2 aligned:** `∃m', 2 ∣ (u₁ − ωᵐ'u₂)` — so `core_step` (inc 22) is step2, dropping
    both to `denExp ≤ k-1`. (Same-orbit pairs also satisfy this directly via `core_step` alone — the 2-step is
    a uniform superset.)
  - **CAUTION (kernel-disproven shortcut):** the tempting "after step1, `u₁ = ωᵏu₂` EXACTLY" is FALSE
    (256/512 cross-orbit pairs fail it). (B) genuinely needs mod-`2√2` (`√2³`) residue analysis — the `u`'s
    depend on `w_p,w_q` mod 4 through `divSqrt2`'s `/2`. The structural proof tracks that; a single big decide
    over `ℤ[ω]/√2³` (64²·64 ≈ 262k) exceeds the kernel heartbeat budget (#10), so NOT a decide — structural.
- **inc 23 ✅ (`GilesSelingerRowOp.lean` `exists_sqrt2_match`): brick (A) DONE** — every matched-active pair is
  √2-matchable `∃m∈{0,1}, √2∣(w_p−ωᵐw_q)`, via the clean swap-orbit proof (norm class ⟹ mod-√2 residue; `ω`
  swaps its components; matched ⟹ same swap-orbit). `ZMod 2` kernel `decide` (256 cases) + parity bridge;
  kernel-pure `{propext,Classical.choice,Quot.sound}`; native_decide 596; lib+ExtractDeps green (9218).
- **Brick (B) DECOMPOSED + VALIDATED (kernel `#eval`, 0/512 cross-orbit failures — the recipe for the next
  increment).** The post-step1 mod-2 alignment splits into two clean halves:
  - **(B′) step1 lands the `u`'s in the `1010` class:** for cross-orbit `0001` matched-active pairs there is a
    √2-matching `m` (brick A) with BOTH `u₁=divSqrt2(w_p+ωᵐw_q)`, `u₂=divSqrt2(w_p−ωᵐw_q)` in the `1010`
    norm-class (`(normSq uᵢ).c` odd). This is the **mod-4 core** (`uᵢ` depend on `w`'s mod 4 via `divSqrt2`'s
    `/2`; `|uᵢ|² = |w_p±ωᵐw_q|²/2`, so the class is a `|·|²`-mod-4 fact). Strengthen brick A to deliver this `m`.
  - **(B″) `1010` ⟹ mod-2 aligned:** the `1010` class is the single ω-orbit `{3,6,9,12}`, so any two `1010`
    elements satisfy `∃m', 2∣(u₁−ωᵐ'u₂)` — a clean `ZMod 2` decide + bridge, exactly like brick A. (B″ also
    closes the `1010` case of Lemma 4 directly via `core_step`, single step.)
- **inc 24 ✅ (`GilesSelingerRowOp.lean`): brick (B″) DONE + the `1010` case of Lemma 4 CLOSED.**
  `exists_mod2_align_of_normSq_c_odd` (a `1010`-norm pair — `(normSq ·).c` odd, mod-2 residue in the single
  ω-orbit `{3,6,9,12}` — is mod-2 ω-aligned `∃m, 2∣w_p−ωᵐw_q`; `ZMod 2` `decide` in `∨¬` form + parity bridge)
  and **`lemma4_1010`** (= brick B″ ∘ `core_step`: a matched `1010` pair drops BOTH entries one denExp level in
  a single `H·Tᵐ`). Kernel-pure `{propext,Classical.choice,Quot.sound}`; native_decide 596; lib+ExtractDeps
  green (9218). [Decidability note: the implication-chain `∀ ZMod2, h₁→h₂→C` failed `Decidable` synthesis at
  this nesting; the `¬h₁ ∨ ¬h₂ ∨ C` form decides — reusable trick.]
- **inc 25 ✅ (`GilesSelingerRowOp.lean`): brick (B′) mod-4 core RESOLVED — far cleaner than the cross-term path.**
  The cross-orbit `0001` step1 is the `m` making `w_p+ωᵐw_q ≡ 1111 (mod 2)` (all coords odd; `#eval`-validated:
  this `m` always exists AND forces the 1010-landing). Then both `w_p±ωᵐw_q` are all-odd, and the **clean
  universal lemma** `normSq_c_mod4_all_odd` (all-odd `z` ⟹ `(normSq z).c ≡ 2 mod 4`, because `Q = a(b−d)+c(b+d)`
  and `(b−d)+(b+d)=2b≡2`) ⟹ `divSqrt2_normSq_c_odd` (both `divSqrt2(w_p±ωᵐw_q)` are `1010`) ⟹ `lemma4_1010`.
  `ZMod 4` decide + parity bridges; kernel-pure; native_decide 596; lib+ExtractDeps green (9218). (The
  cross-term `C.c mod 4` analysis was unnecessary — the all-odd ⟹ Q≡2 collapse is the real mechanism.)
- **inc 26 ✅ (`GilesSelingerRowOp.lean`): `matched_active_dichotomy` — the UNIFORM Lemma-4 case-split DONE.**
  Every matched-active pair is EITHER mod-2 `ω`-aligned (`∃m, 2∣w_p−ωᵐw_q` → `core_step`, the `1010` class +
  same-orbit `0001`) OR step1-able to all-odd (`∃m, w_p+ωᵐw_q` all-coords-odd → `divSqrt2_normSq_c_odd` +
  `lemma4_1010`, the cross-orbit `0001`). **Done KNOB-FREE** — the 12-disjunct `Prop` ∀ does exceed the
  default `Decidable`-instance depth, but a `Bool`-valued `dichB` + `dichB_true : ∀… dichB = true` (single
  `= true` body) sidesteps it with NO `synthInstance`/`maxRecDepth` (the worried-about knobs were AVOIDED;
  cf. the new `elaboration_knob_watchlist` validation check, which separates these elaboration knobs —
  kernel-pure, perf-only — from the `native_decide` soundness gate). All-odd clauses use `≠` (over `ZMod 2`,
  `x+y=1⟺x≠y`) so `rcases` never eliminates a compound equality; explicit left-nested `rcases` pattern +
  `ℤ→𝔽₂` parity bridge. Kernel-pure `{propext,Classical.choice,Quot.sound}`; native_decide 596; lib+ExtractDeps
  green (9218).
- **inc 27 ✅ (`GilesSelingerRowOp.lean`): step1 level computation + cross-orbit 2-step — the full Lemma 4 at the
  PAIR level is now COMPLETE.** `mk_sqrt2_mul_succ` (`√2`-peel `mk(√2·z)(s+1)=mk z s`); `step1_combo_eq`/`_sub`
  (`H·Tᵐ` on a `√2`-divisible all-odd combo keeps the pair at level `s` with the `divSqrt2` numerator);
  `cross_orbit_drop` (composes step1 + `divSqrt2_normSq_c_odd` [both outputs `1010`] + `lemma4_1010` ⟹ the
  cross-orbit pair drops one level in two `H·Tᵐ`; the `−`-combo all-odd from the coord relation
  `(w_p+ωᵐw_q).x+(w_p−ωᵐw_q).x=2w_p.x`). With `core_step` (aligned, one step), BOTH branches of
  `matched_active_dichotomy` are discharged. Kernel-pure `{propext,Classical.choice,Quot.sound}`; nd 596;
  lib+ExtractDeps green (9218).
- **inc 28 ✅ (`ColumnSynthesis.lean`, `04e6d90f`): circuit-realizability foundations** — `embedSnd/embedFst_
  realizableWithin` (an embedded single-qubit word is realizable within its length) + `interp_replicate` +
  `wHTm`/`wHTm_interp` (the `H·Tᵐ` row-op word). Kernel-pure; nd 596; 9218 green.
- **✅ DESIGN RESOLVED (2026-06-10, the inc-28 ⚠🔑 OPEN DESIGN Q): the `Gate2` wrapper = the `ctrl` block
  algebra + det-balanced row-op gadget `ctrl Tᵐ (H·Tᵐ) = CH·(I⊗Tᵐ)`.** Settled from first principles +
  substrate fan-out (the 1212.0506 §two-level-realization fetch failed — ar5iv truncates mid-Lemma-6 — but
  the determinant invariant pins the answer):
  - **Det obstruction (why the naive 2-level op fails, and why GS need an ancilla):** every `Gate2` generator
    has `det ∈ ⟨ω²⟩ = {1,i,−1,−i}` (`embedFst/Snd g`: `det₂(g)²` ∈ {1,ω²,…}; cnots: `−1`) ⟹ ANY `Gate2` word
    has `det ∈ ⟨ω²⟩`. The bare two-level `H·Tᵐ` at a pair has `det = −ωᵐ` — for **odd m NOT realizable on 2
    qubits, period** (so: never attempt controlled-`T`; this is the elementary content behind GS's one-ancilla
    clause). **Fix: balance with an UNCONDITIONAL phase** — `blockdiag(Tᵐ, H·Tᵐ) = Λ₁(H)·(I⊗Tᵐ)`: the spectator
    pair takes a harmless `ωᵐ` unit phase (denExp/normSq invariant), `det = −ω²ᵐ ∈ ⟨ω²⟩` for ALL m, and the
    only controlled piece is the FIXED gate `CH`.
  - **`ctrl P Q : Mat4`** (fst-blocked: `P` on the `fst=0` block, `Q` on `fst=1`) with `ctrl_mul : ctrl P Q *
    ctrl R S = ctrl (P*R) (Q*S)`; `cnot01 = ctrl 1 X`; `embedSnd A = ctrl A A`. Then `CZ = ctrl 1 Z =
    (I⊗H)·cnot01·(I⊗H)` (needs only `HXH=Z`, 2×2 decide) and **`CH = ctrl 1 H = (I⊗B)·CZ·(I⊗B†)`, `B =
    S·H·T·H·S†`** (`BZB† = H` hand-verified: `HZH=X`, `TXT† = [[0,ω⁷],[ω,0]]`, `H·that·H = (1/√2)[[1,i],[−i,−1]]`,
    `S·that·S† = H`; S,X,Z are native ADT gates, `S† = S·Z`). CH word ≈ 21 gates; all dim-2 facts by chunked
    single-mul kernel decides (the `T_mul_T_eq_S` precedent; 19-mul one-shot decides are untested scale).
  - **Gadget action = verbatim the shipped pair-level lemmas**: `(ctrl Tᵐ (H·Tᵐ)).mulVec v` at the `fst=1` pair
    = `invSqrt2*(v₁₀ ± ωSᵐ·v₁₁)` (= `core_step`/`lemma4_1010`/`cross_orbit_drop` shapes), spectators `(v₀₀, ωᵐv₀₁)`.
    Inverse gadget = `(I⊗T^{8−m})·CH` (`CH² = ctrl 1 H² = 1`, `T⁸=1` shipped). Cross-orbit = two gadgets at the
    same pair. Alignment: 6 pairs → canonical `fst=1` pair via ≤3-gate perm words (snd-pairs: id / `X⊗I`;
    fst-pairs: SWAP-conj, `swap = cx01·cx10·cx01`, `swap·ctrl P Q·swap = ctrl′ P Q`; diagonals: one cnot to a
    fst-pair) — perm `mulVec` = index relabel (colDenExp/unit invariant).
  - **Needed small lemmas (absent per fan-out):** `denExp (ωSᵐ·x) = denExp x`, `normSq (ωSᵐ·x) = normSq x`,
    parallelogram `normSq((x+u)/√2)+normSq((x−u)/√2) = normSq x + normSq u`, `mk`-extraction `denExp ≤ t+1 ⟹
    v = mk w (t+1)` (+ `denExp = t+1 ⟺ ¬dividesSqrt2 w`), `normSq_mk` numerator bridge `ΣnormSq(vᵢ)=1 ⟹
    Σ ZOmega.normSq wᵢ = 2^{t+1}` (feeds `exists_matching_residue_pair`'s `.c/.d ≡ 0` hypotheses; both class
    counts even via shipped `sum_c`/`sum_d` + `even_card_filter_of_sum_even` ⟹ actives ∈ {2,4}, ≤2 gadget rounds).
  - **Increment plan:** inc 29 `Gate2Control.lean` (ctrl algebra + CH + gadget realizability ≤28 + action);
    inc 30 alignment perms; inc 31 single-pair column drop (dichotomy→gadgets, spectators invariant, unit kept);
    inc 32 actives-induction ⟹ `ReductionStep C`; inc 33 **quantitative** column lemma (`colLemma_of_reductionStep`
    currently returns UNBOUNDED `∃L` — strengthen to `L ≤ C·colDenExp v + 9` for the O(log 1/ε) headline). Then
    controlled-C + operator-norm (NEXT design checkpoint: the n=3 det parity `⟨ω⁴⟩` bites the Λ-lift the same way
    — design against KMM §2.2–2.3/[9] before coding; the headline norm form likely ancilla-restricted
    `‖(W−Λ(e^{iφ})⊗I)·(I⊗|00⟩)‖`, which is what inc-8/9's leakage budget supports). **T2-remaining ≈ 2000–4100
    LOC**; then T1 (~2000–3900) + T3 (~3000–5700). Full LOC map: memory `[[project_phase6AO_progress_2026_06_09]]`.
- **✅✅ inc 29–33 SHIPPED (2026-06-10): the ENTIRE ReductionStep program is DONE — the dim-4 Giles–Selinger
  column lemma is UNCONDITIONAL, QUANTITATIVE, and kernel-pure.** Commits `4c46e307` (inc 29 `Gate2Control.lean`),
  `9de0a93b` (inc 30 `Gate2Perm.lean`), `f39ac035` (inc 31 `GilesSelingerPairDrop.lean`), `31d49ea3` (inc 32–33
  `GilesSelingerColumnLemma.lean`); lib+ExtractDeps 9222 green; native_decide 596; all headlines
  `lean_verify`-kernel-pure `{propext, Classical.choice, Quot.sound}`.
  - inc 29: `ctrl P Q` block algebra (`ctrl_mul`; `cnot01 = ctrl 1 X`; `embedSnd A = ctrl A A`); **CH = ctrl 1 H
    realized EXACTLY as an 18-gate Gate2 word** via conjugator `V = S·H·T·H·S†·H` (`V·X·V⁻¹ = H`); the
    **det-balanced row-op gadget `rowOpGadget m = ctrl Tᵐ (H·Tᵐ) = CH·(I⊗Tᵐ)`** (≤ 18+m gates, inverse
    `(I⊗T^{8−m})·CH`), exact column action = verbatim `core_step`/`cross_orbit_drop` shapes. 🔑 NEW TOOL:
    **`decide +kernel`** (pure kernel reduction, same trust base as `decide`, NO native_decide, NO heartbeat
    budget) — settles the 17-mul conjugator products that blow both `maxRecDepth` AND the 200k-heartbeat
    elaborator budget under plain `decide`. The det obstruction is documented in-file: every Gate2 word has
    `det ∈ ⟨ω²⟩`, so the bare two-level `H·Tᵐ` (det `−ωᵐ`) is UNREALIZABLE for odd m — the unconditional
    `I⊗Tᵐ` phase balances it (this is the elementary content behind Giles–Selinger's one-ancilla clause).
  - inc 30: `permMat` (pullback convention) + anti-composition + the **12-case ordered-pair alignment table**
    (`exists_pair_alignment`: mutually-inverse ≤5-gate perm words, kernel decide — the decide caught a
    transcription error in one case, the intended self-checking).
  - inc 31: **`exists_pair_drop`** — matched-active pair ⟹ realizable `G` (+ realizable inverse, `Ginv·G = 1`,
    ≤70 gates) dropping BOTH pair entries to `denExp ≤ t`, spectators' denExp unchanged (unit phases), unit
    sum preserved. Helpers: `ω⁸=1` + exponent capping (budget-bounded phases), denExp/normSq unit-phase
    invariance, the √2-parallelogram law, `mk`-extraction, `denExp (mk z (k+1)) = k+1 ⟺ ¬dividesSqrt2 z`.
  - inc 32–33: **`reductionStep_holds : ReductionStep 280`** (numerator-sum bridge `Σ|wᵢ|² = 2^{t+1}` ⟹
    Lemma-5 pair exists ⟹ pair-drop; active-set descent, ≤4 rounds — NO evenness counting needed at budget
    280) + **`column_lemma_bounded`: every unit ℤ[ω][1/√2] column is the first column of an exact 2-qubit
    Clifford+T word of length ≤ 280·colDenExp + 9** (linear in denominator exponent = O(log 1/ε)) +
    `column_lemma_unconditional`. **Circuit-C exact synthesis COMPLETE.**
  - ~~NEXT: controlled-C design checkpoint~~ **✅ RESOLVED + SHIPPED (inc 34–35, 2026-06-10, commits `a3220dfa`
    `4c03033b`; 9224 green; nd 596).** ar5iv §2.2 fetch settled both questions: (i) **W = controlled-C**, with
    the action stated on ancilla-INITIALIZED inputs `α|000⟩+β|100⟩ ↦ ≈ α|000⟩+βe^{iφ}|100⟩` and error
    `|β(e^{iφ}−γ)|² + |β|²‖g‖²` — verbatim the inc-8/9 amplitude+leakage budget; NO full-operator-norm claim
    (the restricted form is the faithful one). (ii) The det-parity analysis gives the per-gate lift rule —
    **target-diagonal gates (T/S/Z/id) lift UNCONTROLLED** (their `s=0` block fixes `|00⟩`; sidesteps the
    det-impossible controlled-T entirely); X→CNOT_s·, Y→S-conj, H→V-conj CNOT (inc-29 conjugator reused),
    cnots→**Toffoli** (CCZ phase-polynomial word `4sab = s+a+b−Σpairs+triple` mod 8, kernel-verified),
    ω→T_sys. Shipped: `CliffordTGate3.lean` (Gate3/Mat8, embedAnc transport at no length cost) +
    `Gate3Control.lean` (ctrl8 algebra; `ctrlLift_word_spec`: EVERY Gate2 word w lifts to ≤30·|w| Gate3 gates
    with `interp3 = ctrl8 D (interp2 w)`, `FixesE00 D`). 🔑 `decide +kernel` MUST be at top level (nested in a
    tactic `have` it re-enters the elaborator heartbeat budget).
  - ~~NEXT: headline assembly (a–e)~~ **✅ inc 36 SHIPPED (`45909061`, 9225 green): `kmm_z_rotation_word` —
    THE KMM Z-ROTATION HEADLINE WORD, UNCONDITIONAL, O(k) GATES.** ∀ φ k: an explicit 3-qubit Clifford+T
    word `W`, length ≤ 16800·k + 270 (linear in k = O(log 1/ε) exponent 1, ε = √2/2^k), with the |0,00⟩
    column RING-EXACTLY the indicator (FixesE00) and the |1,00⟩ column = |1⟩⊗|v⟩ (zero on the s=0 block):
    v unit, v(0,1) = 0, |00⟩-amplitude within √2/2^k of e^{iφ}, leakage ≤ 2√2/2^k. By linearity = the full
    KMM ≤2-ancilla guarantee on ancilla-initialized inputs. NO prime-density hypothesis (only Lagrange
    four-squares + the constructive column lemma). Kernel-pure (lean_verify).
  - ~~NEXT: the ∀U∈SU(2) extension (37–40)~~ **✅ TRACK 2 COMPLETE (inc 37–40 SHIPPED 2026-06-10,
    commits `5f64ac09` `0272c691` `e5e60f43`+`a5525cab` `f669f047`+`a9f0c029`+`2ab38be2`; 9229 green;
    nd 596; all kernel-pure via lean_verify).**
    - **inc 37 `Gate3Unitary.lean`:** `gateMatrix3_unitary` (ONE `decide +kernel` over the 30-element
      `Fintype Gate3`) → `interp3_unitary` (induction, congrArg-calc) → `toComplexMat8` intertwines
      `adjoint8` with `ᴴ` (`toComplex_conj`) → **embedded words ℂ-unitary** →
      `sumNormSq_mulVec_interp3` (squared-ℓ² preservation via `star_mulVec`/`dotProduct_mulVec`).
    - **inc 38 `KMMOperational.lean`:** `kmm_z_rotation_operational` — ∀φ k ∃W (≤16800k+270): ∀α β,
      `sumNormSq(W·(α,β-init) − target) ≤ |β|²(2/4ᵏ + 2√2/2ᵏ)` (8-index decide-dichotomy + two-support
      mulVec collapse; the verbatim KMM §2.2 state-level error).
    - **inc 39 `SU2Euler.lean`:** `su2_euler_decomposition` — ∀U∈SU(2) ∃φ₁φ₂φ₃ c (‖c‖=1):
      `U = c·Λ(φ₁)HΛ(φ₂)HΛ(φ₃)` (closed-form `eulerProd_eq` via `1±e^{iθ}` half-angle factorizations;
      polar `conj_polar` + arccos angle extraction; 3-case a=0/b=0/main). Euler-ZXZ ABSENT from Mathlib.
    - **inc 40 `KMMUniversal.lean`:** **`kmm_universal_headline` — THE ∀U KMM HEADLINE, UNCONDITIONAL.**
      ∀ U∈SU(2), k: ∃ 3-qubit Clifford+T word W, **length ≤ 50400·k + 812** (linear in k = O(log 1/ε)
      exponent 1), global phase c (‖c‖=1): ∀ unit (α,β), embedded W maps the ancilla-initialized state
      within **squared ℓ²-distance 9·(2/4ᵏ + 2√2/2ᵏ)** of the ideal (c⁻¹U)-rotated output. NO
      prime-density hypothesis (Lagrange four-squares + constructive dim-4 column lemma + Euler). Errors
      add through unitarity: `step_triangle` (EuclideanSpace/PiLp Minkowski bridge) + exact `sysH_step`
      Hadamard steps + `pair_norm_lam`/`pair_norm_h` unit-pair preservation along the chain.
      🔑 **Heartbeat-budget decomposition (invariant #10):** the monolithic proof exhausted the 200k
      per-declaration budget (isDefEq/whnf timeouts ATTRIBUTED to innocent sites — the budget is
      cumulative per declaration, the reported position is just where it ran out); hoisting the 3-step
      chain (`chain_bound`, explicit `step_triangle` instantiations + `rw`-aligned action equalities +
      `linarith` assembly — calc-free) and the squaring (`sq_le_of_sqrt_le_three_sqrt`) into top-level
      lemmas with their own budgets + deleting dead `have`s fixed it with zero `maxHeartbeats`.
      🔑 Bare `rw [mulVec_append]` is ambiguous when several `interp3 (· ++ ·)` occurrences exist —
      instantiate explicitly (`mulVec_append Wb [.onSys .H] t₃`) or rewrite the list first.
  - **NEXT: Track 1 (b–d) — FIRST verify §5/§6/§7 numbering vs primary 1403.2975v3; then T3.**

### Track 1 — unconditional scaffolding (paper-independent; advanced while the Track-2 DR is async)

**✅ PRIMARY-SOURCE VERIFICATION COMPLETE (2026-06-10, arXiv:1403.2975v3 PDF read end-to-end, all
40 pp).** The goal-mandated §5/§6/§7 check before any further Track-1 work. Verified structure:
§3 algebra (Def 3.1 rings; Def 3.4 LDE; λ=1+√2, δ=1+ω) · §4 ONE-dim grid problems (**Lemma 4.4**:
`δΔ ≥ (1+√2)²` ⟹ ≥1 solution — CONFIRMED) · §5 TWO-dim grid problems (§5.1 upright Lemmas 5.5/5.6;
§5.3 grid operators; §5.4 **Thm 5.16** 1/6-upright; §5.6 **Thm 5.18** general enumeration —
CONFIRMED; §5.7 scaled grids Def 5.20 / **Prop 5.22** increasing-k / **Lemma 5.23** two-disk
`rR ≥ (1+√2)²/2^k` ⟹ ≥2 solutions = thesis Lemma 5.2.38) · §6 Diophantine `t†t = ξ` (Lemma 6.1
doubly-positive necessary; **Thm 6.2** factoring reduction; full theory in **Appendix C**:
Def C.15 †-decomposable, **Lemma C.16 iff** (solvable ⟺ doubly-positive ∧ †-decomposable),
C.8/C.9/C.11 ℤ[√2]-splitting (p=2 ramified; p≡3,5(8) inert; p≡±1(8) split via x²≡2),
**Lemma C.20** (prime ξ over p †-dec ⟺ p=2 ∨ p≡1,3,5 (8)), **Lemma C.21 EVEN-POWER CRITERION**
(ξᵐ †-dec ⟺ m even ∨ p≡1,2,3,5 (8) — obstruction ONLY at primes over p≡7(8), which are the
ℤ[√2]-split / relatively-INERT ones), Remark C.22 constructive via u²≡−1 (p≡1(4)) / u²≡−2 (p≡3(8)),
**Prop C.26** (n=ξ•ξ·2^ℓ prime ≡1(8) ⟹ solvable — the Algorithm-7.6 easy case; n≡1(8) by
Lemma 8.4/App D) · §7.1–7.3 synthesis (Lemma 7.2 WLOG; **Lemma 7.3 T-count = 2k−2 or 2k**;
Problem 7.4; **§7.2 = ε-region 𝓡_ε eq. (14)**; §7.3 **Algorithm 7.6**, factoring at step 2(b)) ·
§8 analysis (**Hypothesis 8.3 = THE prime-density hypothesis**; Prop 8.8 near-optimality
`m'' + O(log log 1/ε)`; §8.3 worst-case `K+4log₂(1/ε)`, **Conjecture 8.10** typical
`K+3log₂(1/ε)`) · §9 up-to-phase (Cor 9.5 λ∈{1,e^{iπ/8}}; Lemma 9.7 T-count 2k−1/2k+1).
**Numbering errata FIXED in repo (commit this session):** "§4 factoring fast-path" → Thm-6.2/Alg-7.6
factoring path (GridSynth, GridSolver); "§5 Theorem 2" → Thm 5.18 + Prop 5.22 (GridSolver);
"§5 ε-region" → §7.2 eq. (14) (GridSolver); "RS Hypothesis 29" → **Selinger arXiv:1212.6253
Hypothesis 29 = 1403.2975v3 Hypothesis 8.3** (AncillaCompletion, LogLengthHeadline — 1212.6253
uses sequential numbering, CONFIRMED by fetch; its K+12log₂(1/ε) is the ∀SU(2) slope, K+4 the
z-rotation slope, hence the DR's "3–4 not 12"). Historical log entries above retain the old
shorthand; THIS block is the citation source of truth. Thesis refs (Prop 3.2.7/3.2.4,
Lemma 5.2.38) are Ross-thesis numbering, kept as separate-source citations.

**Track 1 (b–d) implementation plan (verified anchors):** (b) ~~`GaussInt2 = ℤ[√2][i]`
EuclideanDomain~~ **MATHEMATICALLY IMPOSSIBLE as roadmapped** — ℤ[√2][i] is an index-2
non-integrally-closed subring of ℤ[ω] (paper Lemma 5.5: `ℤ[ω] = ℤ[√2][i] ∪ (ℤ[√2][i]+ω)`), so it
is never a UFD, let alone Euclidean; caught by the primary-source verification. The correct object
is the FULL `ZOmega = ℤ[ζ₈]`. **✅ (b) SHIPPED 2026-06-10 (`e78d8c43`, 9230 green, kernel-pure):
`ZOmegaEuclideanDomain.lean` — `EuclideanDomain ZOmega`** (Mathlib has none for ℤ[ζ₈]): ℤ[i]-pair
Gaussian rounding on the `{1,ω}`-grading (γ=d+bi, δ=c+ai; relative conj = the existing `σ5`;
`norm t = N_ℤ[i](t·σ5 t)` = sum of two squares ⟹ `norm_nonneg` free), descent crux
`|eγ²−i·eδ²|² < 1` via the **perpendicular-corner rescue** (all-corners: eγ² purely imaginary,
i·eδ² purely real ⟹ value 1/2; algebraic skeleton `A²+B² = S² − 2(e₁(f₁−f₂)+e₂(f₁+f₂))²`).
Plus `IsDomain ZOmega`, `norm_eq_zero_iff` (ℤ[√2]-descent via `Zsqrtd.norm_eq_zero`/`two_ne_sq`),
`norm_σ5`, grading lemmas, natAbs descent. ⟹ PID/UFD/gcd for ℤ[ω] — the C.18–C.21 gcd engine.
🔑 Lean lesson: `field_simp` rewrites inside `round`-atoms and breaks cancellation — prove the
round-free exact-quotient identities first, then close coordinate identities with
`linear_combination` (coefficient −1), keeping `round` atomic.
(c) even-power criterion = Lean-ify **C.16 + C.19/C.20/C.21** over the shipped
`Zsqrt2EuclideanDomain` + new `ZOmega` gcd (splitting law C.8/C.9/C.11; constructive u²≡−1/−2
cases per C.22; lift Mathlib `Nat.eq_sq_add_sq_iff` template).
**✅ (c) inc 1 SHIPPED (`9c7781ec`): `Zsqrt2Units.lean` — Lemma C.2** (doubly-positive units of
ℤ[√2] are squares) by fundamental-unit descent WITHOUT unit-group classification: λ⁻²=3−2√2
shrinks `im.natAbs` (im=1 impossible: re²=3); the φ<1 branch star-flips INSIDE the recursion at
the smaller measure. Real-embedding order `zsqrt2ToReal`.
**✅ (c) inc 2 SHIPPED (`13a7e602`): `RelNormSolvability.lean` — Lemma C.16**
(`relNorm_iff_doublyPositive_decomposable`): t†t = ξ solvable in ℤ[ω] ⟺ ξ doubly-positive ∧
†-decomposable. Infrastructure: `zsqrt2ToZOmega` (ℤ[√2]→+*ℤ[ω]; conj-fixed; σ5↔star;
toComplex↔zsqrt2ToReal via `s2C_eq`), `relNormZsqrt2` + **norm tower**
`N_ℤ[√2](relNorm t) = N_ℤ[ω](t)` ⟹ t≠0 strict positivity via `norm_eq_zero_iff` (no
toComplex-injectivity). **✅ (c) inc 3 SHIPPED (`88818fa4`): Lemma C.19** (`RelNormMultiplicativity.lean`,
`daggerDecomposable_mul_iff`) — Bezout-only (conjHom dvd-transport; IsCoprime.map; gcd_eq_gcd_ab
expansion; conj-fixed ⟺ embedded descent). **✅ (c) inc 4 SHIPPED (`e0ca23a7`): the EVEN-POWER
OBSTRUCTION** (`RelNormEvenPowerObstruction.lean`, `not_daggerDecomposable_of_norm_pow_seven`) —
N(ξ) = ±(a²+b²) for †-decomposables (norm tower + ℤ[i]-Gauss form) and a²+b² ≢ 7 (mod 8); plus
`daggerDecomposable_pow_even`/`DaggerDecomposable.pow`. **✅ (c) incs 5–6 SHIPPED
(`22d7fe95` + `bf19314a`): the C.20 ENGINE** (`daggerDecomposable_of_prime_dvd_normSq` —
three-possibilities via t = gcd(embed ξ, w), dvd_prime_pow, gcd_isUnit_iff, conj-fixed descent)
**+ INSTANCES** (p=2 √2 = λ⁻¹δ†δ; p≡1(4) via u+i / `ZMod.exists_sq_eq_neg_one_iff`; p≡3(8) via
u+√2i / `exists_sq_eq_neg_two_iff`; `ZMod.intCast_surjective` lifts — no val-plumbing)
**+ `daggerDecomposable_pow_iff_seven`** = **LEMMA C.21, THE EVEN-POWER CRITERION (iff)**:
N(ξ)=±p, p≡7(8) ⟹ (ξ^m †-dec ⟺ Even m). **TRACK 1 (a–d) COMPLETE.**
**✅ (d) SHIPPED (`35cb7b09`, 9233 green, kernel-pure): `GridExistenceSharp.lean` —
Lemma 4.4 SHARP product form** (`oneDim_grid_exists_product`): `δ·Δ ≥ (1+√2)²` ALONE gives 1-D
grid existence at every position — the asymmetric tiny-ε-region × huge-disk form Lemma 5.23 /
eq.(21)'s `k₂ ≤ 2+2log₂(1+√2)+2log₂(1/ε)` consumes (center-rounding needed BOTH ≥ 1+√2).
Selinger 1212.6253 Lemmas 16–17 formalized: `OneDimCoverage` + mono/swap/λ-rescale moves
(α ↦ λα; λ• = −λ⁻¹ flip absorbed by the ∀-position), 3-candidate base `(1+√2, √2)` via floor
bracketing, λ-power families (`Int.induction_on`), assembly by λ-power bracketing with the
swapped family at j+1 rescuing the √2-gap (λ ≥ 2). 🔑 Lean: division atoms defeat
nlinarith — use multiplication-only positions (λ⁻¹ = √2−1) + explicit `linear_combination`
product-equalities, then plain `linarith` on the monomial atoms.
Terminal ancilla-free existence stays a tracked `Prop` (strictly weaker than Hyp 8.3 —
relative-norm density, not primality), NEVER an axiom.

### Track 3 + 2-qubit-synthesis JOINED PROGRAM (2026-06-09; user-approved, <10k LOC bar; method = my judgment, elegance-first)

**Reprioritization (user, upstream-driven):** `native_decide` blocks any Mathlib/physlib upstream;
Mathlib *also* rejects slow `decide` (CI), so the 4 sites + the 2-qubit synthesis must be kernel-pure.
Track 3 is therefore **critical path**, done jointly with the (fresh, kernel-pure-by-design) synthesis.

**Probe (sizes + method + LOC estimate ≈ 7.4k central, auto-approved <10k):**
- The 4 `native_decide` cores are consumed by structural wrappers (`KMMCompleteness.bridge_u`/
  `cliffordBase_u`/`ma_step_exists_u`, `KMMLemma3Column`) via `reconstruct_box_data_unitary` + the box
  check ⟹ eliminating a core upgrades its wrapper to fully kernel-pure.
- `bridge_box_core` (`KMMBridge.lean:132`): 1664 of `zomBox²×8` (zomBox=5⁴=625), checks `kSO3≤3`.
  **Method: structural `μ≤3 ⟹ kSO3≤3`** (sde↔kSO3 balancing; `muMeasure_le_kSO3_add_two_u` is the
  reverse, present). ~400–700 LOC. *Most tractable — START HERE.*
- `maStep_exists_core` (`MAStepExists.lean:256`): ~809k `validCol³`. **Method: orthogonality-class
  ORBIT reduction** (signed-perm/Clifford orbits of orthogonal triples → small reps + invariance lemma
  + small kernel `decide`). ~800–1500 LOC.
- `cliffordBase_box_core` (`CliffordBase.lean:291`): `zomBox²×8` filtered `kSO3=0`, ≤6-word coverage.
  **Method: Clifford-orbit coverage** (reduce to coset reps). ~800–1500 LOC.
- `kmm_lemma3_alg2` (`KMMLemma3.lean:113`): ~16.7M over `(ZMod 8)⁴²`. **Method: structural mod-8
  sde-reduction** (ω-action mod 8 symmetry; the gde valuation algebra). ~1000–2000 LOC. *Hardest
  (research-flavoured) — LAST.*
- **2-qubit synthesis (circuit C + controlled-C + leakage bound):** no existing multi-qubit substrate;
  Giles–Selinger column lemma at dim 4 (cleaner than the single-qubit SO(3) route), designed kernel-pure.
  ~3,000–5,000 LOC.

**Build order:** bridge (tractable win + valuation machinery) → maStep → cliffordBase → kmm_lemma3 →
the 2-qubit synthesis (reusing the kernel-pure base-case machinery). Each a complete kernel-pure unit;
ship incrementally. Construction reference: `Lit-Search/Phase-6AO/KMM-1212.0822-...-websearch.md`.

- **Track 3 site 1/4 ✅ — `bridge_box_core` native_decide ELIMINATED (`f6a4f0ad` inc 1 + `2a5e33ca` inc 2).**
  Inc 1 `BridgeParity.lean`: the structural core `sqrt2_sq_dvd_sq_add_sub` (|x|²+|y|² = √2⁴ ∧ √2∣|x|²
  ⟹ √2²∣(x²±y²)) via the parity/δ-ramification calculus (δ=1+ω, δ²=√2·⟨0,1,1,1⟩; equal-parity squares
  agree mod √2; mixed case refuted by the halving lemma). Inc 2 `BridgeStructural.lean`: nine per-entry
  `denExp_bloch_{xx..zz} ≤ 3` bounds for `reconstruct x y k` (one declaration each, Inv #10 budgets;
  uniform script: simp-expansion to `mk`-form → `denExp_mk_le_three` workhorse → `linear_combination`
  with per-entry ω-phase coefficients; xy needs the `+2ω²(w̄−w)` M-correction, yy the `ω⁴=−1` relation).
  The four factor-2 conjugate-pair entries (xz/zx/yz/zy) are UNCONDITIONAL (no hypotheses). Assembled:
  `kSO3_reconstruct_le_three` (∀ x y k — NO box, NO enumeration, NO coordinate bounds) + the moved
  structural `bridge`. `bridgeBoxOk`/`bridge_box_core` (1664-tuple native_decide) DELETED from
  `KMMBridge.lean` (reconstruction substrate + `zomBox` retained for CliffordBase);
  `KMMCompleteness.bridge_u` rewired (coordinate-bound conjuncts of `reconstruct_box_data_unitary`
  now unused there). **`bridge`, `bridge_u`, `kSO3_reconstruct_le_three` all verify kernel-pure
  `{propext, Classical.choice, Quot.sound}`.** Negative result (3× measured): `decide +kernel` on the
  box sweep hits the elaborator pre-eval wall (~108–112 s, ≈100–150k whnf steps) — kernel decide CANNOT
  host these checks; the structural route was the only path. Full lib+ExtractDeps green (9239 jobs).
  Remaining sites: `maStep_exists_core` → `cliffordBase_box_core` → `kmm_lemma3_alg2`.
- **Track 3 site 2/4 ✅ — `maStep_exists_core` native_decide ELIMINATED (`83e7fd13` inc 3).**
  `MAStepStructural.lean`: the Giles–Selinger §6 PARITY ARGUMENT replaces the ~809k-tuple
  `validCol t`³ sweep. The hypotheses contribute exactly 4 mod-2 congruence families (F1 column
  q-sum even; F2 selfDot-√2-part; F3 dot-rational; F4 dot-√2-part); distinct nonzero even-weight
  parity vectors have 𝔽₂-inner-product 1, so all odd columns share ONE pattern, and the matching
  syllable (T={1,2}, HT={2,3}, SHT={1,3}) kills every column. `killCond_engine` = ONE 12-variable
  mod-2 lemma (witness pattern + F2(W) + target F1/F3/F4 ⟹ all 3 kill conditions; the self case
  reuses it since F3(W,W) derives from F1(W) + t²≡t and F4(W,W) from commutativity).
  `someKills_of_orthogonal` holds for ANY even selfDot t — `ma_step_exists`/`ma_step_exists_u`
  DROP the former `kSO3 ≤ 3` hypothesis (strictly stronger: reducing syllable for EVERY
  kSO3 ≥ 1). Box machinery (validCol/realBoxList/intBox + membership chain) deleted from
  MAStepExists + KMMCompleteness. All kernel-pure `{propext, Classical.choice, Quot.sound}`.
  9240 green. 🔑 lessons: .a-coordinate extractions carry BOTH product orientations as separate
  omega-atoms — bridge with `mul_comm` haves; matrix-literal entries reduce definitionally under
  `show` (no simp set needed for `stripRow` row identities); permuted-order engine application
  bridges by bare `omega` (same atoms, reordered sums).
- **Track 3 site 3/4 ✅ — `cliffordBase_box_core` native_decide ELIMINATED
  (`996be365` inc 4a + `36a87704` inc 4b + `f6769a41` inc 4c).**
  4a `ZOmegaTorsion.lean`: |z|²=1 ⟹ z=ωʲ, |z|²=2-lit ⟹ z=√2ωʲ, |z|²=4-lit ⟹ z=2ωʲ
  (aux-decomposed range bashes closing by decide on the CLOSED substituted normSq equation;
  mod-4 square parity splits all-even/all-odd) + Galois positivity 2(|z|²).c² ≤ (|z|²).d².
  4b `CliffordBaseStructural.lean`: blochEntry_reconstruct_zz (R₂₂ = mk (2(|x|²−|y|²)) 6,
  k-free; raw simp-NF level is 18 ⟹ mk_eq_mk_iff + √2¹⁸-lc), kSO3=0 ⟹ 4∣|x|²−|y|²,
  normSq_quantized trichotomy (x=0∧|y|²=4)∨(2,2)∨(|x|²=4∧y=0) via Galois on both coords.
  4c: per-class kernel `decide +kernel` coverage checks cliffordCover_{y2,x2,mid_0..7+
  dispatcher} (640 torsion tuples; 64/chunk — a single 512-tuple decide busts the ~200k
  heartbeat wall; 3-level bounded-∀ Decidable does NOT synthesize — chunk over literal
  exponents + omega-rcases dispatcher) verify the 192-entry cliffordTable; cliffordBase +
  cliffordBase_u rewired (quantization → torsion class → coverage); cliffordBaseBoxOk/
  cliffordBase_box_core DELETED; KMMBridge coordBox/zomBox/mem_zomBox deleted (last box
  remnants); reconstruct_box_data(_unitary) coordinate-bound conjuncts dropped
  (strengthening discipline). **cliffordBase / cliffordBase_u kernel-pure**;
  `nonempty_kmmReduction` now carries ONLY kmm_lemma3_alg2's native axiom — site 4/4 is
  the last. 9242 green. CliffordBase one-time compile ≈ 280 s (the 10 kernel decides).
- **🏆 Track 3 site 4/4 ✅ — `kmm_lemma3_alg2` native_decide ELIMINATED (`8375e175` inc a +
  `e774007c` inc b + `85a64ad7` inc c) ⟹ TRACK 3 COMPLETE: the entire KMM exact-synthesis
  arc is native_decide-FREE.** The T-PAIRING CALCULUS (`KMMLemma3Structural.lean`): with
  `B(x,z) = Σxᵢzᵢ` and `Tₖ = B(x,ωᵏy)`, the statement depends on residues only through
  `(P(x),Q(x),P(y),Q(y),T₀..T₃)` — update formulas `P(x+z) = P+P+2B`,
  `Q(x+z) = Q+Q+(B(x,ωz)−B(x,ω³z))`, P/Q ω-invariance, `Tₖ₊₄ = −Tₖ` (all `ring` over
  destructured `Coord4`). REACHABILITY: `x·ȳ = ⟨T₃,T₂,T₁,T₀⟩` exactly ⟹ norm
  multiplicativity descends to `P·P'+2Q·Q' = ΣTᵢ²` and `P·Q'+Q·P' = T₃T₂+T₂T₁+T₁T₀−T₃T₀`
  (numerically decisive: free-T master FAILS 491k/1.18M; WITH the constraints 0/36864).
  TWO kernel master sweeps `kmm_master_a/b` (qY = −qX substituted; pY-branches −pX / 4−pX;
  262k tuples each, ONE `decide +kernel` decl each, ~80 s — no chunking needed).
  `KMMLemma3Alg2.lean` re-proves the EXACT original statement (consumers untouched modulo
  one import line in `KMMLemma3Column`): `P+P' ∈ {0,4}` dichotomy → massage to
  (P,Q,T)-data → master instance → transport via `gde_add_eq_of` + `Bform` index folds,
  per-k `congrArg₂ gdePQ` + `linear_combination` closers. The ~16.7M-pair `native_decide`
  DELETED from `KMMLemma3.lean`. Kernel-pure; 9244 green; axiom_closure PASS;
  **native_decide-tainted declarations 593 → 546** (the whole KMM completeness/synthesis
  chain un-tainted). Counts refreshed: theorems=12130, modules=929, sorry=0.
  🔑 lessons: per-decl 262k ZMod-8-arith kernel sweeps PASS comfortably (~100× lighter per
  tuple than kSO3-evals); `fin_cases` emits mk-form Fin literals (rw-patterns with
  `(1 : Fin 4).val` DON'T match — normalize via `Nat.reduceAdd` simproc + defeq-`show`s or
  avoid by `congrArg₂`+lc); slim files need explicit Mathlib.Tactic.{Ring,LinearCombination,
  NormNum,FinCases} imports; iterate heavy-decide files by splitting proof-iteration into a
  separate file (masters cache in olean).
- **Track 1(b) brick ✅ — `GaussInt2 = ℤ[√2][i]` is an integral domain (`b5123126`).**
  `lean/SKEFTHawking/FKLW/RossSelinger/Zsqrt2GaussInt2Domain.lean`: `zsqrt2_sq_add_sq_eq_zero`
  (`a²+b²=0 ⟺ a=b=0` over ℤ[√2] — formal reality at the integer-coordinate level via `nlinarith`, **no
  real embedding** needed, which Mathlib lacks for `Zsqrtd 2`) + `GaussInt2.norm_eq_zero` +
  `Nontrivial`/`NoZeroDivisors`/`instIsDomain`. **Fully kernel-pure** (native_decide unchanged at 596).
  Next Track-1 bricks: GaussInt2 `EuclideanDomain` (mirrors the shipped `Zsqrt2EuclideanDomain`) → PID/UFD
  → the splitting law (`x²+1` mod π) → the even-power relative-norm criterion 1(c) → "ancilla strictly
  helps". Track 1(a) ℤ[√2]-ED already shipped.

### Track 2 — remaining circuit layer (faithful factorization; sequenced, NOT de-scoped)

> **⚠ SUPERSEDED (inc-1–6 era snapshot; kept for history).** Two statements below are now STALE and would
> UNDER-claim if read as current: (i) "(5) rounding … hypothesized project-wide … carry it as a tracked
> input" — **inc 8 DISCHARGED the rounding unconditionally** (`kmm_amplitude_approx`); the z-rotation
> headline carries NO rounding hypothesis. (ii) "the precise KMM-1212.0822 construction → DR dispatched" —
> **RESOLVED by the inc-6 web search** (construction = the dim-4 Column Lemma; no DR pending). Current truth
> = the inc 7–16 log + the corrected inc-15/16 block above.

The full `∀U∈SU(2)` O(log 1/ε)-with-≤2-ancillas headline factors as: **(1) keystone ✅ → (2) 2-qubit
semantics ✅ → (3) state-column → ring-unitary (orthonormal completion over ℤ[ω][1/√2]) → (4) 2-qubit
exact synthesis (`Gate2`-word, length O(sde) — the general KMM multi-qubit row-reduction; the major
remaining build) → (5) rounding (target → integer-residual approximant within ε)**. (3)/(4) are general
ring linear algebra + general 2-qubit synthesis — they do NOT need the paper-specific KMM-1212.0822
gate sequence, so they are buildable faithfully. (5) is the §5 grid analysis — already **hypothesized
project-wide** (even the single-qubit `rossSelinger_compile_log_length` takes the rounding quality
`h00` as a hypothesis), so it is consistent to carry it as a tracked input and prove the unconditional
completion+synthesis around it. **Status (inc 1–6 above):** the entire FOUNDATION is built and verified —
the unconditional NT core (1), 2-qubit semantics (2), the unconditional normalized ancilla *state*
existence (3), system-line synthesis at the KMM length (4), the realizable class (5), and the
**O(log 1/ε) length-composition law** (6). **The single remaining Track-2 piece** is brick (B): the
explicit ancilla *unitary* that block-encodes `U` with the ancilla restored to |0⟩ **deterministically**
(NOT the naive (u,v,t₁,t₂) column, which leaks into ancilla-|1⟩ = a post-selected scheme), then its
two-qubit exact synthesis into a `Gate2`-word — which, by inc 6, is then O(log 1/ε) automatically. This
needs the **precise KMM-1212.0822 construction** to formalize faithfully (the project does not guess a
published circuit) → **DR dispatched** (see execution log). Once back, brick B + the synthesis assemble
the full `∀U` headline on the inc-1–6 foundation. Tracks 1 (b/c/d) + 3 (native_decide ×4) remain in scope
and untouched (paper-independent; available for continuations while the DR is async).
