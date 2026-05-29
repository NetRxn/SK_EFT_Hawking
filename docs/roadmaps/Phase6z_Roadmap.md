# Phase 6z: Faithful CCZ-essential SU(8) — literal Clifford+CCZ density via the irrational-angle seed

## Technical Roadmap — May 2026

*Prepared 2026-05-28, following the Phase 6y T-A2′ honest-scope closure (Clifford+T at SU(8)) and two
deep-research seed spikes.*

**Trigger condition.** Phase 6y closed its SU(8) instance (T-A2′) on the **universal Clifford+CCZ+T**
alphabet `cliffordCCZGeneratingSetSU8 = {H_qi, T_qi, CNOT_ij, CCZ}`, whose density rests **entirely on
the `{H,T,CNOT}` (Clifford+T) sub-alphabet** — `CCZ` is over-complete and **unused** in the witness
(`grep`-verified; module docstrings say so). So 6y delivered *Clifford+T at SU(8)*, **not** the
roadmap's intended instance (2) "Clifford+CCZ at SU(8), **CCZ compiled not primitive**". Phase 6z
delivers that faithful, CCZ-essential statement.

**Headline goal.** Prove the **literal Clifford+CCZ alphabet `⟨H, S, CNOT, CCZ⟩` (NO `T`) is dense in
SU(8)**, yielding the UNCONDITIONAL multi-qubit Solovay–Kitaev headline for that alphabet — the same
`SolovayKitaevHeadline_FreeGroup_SUd`-shaped result 6y shipped, but where `CCZ` is the **essential
non-Clifford resource** (no `T`).

**The methodology distinction (this is the scientific point, and the clean phase boundary).**
- **Phase 6y route (per-qubit density):** `T` is a single-qubit infinite-order gate ⟹ `{H,T}` is dense
  in SU(2) per qubit (Phase 6u) ⟹ continuous per-qubit flows for free ⟹ spread by conjugation. CCZ
  never needed.
- **Phase 6z route (von-Neumann / Kronecker seed density):** the literal alphabet is **all
  finite-order** ({H,S} = finite single-qubit Clifford; CCZ order 2), so there is **no** per-qubit
  continuous flow. The first continuous flow must be *manufactured* from an **infinite-order product
  word with an irrational-angle eigenvalue** (a CCZ·Clifford word) via Kronecker accumulation of
  `{gⁿ}`, then spread to `𝔰𝔲(8)` by Clifford conjugation + BCH/Trotter bracket closure. This is the
  CCZ-essential mechanism (CCZ supplies the non-Clifford "twist" that makes the eigen-angle irrational).

Two genuinely different density mechanisms for the same target (SU(8)); 6z is the harder, faithful one.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6z WORK (no exceptions, incl. subagents / post-compaction):**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` "Mandatory References" (Wave Execution
>    Pipeline, Inventory Index, README, Lean-Development-Optimization, Aristotle reference). Use the
>    **`lean4` skill** for all Lean work (LSP/MCP loop — `lean_goal`/`lean_multi_attempt`/
>    `lean_diagnostic_messages`/`lean_local_search`/`lean_leansearch`/`lean_loogle`/`lean_hover_info`/
>    `lean_declaration_file` — beyond `grep`).
> 2. **Read the two DR seed spikes DIRECTLY** (per CLAUDE.md hard-proof discipline — do NOT delegate
>    depth-reading to subagents):
>    - `Lit-Search/Phase-6y/Phase 6y · T-A2′ — Clifford+CCZ Seed Element.md` (DR1: seed
>      `CCZ·(H⊗H⊗H)`, `tr=1/√2`; frames the seed as the easy part, Phase-C lift as the cost).
>    - `Lit-Search/Phase-6y/Phase 6y : SK_EFT_Hawking Irrational-Angle Seed for Density of ⟨H, S, CNOT, CCZ⟩ in SU(8).md`
>      (DR2: the **operative** seed `g₀ = (H⊗H⊗H·CCX)²`, eigenvalues **`(−3±i√7)/4`** [Gate-1 corrected;
>      DR2's stated `(3±i√7)/4` had the Re λ sign flipped], `det=1∈SO(8)`, algebraic-integer
>      irrationality, full Mathlib-decl table + gotchas, BEST/TYPICAL/WORST scope).
>      **DR2 supersedes DR1's seed** (explicit 2-D eigenblock for the flow); both irrationality
>      skeletons are valid.
> 3. **Read this roadmap + the four `docs/roadmaps/Phase6z/` detail docs** (progressive disclosure):
>    `Substrate_Inventory.md`, `Mathlib_Decls.md`, `PreLean_CAS_Gates.md`, `Citations.md`.
> 4. **Read the Phase 6y roadmap** (`docs/roadmaps/Phase6y_Roadmap.md`) — esp. the Wave-1 close block
>    + the "T-A2′ SU(8) RESOLUTION" — to understand what 6y shipped (Clifford+T) and why 6z exists.
> 5. **Wave 0 (CAS gates) is a HARD GATE before any Lean.** See `Phase6z/PreLean_CAS_Gates.md`. The
>    Clifford-orbit-dimension result sets the entire phase budget (BEST/TYPICAL/WORST). Do NOT commit
>    Lean LoC before Wave 0 completes.
> 6. **Pipeline invariants #10 (no `maxHeartbeats` in proofs), #15 (no new axioms), #16 (AI-defect
>    defense)** — RESPECTED. New modules pass the Tier-1/2 checks of `docs/AI-Defect-Defense-Layer.md`.
> 7. **No PM/time estimates** (user direction). LoC estimates are Regime-B internal-velocity only.

---

## Track / Wave catalog

Phase 6z **was scope-gated by Wave 0**. ✅ **Both CAS gates now PASS (2026-05-28) and the
orbit-dimension check returned spanned dim = 63 ⟹ BEST case** — so the budget is locked at the BEST
column: Wave 4 ~400 raw LoC, **Wave 3 (SU(d) Trotter) DROPPED** (no BCH/Trotter closure needed). The
single largest scope risk is eliminated.

| Wave | Content | Gate / dependency | Raw LoC |
|---|---|---|---|
| **6z.0** | **Pre-Lean CAS gates**: `verify_seed.py` (confirm `g₀` spectrum + `det=1`) + Clifford-orbit-dimension check (`dim span{Ad_U(X)}`). | **HARD GATE** — precedes all Lean. | ✅ DONE (PASS/PASS, BEST) |
| **6z.1** | Seed element + **algebraic-integer irrationality** (`g₀∈SO(8)`, char-poly `(λ−1)⁶(λ²+(3/2)λ+1)`, `λ_±=(−3±i√7)/4`, minpoly `2λ²+3λ+2`, `not_rootOfUnity_of_minpoly_not_int`). | 6z.0 seed confirmed (✅ Gate-1 PASS). | ~860 |
| **6z.2** | **First flow**: 1-D circle density (`irrational_dense_on_circle` via `AddSubgroup.dense_or_cyclic`) + unitary spectral log (`X = i·log g₀ ∈ 𝔰𝔲(8)`) ⟹ `exp(tX) ∈ closure⟨…⟩`. | 6z.1. | ~375 (incl. in 860/glue) |
| ~~**6z.3**~~ | ~~**SU(d) Trotter generalization** of `trotter_sequence_tendsto` (SU(2)→SU(8)).~~ | **DROPPED — Gate 2 = BEST (no BCH/Trotter closure needed).** | ~~250~~ → 0 |
| **6z.4** | **Pure-conjugation spread to `𝔰𝔲(8)`** (Clifford-orbit of `X` spans 63-dim **by itself** — Gate-2 confirmed; reuse `suEightTangent_spans` + `flow_conj_mem`/`qubit_iEmbed_conj`, **no bracket closure**) ⟹ `ClosureDenseWitness` for `⟨H,S,CNOT,CCZ⟩`. | 6z.2. **BEST scope (Gate 2).** | **~400** |
| **6z.5** | **Headline + Stage-13**: instantiate `SolovayKitaevHeadline_FreeGroup_SUd` for the literal alphabet via the shipped `…_headline_of_witness` chain; whole-phase fresh-context adversarial review (CP-6z). | 6z.4. | ~150 + review |
| **6z.D** | *Deferred*: multi-dimensional Kronecker–Weyl on `𝕋^d` (only if simultaneous-flow recovery is later needed; **not** needed for the first flow). | re-evaluate post-6z.5. | ~600 |

**Load-bearing risk — ✅ RESOLVED (Gate 2, 2026-05-28):** whether Clifford conjugation of
`X = i·log g₀` **alone spans `𝔰𝔲(8)`** is now settled — **it does** (spanned dim = 63, BEST). No BCH
layer, no multi-layer closure. DR2's "Clifford-orbit-spans" claim is confirmed *by computation*
(`Lit-Search/Phase-6z/orbit_dimension.py`), not by the mis-attributed Aaronson–Gottesman citation.

---

## Reusable substrate (point everything at this — see `Phase6z/Substrate_Inventory.md` for file:symbol)

6z **reuses verbatim** the alphabet-agnostic machinery 6y/6u already shipped — the spread half is
largely done; the *new* work is the seed → first-flow lift. Highlights (full inventory in the detail doc):
- **Conjugation transport:** `GenericSUd.flow_conj_mem`, `permMatrix_fin8_conj`, `qubit_iEmbed_conj`.
- **Tensor-Pauli / SU(8) algebra:** `kronSU8`, `kronSU8_trace`, `suEightTangent`, **`suEightTangent_spans`**
  (the 63 tensor-Paulis span `𝔰𝔲(8)` — reuse for the spanning argument), `CCZ_mat`, `CCZ_SU`.
- **BCH / Trotter:** `bch_order_2_cubic_thm` (dimension-generic), `trotter_sequence_tendsto` (SU(2)
  template to generalize in 6z.3), `SU2BCHBracketClosure.lean`.
- **The SU(2) von-Neumann-density TEMPLATE:** `cliffordT_H_of_G_eq_top_unconditional` /
  `CliffordTV4WitnessUnconditional.lean` — `{H,T}`'s irrational element → accumulation → density. **6z's
  SU(8) seed lift is the direct analogue of this** (the single most relevant prior art in-project).
- **Cartan closed-subgroup:** the `GenericSUdCartan*` chain (closed dense subgroup ⟹ ⊤).
- **Headline-from-witness:** `cliffordCCZSU8_headline_of_witness` (consumes a `ClosureDenseWitness`,
  emits the headline) — 6z.5 feeds the literal-alphabet witness into the SAME chain.
- **Phase A.1 foundation (already shipped under 6y):** `lean/SKEFTHawking/FKLW/CliffordCCZSU8LiteralSeed.lean`
  (`litSeed = CCZ·(H⊗H⊗H)`, `litSeed_trace = 1/√2`, `trace_CCZ_mul`). Kernel-only. **NB: the operative
  seed will switch to DR2's `g₀=(H₃·CCX)²`** (explicit `(−3±i√7)/4` eigenblock for the flow — Gate-1
  corrected from DR2's `(3±i√7)/4`); A.1's trace lemma stands alone and its machinery (`kronSU8`,
  `CCZ_mat`, trace helpers) is reused.

## New substrate to build (none in Mathlib — see `Phase6z/Mathlib_Decls.md`)
- `not_rootOfUnity_of_minpoly_not_int` (algebraic-integer obstruction; ~70 LoC).
- `irrational_dense_on_circle` (1-D Kronecker; ~25 LoC over `AddSubgroup.dense_or_cyclic`).
- Unitary spectral-log wrapper (`g₀ = U·diag(e^{iθ})·U†` → `X = U·diag(θ)·U†`; ~150 LoC — Mathlib's
  spectral theorem is **Hermitian-only**).
- ~~SU(d) `trotter_sequence_tendsto` (mechanical SU(2)→SU(d) port; ~250 LoC)~~ — **NOT needed** (Gate 2
  = BEST: pure Clifford conjugation spans `𝔰𝔲(8)`, no BCH/Trotter closure).
- *(Deferred)* multi-D Kronecker–Weyl on `𝕋^d`.

---

## Cross-cutting

- **Citations** — see `Phase6z/Citations.md`. Universality of `{Toffoli/CCZ, H}`: **Shi 2002 +
  Aharonov 2003**; entangling-gate criterion: **Brylinski–Brylinski 2001**; Shor's-basis /
  Clifford+T: **Boykin et al 1999** (FOCS). **Do NOT cite Aaronson–Gottesman 2004** for universality
  or Clifford-orbit transitivity (it is stabilizer *simulability*). Niven: Carus Monograph Cor. 3.12
  (NOT needed — algebraic-integer route is cleaner).
- **AI-defect defense** (`docs/AI-Defect-Defense-Layer.md`, Invariant #16): new 6z modules pass
  Tier-1 token checks (no `maxHeartbeats` in proofs, no undocumented `axiom`) + Tier-2; the
  `axiom_closure_allowlist` check (P4) should be green for every 6z theorem.
- **Bundle absorption:** HOLD any D4 §9.8 multi-alphabet-showcase extension for a separate
  user-authorized event (as in 6y).
- **Stage-13 CP-6z:** whole-phase fresh-context adversarial review after 6z.5, dispatched only on
  artifacts clean under Tier-1/2 (Invariant #16). Emphasize the honest CCZ-essential claim
  (verify CCZ is genuinely load-bearing in the witness — the inverse of 6y's "CCZ unused" finding).

## Relationship to Phase 6y (keep both honest)
- **6y stays CLOSED** at "Clifford+T at SU(8), CCZ over-complete" (whole-phase sweep GREEN; do not
  reopen). 6z is the strengthening, not a 6y correction.
- 6z's headline is the **CCZ-essential** counterpart; together they're two density mechanisms for the
  same SU(8) target — a clean, publishable pairing (per-qubit Clifford+T vs. von-Neumann CCZ-seed).

## Status legend
✅ SHIPPED · 🟡 IN-PROGRESS · 📝 WORKING DOC · ⏳ NOT STARTED

| Wave | Status |
|---|---|
| 6z.0 CAS gates | ✅ DONE — Gate 1 ✅ PASS (corrected spectrum); Gate 2 ✅ PASS = **BEST** (spanned dim 63). HARD GATE cleared. |
| 6z.1 seed + irrationality | 🟡 IN-PROGRESS — irrationality obstruction ✅ SHIPPED (`CliffordCCZSU8Irrationality.lean`, kernel-only): `not_rootOfUnity_of_not_isIntegral` (reusable) + `seedEigenvalue λ=(−3+i√7)/4` not an algebraic integer (`λ+λ̄=−3/2∉ℤ`) ⟹ not a root of unity. REMAINING: seed `g₀` membership in `⟨H,S,CNOT,CCZ⟩` + char-poly/`|λ|=1`. |
| 6z.2 first flow | ⏳ NOT STARTED |
| ~~6z.3 SU(d) Trotter~~ | ❌ DROPPED (Gate 2 = BEST) |
| 6z.4 pure-conjugation spread | ⏳ NOT STARTED (~400 LoC, BEST scope) |
| 6z.5 headline + Stage-13 | ⏳ NOT STARTED |
| 6z.D Kronecker–Weyl | ⏳ DEFERRED |
