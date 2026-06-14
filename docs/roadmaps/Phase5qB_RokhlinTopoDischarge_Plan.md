# Rokhlin `topo` Discharge — PLAN (LIVE-board #1, flagship)

**Status: PLAN ONLY (not started).** Authorize before executing. Companion: `next-session-phase5qb-resume` memory (CORRECTION banner), `docs/audits/SUBSTRATE_WEAKNESS_LIVE_BOARD_2026-06-13.md` §B1.

## The honest framing (read first — this is the user decision)
Rokhlin's theorem (`16∣σ` for smooth spin 4-manifolds) is **genuinely topological** — there is NO purely algebraic/lattice proof, because the obstruction *is* the point (Freedman's E₈ manifold is topological with σ=8, non-smoothable). So this discharge **does NOT make `16∣σ` unconditional-from-nothing.** What it does:

> **Relocate** the carried hypothesis from `topo : 2 ∣ σ/8` (the bald *conclusion* baked into a struct field — the defining-the-conclusion anti-pattern) **to `arf : Arf(q) = 0`** (the genuine, primitive smooth-spin input — Freedman–Kirby), **and PROVE the bridge `σ/8 ≡ Arf(q) (mod 2)`** so that `2 ∣ σ/8` becomes a *theorem* consequence of `Arf(q)=0`, not an assumption.

Endpoint: *"`8∣σ` proven outright; `16∣σ` proven **given** `Arf(spin refinement)=0` — the irreducible smooth-spin datum — via a proven Gauss-sum bridge, replacing the former bald `2∣σ/8` field."* This is the correct, maximal honest improvement; it eliminates the anti-pattern and is a real substantive theorem, but the topological hypothesis remains (correctly, as `Arf=0`). **Decision for the user: confirm this relocate-and-prove framing is the goal (vs. the cheaper alternative = keep `topo`, just fix paper10 prose).**

## Why it's tractable (the seeds are already on disk)
- `ArfInvariant.lean`: `arf q := q e0 * q e1`, `IsRefinement`, **`gaussSum_arf : gaussSumZ q = 2·signZ(arf q)`**, **`gaussSum_genus_g`**, **`gaussSum_orthogonal`** (multiplicativity under ⊕), `gaussSum_pi`, `signZ_*`. The rank-2 / genus-g Brown–Gauss-sum calculus is built.
- `BlockSignature.lean`: `sig(A⊕B)=sigA+sigB` (σ additive). `E8Signature.lean`: σ(E₈)=8 via integer-Cholesky `decide`. `LatticeSignatureCongr` / classification bricks: the 5q.B normal form `≅ E₈^a⊕(−E₈)^b⊕H^c`, `latticeSig = 8(a−b)`.
- **The bridge holds on the generators** (sanity-checked): per block, (σ/8 mod 2, Arf): E₈→(1,1), −E₈→(−1≡1, 1), H→(0,0). Sum: σ/8 = a−b ≡ a+b = Arf (mod 2) ✓ — because both σ/8 and Arf are ⊕-additive and agree on each generator, and a−b ≡ a+b (mod 2).

## Phases
| W | Goal | Key tools / risk |
|---|---|---|
| **W1** | **Mod-2 symplectic reduction.** Even unimodular `form` reduces mod 2 to a nondegenerate alternating (symplectic) Z/2-space (even ⟹ zero diagonal; unimodular ⟹ nondegenerate over Z/2). Genus-g symplectic basis. | reuse hyperbolic-plane / `B` infra; Mathlib `Matrix` mod-2. Risk: low. |
| **W2** | **Spin refinement as the new primitive.** `def IsSpinRefinement (form) (q : V→ZMod 2) := IsRefinement q ∧ <Wu-compatibility: q on the (zero) characteristic vector>`. Replace `SmoothSpinManifold4.topo` with `q`, `hq : IsSpinRefinement form q`, **`harf : arf q = 0`**. | Risk: **MEDIUM** — encoding `IsSpinRefinement` so it is the genuine constraint (non-vacuous, not over-strong). W3's per-generator decide VALIDATES non-vacuity (E₈ forces arf=1≠0). This is the load-bearing modeling step. |
| **W3** | **Per-generator Arf (decide).** `arf` of the spin refinement on each generator: `arf_E8 = 1`, `arf_negE8 = 1`, `arf_H = 0`, each by `decide` over the finite mod-2 form (mirrors `E8Signature` integer-`decide`). Pair with σ/8 mod 2 per generator. | kernel `decide` over Fin-indexed Z/2; no native_decide. Risk: low (finite). |
| **W4** | **Additivity + the BRIDGE theorem.** `arf` additive under ⊕ (via `gaussSum_orthogonal` + `gaussSum_arf`/`_genus_g`: `gaussSum(q₁⊕q₂)=gaussSum(q₁)·gaussSum(q₂)`). Combine with `latticeSig=8(a−b)` (classification) ⟹ **`sigDivEight_congr_arf : (latticeSig form)/8 ≡ arf q (mod 2)`**. | the real new theorem; additivity bridge. Risk: **MEDIUM** (assembling ⊕-additivity of arf from the Gauss-sum product + sign bookkeeping). |
| **W5** | **Discharge + wire.** `two_dvd_sigDivEight_of_arf_zero : arf q = 0 → 2 ∣ (latticeSig form)/8` (bridge + harf). `SmoothSpinManifold4.rokhlin` now derives `16∣σ` from `(even_unimod, hq, harf)`. Update `HYPOTHESIS_REGISTRY.rokhlin_sigma_mod_16` (carried hyp = `Arf=0`, bridge PROVEN). | wiring; ExtractDeps root-import. |
| **W6** | **Prose + close.** paper10 / D2 / L2: "8∣σ proven; 16∣σ proven given `Arf(spin refinement)=0`, the smooth-spin input; the former `2∣σ/8` field is now a proven consequence." Kernel-pure; `vacuous_statement_audit`/`proxy_body_audit` stay green (the new theorems are substantive); closure reviewer. | honesty discipline. |

## Standing rules
Kernel-pure standard axioms only; **no axiom / native_decide / maxHeartbeats / sorry**; file-gate per brick; ExtractDeps at close; stage own paths; never push unless asked; don't reference the private RD repo. Read `Lit-Search/Phase-5*/` Rokhlin/HM files directly (not via agents) for any tactic-level detail. The new struct field is a *struct-FIELD assumption* (Inv #16 scope note) — register it case-by-case + ensure `proxy_body_audit`'s `fun _ => _.field` body pattern doesn't false-flag the new `rokhlin`.

## Fallback
If W2's `IsSpinRefinement` modeling proves intractable, the **bridge (W3+W4) is provable regardless**: worst case `topo` is RESTATED as `arf q = 0` for an explicit carried refinement + the **bridge proven** — still strictly better than the bald `2∣σ/8` (the anti-pattern is gone; the hypothesis is at the primitive level). Never ship a new axiom for this without explicit user sign-off.
