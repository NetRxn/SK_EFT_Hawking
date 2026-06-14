# Substrate Weakness — RECONCILED LIVE BOARD (2026-06-13 PM)

**Companion to** `SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md` (the 60-item ranked ledger).
**Why this doc:** the audit was the *input* to this session's two `/goals` (Substrate Integrity Gates / ADR-004, commits `6dc125ea`→`4becb5e1`, and FormulaRefSweep `c5f55fb1`). It is therefore a **pre-fix snapshot**. This board re-verifies each load-bearing finding's *current* on-disk state (31 deep-verified by 6 parallel reconcilers with file:line evidence + high confidence; 29 classified inline) and re-ranks what is genuinely **LIVE**.

**Headline:** Of the audit's 7-item **DO-NOW** tier, **4 are fully CLEARED** (#2, #3, #4, #12), **1 is mostly-done** (#14 name-resolution shipped; only the semantic content-audit remains), **2 stay live** (#9, #25). Across all 60, **~12 are CLEARED**, **~16 are correctly-capped literature WALLS** (hedge-only, not defects), and the **single highest live item is #1 (Rokhlin `topo`, 92)** — untouched, flagship, and our own 5-day-old "16∣σ unconditional" memory was an overstatement (verified: `SmoothSpinManifold4` carries an undischarged `topo : 2∣σ/8` field; only `8∣σ` is proven outright).

---

## A. CLEARED — the audit snapshot is stale here (no live work)

| # | Finding (short) | Cleared by | Evidence |
|---|---|---|---|
| 2 | Tracked-hyp ledger drift (11+ undocumented H_*) | SIG W3 `616cc35d` | `HYPOTHESIS_REGISTRY` 31 entries; **all 11 audit-named H_* present, missing-count 0**; `tracked_hypothesis_ledger` hard-fail PASS (23 consumed / 23 covered); md auto-generated; "honest count: 7" prose gone. |
| 3 | Paper7 general-G overclaim | SIG W1 + reprose | paper7 `:305-315` reprosed (Z/2 full, S₃ count, general-G statement-level); 3 stubs renamed `*_TODO`. |
| 4 | native_decide count wrong (199 vs 551) | SIG W5 `047d73cf` | counts.json `native_decide_decl_closure=546` + cluster map (anyon 327 / number-field 154 / other 53 / lattice 12); FKLW & QN keys absent (=0). *Residual cosmetic: literal 551 split not stored — decl-closure chosen instead.* |
| 12 | Phase 6v false-positive close | 6v.9 + SIG pathway-#2 | 9.A–9.E GREEN with real Hamiltonian-derived theorems (BdG TRS antisymmetry, Pfaffian²=det, FK invariant); meta-lesson encoded in pipeline doc. *Residual: flip roadmap header `PENDING`→`CLOSED`.* |
| 34 | Quantum-network trivialities (DEJMPS/GHZ/BBN) | 6AH (prior) | DEJMPS now on non-Werner input (B≠D); GHZ advantage DERIVED two-sided (was hardcoded 0). |
| 39 | Sakharov Λ_J⟺Λ_HK walkback | 6o W4a (prior) | one-way implication on disk; D5 "biconditional retired"; independence substrate-derived (JTGR16-20). *Residual: 1 stale section-intro sentence.* |
| 47 | placeholder 26-vs-43 reconciliation | SIG W1 | PLACEHOLDER 26=26=26; lean_deps type-True == 26 exactly; "43" was a raw-grep over-count of non-theorem markers. |
| 55 | 4 KMM native_decide sites at 596 | 6AO Track-3 (prior) | all 4 cores eliminated (structural T-pairing/GS-parity replacements); closure now 546. |
| 60 | BHThermo He3-A-vs-Balbinot wrong result | 6a W5 (prior) | rewritten around Balbinot 2005 BEC-cooling; regime signs consistent; 0 sorry. |
| 28 | D7 "precise statement TBD" | 6w + 06-05 review | zero "TBD" matches; all 3 headlines have concrete machine-checked biconditionals. *Residual: 1 modestly-overclaiming theorem name.* |
| 37 | Fannes–Audenaert `hAud` (inline) | 6AM W6 (prior) | `quantum_fannes_audenaert_sharp` unconditional (per memory; spot-confirm). |

---

## B. LIVE BOARD — re-ranked by CURRENT load-bearing × impact × achievable

### B1 — Flagship math discharges (hard, but project-specialty; the headline work)
| Rank | # | Item | Score | Achiev | Note |
|---|---|---|---|---|---|
| 1 | **1** | **Rokhlin `topo` factor** — replace `topo : 2∣σ/8` (defining-the-conclusion struct field) with the genuine spin datum `arf : Arf(q)=0` + **prove** `Arf=0 → 2∣σ/8` via the Gauss-sum/Brown bridge already seeded in `ArfInvariant.lean` (`gaussSum_arf`, `gaussSum_genus_g`). No-regret: fix paper10 prose now. | **92** | hard | **The single highest live item. Flagship (paper10 / Z16 count).** Verified on disk by me. |
| 2 | 8 | FKLW Fibonacci SU(2) density via tracked predicate (Cartan closed-subgroup of SU(2); `idComponent≠⊥` is the missing piece) | 65 | hard | The unsound AA axiom was already deleted; landed on tracked Prop. |
| 3 | 10 | Pin⁺ Ω₄≅ℤ/16 (flagship-F) shipped as skeleton tracked Prop + **N14 `w₂=0` docstring bug (~10 LoC easy)** | 63 | hard | Same Arf/bordism family as #1. |
| 6 | 32 | Müger `det(S)≠0⟺Z₂=Vec` forward-only (Dir-2 = Lemma 2.15); FPdim per-MTC native_decide (no Perron-Frobenius); `D²=|G|²` 2-instances | 50 | hard | All honestly disclosed; substance genuinely deferred. |
| 11 | 13 | BHEntropy `verlindeEntropy_SU2k := kaulMajumdarS …0` (its own saddle limit); discharge `H_VerlindeKMLiteralSumDerivation` via genuine Laplace method (`LaplaceMethod.lean` exists) | 44 | hard | **Honestly disclosed** (paper26 tracked-hyp mode + −3/2 non-universality witness) → lower urgency than audit headline. |
| — | 33 | GR program algebraic-only — 2nd Bianchi ∇μGμν=0, Schwarzschild Ric=0, NEC-on-Tμν anchor (inline) | 48 | hard | "first formalization" claims narrower than stated. |
| — | 58 | `PositiveMassTheorem.lean` (paper28, heaviest 6a wave) never shipped; heat-kernel Seeley-DeWitt tracked (inline) | 46 | hard | Genuine deferred deliverable. |

### B2 — Defining-the-conclusion / verdict-by-stipulation cleanups (mostly easy–medium; SIG built detectors, not fixes)
| # | Item | Score | Achiev | Note |
|---|---|---|---|---|
| 9 | Entropic-gravity `rDIndependentNoGo=true` hardcoded for all 8 ctors; **D5 paper prose CONTRADICTS the constants.py disclosure** (paper says aggregator "establishes" the 8/8 closure; disclosure says it's bookkeeping) | 50 | medium | Either compute each verdict from its quantitative falsifier, or reframe D5 prose to a classification-ledger. **The paper/disclosure contradiction is the live bug.** |
| 45 | Bare-arithmetic "physics" stubs (`4*4=16`, `9-3<9`, `IsViable=false` by rfl) — real proofs exist alongside; **slip `proxy_body_audit`** (names don't match `_STRUCTURAL_NAME_RE`) | 34 | easy | Delete the stubs; derive `gibbsDuhemEvaded` from `GibbsDuhemTheorem`. |
| 25 | ChangeOfRings: h2→`_TODO` ✅ + cols/8 superseded by `A1ExtSubstantive` ✅; **residual:** real Mathlib `Ext` functor (T3) unshipped, 2 identity-wrappers remain, **module docstring still says "H2 DISCHARGED"** (contradicts the now-honest `_TODO`) | 33 | medium | `hom_tensor_adjunction_dim` escapes R2 (empty-body parse). |
| 54 | `vestigial_phase_eta_violates_microscope_bound : 1.0 > 1e-15` — bare literals, not the named constants; **the project's own cited GOOD example** | 22 | trivial | Restate over named Lean constants so it breaks on drift. |
| 51 | Paper-17 SemanticTautology (`fracton_bullet_sigma_zero=rfl`) — paper reframed to MCC (honest) ✅; extractor-guard still unimplemented + Lean rfl/decide | 32 | medium | Implement the SemanticTautology graph-guard; push to derivations. |
| 15 | 6 un-suffixed `True:=trivial` stubs (dolan_grady_from_chevalley, a1_is_sub_hopf, …) — now in PLACEHOLDER (citation-guard) but **not renamed `_TODO`**; 2 are easy discharges | 28 | medium | Apply `_TODO`; discharge dolan_grady (quotient-ring) + a1_is_sub_hopf (Sqⁿ-coproduct). |
| 23 | `dai_freed_spin_z4`/`z16_classification` `∃φ,Equiv.refl` — honest docstring, but **slips R2** (`⟨…⟩` body evades the regex); encode as named opaque tracked-Prop | 22 | wall+ | Cobordism iso itself = literature wall; the *encoding* fix is cheap. |
| 53 | `predictsBandSelectiveLightQuarks : Prop` inert field, 0 consumers | 14 | easy | Drop it or name it in the registry entry. |
| 11 | `PinPlusStructure : Prop` empty class (any type inhabitable `⟨⟩`); substantive load carried separately | 14 | easy | Fold `w₂=0` into the class or mark documentary. |

### B3 — native_decide hygiene (shrinks compiler-trust surface)
| # | Item | Score | Achiev | Note |
|---|---|---|---|---|
| 44 | Eliminable Cartan-entry/det + SFDM/Fracton ℚ-threshold native_decides — **verified `by decide`/`by rfl` close them** (E8Lattice, QuantumGroupInstantiation, SFDM, Fracton) | 40 | easy | SIG built only the ceiling; no mechanical replacement. Bulk edit shrinks number-field/lattice/other clusters. A clean dedicated `/goal`. |

### B4 — Deferred pipeline / process / submission-linked (medium; several gate on Phase 7 + user action)
| # | Item | Score | Achiev | Note |
|---|---|---|---|---|
| 17 | H_DESICompatibility — in registry w/ tier ✅; **no anchor ADW predictor** (3 falsifiers only); stale "not active" wording | 52 | medium | Execute 6b.2: ADW FLRW→growth→CPL (w0,wa)→predictor. |
| 18 | Phase 6k quark-rung — Lean shipped, **no `src/quark_rung/`, no figures, no Paper-43, no Stage-13** | 50 | medium | Run Stages 6-13; verify channel ratios not PDG-back-fit. |
| 41 | Phase 7 not closed — Wave-15 sweep + submission auth unrun; **I3 sub-claim STALE (now stage10/13 GREEN, submission-ready)** | 46 | medium | USER: gr-qc arXiv endorsement gates L1 deposit. |
| 40 | AttributionContentSweep — load-bearing 18/18 GREEN ✅; **~440 non-anchor tail + named human-gate items + 2 unbuilt checks** | 44 | easy | Pre-submission widening; implement `bibitem_title_matches_arxiv`. |
| 14 | formula_grounding **semantic** content-audit (the real Wave-21: "conclusion implies the computation") — name-resolution + placeholder-rejection shipped ✅, **semantic check OPEN** | 38 | medium | Catches the next δ_diss-class units bug; current gate would pass a dimensionally-wrong-but-real theorem. |
| 38 | DKMBootstrap — 20 trivialities mostly resolved ✅; **3 residuals**: `IsDKMFeasibleSDPCandidate:=True`, BEC `(2κ)!` stand-in, graphene 0.0756 not lifted | 38 | medium | Lift to convex-cone-positivity / Bogoliubov-derived. |
| — | 30 | T-gate ε≤10⁻³ not reached (GA-SK unstarted); CNOT no Lean Frobenius cert (inline) | 47 | medium | 2/3 universal gates lack machine-checked precision. |
| — | 35 | HaarPauliConstant=1/3 undischarged though **Mathlib has sphere-Haar** (inline) | 44 | medium | Dischargeable. |
| — | 42 | backreaction/polariton provenance — hardcoded SI params bypass EXPERIMENTS (10× κ); Falque off 2.5–10× (inline) | 44 | medium | Material to EFT-feasibility claim. |
| — | 49 | Bundle absorption (D2 Schellekens, flagship-F chapter, I3 Itô/LDP) held (inline) | 42 | medium | Phase-7-linked. |
| — | 59 | 5v process-fix — PG+AGE single-source flip unbuilt; 13-failure-mode coverage unproven (inline) | 41 | medium | Infra gaps. |

---

## C. LITERATURE WALLS — correctly capped, hedge-only (NOT defects; do not "fix")
`#5` degree-8-field native_decide (ADR-002 KEEP) · `#6` ABP/ko/Adams bordism · `#7` FaultTolerant threshold · `#16` Ross-Selinger ancilla-free (KMM 2-ancilla route *is* unconditional — bundle-citation discipline) · `#19` PLOB/REE · `#20` PMNS Catterall · `#22` RT-formula · `#24` Witt DMNO (genuine biconditional now) · `#26` 6AQ device-bound (modeling-assumption, honest) · `#27` cosmology no-gos (correct science) · `#29` 3450/TPFConjecture (1+1D already `decide`) · `#43` vestigial MC (resource-bound) · `#52` ADW cc Level-D tension · `#56` Caves/CCR + RS O(log 1/ε) · `#57` predicate-level MTC/LDP/Schellekens/APS · `#21` m_H structural-only.
**Action for all:** maintain honest hedge prose in the consuming bundles; no Lean change.

---

## D. SIG GATE BLIND-SPOTS (the recurrence path — a coherent hardening `/goal`)
The reconcilers found that several audited anti-patterns **slip the brand-new SIG detectors** — the "presence-not-load" root cause recurring *inside the gates*:
1. **R2 anonymous-constructor evasion** — `z16_classification`'s `⟨Equiv.refl _, …⟩` body starts with `⟨`, evading `proxy_body_audit`'s `^(by exact )?Equiv\.refl` regex (#23).
2. **R2 empty-body parse** — `hom_tensor_adjunction_dim := rfl` on the signature line parses as empty body → R2 silently skips it despite the `_dim` structural name (#25).
3. **R2 structural-name miss** — bare-arithmetic stubs (`tetrad_components`, `nogo_fails_with_three_violations`) don't match `_STRUCTURAL_NAME_RE` (#45).
4. **No paper-prose↔disclosure-category consistency check** — D5 prose asserts an aggregator "establishes the 8/8 closure" while its `MODELING_ASSUMPTION_THEOREMS` entry says it's bookkeeping (#9). Nothing enforces that paper claims match the theorem's disclosure tier.

These four are cheap to close and structurally prevent the recurrence — directly in the spirit of ADR-004 pathway-#2.

---

## E. Recommendation
1. **Next big `/goal` = #1 Rokhlin `topo` discharge** (B1 rank 1) — flagship, highest score, infra seeded; converts a defining-the-conclusion field into a proven Gauss-sum theorem. No-regret immediate: fix paper10's "unconditional 16∣σ" prose → "8∣σ proven outright; 16∣σ given the topological Arf factor."
2. **Quick-win bundle** (one short `/goal`, ~all easy/trivial, high honesty yield): #54 named-constants, #45 delete bare-arithmetic stubs, #44 native_decide→decide bulk, #15 `_TODO` renames + 2 discharges, #25 module-docstring reconcile, #12/#28/#39 cosmetic header/prose, **+ the four SIG blind-spots in §D**.
3. **Hold for submission cycle** (Phase-7-gated, partly user-action): #41/#40/#49/#17/#18 + the §C walls (hedge-only).
4. **Per-program hard discharges** as their own `/goals` when prioritized: #8, #10, #32, #13, #33, #58.
