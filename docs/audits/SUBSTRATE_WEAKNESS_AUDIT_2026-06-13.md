# SK_EFT_Hawking — Whole-Substrate Weakness Audit

**Date:** 2026-06-13  ·  **Method:** programmatic harvest (counts.json / lean_deps.json / native_decide lint) → 16 roadmap-sweep agents (~88 roadmaps + deferral docs, 3.3 MB) + 5 substrate deep-dive lenses (native_decide, tracked-Props, placeholder/triviality, conditional-headlines, strengthening anti-patterns) → reconcile-vs-ground-truth synthesis.

**Scale:** 408 raw findings from 16 roadmap slices + 5 deep-dive lenses → **60 deduplicated ranked items**.

**Ground truth (counts.json 2026-06-10):** library is kernel-clean — **0 axioms, 0 sorry**, 12,463 theorems, 936 modules. The weakness surface is therefore NOT axioms/sorries but four structural classes: defining-the-conclusion, tracked-Prop ledger drift, conditional-headlines, and native_decide kernel-trust. Achievability is rated generously per the project's dev rate; only the named literature walls cap out.

---

## Executive narrative

EXECUTIVE SUMMARY for the PI. 408 raw findings across 16 roadmap slices + 5 deep-dive lenses reconcile to ~60 deduped ledger items. Ground truth holds: the library is kernel-clean (0 axioms, 0 sorry) — every roadmap mention of a live axiom or sorry is stale and was consolidated into one cosmetic item (rank 46) rather than padding the ledger. The real weakness surface is THREE structural classes, all on-disk-verified by the deep-dive lenses.

(1) DEFINING-THE-CONCLUSION AT THE STRUCTURE/DEFINITION LEVEL is the single most load-bearing pattern and it reaches actual paper headlines. The flagship 16∣σ Rokhlin result (rank 1) is 'unconditional' only because the genuinely-topological factor 2∣σ/8 is baked into the SmoothSpinManifold4 struct as an undischarged field — no concrete spin manifold is ever constructed; what is truly proven outright is 8∣σ (van der Blij, both HM+Θ inputs are now theorems, lean_verify clean). The entropic-gravity '8/8 unanimous NO-GO' D5 headline (rank 9) is `cases<;>rfl` over a function STIPULATED constantly true. The Phase-6e BH-entropy 'axiom retirement' (rank 13) redefined verlindeEntropy_SU2k := its own saddle limit so the theorem proves |x−x|=0. The Ext-over-A(1) headline (rank 25) rests on a cols/8 arithmetic proxy plus an h2_discharged:True that discharges nothing. These are not honest hedges — they are substance relocated into definitions while a load-bearing name asserts work that the proof term does not perform.

(2) ONE GENUINE PUBLISHED OVERCLAIM. Paper7 (rank 3) asserts the general-G gauge-emergence equivalence Z(Vec_G)≅Rep(D(G)) as part of '4049 theorems provide end-to-end formal verification' while the Lean is a cluster of `True := trivial` stubs — only the Z/2 and S3 instances are actually verified. Paper9/paper11 hedge the same claim correctly, so the fix is a one-paragraph reprose + a _TODO rename. This is the highest-severity honesty item with a real paper consumer and should be fixed before any submission.

(3) TRACKED-PROP LEDGER DRIFT (rank 2) is the highest-leverage cheap fix. The 'source of truth for the load-bearing tracked-Prop surface' documents ~7 entries but ~18+ genuinely-consumed-undischarged H_* Props exist (H_KLRS_SM_Crossover, H_SubstrateNearSMGFixedPoint, H_MR_FromSMGGap, H_RT_Formula_Valid consumers, etc.) gating paper17/20/21/33/D5 headlines. Bundles cannot hedge dependencies the ledger never recorded. Pure documentation, hours of work, high impact.

A meta-correction the PI should absorb: the audit's own ground-truth native_decide number is wrong (rank 4) — 551 real tactic uses, not 199, and they live ENTIRELY in the anyon/MTC/number-field cluster; FKLW/RossSelinger and QuantumNetwork have ZERO real uses (their matches are 6AO-elimination comments and kernel-purity attestations). The headline-backing native_decides (rank 5: Fibonacci universality, WRT invariants over Q(ζ₅,√φ)) are the legitimate KEEP case (un-decide-able under #10); but a fat tail of gratuitous ones (rank 44: Cartan-entry integer lookups, ℚ threshold inequalities) are mechanically eliminable to decide/norm_num and should be swept to shrink the compiler-trust surface.

On the literature walls: the named three (Ross-Selinger prime-density, 16∣σ classification, Caves/CCR floor) are genuine and correctly capped 55-70 — but note the 2-ancilla KMM ∀U synthesis (rank 16) IS genuinely unconditional (lean_verify clean), so the project's universal-synthesis claim is delivered, just via ancillas not the ancilla-free route; bundles must not swap them. The cosmology/emergent-gravity program (rank 27) resolved to a cluster of honest NO-GOs (vestigial DE/inflation falsified, Wen→ADW ~6000× too weak, cc only reproduced ~10^122) — these are correct science, the only risk is bundle prose framing them as deferred-positives.

PROCESS RED FLAG worth institutionalizing: Phase 6v (rank 12) and Phase 6r-prime (rank 11) both show a passed single-session adversarial close certifying work 30-90% short of intent — the gate is gameable by scope-narrowing. 'Reviewer GREEN is NOT the bar; acceptance criteria are.' Phase 7 (rank 41) is not formally closed: the final fresh-context submission sweep is unrun, I3 is still DRAFTING, and bundle GREEN states predate later 6X re-flagging — plus the gr-qc arXiv endorsement (user action) gates L1 deposit.

---

## Tier — DO NOW (highest priority: load-bearing + achievable)

- Tracked-hypothesis ledger drift: ~11+ undischarged H_* Props consumed as conditional hypotheses but absent from PERMANENT_TRACKED_HYPOTHESES.md ('honest count: 7' wrong by 2-3x)
- Paper7 claims general-G gauge-emergence equivalence Z(Vec_G)≅Rep(D(G)) as formally verified, but its Lean is a cluster of `True := trivial` stubs (only Z/2 and S3 instances proven)
- native_decide ground truth is wrong: 551 real tactic uses (not 199), concentrated entirely in anyon/MTC/number-field cluster; FKLW/RossSelinger & QuantumNetwork have ZERO real uses
- Track B 'entropic-gravity 8/8 unanimous NO-GO' headline rests on a verdict-by-stipulation function (rDIndependentNoGo returns hardcoded true for every constructor)
- δ_diss had a 7-9 orders-of-magnitude dimensional bug that hid for the project's entire history because the converting identity had no Lean theorem — Pipeline Invariant 4 was 'name appears in docstring', not 'content machine-checked'; the Wave-21 lean_grounding_audit is unbuilt
- Phase 6v 'GREEN-NO-FINDINGS' close was a false positive: adversarial review passed shipped-scope while real substance was 30-90% short of intent (LoE-inflation = thread-loss; the gate itself is gameable by scope-narrowing)
- ChangeOfRings H2 'discharged' is `True := trivial` + hom_tensor_adjunction_dim/change_of_rings_ext_dim are identity-wrapper tautologies; the Ext-over-A(1) headline rests on cols/8 arithmetic PROXY not Mathlib's real Ext functor

## Tier — HIGH VALUE

- Rokhlin 16∣σ headline is unconditional only because the topological factor 2∣σ/8 is an undischarged structure field (topo), never proven for any concrete spin manifold
- HEADLINE native_decide: Fibonacci-anyon universality + WRT 3-manifold invariants + Ising/SU(2)_k MTC braid data rest on native_decide over degree-8 number fields — genuinely un-decide-able under #10
- FKLW Fibonacci SU(2) density (closure(range ρ)=⊤) discharged via tracked 'sound predicate v3/v4', not a constructive Cartan closed-subgroup proof; replacement AA axiom was UNSOUND before deletion
- W3 Kirby-Taylor Ω₄^Pin⁺≅ℤ/16 (flagship-F Pin⁺ headline) shipped only as a 'skeleton'; the iso is a tracked Prop (Nonempty equiv asserted), not constructively proven
- Phase 6r-prime self-audit: 'GREEN-with-advisories' close was too optimistic — honest tracked-Prop count is 2 (not 12); 8 shipped predicates were P5 aliases/empty-Prop-class/literal-True dressed as physics
- Phase 6e BHEntropy 'axiom retirement' (gaussianSaddleAsymptotic) is defining-the-conclusion: verlindeEntropy_SU2k REDEFINED := its own saddle limit, proof is |x−x|=0≤1/A; the planned Laplace derivation deferred to tracked Prop
- H_DESICompatibility is DISCHARGE_FUTURE_PHASE scheduled for Phase 6b.2 ('not currently active') — Friedmann-cosmology DESI-match headline has NO anchor predictor; an effort-magnitude deferral of in-scope work
- Phase 6k entire phase: Lean SHIPPED but ALL Python/figures/Paper-43/Stage-13 DEFERRED — Lean PDG-anchored quark-mass/CKM numbers unvalidated against any independent computation path
- Phase 5p Müger modularity biconditional det(S)≠0⟺Z₂(B)=Vec proves only the forward direction; FPdim 'derivation' is per-MTC native_decide eigenvector-witness (no Perron-Frobenius); general D²(Z(Vec_G))=|G|² never proven (2 instances only)
- Trivial Cartan-matrix-entry + SFDM/dark-matter rational-threshold native_decides are ELIMINABLE (decide/norm_num) — gratuitous compiler-trust axioms on integer constants and ℚ inequalities
- Phase 7 Wave 15 pre-submission Stage-13 sweep + user submission authorization never closed; I3 bundle (14th target) stuck at DRAFTING (sourceless lift) — Phase 7 not formally closed, no bundle submitted
- DrinfeldEquivalence + content-bearing True stubs (ocneanu_rigidity, fusion_to_tqft, equivalence_is_monoidal/braided, dolan_grady_from_chevalley, a1_is_sub_hopf, small_uq_*) — named results proven as `True := trivial`
- Phase 5x Paper-17 dark-sector headlines are MCC machine-checked classifications not derivations (5 SemanticTautology theorems incl fracton_bullet_sigma_zero=rfl on hardcoded def); the SemanticTautology graph-extractor guard is unimplemented
- AttributionContentSweep residual: ~440 non-anchor bibkeys only partially swept + human-gate items open; fabrication-class base rate means the un-swept tail can harbor metadata-valid-but-fabricated attributions
- Phase 6s/6o/6n bundle absorption (D.2/D.3 paper lifts) for many shipped waves HELD indefinitely — Lean math shipped but paper consequences not absorbed into any bundle

## Tier — LITERATURE WALLS (high importance, capped achievability)

- Generation-constraint chain (3∣N_f / 16∣σ via bordism) gated on ABP/ko/Adams hypotheses H1/H3/H4 + circularity hazard; Mathlib stable-homotopy wall
- Phase 6p FaultTolerantUQC capstone is CONDITIONAL — assumes both density witness AND p_eff<p_th_AGP; unconditional 'topological protection ⇒ threshold' explicitly never proven
- Phase 6h flagship PMNS prediction (paper40) gated on conjectural 4D Catterall mirror decoupling, rigorous only in 2D; entire Phase 6h inactive (Gate Z.4 NEGATIVE)
- Phase 6c W5 RT-formula bridge entirely conditional on tracked Prop H_RT_Formula_Valid (RT = QG conjecture, no holographic dual derived)
- dai_freed_spin_z4 + z16_classification are vacuous existentials standing in for the ℤ₁₆ cobordism classification — the Papers-8/9/10/17 hidden-sector headline (Mathlib bordism-absent)
- Ancilla-free single-qubit Ross-Selinger ∀U-unconditional synthesis NOT proven — gated on §6 relative-norm/prime-density existence (named literature wall a); BUT the 2-ancilla KMM ∀U route IS genuinely unconditional
- PLOB repeaterless secret-key rate is a labeled SURROGATE, not the operational rate inequality; doubly-gapped (REE + Gaussian/CV both Mathlib-absent)
- Phase 5n 3450 + gapped-interface (TPFConjecture) chirality-wall: chirality wall verdict remains CONDITIONAL on the conjectural TPFConjecture; 3+1D hard case unbuilt
- Phase 6AN/6AM/6t Caves added-noise / CCR floor + Ross-Selinger O(log 1/ε) length-optimality are the named literature walls (c) and (a)
- Phase 6AL Lidskii-Wielandt frame-existence (Hframe) is a genuine Mathlib-absent wall — sharp Fannes-Audenaert log(d-1) constant staged as undischarged hypothesis hAud
- Phase 6n/6o/6q substantive infrastructure (full MTC + Witt-group, LDP Cramér/Varadhan/Gärtner-Ellis, Niemeier/VOA Schellekens classification, full APS index theorem) is predicate-level only
- Phase 5d/5/5f cosmology & emergent-gravity headlines resolved to structural NO-GOs — vestigial DE/inflation falsified on all 3 axes; Wen→ADW perturbative path closed; cosmological-constant only 'reproduced'
- Phase 5x ADW cosmological-constant / KV dark-energy walked back from 'explains DESI' to 'Level D tension' (excluded 2.9-4.4σ); fracton-DM production mechanism unresolved
- Phase 5z flagship m_H prediction is STRUCTURAL-ONLY — 125 GeV reached only on a 1-D tuning curve; paper20 reframed to 'structural identification'
- Phase 5d/5/5f vestigial-gravity Monte Carlo never reached publication-quality detection — RHMC blocked, exponentially-narrow window may be unresolvable at workstation scale

## Tier — WATCH (honest framing / cosmetic / low urgency)

- Phase 6AC teleportation Horodecki f_avg=(2F+1)/3 + utility threshold gated on Haar-integral tracked hypothesis HaarPauliConstant (=1/3), undischarged though Mathlib has the sphere-Haar machinery at pin
- 6AK.1/6AQ device-bound 'ceilings' and 6AQ readout-floor headlines are EQUALITIES for a model channel / model-identified, not physical upper bounds — the device-bound claim is an unformalized modeling assumption
- Phase 6AH/6AC/6AD quantum-network trivialities: DEJMPS correction vacuous on its only input; GHZ-vs-W advantage defined-to-conclude; BBN violators conditional on hand-supplied delta_n_eff hypothesis
- Phase 6r-prime 20k-LoC/≥1-year acceptance bar institutionalizes effort-magnitude deferral; N16 flags most 'Phase 7+' framings are actually tractable — contradicts 'no de-scope from effort' policy
- Phase 6f/6g GR program shipped entirely at algebraic/point-wise scope (no connection-based layer); 2nd Bianchi ∇^μG_{μν}=0, Schwarzschild Ric=0, and the NEC-on-T_μν^emerg correctness anchor all DEFERRED
- T-gate braid never reaches target ε≤10⁻³ (random-search plateau ~4.5e-2, GA-SK NOT STARTED); CNOT shipped from figure-only HZBS transcription with no Lean Frobenius certificate — 2 of 3 universal gates lack completed machine-checked precision
- backreaction.py + polariton(paper12) provenance: SI platform params hardcoded bypassing the corrected EXPERIMENTS chain (10× κ discrepancy); Falque polariton params PROJECTED, off published values by 2.5×/>10×
- Phase 5v process-fix deliverables incomplete: PG+AGE single-source-of-truth flip unbuilt; 13-failure-mode gate-coverage unproven (15/15 RED, CHECK 18 WARN-only); claims-reviewer Class TN false-positive would have merged 2 distinct theorems
- Phase 6q DKMBootstrap shipped 20 P2-P5 anti-pattern theorems requiring a dedicated strengthening pass; IsDKMFeasibleSDPCandidate KEPT as Prop:=True scaffold; BEC NO-GO witnessed by a (2κ)! STAND-IN sequence not derived from the Bogoliubov Hamiltonian
- Phase 6o Wave 4a Sakharov Λ_J⟺Λ_HK biconditional was a P5 self-discharging tautology walked back to one-way implication; D5 §11 still ships the Λ_J=Λ_HK independence via prose hedge not Lean derivation
- EmergentGravityBounds + TPFEvasion + ChiralityWall + DEC-orthogonality 'physics' theorems are bare arithmetic / verdict-by-stipulation with all content in comments — the substantive forms exist elsewhere
- Phase 6h light-quark hierarchy fall-through embeds an inert OPEN-AT-FRONTIER Prop field (predictsBandSelectiveLightQuarks) that no theorem consumes
- vestigial_phase_eta_violates_microscope_bound compares bare literals (1.0>1e-15) not the named constants it claims to relate — the project's OWN cited GOOD example fails to detect constant drift
- Phase 5i/5/5a/5b/5d/3 historical sorry/axiom roadmap text is STALE vs ground truth (0 sorry, 0 axioms) — Z16/gapped-interface/spectral-gap/GaugeErasure/Fermi-Point axioms all converted or discharged
- ~26-43 *_module_summary_marker / *_TODO `True := trivial` cosmetic markers + counts.json placeholder discrepancy (26 reported vs 43 on-disk type-True); honestly-labeled definitional re-exports
- Phase 5g/5i/5o/6s Mathlib upstream-PR contributions never filed — gated on external Zulip/AI-disclosure relationship-building; tensor-categories + PolyQuotQ + matrix-log + Cartan all internal-only; Phase 6x first-pass 'PRs' were alias-only
- Phase 6r 'first SymTFT formalization in any prover' + Phase 6k/6e/6t primacy claims are hedged-but-checkable cross-prover-survey assertions the project's own primacy-claim discipline warns against
- Phase 6a Wave 5 + Phase 6o/6q/6z/6t/6y multiple post-ship overclaim-vs-delivered gaps caught by review (primary-source conflation, headline-from-witness, figure-eight 'in flight', M-S alias-only)
- Phase 6AO native_decide held at 596; 4 KMM-style sites confirmed kernel-decide-INFEASIBLE under #10 — project-tolerated, need structural reproof (6AO Track-3 proved feasible)

---

## Full ranked ledger

### #1 — Rokhlin 16∣σ headline is unconditional only because the topological factor 2∣σ/8 is an undischarged structure field (topo), never proven for any concrete spin manifold

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **92** · _conditional_headline_

**Why it ranks here:** On-disk verified (deep-3): lean_verify on sixteen_convergence_unconditional returns {propext,Classical.choice,Quot.sound}, but SmoothSpinManifold4.rokhlin consumes a `topo : 2∣σ/8` struct field and ZERO concrete instances exist. 8∣σ is genuinely proven (van der Blij, both HM+Θ inputs are theorems); the factor-of-2 to 16 is defining-the-conclusion at struct level. This is THE flagship Phase-5q.B result, feeds the Z16 generation count, and the paper10 framing overstates it. Highest load-bearing × impact; achievability hard (genuine index-theoretic Arf/Â-genus work) but project already cracked the algebraic half so not a literature wall.

**Remediation:** ~~Discharge `topo` for the concrete forms used (E8/-E8/H from classification) via even-unimodularity + spin quadratic refinement (Wu's formula → Arf(q̄)=0 → factor of 2); the Arf chain is already seeded in ArfInvariant.lean.~~ **⚠️ CORRECTION 2026-06-13 — this lattice-Arf remediation path is a NO-GO (FALSE/impossible).** `Arf(redQuad)` is **identically 0 on every even unimodular lattice** (E8: gaussSum=+16, #zeros=136=2⁷+2³ ⟹ Arf=0, yet σ(E8)/8=1 is odd), because the discriminant form L*/L is trivial for unimodular L — so the finite Arf/Gauss-sum apparatus sees only **σ mod 8** and can NEVER supply the σ-mod-16 factor. The geometric Guillou–Marin Arf lives on a smoothly embedded characteristic *surface* (`σ ≡ Σ·Σ + 8·Arf(M,Σ) mod 16`), a different object than the lattice `Arf(redQuad)`. Machine-checked: `lean/SKEFTHawking/RokhlinArfNoGo.lean` (`arfOfForm_e8lit_eq_zero`, `lattice_arf_bridge_refuted`). **`topo : 2∣σ/8` is therefore a PERMANENT irreducible geometric hypothesis (Â-genus-even), not a discharge target; the achievability is a literature/geometric wall, not "hard but tractable."** The ONLY remediation is the disclosure pass: hedge paper10's 'unconditional 16∣σ' to '8∣σ proven outright; 16∣σ given the topological factor 2∣σ/8 carried as a structure field'. (The `redQuad`/`gaussSum` machinery in ArfInvariant.lean is correct and stays — only the false σ-bridge claim is retracted.)

**Sources:** deep-3 (SpinRokhlinInterface.lean:55-88, RokhlinHMRankFour.lean:603, ArfInvariant.lean, paper10:323/329-331); roadmap-b3 (sixteen_convergence_full enumerates not unifies); roadmap-b7 (Phase5qB topo' permanent residual); roadmap-b15 (Phase5c Wang-Rokhlin conditional)

### #2 — Tracked-hypothesis ledger drift: ~11+ undischarged H_* Props consumed as conditional hypotheses but absent from PERMANENT_TRACKED_HYPOTHESES.md ('honest count: 7' wrong by 2-3x)

🟠 `headline` · impact **high** · achiev **easy** · status _open_ · score **90** · _tracked_hypothesis_

**Why it ranks here:** Deep-1 on-disk: 49 Prop-valued H_* defs exist; ledger documents ~7. At least 11 are genuinely consumed as undischarged (h:H_X) with no anchor theorem — H_SubstrateNearSMGFixedPoint(3), H_MR_FromSMGGap(3), H_KLRS_SM_Crossover(2), H_HSCovariantBosonisation(2), H_BilocalPointlikeLimit(2), H_MR_FromADWSubstrate_BCS_LNV(2), H_VestigialRelicCarriesZ16Charge(2), H_PMNSAnglesFromExactSubstrate, H_DecouplingBoundDim6, H_MixedChannelZ16Cancels, H_ScalarChannelIsTetradBifurcationOutput. These gate paper21/17/20/33 headlines. Systemic honesty risk: bundles can't hedge dependencies the source-of-truth never recorded. Easy fix (documentation sweep), high impact (the ledger's whole purpose is the load-bearing tracked-Prop surface).

**Remediation:** grep `def H_[A-Z]...: Prop`, classify each as anchored/genuinely-consumed-undischarged/unused; add KEEP_AS_TRACKED or DISCHARGE_FUTURE entries for the ~11 undocumented consumed ones with status, physics-status, consumer list, 3-criterion check; correct 'honest count: 7' and the sync date. Pure docs, hours.

**Sources:** deep-1 (PERMANENT_TRACKED_HYPOTHESES.md vs 49 H_* defs); roadmap-b1/b2/b3/b5 (H_DESICompatibility, H_RT_Formula, H_VestigialModeIsGraviton, FG/Z16 tracked Props); roadmap-b15 (H_KLRS, H_SubstrateNearSMGFixedPoint)

### #3 — Paper7 claims general-G gauge-emergence equivalence Z(Vec_G)≅Rep(D(G)) as formally verified, but its Lean is a cluster of `True := trivial` stubs (only Z/2 and S3 instances proven)

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **88** · _placeholder_true_

**Why it ranks here:** Deep-2 on-disk: gauge_emergence_statement, half_braiding_gives_action, equivalence_preserves_tensor/braiding, center_universal_property, chirality_independent_of_G are all `:= trivial` type-True, yet paper7:307 asserts 'the gauge emergence theorem Z(Vec_G)≅Rep(D(G)) ... 4049 theorems provide end-to-end formal verification' WITHOUT disclosing the general-G case is a stub. Only Z/2 (4-anyon case analysis) and S3 are actually verified. This is a genuine published-paper overclaim (paper9/paper11 hedge correctly; paper7 does not). Highest-severity honesty failure with a real paper consumer. Hard to discharge (Mathlib lacks Müger/ENO modular-category infra) but the FIX (hedge prose + _TODO rename) is easy.

**Remediation:** Hedge paper7:307-309 to match paper9's careful framing (verified concretely for Z/2,S3; general-G a program target); rename the stubs with _TODO suffix (as FusionCategory/CenterFunctor cluster already was) so names can't be cited as proved. Full discharge is research-grade category theory.

**Sources:** deep-2 (GaugeEmergence.lean:90/64/127, DrinfeldEquivalence.lean:98/108/178, paper7:307-309); roadmap-b3 (DrinfeldEquivalence 4/12 True stubs); roadmap-b9 (CenterFunctor equivalence_is_monoidal/braided True)

### #4 — native_decide ground truth is wrong: 551 real tactic uses (not 199), concentrated entirely in anyon/MTC/number-field cluster; FKLW/RossSelinger & QuantumNetwork have ZERO real uses

⚪ `supporting` · impact **low** · achiev **trivial** · status _open_ · score **74** · _native_decide_

**Why it ranks here:** Deep-0 refined scan: the audit premise (199 / FKLW+QuantumNetwork concentration) is stale. Real distribution: anyon/MTC/braid 328, number-field 124, quantum-group 54, lattice/E8 20, physics-app 20; FKLW/RossSelinger=0 real (all matches are 6AO-elimination comments), QuantumNetwork=0 real (kernel-purity attestations). An auditor trusting the stale count chases clean files and misses the 452 real uses where the trust gap lives. Meta-correction with high leverage on every other native_decide finding; low direct impact but trivially actionable.

**Remediation:** Update docs/counts.json native_decide accounting to separate real tactic uses (551) from doc-mentions; re-point cluster map to anyon/MTC + number-field substrate. Reconcile the 26-vs-43 type-True discrepancy too (deep-2 finding).

**Sources:** deep-0 (grep+python scan, 893 raw lines→551 real); ground-truth counts.json premise contradicted

### #5 — HEADLINE native_decide: Fibonacci-anyon universality + WRT 3-manifold invariants + Ising/SU(2)_k MTC braid data rest on native_decide over degree-8 number fields — genuinely un-decide-able under #10

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **80** · _native_decide_

**Why it ranks here:** Deep-0: the flagship 'Fibonacci braiding universal' / 'first verified quantum 3-manifold invariant' / 'first FPdim derivation' headlines are discharged by native_decide over Q(ζ₅,√φ)/QCyc16/QCyc40 (FibonacciUniversality, FibonacciSextetTrueRep 169-entry B₆ relations, WRTComputation, FPDimension). Elements ARE DecidableEq so kernel decide is type-possible, but rational arithmetic over degree-8 towers blows the heartbeat budget (Invariant #10), so each carries a Lean.ofReduceBool compiler-trust axiom. Load-bearing for multiple publication headlines; the canonical project-tolerated case. Hard to eliminate (research-grade symbolic identities), legitimately KEEP-able.

**Remediation:** KEEP with justification for field-arithmetic cores (canonical un-decide-able). Targeted: convert the small per-scalar substrate identities that headline closures CONSUME (e.g. fib_phi_sq) to structural ring lemmas, shrinking transitive native_decide footprint; gate-compilation Frobenius-distance (GateCompilation/RouabahSplitBraid, at the tractability frontier) stays KEEP.

**Sources:** deep-0 (FibonacciUniversality.lean:142, FibonacciSextetTrueRep, WRTComputation.lean:36/62, FPDimension, QCyc5Ext); roadmap-b0 (SU(3)_k native_decide), roadmap-b6 (Phase5d/5e MTC nd), roadmap-b9 (FPDimension Perron-Frobenius sidestep), roadmap-b15 (Phase5c E8Lattice nd)

### #6 — Generation-constraint chain (3∣N_f / 16∣σ via bordism) gated on ABP/ko/Adams hypotheses H1/H3/H4 + circularity hazard; Mathlib stable-homotopy wall

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **68** · _tracked_hypothesis_

**Why it ranks here:** Multiple slices (b2/b5/b7/b11/b13) + ground truth: the headline three-generation/Rokhlin chain via Ext→Ω^Spin_4≅Z is conditional on H1 (ko-cohomology), H3 (Adams SS collapse — Bott-periodicity wall), H4 (ABP splitting, with an unresolved Rokhlin circularity caveat), all Mathlib-absent. Capped because it's a genuine named literature wall (Mathlib has no spectra/Adams/Thom). NOTE: 5q.B delivers 16∣σ unconditionally (rank 1) WITHOUT this frontier, so it's off the critical path — but the ko/Adams D2/L2 narrative is 'motivational' (H1/H3/H4 carried as Prop:=True). High importance, surface in walls.

**Remediation:** Keep H1/H3/H4 as Prop:=True (avoids axioms); ensure D2/L2 prose flags ko/Adams framing as motivational. Build only on Mathlib trigger (spectra/Adams/Thom land). The H4 anti-circularity constraint (route through Adams SS, not Rokhlin-equivalent fact) must be documented before any discharge attempt.

**Sources:** roadmap-b2 (Phase5r H1/H3/H4), roadmap-b5 (three_generations_axiom_free gated M1/M2/M3), roadmap-b11 (5q.D circularity), roadmap-b13 (5q.D Prop:=True placeholders), roadmap-b12 (5q.T deferred)

### #7 — Phase 6p FaultTolerantUQC capstone is CONDITIONAL — assumes both density witness AND p_eff<p_th_AGP; unconditional 'topological protection ⇒ threshold' explicitly never proven

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **66** · _conditional_headline_

**Why it ranks here:** roadmap-b1: the capstone of all Phase 6p ('MTC infrastructure enables fault-tolerant universal QC') takes both hardest physics inputs as explicit hypotheses; it's a packaging theorem, not a proof Fibonacci braiding achieves fault tolerance. The only cited unconditional source (Bonesteel-DiVincenzo) explicitly disclaims threshold analysis. Genuine open research (Schotte-Zhu-Verstraete; Gács-Harrington CA renormalization). High load-bearing headline, capped as literature wall — keep conditional, do NOT upgrade.

**Remediation:** Keep conditional framing; the achievable improvement is deriving p_eff from a concrete braiding-error model for a worked instance to narrow the assumed surface. Ensure any Phase-6p paper states the threshold satisfaction is assumed.

**Sources:** roadmap-b1 (Phase6p G12, FaultTolerantUQC.lean:25-30); cross-ref deep-3 (TPFConjecture pattern)

### #8 — FKLW Fibonacci SU(2) density (closure(range ρ)=⊤) discharged via tracked 'sound predicate v3/v4', not a constructive Cartan closed-subgroup proof; replacement AA axiom was UNSOUND before deletion

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **65** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b1: the load-bearing density input to FKLW universality (H_Fib=⊤) was never constructively discharged — the generic AA axiom aa_residual_interior_at_one_for_hom was found UNSOUND (SO(d)⊂SU(d) counterexample), deleted, and the close landed on a tracked predicate. counts.json axioms=0 confirms no live axiom, but the 'unconditional density' downstream (Phase 6t base case) inherits the tracked-predicate conditionality, and the roadmap understates this as in-progress Cartan work. High headline impact; hard (genuine Cartan closed-subgroup-of-SU(2) Lie infrastructure).

**Remediation:** Either ship Mathlib-grade Cartan closed-subgroup + classification-of-closed-subgroups-of-SU(2) (structural ruleouts D1-D4.3.b already done; missing piece = idComponent≠⊥ → positive Lie dimension), then discharge the tracked predicate; or formalize as a permanent tracked-Prop with HBS citation in PERMANENT_TRACKED_HYPOTHESES.md. Verify which 'sound predicate v3/v4' is load-bearing and non-vacuous.

**Sources:** roadmap-b1 (Phase6p R5.4/R5.5, CartanSubstrate.lean Wedge B); deep-3 (KMM ancilla route is the unconditional alternative)

### #9 — Track B 'entropic-gravity 8/8 unanimous NO-GO' headline rests on a verdict-by-stipulation function (rDIndependentNoGo returns hardcoded true for every constructor)

🟠 `headline` · impact **high** · achiev **medium** · status _open_ · score **64** · _triviality_

**Why it ranks here:** Deep-4 on-disk: the paper-45/D5 publication-novelty headline ('first complete-mechanism-family NO-GO closure, 8/8 excluded') is, in Lean, entropic_gravity_no_go_count_eight (list-length rfl) + ∀c rDIndependentNoGo c=true (cases<;>rfl over a function STIPULATED constantly true). Defining-the-conclusion: no candidate's exclusion is derived by this theorem. The genuinely-falsifiable per-candidate legs (CPL-region geometry, log-Bayes>jeffreys) exist separately and are good — but the aggregate headline carries no proof load. Honest in docstrings (per-candidate primary-source-cited), so presentational fix not a fabrication. High impact (D5 bundle headline), medium achievability.

**Remediation:** Either reframe the Lean claim as a verified-consistent classification ledger (state in D5 the 8/8 is a literature-review table whose legs are the per-candidate quantitative theorems), OR make rDIndependentNoGo COMPUTE each verdict from that candidate's quantitative falsifier so the aggregate is a genuine conjunction. Same fix-class applies to Track C unimodular-escape counts (JacobsonThermoGRDarkEnergy).

**Sources:** deep-4 (EntropicGravityDarkEnergy.lean:413-449/474, JacobsonThermoGRDarkEnergy.lean:417-478); roadmap-b13 (Phase6m norm_num verdict encodings)

### #10 — W3 Kirby-Taylor Ω₄^Pin⁺≅ℤ/16 (flagship-F Pin⁺ headline) shipped only as a 'skeleton'; the iso is a tracked Prop (Nonempty equiv asserted), not constructively proven

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **63** · _conditional_headline_

**Why it ranks here:** roadmap-b4: the 'first proof-assistant Pin⁺ bordism formalization' headline (Ω₄^Pin⁺≅ℤ/16) had an explicit fallback to tracked-Prop, and session logs show only a Path-γ generator-and-relations skeleton; audit verdict keeps IsKirbyTaylorPinPlusBordism (body Nonempty(Ω≃+ZMod 16)) as a legitimate KEEP tracked Prop. Backs the dai_freed/Z16 anomaly story. High headline; hard (η-route APS or Pin⁺-Spin LES; Mathlib bordism-absent). Also: N14 docstring bug shipped WRONG Pin⁺ obstruction equation (w₂=w₁² is Pin⁻; correct is w₂=0).

**Remediation:** Complete W3.3 (Path α η-route or Path β generators-and-relations / Pin⁺-Spin LES); keep headline framing 'tracked-hypothesis' until the iso is constructive. Fix the N14 w₂=0 obstruction docstring (B12, ~10 LoC) and verify the M4-narrow StiefelWhitney encodes w₂=0 not w₂=w₁².

**Sources:** roadmap-b4 (Phase6r_prime W3, N14, audit #1)

### #11 — Phase 6r-prime self-audit: 'GREEN-with-advisories' close was too optimistic — honest tracked-Prop count is 2 (not 12); 8 shipped predicates were P5 aliases/empty-Prop-class/literal-True dressed as physics

🟠 `supporting` · impact **high** · achiev **medium** · status _partially_resolved_ · score **62** · _triviality_

**Why it ranks here:** roadmap-b4/b11: the SymTFT 'unification crown' first-pass shipped 12 tracked Props of which 10 were anti-patterns — aliases (IsModularBulk:=Is3DTQFT, IsKapustinSaulinaGappedBoundary:=HasLagrangianAlgebra), IsGapped:=True literal, `class PinPlusStructure:Prop` empty body (any type instantiable with ⟨⟩), Z24_and_Z16_disjoint:=24≠16 decidable. The strengthening discipline + per-wave review missed all; only a deep file-by-file audit caught them. Systemic honesty risk (single-session 'all 8 waves shipped' close = under-strengthening red flag). High impact, medium achievability — A1-A5/B1-B12 remediation queue is mostly NOT STARTED.

**Remediation:** Execute the documented Path-A-strict remediation (DELETE aliases, RESTRUCTURE to substantive S-matrix/Müger-center predicates, fix IsGapped/PinPlusStructure bodies); the M3 RP⁴ chart-atlas (~300-500 LoC bespoke) and M-R pessimistic fresh review remain. Confirm the 2 survivors (KT 1990, DMNO 2010) are in PERMANENT_TRACKED_HYPOTHESES.md.

**Sources:** roadmap-b4 (Phase6r_prime audit N1-N24, B1-B12, A1-A5); roadmap-b11 (Phase6r 12→2 reduction)

### #12 — Phase 6v 'GREEN-NO-FINDINGS' close was a false positive: adversarial review passed shipped-scope while real substance was 30-90% short of intent (LoE-inflation = thread-loss; the gate itself is gameable by scope-narrowing)

🟠 `supporting` · impact **high** · achiev **easy** · status _likely_resolved_stale_ · score **61** · _walkback_

**Why it ranks here:** roadmap-b0: a passed adversarial review (the project's normal completion gate) certified work 30-90% short of intent — surrogates renamed as deliverables, substrate-encoded values presented as Hamiltonian-derived, ITE wrappers instead of derivations. The failure mode is the gate being gameable by scope-narrowing ('reviewer GREEN is NOT the bar'). High systemic impact (undermines confidence in every GREEN close); corrective 6v.9 was specified and the roadmap marks 9.A-9.E GREEN. Easy to verify but the lesson is the durable value.

**Remediation:** Verify each of the 23 acceptance criteria has a backing substantive (non-ITE-wrapper) theorem in source. Encode the meta-lesson: a single-session 'all waves shipped' close + reviewer-GREEN-only is insufficient evidence; require acceptance-criteria checkboxes as the bar.

**Sources:** roadmap-b0 (Phase6v ACTUAL CLOSE PENDING, 6v.9)

### #13 — Phase 6e BHEntropy 'axiom retirement' (gaussianSaddleAsymptotic) is defining-the-conclusion: verlindeEntropy_SU2k REDEFINED := its own saddle limit, proof is |x−x|=0≤1/A; the planned Laplace derivation deferred to tracked Prop

🟠 `supporting` · impact **high** · achiev **hard** · status _open_ · score **60** · _triviality_

**Why it ranks here:** roadmap-b14 (BHEntropyMicroscopic.lean:191-247): the 'axioms 2→1→0' headline is technically true but physics substance was relocated, not derived. verlindeEntropy_SU2k := kaulMajumdarS A G_N 0 (the saddle limit itself), so gaussianSaddleAsymptotic proves |x−x|=0 via sub_self;abs_zero;positivity. The actual Verlinde-sum→Kaul-Majumdar Laplace derivation is deferred to tracked Prop H_VerlindeKMLiteralSumDerivation; LaplaceMethodAsymptotic.lean is ABSENT. Paper26's '−3/2 log correction' rests on a definition-equals-target move. The project's own 'defining-the-conclusion' anti-pattern. High impact, hard (genuine Laplace/Watson's-lemma assembly).

**Remediation:** Execute the planned Wave-7 Sub-tasks A-C: a genuine Laplace-method bounded-remainder lemma, the Kaul-Majumdar I0-I1 port, and discharge H_VerlindeKMLiteralSumDerivation so verlindeEntropy_SU2k is a literal Verlinde sum. Until then, label the −3/2 coefficient conditional on the saddle-limit definitional choice in paper26.

**Sources:** roadmap-b14 (Phase6a Wave 7, BHEntropyMicroscopic.lean:191-247)

### #14 — δ_diss had a 7-9 orders-of-magnitude dimensional bug that hid for the project's entire history because the converting identity had no Lean theorem — Pipeline Invariant 4 was 'name appears in docstring', not 'content machine-checked'; the Wave-21 lean_grounding_audit is unbuilt

🟠 `supporting` · impact **high** · achiev **medium** · status _open_ · score **59** · _other_

**Why it ranks here:** roadmap-b14: a [m²/s]-as-[s⁻¹] error in compute_dissipative_correction persisted since first commit because Invariant 4 ('every formula has a Lean theorem') was satisfied by a docstring reference, not by content-checking; tests passed on hand-picked γ with only |δ_diss|<0.1. The roadmap explicitly calls it a canary: 'almost certainly other weakly-anchored formulas where smaller bugs could hide.' The systemic Wave-21 audit (lean_grounding_audit validate.py check + sweep of ~137 formulas.py functions) is OPEN. High impact (correctness-of-the-core-product), medium achievability.

**Remediation:** Execute Wave 21: implement lean_grounding_audit (function has Lean ref → theorem exists → theorem's CONCLUSION implies the computation, not just mentions it) and run the one-time sweep over formulas.py. This catches the class, not just the instance.

**Sources:** roadmap-b14 (Phase5u Wave 1 + Wave 21)

### #15 — DrinfeldEquivalence + content-bearing True stubs (ocneanu_rigidity, fusion_to_tqft, equivalence_is_monoidal/braided, dolan_grady_from_chevalley, a1_is_sub_hopf, small_uq_*) — named results proven as `True := trivial`

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **57** · _placeholder_true_

**Why it ranks here:** Deep-2: a family of type-True theorems each named after substantive unproven content. Four were renamed _TODO post-2026-04-26 audit so the name can't be mistaken for proved; the others (dolan_grady_from_chevalley — the ACTUAL cubic DG relation, with only DG_COEFF=16 arithmetic proven; davies_roan_classification; a1_is_sub_hopf_algebra; oq_coideal; small_uq_dim/su2k_connection) still carry result-suggestive names. None is currently a paper headline so supporting not headline, but the un-suffixed ones risk a future citation-as-proved.

**Remediation:** Apply _TODO rename uniformly to the six un-suffixed members. Discharge opportunistically: dolan_grady_from_chevalley is a quotient-ring computation (easy/medium), a1_is_sub_hopf_algebra is a finite Sq^n-coproduct check (easy); davies_roan + small_uq bridges need rep-category infra (medium). None is a literature wall.

**Sources:** deep-2 (FusionCategory.lean:153/159, CenterFunctor.lean:119/124, CoidealEmbedding.lean:185, OnsagerAlgebra.lean:352, SteenrodA1.lean:195, RestrictedUq.lean:187/202); roadmap-b9 (FusionCategory placeholders); ground truth (26 *_TODO True theorems)

### #16 — Ancilla-free single-qubit Ross-Selinger ∀U-unconditional synthesis NOT proven — gated on §6 relative-norm/prime-density existence (named literature wall a); BUT the 2-ancilla KMM ∀U route IS genuinely unconditional

🟡 `headline` · impact **medium** · achiev **literature_wall** · status _partially_resolved_ · score **58** · _literature_wall_

**Why it ranks here:** Deep-3 (verified both): rossSelinger_synth_of_residual isolates the gate as t₀†t₀=√2^{2k}−u·u* (Ross Problem 3.2.4); gridFindT_isSome_of_residual lifts a genuine diophantineSearch_complete (not tautological). The remaining gap is the prime-density input that the source literature itself discharges only randomized-under-prime-distribution (Selinger Hyp 29 = RS Hyp 8.3); Mathlib Dirichlet insufficient. COUNTERWEIGHT: kmm_universal_headline (deep-3, lean_verify {propext,Classical.choice,Quot.sound}) IS unconditional ∀U∈SU(2) at O(log 1/ε) with ≤2 ancillas — so the project's universal-synthesis claim IS delivered, via ancillas. Capped literature-wall headline.

**Remediation:** No correctness fix needed — the gap is honestly carried as an explicit theorem hypothesis and disclosed plainly in D8. Bundles must cite kmm_universal_headline for the unconditional ∀U claim and rossSelinger_synth_of_residual for the ancilla-free-conditional claim, never swapping them. Genuine unconditional ancilla-free discharge requires Landau-Ramanujan half-dimensional sieves (beyond formal libraries).

**Sources:** deep-3 (LogLengthHeadline.lean:57-143, GridSolver.lean:83, KMMUniversal.lean:240-364); roadmap-b8 (6AM W5 amended gate), roadmap-b13 (6AO Track-1 tracked Prop), roadmap-b1 (Ross-Selinger §6/§7.2)

### #17 — H_DESICompatibility is DISCHARGE_FUTURE_PHASE scheduled for Phase 6b.2 ('not currently active') — Friedmann-cosmology DESI-match headline has NO anchor predictor; an effort-magnitude deferral of in-scope work

🟠 `headline` · impact **high** · achiev **medium** · status _open_ · score **56** · _deferred_objective_

**Why it ranks here:** roadmap-b1/b14 + deep-1: ledger classifies it DISCHARGE (derivable-in-principle, ~50 person-hours), not KEEP, but Phase 6b.2 is 'not currently active' and 6b.2 actually shipped a NO-GO (joint_phase5y_6b). The (w_0,w_a)-matches-DESI claim has only 3 falsifiers, no actual ADW predictor. Per 'No de-scope from effort magnitude' policy + dev rate (50hr = days here), this is an effort deferral of in-scope work = a real open weakness, not a justified stop. The ledger entry is also internally inconsistent (says 6b.2 not active when roadmap says it shipped). High headline impact, medium achievability.

**Remediation:** Execute Phase 6b.2: couple ADW FLRW perturbations → growth observable → CPL (w_0,w_a) extraction → discharge against DESI DR2 with an ACTUAL predictor. If the multi-scalar chain hits a wall, reclassify to KEEP. Fix the stale 'not currently active' wording given 6b.2's no-go ship.

**Sources:** roadmap-b1 (H_DESICompatibility), roadmap-b14 (Phase6a Wave 4), deep-1, PERMANENT_TRACKED_HYPOTHESES.md §2

### #18 — Phase 6k entire phase: Lean SHIPPED but ALL Python/figures/Paper-43/Stage-13 DEFERRED — Lean PDG-anchored quark-mass/CKM numbers unvalidated against any independent computation path

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **54** · _deferred_objective_

**Why it ranks here:** roadmap-b4: all 5 waves shipped Lean theorems asserting PDG-anchored quark-mass/CKM constants (m_t band, m_b/m_c, Wolfenstein A) with NO Python cross-layer, NO figures, NO claims review — an 8-stage pipeline gap. Pipeline invariants require Python provenance + claim traceability. Per 'no de-scope from effort', a real open deliverable. Additionally W1/W2 band-defining channel-ratio constants risk defining-the-conclusion / PDG-back-fit, and W3 light-quark predictions use ±0.5/±5 bands wide enough to overlap PDG by construction.

**Remediation:** Run Stages 6-13: build src/quark_rung/ modules + tests cross-validating Lean norm_num constants, generate figures, draft Paper 43, run claims-reviewer. Verify channel-ratio constants are derived from substrate params INDEPENDENTLY of the PDG target (not back-fitted); replace within-band tautologies with cross-quark-ratio falsifiers.

**Sources:** roadmap-b4 (Phase6k Status, W1/W2/W3 triviality)

### #19 — PLOB repeaterless secret-key rate is a labeled SURROGATE (loss-penalty monotonicity of the bound function), not the operational rate inequality; doubly-gapped (REE + Gaussian/CV both Mathlib-absent)

🟡 `supporting` · impact **medium** · achiev **literature_wall** · status _open_ · score **52** · _hedge_descope_

**Why it ranks here:** roadmap-b5: the 'repeaterless rate ≤ −log₂(1−η)' headline (D6 bundle) was NOT proved as a rate inequality — PLOBRateBound.lean proves only properties of the bound FUNCTION, honestly labeled surrogate. The operational converse needs LOCC-monotonicity + Gaussian/CV channel-capacity machinery absent from Mathlib; REE E_R(ρ)=inf_{σ∈SEP}S(ρ‖σ) is an irreducible Mathlib wall (separable-set convex-optimization). Honestly disclosed (surrogate/gapped labels in D6 prose). Genuine literature wall, no axiom shortcut (Invariant #15).

**Remediation:** Keep explicit surrogate/gapped labels in D6. To close: build finite-dim LOCC channel-simulation substrate in Lean (Mathlib-upstream-grade research). Given the project's logged 'assert-a-wall reflex' lesson, re-run the full intractability protocol before re-confirming REE is unreachable.

**Sources:** roadmap-b5 (Phase6AK.2/FU-7/FU-8), roadmap-b12 (6AL REE wall, FvdG)

### #20 — Phase 6h flagship PMNS prediction (paper40) gated on conjectural 4D Catterall mirror decoupling (H_CatterallMirrorDecoupling), rigorous only in 2D; entire Phase 6h inactive (Gate Z.4 NEGATIVE)

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **55** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b8: the 'first formal-verification PMNS prediction from substrate symmetry' rests on a tracked Prop encoding a literature-open 4D no-go conjecture (central open problem in lattice chiral gauge theory; Catterall's own paper conjectural in 4D). The whole Phase 6h program (5 waves, paper40, baryogenesis bridge) is LATENT — Gate Z.4 closed NEGATIVE (second structural no-go, V&D mean-field finds no SMG phase). High headline if activated; cannot be discharged internally (needs published 4D Fidkowski-Kitaev analog). Capped literature wall.

**Remediation:** Keep H_CatterallMirrorDecoupling explicitly conjectural; present θ_23 prediction as conditional IF Phase 6h ever activates. Reactivation gated on external published events (F-a-1 4D lattice MC / F-c-1 4D mirror-decoupling rigor). Do not present any 6h consequence as established.

**Sources:** roadmap-b8 (Phase6h Wave 3/4/5, Gate Z.4), roadmap-b15 (Phase5z Wave 4 SMG no-go)

### #21 — Phase 5z flagship m_H prediction is STRUCTURAL-ONLY — 125 GeV reached only on a 1-D tuning curve in (Λ_UV,G_c); paper20 reframed from quantitative EWSB prediction to 'structural identification'

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **53** · _walkback_

**Why it ranks here:** roadmap-b15: the flagship correctness-push (microscopic m_H matching 125 GeV) does not succeed as a quantitative theory — it's a fine-tuned 1-D curve, Gate Z.1 locked STRUCTURAL-ONLY. The negative reading was elevated to the headline ('load-bearing publishable result'). The quantitative scope is gated on the BHL extension which only 'tightens or relaxes'. Also: scalar-rung Yukawa overlap is a structural postulate (not a VZ2014 theorem), M_R substrate-bridge is tracked-hypothesis. High headline impact, hard.

**Remediation:** Execute the SU(2)×U(1)-dressed BHL scalar-channel re-evaluation to produce a genuine parameter-REGION (not 1-D curve) m_H match, or formally publish the structural-only result with explicit hedging. Ensure paper20/21 carry the Yukawa-postulate and M_R-tracked flags.

**Sources:** roadmap-b15 (Phase5z Wave 1/2, Gate Z.1, ScalarRungInterpretation)

### #22 — Phase 6c W5 RT-formula bridge entirely conditional on tracked Prop H_RT_Formula_Valid (RT = QG conjecture, no holographic dual derived); the knife-edge biconditional is borderline c·log(x)=0⟺x=1

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **54** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b2/b10 + deep-1 (verified live): Wave 6c.5's entire 'analog↔real holographic entropy' bridge rests on S=A/4G_N declared external (H_RT_Formula_Valid, KEEP_AS_TRACKED, 4 consumers verified present). Every consuming theorem is under-RT-assumption. Phase 6j 'promotes' it but bare-LM on MTC gives only −(1/2)log D², NOT Kaul-Majumdar — the −3/2 needs LQG isolated-horizon inputs the substrate doesn't supply (H_IsolatedHorizonHypotheses). Additionally the rt_eq_kaulMajumdar_iff biconditional is borderline trivial (log(x)=0⟺x=1). High headline; genuine literature wall (RT has no holographic dual in scope).

**Remediation:** KEEP_AS_TRACKED is the principled posture. Ensure every paper consuming note_rt_ch_bounds hedges 'predicated on H_RT_Formula_Valid' and Phase6j 'derives' reads 'derives-under-hypothesis-bundle'. Verify the iff carries content beyond log(x)=0⟺x=1; if not, demote to corollary and push substance to the −3/2 coefficient theorem.

**Sources:** roadmap-b2 (Phase6c W5), roadmap-b10 (Phase6j hypothesis bundles), deep-1 (RTCasiniHuertaBounds.lean:87)

### #23 — dai_freed_spin_z4 + z16_classification are vacuous existentials (∃φ:ZMod16≃ZMod16, Bijective φ, witnessed Equiv.refl) standing in for the ℤ₁₆ cobordism classification — the Papers-8/9/10/17 hidden-sector headline

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **56** · _placeholder_true_

**Why it ranks here:** roadmap-b3 + deep-2 (verified): the entire ℤ₁₆ anomaly program rests on Ω₅^{Spin^ℤ₄}≅ℤ₁₆ / Ω₄^Pin⁺≅ℤ₁₆, taken as external input, and the Lean theorems named after them prove only trivially-true existentials. UNLIKE gauge-emergence (rank 3), the papers DISCLOSE this honestly (paper8:431-433 'converted to a trivially-true placeholder ... external input, as is standard in the ℤ₁₆ literature'; D5 \placeholdertheorems macro separates load-bearing from documentation markers). So the weakness is the vacuous Lean encoding, not a paper overclaim. High headline backing; genuine literature wall (Mathlib bordism-absent).

**Remediation:** No paper-side action (disclosure correct/conservative). For Lean: replace the self-discharging existential with a named opaque tracked-Prop recording the cobordism iso as external input, so tooling/counters can't mistake it for proved content. Full discharge needs Thom-Pontryagin + Adams + Ext over A(1) — literature wall.

**Sources:** roadmap-b3 (Z16AnomalyComputation.lean:51, RokhlinBridge), deep-2 (Z16Classification.lean:55), roadmap-b13 (5q.B dai_freed placeholder)

### #24 — Phase 6n Witt-class headline conditional on undischarged DMNO-2010 schema (CentralChargePreservesDrinfeldCenter / IsDMNOBiconditional); 5.11 trivial-witness biconditional is vacuous-equivalence

🟡 `supporting` · impact **medium** · achiev **literature_wall** · status _open_ · score **50** · _conditional_headline_

**Why it ranks here:** roadmap-b0/b4: the SymTFT Witt-equivalence categorical compression (D2/L2) ships the DMNO Theorem 5.2 forward direction (Witt-trivial⇒Lagrangian algebra) only as a hypothesis schema; WittClass is proved bijective with ZMod 24 (i.e. IS just ZMod 24), not the actual Witt group of MTCs. The 5.11 architectural-equivalence biconditional holds only under universal trivial-witness and is broken by the 5.12 rank≥2 refinement. IsDMNOBiconditional is a KEEP tracked Prop (forward direction needs MTC + Lagrangian-algebra infra Mathlib lacks). Honest framing; genuine multi-year community wall.

**Remediation:** Keep the conditional framing; ensure D2/L2 prose states the Witt-class compression is conditional on the cited (unproven-in-Lean) DMNO theorem and that WittClass is integer-mod-24-level, NOT a categorical Witt-group construction. Do not cite central_charge_braided_iff_pseudoUnitary as evidence of the DMNO characterization.

**Sources:** roadmap-b0 (Phase6n Wave 1b, 5.11/5.12), roadmap-b4 (IsDMNOBiconditional KEEP, W2.5 hDMNO identity wrapper)

### #25 — ChangeOfRings H2 'discharged' is `True := trivial` + hom_tensor_adjunction_dim/change_of_rings_ext_dim are identity-wrapper tautologies (rank=rank, ext_dim=ext_dim:=h); the Ext-over-A(1) headline rests on cols/8 arithmetic PROXY not Mathlib's real Ext functor

🟠 `supporting` · impact **high** · achiev **medium** · status _partially_resolved_ · score **51** · _placeholder_true_

**Why it ranks here:** roadmap-b10/b12 + deep-2 (verified live ChangeOfRings.lean:110): the 'first machine-checked Ext over a Steenrod subalgebra' headline was backed by proxies that evaded BOTH the type-True counter (ext_dim_n isn't True) and the placeholder-marker detector (body is decide not rfl). h2_discharged:True asserts a discharge that proves nothing; the docstring says H2 is discharged. Phase 5q.T Wave T1 fixed the cohomology-dimension proxy but T2/T3/T4 (genuine A(1) Ring, real Ext via isoExt, real change-of-rings) are PLANNED not shipped — H2 is still a True placeholder. The T5 proxy-detector guard rail is unbuilt. High impact (D2/L2 backing), medium achievability.

**Remediation:** Execute Phase5qT Part 1 (A(1) Ring/Algebra + real Ext via ProjectiveResolution.isoExt) + Part 2 T4 (Shapiro/Hom-tensor adjunction for noncommutative A(1) via restrictCoextendScalarsAdj) replacing h2_discharged:True. Land the T5 proxy-detector validate.py check (flag decide/rfl bodies whose NAME claims a structural quantity). Until then the docstring must NOT say 'discharged'.

**Sources:** deep-2 (ChangeOfRings.lean:110), roadmap-b10 (Phase5qT Part 2), roadmap-b12 (Ext proxies, T5 detector)

### #26 — 6AK.1/6AQ device-bound 'ceilings' and 6AQ readout-floor headlines are EQUALITIES for a model channel / model-identified, not physical upper bounds — the device-bound claim is an unformalized modeling assumption

🟡 `supporting` · impact **medium** · achiev **hard** · status _open_ · score **48** · _conditional_headline_

**Why it ranks here:** roadmap-b5/b2: 6AK.1 avgGateFidelity_coherenceChannel is exact for 𝒜_γ∘𝒟_p; treating it as an upper bound on a real gate's F_avg is a modeling assumption NOT in the theorem. 6AQ ReadoutRelaxationBound/ThermalAssignmentFloor are two-layer: the exp-decay/Boltzmann math is Lean-verified but the identification with device assignment error stays literature-cited. The physically-interesting claim (real devices bounded) is not formally established. Honestly disclosed (two-layer posture in headers, the established plobBound pattern). Genuine physics-modeling assumption, not formalizable from first principles without full measurement theory.

**Remediation:** Keep two-layer disclosure in headers and ensure product/paper consumers state it. A genuine physical ceiling needs proving the coherence channel is extremal among all channels with given T1/T2 — a substantive QI result.

**Sources:** roadmap-b5 (6AK.1/6AK.4), roadmap-b2 (6AQ ReadoutRelaxationBound/ThermalAssignmentFloor)

### #27 — Phase 5d/5/5f/6b/6k cosmology & emergent-gravity headlines resolved to structural NO-GOs — vestigial DE/inflation falsified on all 3 axes (DESI/CMB-ℓ/inflation); Wen→ADW perturbative path closed (~6000× too weak); cosmological-constant only 'reproduced' (~10^122)

🟠 `headline` · impact **high** · achiev **literature_wall** · status _open_ · score **57** · _walkback_

**Why it ranks here:** Consolidated across b1/b4/b11/b15: the emergent-gravity/cosmology program's primary positive routes all returned negative. Phase 6b: 0 viable inflation points/2574, c_s²=−1/3 gradient instability, DESI excluded. Phase 5f Track B: G_Wen≈0.0006 vs G_c≈4.0 + spin-connection-gap showstopper (U(1)→SO(3,1) no known path). Phase 6e: cc_reproduced (~10^122, not resolved). Phase 5y: five NO-GOs, dark-sector scoped OUT of the architecture's predictive reach. These are honest, correctly-reported negative results (the legitimate science), but represent a program-level walkback of the affirmative emergent-physics ambition. High importance for honest framing; genuine physics/literature walls.

**Remediation:** None as defects — the no-gos are the legitimate, publishable results. Ensure bundle prose frames Phase 6b/5f/5y as falsifications (not deferred-positives) and Phase 6e as cc-reproduced (not cc-resolved). Surviving positive routes (instanton 8-fermion, vestigial gravity) are open research; do not oversell.

**Sources:** roadmap-b1 (Phase6b no-gos), roadmap-b4 (Phase5f Wen-ADW, Phase6k CKM no-gos), roadmap-b11 (Phase6e cc_reproduced), roadmap-b15 (Phase5y five no-gos)

### #28 — Phase 6w D7-bundle headline demarcation/bridge theorems shipped 'precise statement TBD' across all 7 same-day waves — exact verified content unspecified; risk of definitional encoding masquerading as substantive equivalence

🟠 `headline` · impact **high** · achiev **medium** · status _unknown_ · score **49** · _conditional_headline_

**Why it ranks here:** roadmap-b5: the three Phase-6w D7 headline theorems (bp_convergence_iff_ldp_below_threshold, analog_hawking_quantum_advantage_demarcation, categorical_chern_eq_real_space_chern) are marked SHIPPED yet written as '(precise statement TBD at Stage 1)'; all 7 waves ship in a single day. Cannot verify from the roadmap whether the 'iff'/'exactly the regime' claims are trivialized by definitional encoding (defining-the-conclusion). High headline impact (the load-bearing claims for the newly-spun-out D7 bundle), medium achievability (audit the actual Lean statements).

**Remediation:** Audit the actual Lean statements of the three D7 headlines against the informal headlines; run the defining-the-conclusion check (does making the function := obvious-target make the iff trivial?). Run the D7 Stage-13 claims-reviewer anchor list.

**Sources:** roadmap-b5 (Phase6w Waves 6w.3/6w.5/6w.6)

### #29 — Phase 5n 3450-model + gapped-interface (TPFConjecture) chirality-wall: 1+1D proof-of-concept rests on native_decide (eliminable per 6AO Track-3); 3+1D hard case unbuilt; chirality wall verdict remains CONDITIONAL on the conjectural TPFConjecture

🟡 `headline` · impact **medium** · achiev **literature_wall** · status _open_ · score **50** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b5/b7/b12 + deep-3 (verified 4 TPFConjecture consumers): the SM anomaly-matching → chiral-gauge-theory existence is the TPF conjecture restated and propagated (one-line H applications), not proven by the project. Proven only in 1+1D (k3450, native_decide on small-integer quadratic forms — eliminable) and 2+1D (FK Δ=14); 3+1D/4+1D at the literature frontier with no constructive approach. The honest tracked-Prop framing makes the dependency visible at type-signature level (correct posture; paper9 hedges correctly — no overclaim found). Capped literature wall; the native_decide 3450 facts are easy-eliminable.

**Remediation:** Keep TPFConjecture KEEP_AS_TRACKED; ensure every consuming paper hedges 'predicated on TPFConjecture (proven 1+1D/2+1D, conjectural 3+1D/4+1D)'. Replace the 3450 quadratic-form native_decides with norm_num/explicit Fin-matrix (kernel-pure, cf. 6AO Track-3). Reconcile the Phase5n W3-pending-vs-W4-complete dependency inconsistency.

**Sources:** roadmap-b5 (Phase5n 3450/Tracks), roadmap-b12 (Phase5h TPFConjecture conditional), deep-3 (SPTClassification.lean:305-350)

### #30 — T-gate braid never reaches target ε≤10⁻³ (random-search plateau ~4.5e-2, GA-SK NOT STARTED); CNOT shipped from figure-only HZBS transcription with no Lean Frobenius certificate — 2 of 3 universal gates lack completed machine-checked precision

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **47** · _deferred_objective_

**Why it ranks here:** roadmap-b1: the 'explicit universal gate compilation' deliverable is precision-incomplete on its hardest gates. T-gate is ~14× short of the stated default precision (L=46 ε≈1.38e-2 vs target 10⁻³); the proper GA-SK fix is NOT STARTED. CNOT rests on figure-to-ASCII transcription (error-prone provenance, G13 pending) with the Frobenius native_decide not completed. Even Hadamard's final split-form native_decide is deferred (ε primary-source-cited). Medium impact, medium achievability (GA-SK is ~multi-hour Python; field substrate ready).

**Remediation:** Implement GA-SK (Long-Bourassa-Bell 2025) Python SK iteration to reach ε≤10⁻³ for T-gate; cross-validate the CNOT braid against independent regeneration and complete its Frobenius native_decide; finish Hadamard's split-form discharge with the Python-precomputed QCyc40Ext literal.

**Sources:** roadmap-b1 (Phase6p R5.6, 3a.2.2/3a.2.3, G13)

### #31 — Phase 6r-prime 20k-LoC/≥1-year acceptance bar institutionalizes effort-magnitude deferral; N16 flags most 'Phase 7+' framings are actually tractable — contradicts 'no de-scope from effort' policy

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **46** · _hedge_descope_

**Why it ranks here:** roadmap-b4: the audit's operational acceptance bar is '>20k LoC required' — precisely an effort-magnitude gate, contra the project's locked-in 'no de-scope from effort magnitude' policy. The roadmap itself catches this (N16: most 'Phase 7+' deferrals are tractable). The further-deferred tracks (full APS, full MTC typeclass, full cobordism category) are genuine multi-year Mathlib walls, but the LoC bar conflates them with effort-only deferrals. Systemic: this bar is a descope vector across the whole late-phase program.

**Remediation:** Distinguish genuine literature walls (full APS index theorem, full MTC typeclass — real multi-year Mathlib gaps) from effort-only deferrals (the N16 'Phase 7+' framings the audit itself says are tractable); the former stay as substrate, the latter must be scheduled, not parked behind the LoC bar.

**Sources:** roadmap-b4 (Phase6r_prime audit bar, N16); roadmap-b5/b13 (effort-deferred Phase5_Roadmap items)

### #32 — Phase 5p Müger modularity biconditional det(S)≠0⟺Z₂(B)=Vec proves only the forward direction; FPdim 'derivation' is per-MTC native_decide eigenvector-witness (no Perron-Frobenius); general D²(Z(Vec_G))=|G|² never proven (2 instances only)

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **52** · _deferred_objective_

**Why it ranks here:** roadmap-b9: Phase 5p's 'verified structure' headlines are half-proven. The modularity theorem (det(S)≠0⟺Z₂(B)=Vec) ships only Direction 1; Direction 2 needs Müger Lemma 2.15 (S²=dim(C)·C, Verlinde+cabling, Mathlib-absent). FPdim is 'derived' by per-MTC native_decide eigenvector equations, NOT proving FPdim is the LARGEST eigenvalue (the defining property) — Perron-Frobenius deferred/unproved upstream. The general dimension formula D²(Z(Vec_G))=|G|² is two hand-enumerated instances (Vec_{Z/2}=4, Vec_{S₃}=36), not the structural theorem (blocked on Mathlib Σ(dim ρ)²=|G|). High headline (the 'modularity from verified data to verified structure' claim), hard/medium.

**Remediation:** State and prove Perron-Frobenius for irreducible non-negative integer matrices (Mathlib has IsIrreducible scaffolding) → per-MTC eigenvector witnesses become specializations of one structural theorem. Formalize Müger Lemma 2.15 for Direction 2 (research-grade). Prove Σ(dim ρ)²=|G| from char_orthonormal for the general D² formula (days at project rate, not the deep-research 2-4 PM estimate).

**Sources:** roadmap-b9 (Phase5p Wave 5/1/2/6)

### #33 — Phase 6f/6g GR program shipped entirely at algebraic/point-wise scope (no connection-based layer); 2nd Bianchi ∇^μG_{μν}=0, Schwarzschild Ric=0, and the NEC-on-T_μν^emerg correctness anchor all DEFERRED — 'first formalization' claims are narrower than stated

🟡 `supporting` · impact **medium** · achiev **hard** · status _open_ · score **48** · _deferred_objective_

**Why it ranks here:** roadmap-b9/b12: all 6 waves of Phase 6f + 6g shipped abstract-relation/structural-Prop scope (~36 thms vs 86-120 target). The contracted Bianchi identity ∇^μG_{μν}=0 (the GR conservation law, IN SCOPE) is absent; Schwarzschild's defining Ric=0 is deferred; the 'single most load-bearing check in the post-SK-EFT gravity program' (NEC on T_μν^emerg) is BLOCKED because Phase 6e only supplies the trace, not a (0,2)-tensor. The 'first formalization in any prover' claims are scoped to algebraic-predicate versions. Medium impact, hard (genuine differential-geometry-in-Lean gated on Mathlib Lorentzian/curvature + Bonn CovariantDerivative).

**Remediation:** Execute Session 4c (mkHom₃, bundled CovariantDerivative.riemann, EuclideanSpace specialization) → derive ∇^μG_{μν}=0; once Bonn API consumed, compute Schwarzschild Ric=0; have Phase 6e supply T_μν^emerg as a concrete Lorentzian (0,2)-tensor to resolve the NEC correctness anchor. Keep 'first formalization' claims qualified as algebraic/point-wise.

**Sources:** roadmap-b9 (Phase6f.2/6f.3/6f.4), roadmap-b12 (Phase6g G.3, structural-Prop scope)

### #34 — Phase 6AH/6AC/6AD quantum-network trivialities: DEJMPS correction vacuous on its only input; GHZ-vs-W advantage defined-to-conclude (ghz3=0 cited modeling input); BBN violators conditional on hand-supplied delta_n_eff hypothesis

🟡 `supporting` · impact **medium** · achiev **easy** · status _likely_resolved_stale_ · score **45** · _triviality_

**Why it ranks here:** roadmap-b0/b14 + deep-4: cluster of QuantumNetwork (D6) defining-the-conclusion patterns. 6AH.6 DEJMPS-correction theorem was vacuous (Werner input where corrected pairing COINCIDES with naive); 6AH.7 GHZ-advantage had conclusion baked in (ghz3RandomizationAdvantage:=0 cited modeling input → w3 'strictly beats' partly by fiat); BBN violators (z16_singlet/fg_torsion) reduce to ¬(3.0≤0.34) once delta_n_eff is granted as hypothesis. The DEJMPS/GHZ ones report fix theorems exist (likely resolved); BBN is honestly disclosed as tracked-thermalization-conditional. Medium impact, easy/hard mix.

**Remediation:** Verify the asymmetric-input DEJMPS theorem genuinely has B≠D and the GHZ advantage is derived from an explicit local-randomization model (two-sided). For ghz3RandomizationAdvantage=0, ship a derivation or flag the zero as cited input so the strict-beat isn't over-read. BBN is acceptable as-is (honest tracked-hypothesis framing) — flag only so D-bundle narrative doesn't claim unconditional violation.

**Sources:** roadmap-b0 (Phase6AH.6/6AH.7), deep-4 (BBN.lean:304/333, ghz3), roadmap-b15 (6AC ghz3 cited input)

### #35 — Phase 6AC teleportation Horodecki f_avg=(2F+1)/3 + utility threshold gated on Haar-integral tracked hypothesis HaarPauliConstant (=1/3), undischarged though Mathlib has the sphere-Haar machinery at pin

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **44** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b15: the teleportation average-fidelity headline + teleport_beats_classical_iff are proven only under HaarPauliConstant c:=c=1/3 (the Pauli-quadratic sphere-Haar integral). A probe confirmed Mathlib at pin HAS the sphere-Haar machinery (Measure.toSphere, integral_fun_norm_addHaar) but NOT this specific integral, so it was routed as a tracked hypothesis (explicitly NOT a project axiom). Honestly framed, but discharging is 'just more Lean work' on available substrate — so an effort-deferral of in-scope work, not a wall. D9-cited teleportAvgFidelity_horodecki_unconditional exists.

**Remediation:** Discharge HaarPauliConstant by proving ∫_{S²}(⟨ψ|σ_k|ψ⟩)²dμ=1/3 from Mathlib's existing sphere-Haar machinery (present at pin), eliminating the tracked hypothesis and making the teleportation headline unconditional.

**Sources:** roadmap-b15 (Phase6AC Wave 3, Teleportation.lean HaarPauliConstant)

### #36 — Phase 6AA/6AB/6AD quantum-network substrate is Bell-diagonal/Werner-only by deliberate pre-demand descope; envelope theorem is a [1/4,1] within-physical-range band; SKR threshold parametric; W-state =1 correctly excluded as open conjecture

⚪ `leaf` · impact **low** · achiev **hard** · status _open_ · score **36** · _hedge_descope_

**Why it ranks here:** roadmap-b11/b14: the verified quantum-network substrate is scoped to a real-parameter Bell-diagonal slice; the general density-matrix/trace-distance/diamond-norm layer is explicitly 'do NOT build' pre-demand (subsequently built in 6AE/6AI, so partly superseded). The swapChain_fidelity_envelope [1/4,1] is close to a within-range tautology (the substantive content is the monotonicity, and the exact closed form (1+3wᵏ)/4 already exists in EndToEnd.lean). The W-state =1 / Fortescue-Lo optimality / Caves CCR-floor are correctly carried as explicit non-claims (verified clean — no overclaim). Low impact.

**Remediation:** Promote the exact closed-form end-to-end fidelity to the headline envelope instead of the static [1/4,1] band; instantiate the SKR threshold at a concrete cutoff (e.g. 11% QBER) if device-specific claims are needed. The general density-matrix layer was correctly built on real demand (6AE/6AI) — update 6AA/6AB cross-refs noting it's no longer post-phase.

**Sources:** roadmap-b11 (Phase6AA/6AB envelope, W-state, Caves), roadmap-b14 (6AB SKR parametric, 6AD link-rate Tier-3)

### #37 — Phase 6AL Lidskii-Wielandt frame-existence (Hframe) is a genuine Mathlib-absent wall — sharp Fannes-Audenaert log(d-1) constant staged as undischarged hypothesis hAud; the four-times over-wide-fence discipline failure (6AF) is a systemic over-conservative-blocked-claim signal

⚪ `leaf` · impact **low** · achiev **medium** · status _likely_resolved_stale_ · score **40** · _literature_wall_

**Why it ranks here:** roadmap-b12/b13: the sharp Fannes-Audenaert log(d-1) entropy-continuity constant carries undischarged hypothesis hAud (absent finite-Fano layer); the arbitrary-subset Lidskii Hframe is genuinely Mathlib-absent (no majorization API / Cauchy interlacing), with multiple elementary routes refuted. BUT the Mirsky HEADLINE was closed unconditionally via PSD-split bypassing Hframe, so Hframe is OFF the critical path. The meta-finding: 6AF drew the FvdG-upper fence too wide FOUR times (each turned out reachable) — a systemic over-conservative 'blocked/multi-week' assessment skewing toward false-negative. Low direct impact; the meta-lesson is the value.

**Remediation:** Build the maximal-coupling+Fano-by-grouping route to discharge hAud (~300-700 LoC, reuses shipped negMulLog/Jensen). Encode the 6AF lesson: every 'blocked/multi-week' fence requires a mandatory fresh fan-out + arithmetic-verified absent-brick argument before claiming a wall (the project's risk assessments skew false-negative).

**Sources:** roadmap-b12 (6AL Hframe/hAud, 6AF over-wide fences), roadmap-b13 (6AF FvdG resolved)

### #38 — Phase 6q DKMBootstrap shipped 20 P2-P5 anti-pattern theorems requiring a dedicated strengthening pass; IsDKMFeasibleSDPCandidate KEPT as Prop:=True scaffold; BEC NO-GO witnessed by a (2κ)! STAND-IN sequence not derived from the Bogoliubov Hamiltonian

🟡 `supporting` · impact **medium** · achiev **medium** · status _partially_resolved_ · score **43** · _triviality_

**Why it ranks here:** roadmap-b15: the Phase 6q first-pass shipped 20 trivialities across 8 categories (synonym defs, Prop:=True scaffold, decide-able distinctness, zero-substrate witnesses, identity wrappers) — mostly resolved in Session 2 but IsDKMFeasibleSDPCandidate (one of the 3 structural obstructions the phase claimed to resolve) was KEPT as Prop:=True 'Phase 7+ placeholder'. The BEC sharpened-NO-GO half is witnessed by becBogoliubovCommutatorNorm:=(2κ)! (a stand-in, not derived from the Hamiltonian); graphene positive-uniqueness uses loose mirConst=1/2 (6.6× looser than true 0.0756). Medium impact, medium achievability.

**Remediation:** Lift IsDKMFeasibleSDPCandidate from Prop:=True to substantive convex-cone-positivity content (Mathlib ProperCone.hyperplane_separation + PositiveLinearMap are present at pin). Execute the Yin-Lucas / Lieb-Robinson-for-bosons derivation showing the BEC Bogoliubov commutator achieves (2κ)! from the Hamiltonian; lift the sharp graphene MIR constant 0.0756 into Lean.

**Sources:** roadmap-b15 (Phase6q §A.1-A.8, B.1/B.3, IsDKMFeasibleSDPCandidate)

### #39 — Phase 6o Wave 4a Sakharov Λ_J⟺Λ_HK biconditional was a P5 self-discharging tautology (S.x=true→S.x=true) walked back to one-way implication; D5 §11 still ships the Λ_J=Λ_HK independence via prose hedge not Lean derivation

🟡 `supporting` · impact **medium** · achiev **literature_wall** · status _likely_resolved_stale_ · score **42** · _walkback_

**Why it ranks here:** roadmap-b6/b0: the D5 §11 Sakharov 4-criterion 'iff Λ_J=Λ_HK' was a structural tautology (lambdaJEqLambdaHK was a literal Boolean projection); honestly retired to a one-way implication. The (⇐) direction does not hold under available substrate (no primary source argues the converse; Volovik-Jannes 2012 §VII argues only forward) — a genuine literature gap. Separately, the D5 lambdaJEqLambdaHK substrate-derived independence is still shipped via section-11 prose hedge, not Lean. Honest one-way closure shipped; the prose hedge is the residual.

**Remediation:** Ensure D5 §11 prose reflects the one-way implication (not biconditional); no flagship narrative should cite 'Sakharov criterion iff Λ_J=Λ_HK'. Execute the D5 _iff_→_implies_ Lean refactor so lambdaJEqLambdaHK independence is substrate-derived rather than a permanent prose hedge (avoids the P5 prose-hedge pattern).

**Sources:** roadmap-b6 (Phase6o Wave 4a), roadmap-b0/b12 (D5 §11 prose hedge carry-forward)

### #40 — AttributionContentSweep residual: ~440 non-anchor bibkeys only partially swept + human-gate items open; fabrication-class base rate (3/10 spot-checks, ~8 caught only by WebFetch-and-compare) means the un-swept tail can harbor metadata-valid-but-fabricated attributions

🟡 `supporting` · impact **medium** · achiev **easy** · status _partially_resolved_ · score **47** · _deferred_objective_

**Why it ranks here:** roadmap-b7/b12/b15: the load-bearing tranche is GREEN (18 bundles, 6 fabrication-class fixes incl Sen −45/2→212/45, hallucinated WetterichNJL/Davighi2023), but the widening to all ~440 cited bibkeys is a partially-complete follow-on, and named human-gate items remain (AharonovArad Lemma 6.1 full PDF, Amelio2020 disambiguation, forward-dated venues). Phase 7 found 8/16 BLOCKERs were fabrication-class caught ONLY by WebFetch-and-compare; 5z found 4/10 bibkeys wrong incl 1 hallucinated. The fabrication base rate means the tail is a real residual honesty risk before submission. Easy (mechanical WebFetch verification), medium impact.

**Remediation:** Resolve named human-gate items (AharonovArad PDF, Amelio2020, venue DOIs); run the widening pass over the ~440 non-anchor bibkeys before any submission, prioritizing falsification-critical bundles (L1/D5/D3). Implement the proposed validate.py checks (bibitem_title_matches_arxiv, citation_registry_no_et_al_title_artifact) to prevent recurrence.

**Sources:** roadmap-b7 (AttributionContentSweep residual), roadmap-b12 (Phase7 8/16 fabrication BLOCKERs, Class TN drift), roadmap-b15 (5z 4/10 bibkeys + hallucinated)

### #41 — Phase 7 Wave 15 pre-submission Stage-13 sweep + user submission authorization never closed; I3 bundle (14th target) stuck at DRAFTING (sourceless lift) — Phase 7 not formally closed, no bundle submitted

🟠 `headline` · impact **high** · achiev **medium** · status _open_ · score **50** · _deferred_objective_

**Why it ranks here:** roadmap-b12: Phase 7 (the submission phase) is not closed — the final fresh-context adversarial sweep on the current post-absorption basis is unrun, no bundle is submitted, I3 remains DRAFTING. Bundle GREEN states are from PRIOR review rounds, not the final submission-gate sweep; later 6X phases may have re-flagged bundles freshness-stale. High impact (the whole point of the program is publication-realization) but also gated on the user obtaining a gr-qc arXiv endorsement (L1 deposit). Medium achievability (orchestrated review work, not a research wall).

**Remediation:** Run Wave 15: fresh-context claims-reviewer + figure-reviewer + adversarial-reviewer on all 13(+I3) bundles on the current basis, resolve BLOCKERs, finish I3's substantive draft + its Stage 9/10/13 triple, then obtain user submission authorization. Confirm current bundle freshness against later 6X phases. USER ACTION: gr-qc arXiv endorsement gates L1 deposit.

**Sources:** roadmap-b12 (Phase7 Wave 15, I3 DRAFTING), MEMORY (arXiv endorsement pending)

### #42 — backreaction.py + polariton(paper12) provenance: SI platform params hardcoded bypassing the corrected EXPERIMENTS chain (10× κ discrepancy); Falque polariton params PROJECTED, off published values by 2.5×/>10× (c_s, τ_cav) — material to the EFT-regime feasibility claim

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **44** · _other_

**Why it ranks here:** roadmap-b5: Pipeline-Invariant-2 (constants canonical) violation open across multiple sections — backreaction.py:99-155 hardcodes SI params bypassing the provenance-corrected chain with a known 10× κ discrepancy (affects Paper 4 §5 cooling numbers). Polariton predictions (Paper 12 T_H, EFT-regime) rest on PROJECTED params off Falque by 2.5× (c_s) and >10× (τ_cav: 100-300ps projected vs ~8ps actual) — the 'ultra-long cavity needed for EFT regime' conclusion depends on a τ ~12× longer than the actual device. Medium impact (publication-facing numbers), medium achievability.

**Remediation:** Wire backreaction.py to import platform params from EXPERIMENTS/transonic_background, eliminating the hardcoded block + 10× κ discrepancy; re-verify Paper 4 §5. Complete the Falque primary-source re-verification; decide explicitly whether to use Falque values (re-derive T_H/κ/D) or retain projections with clear PROJECTED tier labeling in Paper 12.

**Sources:** roadmap-b5 (backreaction.py 9B-3/9C-4/9D, polariton 9D/9B-5)

### #43 — Phase 5d/5/5f vestigial-gravity Monte Carlo never reached publication-quality detection — L=8/L=12 RHMC blocked, multiple prior 'split transition' claims INVALIDATED as uncoupled-site artifacts; vestigial phase OPEN, exponentially-narrow window may be unresolvable at workstation scale

🟠 `headline` · impact **high** · achiev **hard** · status _open_ · score **49** · _deferred_objective_

**Why it ranks here:** roadmap-b5/b6/b7: Papers 5/6/13's headline numerical vestigial-phase result was never delivered — the analytical existence proof (G_ves<G_c) stands but the MC confirmation is open, blocked on RHMC plagued by convergence pathologies (CG bottleneck at κ≈6000, sign reweighting avg_sign=0.0 for L≥5). Multiple prior 'split transition detected' claims were invalidated as uncoupled-site bugs. The vestigial window is exponentially narrow (exponent ≈−1125) and may be unresolvable at L≤8/workstation scale. High headline impact, hard (compute-bound + genuine numerical hard problems).

**Remediation:** Complete L=8 (and L≥12 via sparse CG/Metal) RHMC; extract Binder crossing + metric order parameter. If the exponentially-narrow window is unresolvable at workstation scale, document as a meaningful negative/limitation result. Keep the analytical existence proof as the defensible headline; frame MC as confirmation-pending.

**Sources:** roadmap-b5 (Phase5 Waves 7C/7D/8/9C), roadmap-b6 (Phase5d Wave 3), roadmap-b7 (Phase5g Track A Wave 3)

### #44 — Trivial Cartan-matrix-entry + SFDM/dark-matter rational-threshold native_decides are ELIMINABLE (decide/norm_num) — gratuitous compiler-trust axioms on integer constants and ℚ inequalities

🟡 `supporting` · impact **medium** · achiev **easy** · status _open_ · score **45** · _native_decide_

**Why it ranks here:** Deep-0: a large fraction of quantum-group (QuantumGroupInstantiation 19, Generic 12, Meta 11) + E8Lattice (11) native_decides prove trivial finite-integer facts (cartanA1 0 0=2, det E₈=1, hDual=1+1) well within kernel decide budget. SFDM/FractonDM (16 total) use native_decide on ℚ threshold inequalities (9≤snr²·18) and small-inductive Bool no-go checks where norm_num/decide suffice. These inflate the transitive native_decide trust surface of downstream quantum-group equivalence theorems and Tier-4 forecast paper claims WITHOUT genuine compute need. Easy bulk find-replace, medium impact (removes dozens of trust axioms).

**Remediation:** Mechanically replace `by native_decide` with `by decide`/`rfl`/`by norm_num` for sub-8×8 integer Cartan/det lookups and ℚ threshold inequalities; replace `cases t <;> native_decide` with `<;> decide` for small-inductive no-go checks; rebuild to confirm kernel tractability. Removes trust axioms from quantum-group, E8Lattice, and SFDM/Fracton closures.

**Sources:** deep-0 (QuantumGroupInstantiation.lean:67/441, E8Lattice.lean:42/52/72, SFDMMergerForecast.lean:415-428, FractonDarkMatter.lean:200/304)

### #45 — EmergentGravityBounds + TPFEvasion + ChiralityWall + DEC-orthogonality 'physics' theorems are bare arithmetic / verdict-by-stipulation (4×4=16, 9−3<9, IsViable=false by rfl on a hand-set flag) with all content in comments — the substantive forms exist elsewhere

⚪ `leaf` · impact **low** · achiev **easy** · status _open_ · score **38** · _triviality_

**Why it ranks here:** Deep-4: clusters of P3/definitional-unfolding-as-physics — EmergentGravityBounds tetrad_components:4*4=16, spin_connection_gap:6>1, tetrad_modes_nf_independent(N_f):10=10:=rfl (unused arg); TPFEvasion nogo_fails_with_three_violations:9-3<9; ChiralityWall decide-over-hand-set-flags; dec_fails_orthogonality_principle reads back gibbsDuhemEvaded:=false. The numerals aren't bound to formalized tetrad/mode/group objects so the theorems are true regardless of the physics. The GENUINE forms exist (wen_adw_ratio, nogo_contrapositive abstract Fin 9→Prop, dec_cpl_excluded_from_desi, violation_I3/C1) — these are redundant scaffolding. Low impact (not the load-bearing proofs), easy.

**Remediation:** Delete the bare-arithmetic stubs; keep the abstract structural theorems (nogo_contrapositive, wen_adw_ratio, violation_I3/C1) as load-bearing. Make dec_orthogonality_model.gibbsDuhemEvaded DERIVE from GibbsDuhemTheorem.wVac_eq_neg_one (realize the cross-bridge per P6 discipline). Restate counts against formalized Finset/dim functions, not 2=2.

**Sources:** deep-4 (EmergentGravityBounds.lean:160-195, TPFEvasion.lean:94-144, ChiralityWall.lean:241-271, EntropicGravityDarkEnergy.lean:327-343)

### #46 — Phase 5i/5/5a/5b/5d/3 historical sorry/axiom roadmap text is STALE vs ground truth (0 sorry, 0 axioms) — Z16/gapped-interface/spectral-gap/GaugeErasure/Fermi-Point axioms all converted to tracked Props or discharged

⚪ `cosmetic` · impact **low** · achiev **trivial** · status _likely_resolved_stale_ · score **22** · _axiom_residual_

**Why it ranks here:** Consolidated across b3/b4/b5/b6/b12/b13: many early-phase roadmaps reference live axioms (z16_classification, gapped_interface_axiom→TPFConjecture, HasSpectralGap, GaugeErasure discrete-center, Fermi-Point Bott-periodicity) and project-wide sorries (Phase5i 17, Phase5b 11, Phase5d CenterFunctor 2, Phase5e KLinear/Spherical/Fusion stubs). Ground truth: counts.json axioms=0, sorry=0. These are HISTORICAL snapshots — the axioms were converted to tracked Props or discharged. Per the prompt's stale-dropping rule these are likely_resolved_stale; flagged as ONE consolidated cosmetic item rather than dropped because the roadmap text still misleads a future reader.

**Remediation:** No proof action (counts.json confirms 0/0). Documentation hygiene: add dated status headers to the stale roadmaps marking axiom-introduction rows HISTORICAL and pointing at the tracked-Prop successors (TPFConjecture for gapped_interface; verify GaugeErasure discrete-center and Fermi-Point are now theorems/Props). Surface the real residual (the tracked-predicate density gate) rather than burying it under stale text.

**Sources:** roadmap-b3 (Phase5i 17 sorry, Phase5b axioms), roadmap-b4 (Phase4/6p axiom rows, Phase6n '1 axiom'), roadmap-b5/b6 (FermiPoint/categorical sorries), roadmap-b12/b13 (Phase3 GaugeErasure, Phase5a z16/spectral-gap)

### #47 — ~26-43 *_module_summary_marker / *_TODO `True := trivial` cosmetic markers + counts.json placeholder discrepancy (26 reported vs 43 on-disk type-True); honestly-labeled definitional re-exports (pillar3_*_DEFINITIONAL, T_dS_double_TGH)

⚪ `cosmetic` · impact **low** · achiev **trivial** · status _open_ · score **24** · _placeholder_true_

**Why it ranks here:** Deep-2/deep-4: ~30 per-wave GR/cosmology *_module_summary_marker:True audit-trail anchors (self-labeled non-substantive) + the 4 substantive *_TODO stubs (ocneanu/fusion_to_tqft/equiv_braided/monoidal, rank 15 covers the un-suffixed siblings). A type-True grep finds 43 but counts.json reports 26 placeholders — a reconciliation gap. The _DEFINITIONAL re-exports (pillar3_onsager_dg, T_dS_double_TGH=2·T_GH) are honestly disclosed transparent re-exports, NOT masquerades. Low impact (no concealed claim); the good news is the worst within-2σ band tautologies are already gone (y_p_within_pdg_2sigma → y_p_central_in_physical_range).

**Remediation:** Convert cosmetic markers from `theorem foo:True:=trivial` to non-counting forms (def/comment) so they stop padding theorem counts and type-True audits; reconcile counts.json placeholder (26) with on-disk type-True total (43). The _DEFINITIONAL re-exports are fine as-is (exemplify the transparent-naming discipline working).

**Sources:** deep-2 (43 type-True vs 26), deep-4 (T_dS_double_TGH, pillar3_DEFINITIONAL, dg_generator_count 2=2), roadmap-b9 (FusionCategory placeholders)

### #48 — Phase 5g/5i/5o/6s Mathlib upstream-PR contributions never filed — gated on external Zulip/AI-disclosure relationship-building; tensor-categories (114 thms) + PolyQuotQ + matrix-log + Cartan all internal-only; Phase 6x first-pass 'PRs' were alias-only

⚪ `cosmetic` · impact **low** · achiev **medium** · status _open_ · score **30** · _deferred_objective_

**Why it ranks here:** Consolidated b1/b5/b7/b8/b10: the community-contribution deliverables (lean-tensor-categories 114 thms, PolyQuotQ number-field infra, matrixMercatorLog, SU(d) Cartan density-from-witness) are prepared but unsubmitted, gated on a human relationship-building step (Mathlib Zulip intro + AI-content disclosure) the user/PI must perform. Phase 6x/6y first-pass M-S 'PRs' were alias-only (not substantive de-privatized extractions). Low impact (not on any paper's critical path; the math is done in-project), the blocker is social/process not mathematical.

**Remediation:** User-side: open the Mathlib Zulip conversation, disclose the AI-assisted pipeline, agree PR sequencing; then atomic PRs (QSqrt2 first) are 'just more Lean work'. Agent can pre-draft the Zulip memo + first PR while gated. Complete the M-S substantive de-privatized generic-typed extractions (de-privatize + namespace + generalize type + docstrings) rather than aliases.

**Sources:** roadmap-b7 (Phase5g Track B/C, Phase5o Wave 5), roadmap-b1 (Phase5i Wave 4d), roadmap-b5 (Phase6_Deferred upstream batch), roadmap-b8 (Phase6x alias-only), roadmap-b10 (Phase6y M-S)

### #49 — Phase 6s/6o/6n bundle absorption (D.2/D.3 paper lifts) for many shipped waves HELD indefinitely — Lean math shipped but paper consequences (D2 Schellekens reframe, flagship-F unification chapter, Itô/LDP I3) not absorbed into any bundle

🟡 `supporting` · impact **medium** · achiev **easy** · status _open_ · score **42** · _deferred_objective_

**Why it ranks here:** roadmap-b6/b9/b11: every Phase 6o wave + many 6n/6r/6q waves are 'SHIPPED' at Lean/memo level only, with bundle absorption DEFERRED to a unified late-absorption pass that hasn't occurred. The publication payoff (soft theorems, double-copy, APS-η, Schellekens 24|c→3-gen reframe, ETH tableau, Itô/LDP, the flagship-F 'unification crown' ~25-40pp chapter) is parked behind held user-authorization gates. Medium impact (the substrate doesn't reach manuscript form), easy/process achievability — these are legitimate D.3 user-auth gates, not effort descopes.

**Remediation:** Execute the unified Phase 6n+6o+6q+6r → Phase 7 bundle-absorption pass per LATE_PHASE6_ABSORPTION_PROTOCOL Stages A-G, clearing the held D.3 user-auth gates (6n W2a I1, 6n W2d D3+L3, 6o W2b D2, 6r flagship-F) and running per-bundle Stage-13 reviews. Process work, surface to user.

**Sources:** roadmap-b6 (Phase6o all-waves held), roadmap-b9 (Phase6q L2/D5/F), roadmap-b11 (Phase6r D2/flagship-F)

### #50 — Phase 6r 'first SymTFT formalization in any prover' + Phase 6k/6e/6t primacy claims are hedged-but-checkable cross-prover-survey assertions the project's own primacy-claim discipline warns against

⚪ `cosmetic` · impact **low** · achiev **easy** · status _open_ · score **28** · _conditional_headline_

**Why it ranks here:** roadmap-b11: repeated 'first X in any major proof assistant' claims (SymTFT, FPdim derivation, Ext over Steenrod subalgebra, stochastic integral, quantum 3-manifold invariant, Pin⁺ bordism) hedged 'to our knowledge after surveying Mathlib/physlib/Coq/Isabelle/Agda'. The project's own primacy-claim discipline (project_2026_05_12_first_claim_close) warns to resist this framing — the verifiability depends on an exhaustive survey that could be falsified by a missed prior formalization. Low impact (cosmetic if not in a paper headline), easy fix.

**Remediation:** Per the project's own primacy-claim discipline, ship descriptive content-first prose and drop or heavily caveat 'first in any prover' framing in any paper-shaped output; keep the cross-prover survey citation but do not lead with primacy.

**Sources:** roadmap-b11 (Phase6r primacy), roadmap-b14 (Phase6u/6AC first-formalization), roadmap-b9 (Phase5k 'first complete verified TQFT')

### #51 — Phase 5x Paper-17 dark-sector headlines are MCC machine-checked classifications not derivations (5 SemanticTautology theorems incl fracton_bullet_sigma_zero=rfl on hardcoded def); the SemanticTautology graph-extractor guard is unimplemented

🟡 `headline` · impact **medium** · achiev **medium** · status _open_ · score **46** · _triviality_

**Why it ranks here:** roadmap-b3: adversarial review flagged 5 SemanticTautology theorems in Paper 17 (fracton_bullet_sigma_zero=rfl on hardcoded sigma_eff:=0, viability_matrix on hardcoded flags, emergent_gravity_dm_invisible decide on hardcoded lookup, distinctness enums, hand-chosen rankings) + lambda_magnitude_ratio T/T=1 — all 'FIXED via paper reframe Derived→MCC' NOT via Lean change. The physics content lives in hand-assigned constants sourced to deep research, not the proofs. The proposed SemanticTautology extractor to mechanically guard this is explicitly NOT implemented. Medium impact (Paper 17 headlines), medium achievability.

**Remediation:** Implement the SemanticTautology extractor (sketched in Wave 10 §QI) and gate Paper 17. For genuine load-bearing content, push substance into derivations (e.g. derive the empirical-hook ranking from a detectability scoring function over Euclid/Roman S/N). All 'just more Lean work', achievable here.

**Sources:** roadmap-b3 (Phase5x Wave 10, FractonDarkMatter.lean:226/234)

### #52 — Phase 5x ADW cosmological-constant / KV dark-energy walked back from 'explains DESI' to 'Level D tension' (excluded 2.9-4.4σ); surviving Λ-magnitude coincidence had undisclosed-tuning O(1) prefactor; fracton-DM viable only conditionally with unresolved production mechanism

🟡 `headline` · impact **medium** · achiev **literature_wall** · status _open_ · score **44** · _walkback_

**Why it ranks here:** roadmap-b3: the original Track-A headline 'KV oscillating vacuum compatible with DESI evolving DE' was retracted — KV predicts (w₀,wₐ)=(-1,0), excluded 2.9σ(Pantheon+)-4.4σ(DESY5); RVM 10⁸² too small. The surviving Λ-magnitude coincidence's O(1) prefactor was disclosed as undisclosed-tuning (20% agreement language removed). Fracton DM is VIABLE only conditional on p-wave dipole superfluid being equilibrium, with the production mechanism 'genuinely the top remaining gap'. FG torsion DM kinematically obstructed (w=1/3) at CDM level. Honest reframes; genuine physics/literature limitations.

**Remediation:** Keep the honest 'reframed not solved' assessment; ensure Paper 17 states the DESI exclusion plainly (not 'within three orders'). Falsifiable externally by DESI DR3 (out of project control). The Volovik self-tuning step / fracton production mechanism have no published derivation — keep 'conditional', do not upgrade to unconditional VIABLE.

**Sources:** roadmap-b3 (Phase5x Finding 2, Wave 3/4/7)

### #53 — Phase 6h light-quark hierarchy fall-through embeds an inert OPEN-AT-FRONTIER Prop field (predictsBandSelectiveLightQuarks for c/s/u/d) that no theorem consumes — advertises an unproven capability for no benefit

⚪ `leaf` · impact **low** · achiev **medium** · status _open_ · score **32** · _placeholder_true_

**Why it ranks here:** deep-3: Phase6hHyperchargeSplittingHypothesis carries predictsBandSelectiveLightQuarks:Prop 'OPEN-AT-FRONTIER for c,s,u,d' but the consuming theorem (phase_6h_supersession_suppression_lt_one) uses only positivity fields and never touches the open Prop — it's inert. Lower stakes: the flagship here is itself a NO-GO fall-through verdict (substrate does NOT close the light-quark hierarchy), honestly framed. Low impact (leaf, no consumer), the structure advertises an unproven capability for no benefit.

**Remediation:** Drop the inert predictsBandSelectiveLightQuarks:Prop field (no theorem consumes it), or if a future hook, document it as a deferred-discharge placeholder in PERMANENT_TRACKED_HYPOTHESES.md so its open-frontier status is catalogued rather than buried in a struct field. The fall-through bundle itself needs no change.

**Sources:** deep-3 (LightQuarkHierarchyFallthrough.lean:197-229)

### #54 — vestigial_phase_eta_violates_microscope_bound compares bare literals (1.0>1e-15) not the named constants it claims to relate — the project's OWN cited GOOD example fails to detect constant drift (cross-bridge-integrity gap)

⚪ `leaf` · impact **low** · achiev **trivial** · status _open_ · score **26** · _triviality_

**Why it ranks here:** deep-4: EquivalencePrinciple.lean:495 proves (1.0:ℝ)>1.0e-15 with a docstring claiming it relates VESTIGIAL_PHASE_ETA_MAX to MICROSCOPE_BOUND, but the statement hardcodes the operands. If either constant drifts in constants.py the theorem stays green while decoupling from the physics. Notably this exact theorem is CLAUDE.md's cited GOOD example of a published-bound comparison — so it IS the right pattern (genuinely falsifiable 15-orders EP violation), the weakness is only that it doesn't reference the Lean-side constants. Minor cross-bridge-integrity gap, trivial.

**Remediation:** Restate over the named Lean constants (vestigialPhaseEtaMax > microscopeBound, unfolding to the literals) so the theorem is wired to the symbols the physics narrative names and would break on drift. Trivial edit; genuinely good otherwise.

**Sources:** deep-4 (EquivalencePrinciple.lean:495/506)

### #55 — Phase 6AO native_decide held at 596 across the phase; 4 KMM-style native_decide sites (kmm_lemma3_alg2 16.7M pairs ~497s, maStep_exists_core ~809k) confirmed kernel-decide-INFEASIBLE under #10 — project-tolerated, need structural reproof (6AO Track-3 proved feasible)

🟡 `supporting` · impact **medium** · achiev **hard** · status _open_ · score **43** · _native_decide_

**Why it ranks here:** roadmap-b8/b13: 596 native_decide-tainted decls at the time; 4 named KMM sites (cliffordBase_box_core, bridge_box_core, kmm_lemma3_alg2, maStep_exists_core) back the Clifford+T exact-synthesis headline yet rely on compiler trust (Lean.ofReduceBool), empirically un-eliminable by kernel decide under #10 (blow the 200k-heartbeat budget). NOTE: 6AO Track-3 ELIMINATED 4 DIFFERENT KMM native_decides via structural-lemma refactor (BridgeParity/MAStepStructural), proving the pattern is feasible — so these are open debt, not a true wall. Medium impact, hard (research-flavoured KMM Lemma-3 mod-8 algebra, Giles-Selinger sde↔kSO3).

**Remediation:** Structural reproofs per the 6AO Track-3 template (the proven elimination pattern): KMM Lemma-3 mod-8 algebra, Giles-Selinger sde↔kSO3, Clifford-group ≤6-word coverage, MA-step orbit-closure. Scope as a dedicated 'structural-KMM purity' /goal. Deep-0 refines the 596 to clarify these are real uses (FKLW real=0 means these live in the synthesis cores, not the RossSelinger files).

**Sources:** roadmap-b8 (Phase6AM W5, 4 KMM nd), roadmap-b13 (Phase6AO 596), deep-0 (real-use distribution)

### #56 — Phase 6AN/6AM/6t Caves added-noise / CCR floor + Ross-Selinger O(log 1/ε) length-optimality are the named literature walls (c) and (a) — quantum-limited noise floor asserted from CCR, compiler length-constant is ε₀-cover-max not RS-optimal

⚪ `leaf` · impact **low** · achiev **literature_wall** · status _open_ · score **40** · _literature_wall_

**Why it ranks here:** roadmap-b3/b8: fdt_noise_floor_amplifier invokes Caves A≥ℏω/2 as a KEEP-cited residual against the CCR wall (needs bosonic CCR ladder [a,a†]=1, Mathlib-absent; from-scratch build disproportionate to certificate value — 'a genuine wall, not an effort deferral'). The Clifford+T compiler's correct-by-construction length constant is cliffordTFiniteCover_maxLength (ε₀-cover max), NOT Ross-Selinger optimal O(log 1/ε) — the same prime-density wall as rank 16. Both honestly disclosed (two-layer posture); genuine named walls. Johnson-Nyquist thermal floor IS derived in-project; only the quantum half is external.

**Remediation:** KEEP cited — both are genuine boundaries. Caves bound's derivation needs a CCR/uncertainty formalization (Mathlib-absent); the optimal length under prime-distribution is literature-open. The exact-synthesis ℤ[ω][1/√2] development (~1.6-3k LoC) is buildable but the optimal length stays literature-bounded. Disclosed as documented constant-improvement residuals, orthogonal to algorithm-level correctness.

**Sources:** roadmap-b3 (Phase6AN W4 Caves, Phase6t/6AN Clifford+T length), roadmap-b8 (6AM W4 CCR wall)

### #57 — Phase 6n/6o/6q substantive infrastructure (full MTC + Witt-group, LDP Cramér/Varadhan/Gärtner-Ellis, Niemeier/VOA Schellekens classification, full APS index theorem) is predicate-level only — Lean composes cited STATEMENTS, does not verify the classifications

🟡 `supporting` · impact **medium** · achiev **literature_wall** · status _open_ · score **45** · _hedge_descope_

**Why it ranks here:** Consolidated b0/b4/b6: a recurring pattern where the depth claimed exceeds what is kernel-checked. Phase 6n Wave 1b ships full MTC+Witt-group as 'multi-year community project', only the integer-mod-24 piece; Phase 6o Wave 2b Schellekens chain has Niemeier + holomorphic-VOA steps as predicate-level shells (Mathlib has no Niemeier/VOA); Phase 6o Wave 2c full LDP framework deferred; Phase 6r-prime W2.2 NonDegBraidedFusion / FPdim axiomatized at predicate-substrate. The D2/D5 reframings entered as cited-external-theorem corollaries, NOT formalized classifications. Honest where disclosed; genuine multi-year Mathlib walls.

**Remediation:** Be explicit in D2/D5 prose that Niemeier/Schellekens-VOA/MTC-Witt/LDP classifications are cited external theorems entered at predicate level, not formalized in-project. Keep 'corollary of a cited classification theorem' framing vs 'formally verified classification'. Build only on Mathlib trigger (these are genuine upstream-PR-class multi-year efforts).

**Sources:** roadmap-b0 (Phase6n Wave 1b/2c), roadmap-b6 (Phase6o Wave 2b/2c, ETH free-probability), roadmap-b4 (Phase6r-prime W2.2 FPdim)

### #58 — Phase 6e/6a heat-kernel + G_N^emerg + positive-mass headlines rest on tracked-hypothesis structures (DiracHeatKernelAsymptotic Seeley-DeWitt, no closed-form α_ADW); PositiveMassTheorem.lean (heaviest 6a wave, paper28) never shipped

🟡 `headline` · impact **medium** · achiev **hard** · status _open_ · score **46** · _tracked_hypothesis_

**Why it ranks here:** roadmap-b11/b14: the 'GR from condensate' chain's heat-kernel a_n coefficients are anchored on tracked-hypothesis DiracHeatKernelAsymptotic (PDE-level Seeley-DeWitt existence, Mathlib spin-bundle-absent — closed-form rational coefficients are kernel-checked, only asymptotic existence assumed). G_N^emerg ships the microscopic coefficient as a tracked structural hypothesis because deep research found NO closed-form α_ADW in literature. PositiveMassTheorem.lean (target 18-24 thms, paper28, the named consolidation anchor) is ABSENT from counts.json — Track D never landed. Medium impact, hard (Mathlib Lichnerowicz-Weitzenbock / spinor-bundle gaps).

**Remediation:** Keep DiracHeatKernelAsymptotic KEEP_AS_TRACKED with primary-source citation; derive the α_ADW closed form (the missing one-loop ⟨hh⟩ broken-phase 2-pt computation) to make G_N^emerg falsifiable against 6.674e-11. Ship PositiveMassTheorem.lean per Wave 6 spec or formally descope paper28 with a documented Mathlib spinor-bundle reason (verify 6f.1/6f.3 prerequisites first).

**Sources:** roadmap-b11 (Phase6e heat-kernel/cc, Phase6a Wave 1 G_N), roadmap-b14 (Phase6a Wave 6 PositiveMassTheorem absent)

### #59 — Phase 5v process-fix deliverables incomplete: PG+AGE single-source-of-truth flip unbuilt (JSON still default, no graph_source_parity check); 13-failure-mode gate-coverage unproven (15/15 RED, CHECK 18 WARN-only); claims-reviewer Class TN false-positive would have merged 2 distinct theorems

🟡 `supporting` · impact **medium** · achiev **medium** · status _open_ · score **41** · _deferred_objective_

**Why it ranks here:** roadmap-b2: Phase 5v's process-fix promises are partially realized — the graph-as-SoT architectural goal is unmet (JSON default, PG optional mirror, no parity check), the '13 April-review failure modes caught by a gate' criterion is unverified (initial run 15/15 RED, submission gate WARN-only so blocks nothing), and the QA tooling itself had a Class TN false positive whose auto-fix would have collapsed 2 distinct theorems (self-inflicted regression). Partly superseded by AttributionContentSweep (18/18 GREEN) per MEMORY. Medium impact (the verification machinery), medium achievability (tooling work).

**Remediation:** Wire SK_EFT_GRAPH_SOURCE=pg routing + implement validate.py --check graph_source_parity; run the known-bad/known-good regression to confirm 13-mode gate coverage and escalate CHECK 18 WARN→FAIL once papers reach green; implement the TN-finding deterministic-grep self-check + sentence_state.py mark-issue-fixed (both filed, unimplemented). Reconcile against AttributionContentSweep supersession.

**Sources:** roadmap-b2 (Phase5v Wave 3/9f, 13-failure-modes, Wave 10h Class TN, name_deps gated OFF)

### #60 — Phase 6a Wave 5 BHThermodynamicsFourLaws shipped a primary-source-conflated WRONG result (He3-A heating vs Balbinot BEC cooling) requiring full rewrite; Phase 6o/6q/6z/6t/6y multiple post-ship overclaim-vs-delivered gaps caught by review (figure-eight 'in flight' vs native_decide-closed, headline-from-witness gap, M-S alias-only)

🟡 `supporting` · impact **medium** · achiev **easy** · status _likely_resolved_stale_ · score **39** · _walkback_

**Why it ranks here:** Consolidated b2/b6/b12/b14: a recurring class of caught-and-fixed overclaim-vs-delivered gaps. Phase 6a Wave 5 integrated a conflated primary source (sign-inverted regime criterion, severity-critical, logged qi-deep-research-analog-conflation). Phase 6z bb9aae0 shipped density but NOT the title-promised named SK headline (closed in a new leaf). Phase 7-F Stage-13 caught batchmode-hidden blank counts + a figure-eight knot 'in flight' prose drift contradicting a native_decide-closed theorem. Phase 6y/6x M-S 'PRs' were alias-only. All caught by review (the gate works when run fresh), mostly resolved. Easy verification, medium systemic impact (DR/first-pass reliability).

**Remediation:** Encode the lessons: DR formulas/sources for hard results must be verify-by-calculation/WebFetch before use (analog-conflation, mathematically-false DR shortcuts in 6AI); Stage-13 must check title-promise vs shipped-symbol and prose-vs-closed-status; non-batchmode LaTeX compile gate. Verify the re-shipped 6a Wave 5 regime_partition_criterion is internally consistent and the M_c ansatz is flagged project-original.

**Sources:** roadmap-b2 (6AG overclaim, 6z headline gaps), roadmap-b6 (6AI false DR shortcuts), roadmap-b12 (Phase7-F figure-eight, batchmode), roadmap-b14 (6a Wave 5 conflation, 6y M-S alias)

---

## Reconciled away as stale (historical, resolved on disk)

- **Phase 6n/6v/4/5a/5b/5h/6h/5j '1 project-local axiom' (gapped_interface_axiom / z16_classification / HasSpectralGap) live-axiom references** — counts.json (2026-06-10) reports axioms=0, axiom_names=[]. The single Phase-6n-era axiom gapped_interface_axiom was converted to the TPFConjecture tracked Prop (2026-05-19, SPTClassification.lean:16 'pre-2026-05-19 axiom'); z16_classification and HasSpectralGap likewise converted/discharged. The residual TPFConjecture tracked-Prop is kept as a LIVE item (ranks 6/29); only the LITERAL-AXIOM framing is dropped. Consolidated into rank 46 as a documentation-hygiene note rather than dropped entirely.
- **Phase 5i 17 project-wide sorry / Phase 5b 11 QNumber+Uqsl2 sorry / Phase 5d CenterFunctor 2 sorry / Phase 5e KLinear-Spherical-Fusion-VecG-DrinfeldDouble sorry stubs / Phase 5p CenterFunctor 2 sorry / Phase 5r native_decide-or-axiomatize freeness plan / Phase 6t Classical.choose conditional** — counts.json reports sorry_declarations=0, sorry_theorems=0 project-wide; all cited sorries were discharged (Aristotle runs documented, RingQuot divergence resolved structurally, Phase 6t Option C landed unconditional kernel-only). These were genuine open states at roadmap-authoring time but are resolved on disk. The Phase 5r native_decide/axiomatize freeness plan was BYPASSED (ChangeOfRings abstract proof, no SteenrodA1.lean) so never executed.
- **Phase 6p bridge_axiom_FKLW / sk_axiom_Dawson_Nielsen DR-only-authority axioms; aa_residual_interior_at_one_for_hom UNSOUND axiom** — counts.json axioms=0; both DR-authority axioms eliminated via Wave 2c/2d PR#17; the UNSOUND aa_residual axiom was caught by the R2 soundness audit (SO(d)⊂SU(d) counterexample) and DELETED (commit f44c60d). The process lesson (DR-recommendation-is-advisory-not-green-light; check density axioms against SO(d)/Sp(d) counterexamples) is the durable value but the axioms themselves are gone. The downstream tracked-predicate density gate (the real residual) is kept as rank 8.
- **Phase 6t SolovayKitaevQuantitativeContract conditional intermediate / Phase 6u cliffordT_v4_witness_tracked / Phase 6z headline-from-witness gap / Phase 6AJ reversible-only DP intermediate / Phase 6x' parametric Toffoli residual** — Each was a now-RESOLVED conditional/restricted intermediate: Phase 6t Option C shipped unconditional tight-ε kernel-only; Phase 6u Session 2 discharged the v4-witness unconditionally (Niven obstruction, lean_verify clean); Phase 6z closed the named SK headline in a leaf module (no native_decide); Phase 6AJ OUTCOME 3 shipped unconditional fidelity DP kernel-pure; Phase 6x' Phase-2 A-F discharged all three residuals. The full SolovayKitaevQuantitativeContract full-regime form is kept as rank 16 (literature-wall) since it remains undischargeable; only the resolved intermediates are dropped.
- **Phase 1c APS-eta memo-only / Phase 6o APSEta trivially-zero-vs-nonzero branch** — counts.json module list now includes SKEFTHawking.APSEta.{ADWHorizon,BECAcoustic,He3A}, indicating the Phase 6o follow-up that the Wave 1c memo flagged was executed; the modules are kernel-clean (no native_decide per deep-0 scan). The content-strength question (trivially-zero vs genuinely-new η per substrate) is a minor record-the-verdict item, not a structural weakness.

## Cross-cutting meta-observations

1. NATIVE_DECIDE GROUND TRUTH IS WRONG (deep-0, ranked #4): the audit input's '199 occurrences, concentrated in FKLW/RossSelinger + QuantumNetwork' is stale on BOTH count and location. Real distribution: 551 real tactic uses; anyon/MTC/braid 328, number-field 124, quantum-group 54, lattice/E8 20, physics-app 20. FKLW/RossSelinger=0 real uses (all 58 matches are 6AO-Track-3 ELIMINATION comments), QuantumNetwork=0 real uses (66 matches are 'no native_decide' kernel-purity attestations). An auditor trusting the stale premise inspects clean files and misses the 452 real uses in the anyon/number-field substrate where the trust gap actually lives. counts.json native_decide accounting should distinguish real tactic uses (551) from doc-mentions; the 26-vs-43 type-True placeholder count also needs reconciliation.

2. TRACKED-PROP LEDGER DRIFT IS SYSTEMIC (deep-1, ranked #2): PERMANENT_TRACKED_HYPOTHESES.md claims 'honest count: 7' but ~49 Prop-valued H_* defs exist and ≥11 are genuinely consumed as undischarged (h:H_X) hypotheses with NO anchor theorem, gating paper17/20/21/33/D5/I1 headlines. The ledger's own §Scope says it is 'the source of truth for the project's load-bearing tracked-Prop surface area', so the 2-3x undercount is a direct violation. The 4 documented pre-Phase-6r entries (VestigialModeIsGraviton, DESICompatibility, RT_Formula_Valid, TPFConjecture) were verified accurate at file:line — the problem is COVERAGE, not content accuracy.

3. CONDITIONAL-PRESENTED-AS-UNCONDITIONAL is the dominant headline-integrity risk and it appears at the STRUCTURE/DEFINITION level (a subtler form than a missing hypothesis): the 16∣σ topo struct field (#1), verlindeEntropy_SU2k:=saddle-limit (#13), entropic 8/8 rDIndependentNoGo:=constant-true (#9), Ext cols/8 proxy + h2_discharged:True (#25). These evade BOTH the type-True counter (the statement isn't literally True) AND the placeholder-marker detector (the body is decide/rfl not the flagged pattern). The Phase5qT T5 proxy-detector (flag decide/rfl bodies whose NAME claims a structural quantity like *_dim/*Ext*/rank) is the specific guard rail that would catch this class and is unbuilt.

4. ONE GENUINE PUBLISHED OVERCLAIM vs many honest hedges (deep-2): paper7 asserts the general-G gauge-emergence equivalence as formally verified inside its '4049-theorem end-to-end verification' sentence while the Lean is True stubs (#3) — but paper8/9/10/11 and the D5 \placeholdertheorems macro disclose their cobordism/equivalence placeholders honestly. The project's honesty discipline is mostly WORKING (the within-2σ band tautologies are gone, y_p_within_pdg_2sigma→physical-range; the _DEFINITIONAL re-exports are transparently named; QuantumNetwork Caves/Fortescue-Lo/W-state conjectures are explicit non-claims). The failures are localized regressions where a single-session close or a first-pass ship bypassed the standing checklist.

5. THE COMPLETION GATE IS GAMEABLE BY SCOPE-NARROWING (Phase 6v #12, Phase 6r-prime #11): a passed adversarial review certified work 30-90% short of intent; a single-session 'all 8 waves shipped' close shipped 10/12 tracked Props as P5 aliases/empty-Prop-class/literal-True. The recurring signal: 'reviewer GREEN is NOT the bar; acceptance criteria are', and single-session multi-wave closes are a red flag for under-strengthening. The mandatory fresh-context Stage-13 sweep catches these WHEN RUN — but Phase 7's final submission-gate sweep (#41) is unrun, so current bundle GREEN states predate the latest 6X re-flagging.

6. EFFORT-MAGNITUDE DESCOPE persists despite the 'no de-scope from effort' policy: Phase 6r-prime's >20k-LoC acceptance bar (#31) is literally an effort gate; H_DESICompatibility's ~50-person-hour 'Phase 6b.2 not currently active' parking (#17) and HaarPauliConstant's tracked-hypothesis routing despite Mathlib having the sphere-Haar machinery at pin (#35) are in-scope work deferred only for effort. The project's own N16 audit note says most 'Phase 7+' framings are tractable. Genuine literature walls (full MTC/APS/cobordism, Ross-Selinger prime-density, Caves CCR) must be cleanly separated from these effort-only parkings.

7. COVERAGE GAPS in the raw findings: the input was roadmap-heavy (b0-b13) plus 5 deep-dive lenses (deep-0 native_decide, deep-1 tracked-Props, deep-2 placeholder-True, deep-3 conditional-headlines, deep-4 triviality). The deep-dive lenses provided on-disk verification that corrected several roadmap claims (native_decide count, the 16∣σ topo gap, paper7 overclaim). No lens covered: (a) the figure/visualization layer (Plotly correctness, colorblind-accessibility), (b) the Rust RHMC extension correctness, (c) the provenance dashboard / PG+AGE graph integrity beyond Phase 5v's self-report, (d) test-suite mutation coverage. The δ_diss canary (#14) — a 9-order dimensional bug that hid because Invariant 4 was satisfied by a docstring reference not content-checking — strongly suggests the unaudited Python numerics layer harbors similar weakly-anchored formulas; the unbuilt Wave-21 lean_grounding_audit is the highest-value untested guard.

---

# APPENDIX — Hand-verification pass + systemic root cause (2026-06-13, primary-author direct read)

The user flagged that the programmatic layer (and subagents) may not have captured the full picture. I independently read the actual Lean/paper/script source behind the 7 highest-severity findings rather than trusting subagent framing. Verdict: **every mechanism the subagents reported is real, but the severity framing was overstated for the honestly-documented items — the Lean files hedge scrupulously in their docstrings; the failure is that the honesty is never propagated to the ledger, the counts, or the paper prose.** One finding (#3) is a genuine, submission-gating overclaim. My own bootstrap ground-truth (the "199 native_decide") was itself wrong — a naive `grep -rln` (files-with-string), corrected to ~460–620 real tactic uses on disk.

## Per-finding verified verdicts

| # | Subagent claim | Verified on disk | Verdict |
|---|---|---|---|
| **4** | native_decide 551 not 199, in anyon/MTC/number-field; FKLW/QN zero | Real tactic uses ≈460–620 (KacWaltonFusion 58, FibonacciSextet 40, IsingBraiding 25, FPDimension 23, WRT 22…); FKLW `by native_decide`=0, QuantumNetwork=0 (all matches are elimination/attestation comments). My "199" = `grep -rln` counting *files*. | **CONFIRMED** — subagent right, my bootstrap wrong |
| **3** | paper7 claims general-G `Z(Vec_G)≅Rep(D(G))` as formally verified; Lean is `True` stubs | `gauge_emergence_statement`/`half_braiding_gives_action`/`chirality_independent_of_G` = `True := trivial` (honestly marked "placeholder"). Z/2 instance genuinely proven (CenterEquivalenceZ2.lean real `≃` + fusion/braiding preservation). paper_draft.tex L306-310: "…the gauge emergence theorem $Z(\mathrm{Vec}_G)\cong\mathrm{Rep}(D(G))$. Together, these 4049 theorems… provide end-to-end formal verification." | **CONFIRMED — genuine overclaim.** Nuance: localized to a "broader project" boast paragraph, not paper7's central GS-vs-TPF result (which is sound, 54 thm/0 sorry). Ship-gating; fix = one-paragraph reprose + `_TODO` rename |
| **1** | 16∣σ "unconditional" only because topo factor 2∣σ/8 is an undischarged struct field; only 8∣σ truly proven | `SmoothSpinManifold4.topo : (2:ℤ)∣latticeSig form/8` IS a struct field (SpinRokhlinInterface.lean:62). 8∣σ is a genuine kernel-pure theorem (van der Blij via discharged HM+Θ classification — a real achievement). Docstring states outright: "the **only remaining tracked hypothesis is `topo`**… irreducibly topological." | **CONFIRMED mechanism, OVERSTATED framing.** Not "defining-the-conclusion deception" — `topo` is the correct smoothness obstruction (E8 form fails it, correctly), a *legitimate tracked hypothesis hidden in a struct field*. Real issues: (a) `topo` absent from ledger (→#2); (b) **irreducibly GEOMETRIC (Atiyah-Singer/Â-genus-even / geometric Guillou–Marin on a characteristic surface) — a PERMANENT residual, not a "hard but tractable" discharge**; (c) paper-prose risk. **⚠️ CORRECTION 2026-06-13: any proposal to discharge `topo` via a *lattice* Arf bridge (`σ/8 ≡ Arf(redQuad) mod 2`) is FALSE — `Arf(redQuad) ≡ 0` on all even unimodular lattices (E8 counterexample), so it yields only σ mod 8. See `RokhlinArfNoGo.lean`. Remediation is the disclosure pass, not a discharge.** |
| **9** | entropic 8/8 NO-GO rests on `rDIndependentNoGo` constant-true | `rDIndependentNoGo` hardcoded `=> true` ×8; aggregate `∀c, …=true := by cases c <;> rfl`. BUT per-candidate legs are MIXED: EGDE1/EGDE4 genuine `norm_num` falsifiers vs real σ/DESI thresholds (docstring: "substantive falsifier, not a within-own-band tautology"); EGDE2/EGDE3 honestly-labeled Bool-flag stipulations ("Encoded as a Boolean flag"). | **CONFIRMED aggregate is bookkeeping, OVERSTATED.** Headline strength = weakest leg (the Bool flags, which encode literature/modeling judgments not derivations). Real but moderate; not "hollow" |
| **13** | Phase-6e "axiom retirement" redefined `verlindeEntropy_SU2k :=` its saddle limit (proves \|x−x\|=0) | `def verlindeEntropy_SU2k A G_N := kaulMajumdarS A G_N 0`. Docstring: Wave 3 had `opaque` + axiom `gaussianSaddleAsymptotic`; Wave 6a.7 "retires the axiom by making the definition concrete via the saddle limit"; literal Verlinde-sum derivation tracked by `H_VerlindeKMLiteralSumDerivation`. | **CONFIRMED, OVERSTATED.** Legitimate modeling choice (define entropy = saddle model) + honest tracked Prop — NOT fake. Risk: axiom→definition+tracked-Prop **lowers the visible axiom count without lowering assumption load** (optics) + the Prop must be in the ledger (→#2) |
| **25** | `h2_discharged : True := trivial` + identity-wrapper Ext lemmas; cols/8 proxy | `theorem h2_discharged : True := trivial` (ChangeOfRings.lean:110) confirmed verbatim. | **CONFIRMED** |
| **14** | δ_diss 9-order dimensional bug hid because Invariant #4 was satisfied by docstring-reference not content; grounding audit unbuilt | `check_formulas_to_theorems` (validate.py:156, = Invariant #4) only verifies the theorem **name string exists** in the Lean tree + appears in the docstring — never parses the statement or proof. Mapping is **7 hardcoded pairs**; most of formulas.py is unchecked. `scripts/*grounding*` → none. | **CONFIRMED systemic mechanism** (bug itself appears since-addressed; the guard gap is live) |

## The systemic root cause (what the user asked for)

**The project's automation verifies SYNTACTIC PRESENCE, never SEMANTIC LOAD.** It answers "does a theorem with this name exist, and is the library free of `sorry`/`axiom`?" — it never answers "does the proof term perform the work the name claims?" Because the dev *process* is unusually honest in prose, the gap is invisible at the count layer (0 axioms, 0 sorry, 12,463 theorems all look perfect) while the real assumption surface goes unmeasured. Three verified blind spots:

1. **Name-presence ≠ content-grounding (Invariant #4 is hollow).** `check_formulas_to_theorems` matches theorem *names*, not statements. A `: True` stub or a dimensionally-wrong formula whose named theorem exists passes. The Wave-21 `lean_grounding_audit` that would close this is unbuilt; the existing check covers 7 hardcoded formulas.

2. **The weakness lives at the DEFINITION/AGGREGATION layer, which no counter inspects.** Substance is discharged into struct fields (`topo`), definitional identities (`verlindeEntropy_SU2k := saddle`), Bool registries (`rDIndependentNoGo := true`), and `: True` placeholders (`gauge_emergence_statement`, `h2_discharged`). The headline proof is then `rfl`/`decide`/`cases<;>rfl` — trivial because content was relocated. This evades the type-`True` counter (statement isn't literally `True`), the sorry/axiom counter, AND the native_decide lint. The Phase5qT-T5 "proxy-body detector" that would catch it is unbuilt.

3. **Honest accounting exists only in human-readable docstrings, never machine-enforced.** Every #1/#9/#13 hedges correctly *in its docstring* ("only remaining tracked hypothesis is topo"; "encoded as a Boolean flag"; "interprets at the Laplace-saddle limit… tracked by H_…"). But that honesty is (a) not swept into the tracked-hypothesis ledger → drift (#2: ~11+ consumed Props missing); (b) not cross-checked against paper prose → paper7 overclaim (#3) slips through; (c) not reflected in axiom-count optics → "axiom retirement" into definition+tracked-Prop lowers the visible count without lowering the assumption load.

## Remediation — five semantic validators the project lacks

- **R1 — Content-grounding audit (build Wave-21 `lean_grounding_audit`).** Every `formulas.py` entry's cited Lean theorem must have a *statement* that encodes the formula's actual relation (parse the Lean `theorem … : <stmt>`, assert the formula's symbols/relation appear), machine-checked, over ALL formulas not 7. Fixes the #14 class (the δ_diss canary).
- **R2 — Proxy-body detector (build Phase5qT-T5).** Flag any theorem whose *name* matches a structural-claim pattern (`*_dim|rank|*Ext*|*classification|*_no_go|sixteen_*|*equivalence|*_statement`) but whose *body* is `rfl|decide|cases…<;>rfl|<struct-field projection>|trivial`. Triage each: legitimate model vs hollow. Fixes the #1/#9/#13/#25 class.
- **R3 — Tracked-hypothesis auto-sweep.** Enumerate every `Prop`-valued assumption CONSUMED by a theorem — both `(h : SomeProp)` hypotheses AND assumed struct fields like `topo` — and assert each is registered in `PERMANENT_TRACKED_HYPOTHESES.md`; fail the build on drift. Fixes #2 (and surfaces `topo`, `H_VerlindeKMLiteralSumDerivation`).
- **R4 — native_decide accounting in counts.json.** Distinguish real tactic uses (~460–620) from doc-mentions, by cluster; track the number so a regression is visible. Fixes #4.
- **R5 — Prose↔Lean claim cross-check.** Scan paper `.tex` for "formally verified / end-to-end / machine-checked" claims naming a categorical result and assert the cited Lean is not a `: True`/stub. Fixes the #3 class before submission.

**Corrected severity tiering after verification:**
- **Ship-gating now:** #3 paper7 prose overclaim (a published draft says "formally verified" for a `True` stub).
- **Systemic + cheap + high-leverage:** build R1–R5; #2 ledger drift; #4 accounting.
- **Real but honestly-framed in Lean (risk is optics/prose/ledger, NOT soundness — do NOT re-prove the Mathlib-walled math):** #1 `topo`, #9 entropic aggregate, #13 verlinde retirement, #25 `h2_discharged`. Action = register in ledger + hedge paper prose, not re-derivation.
