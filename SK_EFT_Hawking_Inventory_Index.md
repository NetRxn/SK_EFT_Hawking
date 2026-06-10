# SK-EFT Hawking — Inventory Index

**Purpose.** LLM-friendly comprehensive index for the SK-EFT Hawking project. **This file is pointers only — no embedded content.** Every entry is `file path + one-line summary`. For full content read the pointed-to file. For comprehensive prose see `SK_EFT_Hawking_Inventory.md`. For live counts read `docs/counts.json`.

**Last synced:** 2026-06-10 (Phase 6AP COMPLETE — QuantumNetwork substrate completions, all 5 waves + W3b capstone, kernel-pure, 0 axiom / 0 sorry, full `lake build SKEFTHawking.ExtractDeps` green (9249 jobs), counts 12159 thm / 934 mod, `validate.py` ALL CHECKS PASSED. New: `QuantumNetwork/{KroneckerOpNorm, UnitaryDiamond, MatrixNormBridge, ErasureRateBound}.lean` + `FKLW/CompiledGateDiamond.lean` — W1 general rational exp-enclosure `expNeg_enclosure` (in `NumericalBounds`); W2 `l2_opNorm_kronecker_one_le` (ancilla register preserves L²-opnorm; Mathlib-upstream candidate); W3 the **AKN bound** `diamondDist_unitaryKraus_le : diamondDist Φ_U Φ_V ≤ ‖U−V‖_op` + trace-norm Hölder transfer from PhysLib (`traceNorm_eq_physlib` identification; subadditivity + both Hölder bounds) + the global-phase non-sharpness caveat AS a theorem (`diamondDist_unitary_smul_phase`); W3b row-sum→L²-opnorm bridge + the **END-TO-END compiled-gate diamond certificate** `diamondDist_cliffordTCompile_le` (compile U to ε ⟹ channel within `√2·ε` diamond, every link kernel-checked); W4 `erasureBound` formula + `erasureBound_le_plobBound` (two-layer posture mirroring PLOBRateBound); W5 RS-citation flags resolved via the 6AO primary-source verification (pointers added). Prior sync:) 2026-06-08 (Phase 6AN COMPLETE — all 5 waves, kernel-pure, 0 axiom / 0 sorry, full `lake build SKEFTHawking.ExtractDeps` green (9132 jobs), counts 11608 thm / 883 mod. New: `QuantumNetwork/{NetworkCapacity, ComposedGateFidelity, FDTNoiseFloor}.lean` (channel-composition diamond budget, multipath flow/cut weak-duality+path-bottleneck capacity, composed coherence⊕control gate-fidelity bound, FDT Johnson–Nyquist noise floor + LDP rare-event tail) + `FKLW/CliffordTCompiler.lean` (correct-by-construction Clifford+T gate compiler — named `cliffordTCompile` + loop invariant + termination + unconditional algorithm-level error+length correctness). Built on shared `main` alongside concurrent Phase 5q work. Prior sync:) 2026-06-02 (Phase 6AG FULLY COMPLETE — operational QN certification layer, all 4 asks DONE incl. the **LAST public fence now DOWN**: the general-qudit average-gate ↔ entanglement-fidelity identity `avgGateFidelity_eq : F_avg(Φ)=(d·F_e+1)/(d+1)` proven kernel-pure & UNCONDITIONAL via the constructive Gaussian→sphere route — bricks `QuantumNetwork/Gaussian{Moments,Wick,Polar,ComplexMoment,ComplexTensor}.lean` + `GateFidelity.lean` (`complexSphereTensor` = the degree-(2,2) unitary-2-design 2nd moment as a THEOREM, no Weingarten import; `sphere_braKet_normSq` contraction; `kraus_normSq_sum` CPTP collapse). counts regenerated `docs/counts.json` **790 mod/10393 thm/0 axiom/0 sorry**, kernel-pure; D6 §6(iv′)+preprint §3e updated. Prior sync below:) 2026-06-02 (Phase 6AF FULLY COMPLETE — public QI analytic frontier: trace-distance metric, Uhlmann fidelity, BOTH Fuchs–van de Graaf bounds, diamond-distance attainment, and the **Watrous Choi sandwich** `‖J‖₁/d ≤ ‖·‖_◇ ≤ d‖J‖∞` both one-sided bounds proven — `diamondDist_ge_maxEntangled` + `diamondDist_le_choi_opNorm` in `QuantumNetwork/DiamondNormChoi{,Upper}.lean`; counts regenerated `docs/counts.json` 778 mod/10237 thm/0 axiom/0 sorry, kernel-pure. Prior sync below:) 2026-05-31 (verified-quantum-compilation arc COMPLETE — Phases 6u→6x→6x′→6y→6z; counts from `docs/counts.json` regenerated 2026-05-30). Highlights: Phase 6z literal Clifford+CCZ no-`T` **dense in SU(8)** (`cliffordCCZLiteral_dense`, `bb9aae0`); Phase 6y **first kernel-verified Solovay-Kitaev at arbitrary SU(d)** (`solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight` + concrete-radius `matrixMercatorLog`); Phase 6x′ **unconditional Toffoli lower bound** `channelSde2_le_toffoliCost` + `cliffordOnly_not_dense` (Mukhopadhyay 2401.08950). Full build clean, **0 axioms, 0 sorries**, all headlines kernel-pure. Publication: corpus consolidated into new Tier-1 bundle **D8** (authorized 2026-05-31; `PAPER_STRATEGY.md` §2.2 — 17 bundle targets). **Sync source:** `docs/counts.json` (2026-05-30). NOTE: this index's per-family module map below predates several phases (last full reconcile 2026-05-26); `docs/counts.json` field `lean.module_names` is the canonical current module list (751 modules).

**Size discipline.** Target ~50–80 KB. Keep under 100 KB so future LLM bootstraps can read it in a single `Read` call (the harness truncates files >256 KB and may skip files much smaller than that). When this file approaches 100 KB, prune narrative — move it to `SK_EFT_Hawking_Inventory.md` or `temporary/working-docs/`. Do NOT inline session logs, wave-history, or per-commit detail; those belong in `temporary/working-docs/` or the prose inventory.

**Sibling docs (read on bootstrap):**
- `README.MD` — project framing (public-facing).
- `../CLAUDE.md` (workspace root) — agent guidance and conventions; project-level guidance for SK_EFT_Hawking lives here (there is no separate per-repo `CLAUDE.md`).
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage wave protocol and 15 pipeline invariants.
- `docs/PAPER_STRATEGY.md` — 17-bundle publication architecture (D8 added 2026-05-31).
- `docs/PERMANENT_TRACKED_HYPOTHESES.md` — load-bearing tracked Props.
- `docs/BUNDLE_READINESS_HEATMAP.md` — per-bundle Stage-13 readiness.
- `SK_EFT_Hawking_Inventory.md` — full prose inventory (the upstream this index summarizes).

---

## 1. One-page state snapshot

**Counts (from `docs/counts.json` regenerated 2026-06-08, post-Phase-6AN; also reflects concurrent Phase 5q work on shared `main`):**

| Metric | Value |
|---|---:|
| Lean theorems (total) | 11608 |
| Lean theorems (substantive) | 11582 |
| Lean theorems (placeholder `True := trivial`) | 26 |
| Lean modules | 883 |
| Lean definitions | 6988 |
| Lean axioms | **0** (project-local) |
| Lean sorries | **0** |
| Aristotle-proved theorems | 322 |
| Aristotle runs | 44 |
| Python source modules | 132 |
| Test files | 110 |
| Figures (PNG) | 162 |
| Notebooks | 89 |
| Papers (drafts) | 42 |
| Publication bundles (per PAPER_STRATEGY) | 17 |
| **Phase 6r SymTFT modules** | 18 (~2,650 LoC, originally shipped 2026-05-25 Session 1) |
| **Phase 6r-prime ADDITIONAL modules** | 20+ (Sessions 1–5 substantive substrate; M1–M5 + A1–A5 + B1–B12) |
| **Phase 6r/6r' total SymTFT+CrossBridges+APSEta-asymmetry LoC** | ~9,910 lines |

**Toolchain pins:**
- Lean: `leanprover/lean4:v4.29.1` (`lean/lean-toolchain`).
- Mathlib: rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (v4.29.1 tag, 2026-04-17) — `lean/lakefile.toml`.
- Lean REPL: tag `v4.29.0` (must match toolchain) — `lean/lakefile.toml`.
- Python: `>=3.14`, uv-managed (`pyproject.toml`).
- Rust: PyO3 abi3-forward-compat (`rust/`).

**Recent ships (newest first):**
- **2026-05-31 (Stakeholder + strategy doc sync; D8 bundle authorized)** — Verified-quantum-compilation arc (6u→6z) consolidated into new Tier-1 bundle **D8** "Kernel-Verified Universal Quantum Gate Compilation" (`PAPER_STRATEGY.md` §2.2; 16→17 targets). `PAPER_DRAFT_MAPPING.md` re-points 6p/6t from D4 §9.x into D8 + adds 6u/6v/6x/6x′/6y/6z rows. New consolidated stakeholder pair `docs/stakeholder/Phase6x-6z_VerifiedQuantumCompilation_{Implications,Strategic_Positioning}.md`. Inventory + companion-guide counts refreshed to 9944 thm / 751 modules. No Lean change. Next op step: `papers/D8/` skeleton + Stage-9/10/13 triple per `BUNDLE_LIFT_PROCEDURE.md`.
- **2026-05-30 (Phase 6x′ COMPLETE — Mukhopadhyay channel-rep, Stage-13 GREEN)** — `lean/SKEFTHawking/FKLW/Mukhopadhyay*.lean` family. Phase 1 capstone `cliffordOnly_not_dense` (`838d96ff`): ⟨H,S,CNOT⟩ finite (channel-rep → signed-permutation morphism) → NOT dense in SU(8), the 6z CCZ-essentiality converse. Phase 2 full discharge → UNCONDITIONAL `channelSde2_le_toffoliCost` (`T^of(U) ≥ sde₂(Û)`): `MukhopadhyayMatrixSde2` (sde2ℂ/matrixSde2/channelSde2) + Theorem 3.8 `channelRep_CCZ_isHalfInt` + Lemma 3.10 `channelRep_interp_isRat` (dyadic entries). Build **9944 thm / 0 axiom / 0 sorry / 751 modules**, kernel-pure, zero new native_decide, no maxHeartbeats. Full MITM minimality (Conj 4.8) permanently OUT.
- **2026-05-30 (Phase 6y COMPLETE — first kernel-verified SU(d) Solovay-Kitaev, Stage-13 GREEN)** — `lean/SKEFTHawking/FKLW/GenericSUd*.lean` + `TrappedIonSU4.lean` + `CliffordCCZSU8.lean` family. Generic headline `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight` (arbitrary d≥2). Existential-radius regime blocker ELIMINATED via concrete-radius matrix logarithm `matrixMercatorLog`/`exp_matrixMercatorLog` (Mathlib-PR-quality). Length-exponent corrected to honest `log 5/log(3/2)`, `SkLengthPolylogBound_sud_holds` discharged. Instances `trappedIonSU4_solovayKitaev_headline_unconditional` (SU(4) MS, Brylinski-Brylinski) + `cliffordCCZSU8_solovayKitaev_headline_unconditional` (SU(8) Clifford+T, CCZ over-complete). M-S Mathlib tracks alias-only. ~115 commits, kernel-pure.
- **2026-05-29 (Phase 6z COMPLETE — first T-free CCZ-essential SU(8) density, Stage-13 GREEN-no-findings)** — 10 new `lean/SKEFTHawking/FKLW/CliffordCCZSU8{GenLift,LineTransport,Transport,ConjClosure,PauliWords,KronK8Closure,Irreducible,OrbitWitness,OrbitProps,Density}.lean` + `CliffordCCZSU8LiteralHeadline.lean`. Literal ⟨H,S,CNOT,CCZ⟩ (no T) **dense in SU(8)**: `cliffordCCZLiteral_dense` + `cliffordCCZLiteral_H_of_G_eq_top` + `cliffordCCZLiteral_solovayKitaev_headline_unconditional` (`bb9aae0`). Mechanism: seed `CCZ·(H⊗H⊗H)` trace 1/√2∉𝒪 (infinite-order) + von-Neumann first flow + Clifford-conjugation irreducibility (`clifford_irreducible_spans`/`cliffOrbit_spans_su8`). Build 8926 jobs, kernel-pure; CCZ confirmed load-bearing.
- **2026-05-25 (Phase 6u COMPLETE — alphabet-agnostic SK substrate + Clifford+T UNCONDITIONAL)** — generic `GeneratingSet`-parametrized Solovay-Kitaev substrate (Waves 1–6 + Wave 4b) + Track T-S Clifford+T: `cliffordT_density_unconditional` (⟨H,T⟩ dense via Niven, `CliffordTInfiniteOrder.lean`) + headline `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional`. CP1+CP2 GREEN. ~3,900 LoC / 15+ modules. (Phase 6x Read-Rezayi k5/k7 + alphabet substrates + Mathlib M.1/M.2/M.4 tracks shipped 2026-05-26.)
- **2026-05-26 PM (Phase 6w Wave 6w.1 KZM-Unruh bridge foundation SHIPPED)** — New module `lean/SKEFTHawking/KibbleZurekUnruh.lean` (+1 module, +6 substantive theorems + 2 lemmas) encoding the Kibble-Zurek-Unruh correspondence. Headline `surface_gravity_bounds_kzm_exponent` combines (i) universal KZM scaling exponent `μ = νz/(1+νz) ∈ (0,1)` (substantively bounded via `kzmScalingExponent_pos` + `kzmScalingExponent_lt_one`), (ii) WKB modified-unitarity spectral budget `1 - δ_k > 0`, and (iii) surface-gravity positivity `κ > 0` (from `WKBConnection.ExactWKBParams`) into the load-bearing strict inequality `μ·κ·(1-δ_k) < κ·(1-δ_k)`. Companion lemmas: `hawking_occupation_strictly_below_alpha` (β² < α² under low dissipation, uses `b.unitarity` substantively); `kzm_defect_rate_strictly_below_horizon_rate` (bare form μ·κ < κ); `kzm_unruh_thermal_matches_hawking` (substantive `2π·T_H = κ` via `field_simp`, NOT rfl-trivial); `kzmScalingExponent_1d_tfim_eq_one_half` (Zurek 1996 ν=z=1 → μ=1/2 numerical witness). Primary source `TindallMelloFishmanStoudenmireSels2026Science392` (Science 392, 868 (2026), DOI 10.1126/science.adx2728, arXiv:2503.05693) cached at `Lit-Search/Phase-6w/primary-sources/` (3.8MB PDF + Crossref JSON + abstract.txt). Bundle citation passes: D1 §9.1 NEW subsection "Independent cross-check: Kibble-Zurek-Unruh universality"; E1 §6 paragraph; E2 §7 paragraph; all three papers LaTeX-compile clean with no undefined references. Build clean **8707 jobs** (+1 from 8706); zero new project-local axioms; zero sorries. Preemptive-strengthening 5-question audit applied; 2 P5 candidates eliminated proactively (deleted `kappaToInverseQuenchRate_pos`; strengthened `kzm_unruh_thermal_matches_hawking` to substantive `2π·T_H = κ`). `validate.py --check citation_primary_sources_present` PASS. Stage 13 adversarial review deferred to Wave 6w.7 consolidated Phase-6w sweep.
- **2026-05-26 (Round-3 adversarial-review remediation post Session 5)** — Two REQUIRED findings shipped from a fresh adversarial review pass: (R-1) `RP4_isPinPlusObstruction` rfl-by-design P5 anti-pattern remediated by shipping the substantive Karoubi 1968 §5 mod-2 binomial computation as three new theorems in `StiefelWhitney.lean`: `karoubi_RP4_w2_eq_zero_mod_2` (the bare `Nat.choose 5 2 % 2 = 0` arithmetic), `karoubi_RP4_w_values` (the full 5-coefficient table), `karoubi_RP4_instance_consistent` (the instance ↔ binomial-computation bridge); the substantive content is now visible at the Lean-theorem level rather than hidden in instance data. (R-2) `Phase6rPrimeClose.lean` conjunct #66 P2 redundancy remediated by replacing the prior 4-sub-conjunct algebra-data bundle (which exactly duplicated conjuncts #52/#53/#55/#56) with the substantive Karoubi binomial computation. Build clean **8693 jobs**; counts regen via `update_counts.py`: 445 modules / 7713 theorems / 0 axioms / 0 sorries / 5775 defs / 442 instances. Substantive content now visible at both file level + closure level.
- **2026-05-26 (Phase 6r-prime Session 5 close)** — Cross-iso `electric_squared_iso_vacuum` SUBSTANTIVELY SHIPPED in `lean/SKEFTHawking/SymTFT/A5VacuumPlusElectric.lean`. First object-level Z₂ fusion-rule lemma `e ⊗ e ≅ 𝟙` in `Center (VecG_Cat k G2)`. Half-braiding equality `electric_tensor_electric_β_hom_eq_vacuum` proven via 5-step chain: `Center.tensor_β` unfold → `signHalfBraiding` substitution → `whiskerLeft_comp`/`comp_whiskerRight` distribution → `congr 2` prefix → `sign_factors_cancel` helper (associator-inv-naturality + comp_whiskerRight + braiding_naturality_right + `signEndo_sq` + id_whiskerRight). `Phase6rPrimeClose.lean` closure extended **66 → 68 conjuncts**. Dual-phase 6r + 6r-prime Round 2 adversarial review GREEN: 0 BLOCKER + 0 REQUIRED + 3 ADVISORY (ADV-1 bundle-absorption pre-draft alignment [HELD for unified event]; ADV-2 optional consumer η-refactor; ADV-3 MonObj/ComonObj axiom-instance follow-on on `unitPlusElectricObj`, naturally Mathlib-PR-quality strengthening). Build clean **8693 jobs**. Zero sorries; zero new axioms; project axiom count UNCHANGED at 0. 2 legitimate tracked Props (KT 1990 + DMNO 2010). Files: `A5VacuumPlusElectric.lean` (+110 LoC), `Phase6rPrimeClose.lean` (+#67+#68), `temporary/working-docs/phase6r-prime/dual_phase_adversarial_review_round2.md` (new).
- **2026-05-25 (Phase 6r-prime Sessions 2–4 close)** — Substantive substrate ships across M3 Layer A/B (RP⁴ via antipodal Setoid quotient + CompactSpace + IsLocalHomeomorph + ChartedSpace + `IsManifold (𝓡 4) ω RP4` via chart-transition piecewise decomposition; 5 new modules `RP4.lean` / `RP4Smooth.lean` / `RP4LocalHomeomorph.lean` / `RP4ChartedSpace.lean` / `RP4IsManifold.lean`); A5(a-c) substrate (`VecGPreadditive.lean` / `CenterPreadditive.lean` / `CenterBiproducts.lean` / `CenterBiproductsHalfBraiding.lean`); A5(b)-pt2 full HalfBraiding instance `diagBiprodHalfBraiding` via `biprodTensor_hom_ext` Mathlib-PR-quality lemma + 7-step rewrite chain; A5(c-e) substrate ships #50–#66 (MonObj/ComonObj morphisms on `unitPlusElectricObj`, e²=𝟙 substrate via GradedObject convolution, `vacuum² ≅ vacuum` lift in Center C, `vacuum³ ≅ vacuum` cube); M4-narrow `StiefelWhitney.lean` (opaque CohomologyMod2 + HasStiefelWhitney typeclass + substantive `IsPinPlusObstruction RP4 := w 2 = 0` per Karoubi 1968 mod-2 binomial). Round 1 dual-phase adversarial review GREEN-with-3-REQUIRED-5-ADVISORY → Round 2 GREEN.
- **2026-05-25 (Phase 6r-prime Session 1 close)** — Phase 6r-prime substantive substrate CLOSED at GREEN-with-advisories. 11 of 12 Phase 6r tracked Props discharged or constructively derived (only #10 KEEPs as program-D-class identity). Ships: C3 + C2 + W1 (`PinPlusManifold4.lean`/`PinPlusBordism4.lean`/`PontryaginDualPinPlus.lean`/`AndersonDualSubstrate.lean`/`AndersonDualFunctor.lean` for M5) + W2 (`FrobeniusPerronDim.lean`/`LagrangianAlgebra.lean` substantive DMNO biconditional) + W3-minimal Path γ Kirby-Taylor generator-and-relations skeleton + W4 (`SubstrateEtaInvariant.lean` substantive Witten-Yonekura η via `ZMod.toAddCircle`) + C1 (`ToricCodeLagrangianAnyons.lean` substantive anyon-set classification). Post-audit honest tracked-Prop count: **2 (KT 1990 + DMNO 2010)**, down from 12 nominal via A1-A4 P5/P2 anti-pattern remediation.
- **2026-05-25 (Phase 6r SymTFT formalization SUBSTANTIVELY CLOSED)** — All 8 Waves shipped + strengthening + 2-round adversarial review GREEN in single autonomous-loop session. 18 new Lean modules under `lean/SKEFTHawking/SymTFT/` + `CrossBridges/SMMatterAsSymTFTBoundary.lean` + `APSEta/SubstrateBulkAsymmetry.lean` (~2,650 LoC; commit `a7ea1bf`). Primary anchor Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 *"Boundary SymTFT"*. 12 tracked Props introduced at predicate-substrate level (subsequently consolidated to 2 legitimate post-Phase-6r-prime audit). Citation corrections shipped: `2207.04050` → `2207.10700` (Davighi-Gripaios-Lohitsiri), `1610.07478` → `1610.07010` (Tachikawa-Yonekura), Pin⁺ bordism dimension correction (`Ω_4^{Pin⁺}≅ℤ/16` + `TP_5(Pin⁺)≅ℤ/16` per Kirby-Taylor 1990 + Freed-Hopkins arXiv:1604.06527; `Ω_5^{Pin⁺}=0`). Bundle absorption HELD for unified user-authorized event (2-of-4 GO conditions trip for D.3 absorption per `Wave 2b.3 + Wave 3b.2 + Wave 3b.3`).
- **2026-05-25** Phase 6q strengthening close + 3 substantive deferred-item lifts SHIPPED — §A 20-item resolution (5 deletions, 3 abbrev demotions, A.6 conjunct cleanup, A.3 substantive companion, A.4/A.7 docstring strengthening) + B.1 Python graphene MIR companion (substantive `(2·β_2/(4π))^(1/3) ≈ 0.0756`; the Lean substrate-level `1/2` placeholder is a safe upper bound) + B.2 reverse-direction LDP biconditional + B.3 BEC Bogoliubov substantive unbounded-norm proof (new module `BECBogoliubovBosonicGrowth.lean` with witnessed concrete `(2κ)!` sequence; both halves of bimodal outcome now witnessed by distinct concrete substrates). All headlines kernel-only; lake build 8638 jobs clean; pytest 4220 total / 4152 default-run / 68 slow-deselected, 0 failures; zero new axioms. See `docs/roadmaps/Phase6q_Roadmap.md` Sessions log Session 2.
- **2026-05-23 PM** Phase 6q DKM transport bootstrap SUBSTANTIVELY CLOSED — all 5 Waves shipped in single autonomous-loop session; 10 new Lean modules under `lean/SKEFTHawking/DKMBootstrap/` (~2,375 LoC Session 1; zero sorries, zero new axioms); bimodal outcome BOTH halves shipped substantively (positive uniqueness on graphene + sharpened NO-GO on super-factorial-unbounded substrates). Bundle placement BOTH L2 + D5. See `temporary/working-docs/phase6q/wave_2c_positioning.md` for full closing positioning.
- **2026-05-23** Phase 6t Path A Option C ship — `SkApproxCSuperQuadraticBound_holds` + unconditional tight-ε strict headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` in `lean/SKEFTHawking/FKLW/SolovayKitaevPathA.lean`. Kernel-only. See `temporary/working-docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`.
- **2026-05-23** D4 bundle closed at GREEN-with-advisories (Stage 9/10/13 round-2 cycle). 10/14 bundles GREEN. See `docs/BUNDLE_READINESS_HEATMAP.md`.
- **2026-05-22** Phase 5 Step 13 — `fibonacci_density_F21_unconditional` discharged kernel-only in `lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean`. See `temporary/working-docs/PHASE5_STEP13_COMPLETE.md`.
- **2026-05-19** Phase 5h Wave 2 — `axiom gapped_interface_axiom` retired into `TPFConjecture` tracked Prop; project axiom count 1 → 0.

**Build state (as of 2026-05-26 AM, post Phase 6r-prime Session 5 cross-iso ship):**
- `lake build SKEFTHawking` clean (**8693 jobs**).
- `uv run python -m pytest tests/` clean (carryover; no Python ships in Phase 6r-prime Sessions 2–5 beyond Phase 6q's Python ships).
- `uv run python scripts/validate.py` PASS verified at Phase 6r close (2026-05-25); revalidation pending refreshed `lean_deps.json` from `update_counts.py` (in flight at sync time).

---

## 2. Public-facing framing pointers

For the public narrative of what the project does, see `README.MD`. Key story arcs:
- **Analog Hawking radiation** — SK-EFT corrections to BEC / polariton / graphene-Dirac-fluid sonic horizons (Bundle D1).
- **Three generations from anomaly + modular invariance** — `c₋ = 8·N_f` and `24 | c₋` force `3 | N_f` (Bundle D2).
- **The "16 convergence"** — SM Weyl count, ℤ₁₆ classification, Rokhlin theorem, Kitaev DIII period all the same 16 (Bundle D2).
- **Chirality wall** — formal analysis of Thorngren-Preskill-Fidkowski's 5-of-9 evasion of Golterman-Shamir (Bundle D2).
- **Emergent gravity from microscopy** — ADW + tetrad gap equation + GW170817 vestigial-graviton falsification (Bundle D3).
- **Topological quantum computation** — Onsager → U_q(sl₂) → Hopf algebra → SU(2)_k → trefoil → Fibonacci universality (Bundle D4).
- **Dark sector under substrate constraints** — Gibbs-Duhem NO-GO for emergent dark energy; SFDM merger forecast; fracton DM viability (Bundle D5).
- **Formally verified statistical estimators + geometric quantum gate** — jackknife variance non-negativity + Fermi-Hubbard doublon SWAP.

---

## 3. Lean module map

**751 Lean modules** (per `docs/counts.json` regen 2026-05-30; the jump from the 445 at 2026-05-26 Phase 6r-prime close is the verified-quantum-compilation arc — `FKLW/GenericSUd*` ×104, `CliffordCCZSU8*` ×45, `TrappedIonSU4*` ×27, `ReadRezayiK5/K7*` ×16, `Mukhopadhyay*` ×13 — plus the `FaultTolerance/` D6 substrate and the Phase-6w tensor-network modules) under `lean/SKEFTHawking/`. Grouped by subdirectory or topical family. For full per-module theorem counts + key results, see `SK_EFT_Hawking_Inventory.md` Section 2. For the canonical module-name list, see `docs/counts.json` field `lean.module_names`.

### 3.1 Subdirectory families (sub-packages)

| Subdirectory | Purpose | Pointer |
|---|---|---|
| `lean/SKEFTHawking/FKLW/` | Freedman-Kitaev-Larsen-Wang density program **and the full verified-quantum-compilation arc (bundle D8)**: Fibonacci SU(2) density (Phase 6p/6t) + alphabet-agnostic SK substrate + Clifford+T (6u) + arbitrary-dimension SU(d) SK with `GenericSUdMatrixMercatorLog` (6y) + T-free CCZ-essential SU(8) `CliffordCCZSU8LiteralHeadline` (6z) + Mukhopadhyay Toffoli bounds (6x′) + Read-Rezayi alphabets + trapped-ion SU(4) (6x/6y). | `ls lean/SKEFTHawking/FKLW/` |
| `lean/SKEFTHawking/FaultTolerance/` | **Bundle D6 fault-tolerant-QC substrate** (Phase 6v): Williamson-Yoder gauging-QEC overhead, Shor ECC-256 T-counts, APM-LDPC hashing bound, W-state QFT, AGP threshold, plus the noise-model substrate. | `ls lean/SKEFTHawking/FaultTolerance/` |
| `lean/SKEFTHawking/CrooksAnalogHawking/` | Sakharov-horizon Crooks bridge; SK-EFT entropy current + Gallavotti-Cohen. | `ls lean/SKEFTHawking/CrooksAnalogHawking/` |
| `lean/SKEFTHawking/GloriosoLiu/` | Glorioso-Liu SK-EFT axiomatic skeleton + Onsager reciprocity + KMS. | `ls lean/SKEFTHawking/GloriosoLiu/` |
| `lean/SKEFTHawking/QuantumCrooks/` | Quantum Crooks no-go (Perarnau-Llobet) + Tasaki / Åberg / Kafri-Deffner / Kirkwood-Dirac variants. | `ls lean/SKEFTHawking/QuantumCrooks/` |
| `lean/SKEFTHawking/SymTFTAudit/` | SymTFT applicability audit + Drinfeld center + Witt-class + free k-linear / Deligne-tensor closure. | `ls lean/SKEFTHawking/SymTFTAudit/` |
| `lean/SKEFTHawking/LDP/` | Large-deviation framework (Cramér, Sanov, Varadhan, contraction). | `ls lean/SKEFTHawking/LDP/` |
| `lean/SKEFTHawking/Resurgence/` | SK-EFT resurgence + Borel summation + Stokes bound. | `ls lean/SKEFTHawking/Resurgence/` |
| `lean/SKEFTHawking/Itô/` | Stochastic calculus (Itô isometry / lemma / Novikov / quadratic variation / semimartingale). Phase 6o I3 target. | `ls lean/SKEFTHawking/Itô/` |
| `lean/SKEFTHawking/APSEta/` | Atiyah-Patodi-Singer η-invariant for analog horizons. | `ls lean/SKEFTHawking/APSEta/` |
| `lean/SKEFTHawking/Schellekens/` | Schellekens chain (anomaly polynomial, holomorphic VOA c=24, Niemeier lattice, spin bordism). | `ls lean/SKEFTHawking/Schellekens/` |
| `lean/SKEFTHawking/DoubleCopy/` | Gauge-theory ⇄ gravity scattering double-copy (BCJ, Petrov-D, single-copy, Weyl spinor). | `ls lean/SKEFTHawking/DoubleCopy/` |
| `lean/SKEFTHawking/SoftTheorems/` | Boostless / Carrollian cosmological soft theorems; dissipative no-go; noise-floor prediction. | `ls lean/SKEFTHawking/SoftTheorems/` |
| `lean/SKEFTHawking/ETH/` | Eigenstate thermalization hypothesis refutation on horizon-MTC substrate. | `ls lean/SKEFTHawking/ETH/` |
| `lean/SKEFTHawking/QCyc40/` | Q(ζ₄₀) cyclotomic-field substrate (Phase 6p T-gate compiler). | `ls lean/SKEFTHawking/QCyc40/` |
| `lean/SKEFTHawking/DKMBootstrap/` | Phase 6q DKM transport bootstrap on SK-EFT-Hawking horizon transport (Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255 specialization). **11 modules, 2,716 LoC** (Session 1: 10 modules, ~2,375 LoC, 2026-05-23; Session 2: BECBogoliubovBosonicGrowth.lean, 341 LoC, 2026-05-25 strengthening close); zero sorries, zero new axioms. Track 1 (Predicates/AxiomSet/KMSConsistency/NoCrossing/SDPStructure/LinearFunctionals/LDPBridge) builds DKM substrate + resolves three Phase 6o Wave 1c NO-GO obstructions; Track 2 (SKEFTSpecialization/E1E2CrossBridge/HorizonTransportBootstrap) specializes to 3 platforms (graphene/BEC/polariton) with bimodal outcome (positive uniqueness on graphene + sharpened NO-GO on super-factorial-unbounded). Wave 2b.4 module `BECBogoliubovBosonicGrowth.lean` lifts the sharpened-NO-GO half to a witnessed concrete substrate-level stand-in sequence `(2κ)!` (substantive Lieb-Robinson-for-bosons derivation deferred). Python numerical companion at `src/dkm_bootstrap/` ships substantive graphene MIR constant `(2·β_2/(4π))^(1/3) = 0.07562892800257...` (30 dps mpmath). | `ls lean/SKEFTHawking/DKMBootstrap/` |
| `lean/SKEFTHawking/SymTFT/` | **Phase 6r SymTFT formalization** (substrate-to-bulk unification under KOZ + FMT + Bhardwaj-Copetti-Pajer-Schäfer-Nameki *Boundary SymTFT* arXiv:2409.02166 framework) + **Phase 6r-prime substantive substrate discharge** (Sessions 1–5, 2026-05-25/26). **38 modules, ~9,910 LoC total across `SymTFT/` + `CrossBridges/SMMatterAsSymTFTBoundary.lean` + `APSEta/SubstrateBulkAsymmetry.lean`**; zero sorries; zero new axioms; **2 legitimate tracked Props** (KT 1990 Pin⁺ bordism cyclic-generation + DMNO 2010 Witt-trivial ⟺ Lagrangian-algebra biconditional, both meeting 3-criterion bar). **Module families:** (a) **Bulk SymTFT data** — `Basic.lean`, `BulkTQFT.lean`, `BulkInstances.lean`, `BulkBoundaryCorrespondence.lean`, `DrinfeldCenterAsBulk.lean`. (b) **Frobenius / Lagrangian-algebra substrate** — `FrobeniusAlgebra.lean`, `FrobeniusPerronDim.lean`, `LagrangianAlgebra.lean`, `GappedBoundary.lean`, `ToricCodeLagrangian.lean`, `ToricCodeLagrangianAnyons.lean`. (c) **Pin⁺ / Z₁₆ / Anderson-dual** — `PinBordism.lean`, `PinPlusManifold4.lean`, `PinPlusBordism4.lean`, `PontryaginDualPinPlus.lean`, `AndersonDualSubstrate.lean`, `AndersonDualFunctor.lean`, `StiefelWhitney.lean`, `SpinSymTFT.lean`, `SpinSymTFTSchellekensAlignment.lean`, `Z16ViaSpinSymTFT.lean`. (d) **RP⁴ + smooth structure (M3 layer)** — `RP4.lean`, `RP4Smooth.lean`, `RP4LocalHomeomorph.lean`, `RP4ChartedSpace.lean`, `RP4IsManifold.lean`. (e) **SM matter + dark sector boundary** — `IsSMMatterTopologicalBoundary.lean`, `AlternativeBoundaries.lean`, `SubstrateToBulkIdentification.lean`, `SubstrateEtaInvariant.lean`. (f) **A5 toric-code object-level (Drinfeld biproducts + Center C)** — `VecGPreadditive.lean`, `CenterPreadditive.lean`, `CenterBiproducts.lean`, `CenterBiproductsHalfBraiding.lean`, `A5VacuumMonObj.lean`, `A5VacuumPlusElectric.lean`, `A5LagrangianCenterUnit.lean`. (g) **Closure** — `Phase6rPrimeClose.lean` (68-conjunct consolidated substantive closure theorem; M-R adversarial-review reviewer anchor). Primary anchor: Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 (substantive boundary-SymTFT framework) + Kirby-Taylor 1990 (Pin⁺ Z₁₆) + Freed-Hopkins arXiv:1604.06527 (Anderson dual) + DMNO arXiv:1009.2117 (Witt-trivial ⟺ Lagrangian-algebra biconditional) + Karoubi 1968 §5 (RP⁴ mod-2 binomial Stiefel-Whitney values) + Davighi-Gripaios-Lohitsiri arXiv:2207.10700 (cited; non-Abelian-finite-group cobordism). | `ls lean/SKEFTHawking/SymTFT/` |
| `lean/SKEFTHawking/CrossBridges/` | Cross-bridge modules for Phase 6r SymTFT consumers. Currently 1 module: `SMMatterAsSymTFTBoundary.lean` (Wave 3a.3 substantive SM-matter-as-SymTFT-boundary biconditional with `IsBoundarySymTFTCorrespondence` + `witt_triviality_iff_has_lagrangian_algebra`; consumed by D2 + L2 bundle pre-drafts). | `ls lean/SKEFTHawking/CrossBridges/` |

### 3.2 Topical groupings (top-level `.lean` files)

For each topical area below, modules live directly under `lean/SKEFTHawking/`. Browse via `ls lean/SKEFTHawking/` and `grep "^theorem " lean/SKEFTHawking/<Module>.lean | wc -l` for counts.

- **Hawking pipeline core** — `AcousticMetric.lean`, `WKBAnalysis.lean`, `WKBConnection.lean`, `SKDoubling.lean`, `SecondOrderSK.lean`, `ThirdOrderSK.lean`, `HigherOrderSK.lean`, `CGLTransform.lean`, `HawkingUniversality.lean`, `StimulatedHawking.lean`.
- **Analog platforms** — `PolaritonTier1.lean`, `DiracFluidMetric.lean`, `DiracFluidSK.lean`, `DiracFluidWKB.lean`, `GrapheneHawking.lean`, `GrapheneNoiseFormula.lean`, `QuasiOneDReduction.lean`.
- **ADW emergent gravity** — `ADWMechanism.lean`, `TetradGapEquation.lean`, `TetradFormalism.lean`, `EinsteinCartanExtension.lean`, `LinearizedEFE.lean`, `NonlinearEFE.lean`, `FLRWDynamics.lean`, `EmergentGravityBounds.lean`, `GravitationalWaves.lean`, `EquivalencePrinciple.lean`, `HeatKernelExpansion.lean`, `HigherCurvatureStructure.lean`, `MicroscopicCoefficientMatch.lean`.
- **Classical-GR algebra (Phase 6f)** — `Curvature.lean`, `EinsteinTensor.lean`, `EnergyConditions.lean`, `ExactSolutions.lean`, `ADMFormalism.lean`, `LeviCivita.lean`, `LorentzianMetric.lean`, `LorentzianBundle.lean`, `RiemannianConnection.lean`, `RiemannCoordinate.lean`, `RiemannDifferentialBianchi.lean`, `BundleRiemann.lean`, `BundleRiemannAux.lean`.
- **Singularity / causal structure (Phase 6g)** — `CausalStructure.lean`, `NullGeodesic.lean`, `RaychaudhuriEquation.lean`, `FocalPoint.lean`, `PenroseSingularity.lean`, `PenroseSingularityCurveTheoretic.lean`, `HawkingPenroseSingularity.lean`, `HawkingPenroseSingularityCurveTheoretic.lean`, `AreaTheorem.lean`, `AreaTheoremCurveTheoretic.lean`, `CauchyProblem.lean`, `NoHairTheorem.lean`, `NonlinearDiffInvariance.lean`.
- **Black-hole thermodynamics** — `BHEntropyMicroscopic.lean`, `BHThermodynamicsFourLaws.lean`, `BHLGaugeEmbedding.lean`, `KerrSchild.lean`, `JacobsonThermoGRDarkEnergy.lean`, `RTReplicaTrickOnMTC.lean`, `RTCasiniHuertaBounds.lean`, `CasiniHuertaModularHamiltonianMTC.lean`, `QECHolographyBridge.lean`, `HolographicCFunctionMTC.lean`, `ScramblingTimeQuantitative.lean`.
- **Chirality wall / Z₁₆ / anomaly** — `ChiralityWall.lean`, `ChiralityWallMaster.lean`, `GoltermanShamir.lean`, `TPFEvasion.lean`, `TPFDisentangler.lean`, `SPTClassification.lean`, `SPTStacking.lean`, `Z16Classification.lean`, `Z16AnomalyComputation.lean`, `Z16AnomalyForcesThetaBar.lean`, `GenerationConstraint.lean`, `ModularInvarianceConstraint.lean`, `RokhlinBridge.lean`, `AlgebraicRokhlin.lean`, `ArfInvariant.lean`, `EvenLatticeForm.lean`, `LatticeSignature.lean`, `LatticeTheta.lean`, `SpinRokhlinInterface.lean`, `A1ExtSubstantive.lean`, `WangBridge.lean`, `SpinBordism.lean`, `SteenrodA1.lean`, `A1Ring.lean`, `A1Resolution.lean`, `A1Ext.lean`, `ChangeOfRings.lean`, `ExtBordismBridge.lean`, `SMFermionData.lean`, `SMGClassification.lean`, `KMatrixAnomaly.lean`, `VillainHamiltonian.lean`, `FKGappedInterface.lean`, `ModularityTheorem.lean`, `InstantonZeroModes.lean`, `Mat13K5Ext.lean`. **Phase 5q.B van der Blij / Route-C analytic spin-bordism leg (`16∣σ` unconditional drive):** `E8Signature.lean`, `LatticeSignatureCongr.lean`, `BlockSignature.lean`, `GeneratorNondeg.lean`, `LatticeSigBlock.lean`, `RokhlinClassification.lean`, `LatticePrimitive.lean`, `SplitHyperbolic.lean`, `VanDerBlijReduction.lean` (capstone: even-unimodular `8∣σ` reduced to [HM]+[Θ]), `ThetaModularity.lean` ([Θ] definite build), `HasseMinkowskiLocal.lean` (`finite_field_form_isotropic`, [HM-p] residue-field), `LatticeContent.lean` (`exists_primitive_isotropic_of_isotropic` + weakened-[HM] capstone), `MultivarPoisson.lean` ([Θ1] n-dim Poisson engine: origin-collapse + `integral_eq_tsum_zspan` + char-periodicity + Tonelli crux `cube_integral_char_periodisation` + descent foundation), `MultivarPoissonDescent.lean` (torus descent `F♯=torusDescent` of the periodisation through the open quotient covering map — the `C(UnitAddTorus (Fin d),ℂ)` for Fourier inversion).
- **Goltern-Shamir / lattice fermions** — `LatticeHamiltonian.lean`, `MajoranaKramers.lean`, `MajoranaRung.lean`, `MajoranaRungDecoupling.lean`, `MajoranaRungSMG.lean`, `BdGHamiltonian.lean`, `PauliMatrices.lean`, `WilsonMass.lean`, `GTCommutation.lean`, `GTWeylDoublet.lean`, `FermiPointTopology.lean`, `FermionBag4D.lean`, `GaugeFermionBag.lean`, `GaugeErasure.lean`, `GaugeEmergence.lean`, `GaugingStep.lean`, `QuarkRungMajoranaChannel.lean`, `QuarkRungScalarChannel.lean`, `ScalarRungInterpretation.lean`.
- **Topological QC — quantum groups + MTCs** — `Uqsl2.lean`, `Uqsl2Hopf.lean`, `Uqsl2Affine.lean`, `Uqsl2AffineHopf.lean`, `Uqsl3.lean`, `Uqsl3Hopf.lean`, `QuantumGroupGeneric.lean`, `QuantumGroupCoproduct.lean`, `QuantumGroupAntipode.lean`, `QuantumGroupHopf.lean`, `QuantumGroupInstantiation.lean`, `QuantumGroupMeta.lean`, `RestrictedUq.lean`, `RepUqFusion.lean`, `CoidealEmbedding.lean`, `OnsagerAlgebra.lean`, `OnsagerContraction.lean`, `KLinearCategory.lean`, `FusionCategory.lean`, `FusionExamples.lean`, `VecG.lean`, `VecGMonoidal.lean`, `KacWaltonFusion.lean`, `SphericalCategory.lean`, `RibbonCategory.lean`, `MugerCenter.lean`, `FPDimension.lean`, `D2Formula.lean`, `DrinfeldCenterBridge.lean`, `DrinfeldDouble.lean`, `DrinfeldDoubleAlgebra.lean`, `DrinfeldDoubleRing.lean`, `DrinfeldEquivalence.lean`, `CenterEquivalenceZ2.lean`, `CenterFunctor.lean`, `CenterFunctorZ2.lean`, `CenterFunctorZ2Equiv.lean`, `S3CenterAnyons.lean`, `ToricCodeCenter.lean`, `StringNet.lean`, `TQFTPartition.lean`, `TemperleyLieb.lean`, `JonesWenzl.lean`, `WRTInvariant.lean`, `WRTComputation.lean`, `SurgeryPresentation.lean`, `FigureEightKnot.lean`.
- **SU(2)_k / SU(3)_k / Ising / Fibonacci** — `SU2kFusion.lean`, `SU2kMTC.lean`, `SU2kSMatrix.lean`, `SU3kFusion.lean`, `SU3k2FSymbols.lean`, `SU3k2SMatrix.lean`, `IsingBraiding.lean`, `IsingGates.lean`, `FibonacciMTC.lean`, `FibonacciBraiding.lean`, `FibonacciQutrit.lean`, `FibonacciQutritUniversality.lean`, `FibonacciUniversality.lean`, `FibonacciQuintetTrueRep.lean`, `FibonacciQuintetUniversality.lean`, `FibonacciQuintetUniversalityExt.lean`, `FibonacciSextetTrueRep.lean`, `BraidGroup.lean`, `TgateFibBraid.lean`, `CNOTBraidTQSim.lean`, `GateCompilation.lean`, `ChiralSSB_QCD.lean`.
- **Number-field substrate** — `QNumber.lean`, `QSqrt2.lean`, `QSqrt3.lean`, `QSqrt5.lean`, `QCyc3.lean`, `QCyc5.lean`, `QCyc5Ext.lean`, `QCyc15.lean`, `QCyc15SqrtPhi.lean`, `QCyc16.lean`, `QCyc40Ext.lean`, `QCyc80.lean`, `QCyc80Ext.lean`, `QLevel3.lean`, `PolyQuotQ.lean`, `PolyQuotOver.lean`, `PolyQuotQCharacterisation.lean`, `E8Lattice.lean`, `MazurSigmaModelRigidity.lean`.
- **Fracton / vestigial / dark sector** — `FractonDarkMatter.lean`, `FractonFormulas.lean`, `FractonGravity.lean`, `FractonHydro.lean`, `FractonNonAbelian.lean`, `VestigialGravity.lean`, `VestigialEOS.lean`, `VestigialMapping.lean`, `VestigialSusceptibility.lean`, `VestigialInflationNoGo.lean`, `CondensedMatterAnalog.lean`, `GibbsDuhemTheorem.lean`, `QTheoryNoGoTheorem.lean`, `DarkEnergyObstructionPrinciple.lean`, `DESIComparison.lean`, `DarkSectorSynthesis.lean`, `DarkSectorClassificationExtension.lean`, `ClassificationTableDark.lean`, `HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`, `FangGuTorsionDM.lean`, `SFDMMergerForecast.lean`, `CausalSetDarkEnergy.lean`, `EntropicGravityDarkEnergy.lean`, `CosmologicalConstant.lean`, `CosmologicalPerturbations.lean`.
- **QCD strong-coupling + center-symmetry** — `CFLChiralLagrangian.lean`, `CenterSymmetryConfinement.lean`, `ChiralSSB_QCD.lean`, `CPPhaseSubstrate.lean`, `StrongCPTopologicalDE.lean`, `SubstrateAxion.lean`, `SubstrateInstantonSpectrum.lean`, `ThetaVacuumFiniteT.lean`, `EWPhaseTransition.lean`, `EWBaryogenesisChiralityWall.lean`, `LightQuarkHierarchyFallthrough.lean`, `CKMApexSubstrateConstraint.lean`, `NeutrinoMixing.lean`, `BBN.lean`.
- **Statistical estimators** — `VerifiedStatistics.lean`, `VerifiedJackknife.lean`.
- **Lattice / MC support** — `HubbardStratonovichRHMC.lean`, `WetterichNJL.lean`, `SU2PseudoReality.lean`, `SO4Weingarten.lean`, `QuaternionGauge.lean`, `WaveEquation1D.lean`.
- **Fermi-Hubbard** — `FermiHubbardDimer.lean`.
- **Classical-simulability / tensor-network demarcation (Phase 6w, bundle D7)** — `KibbleZurekUnruh.lean` (KZM-Unruh bridge), `BeliefPropagation.lean`, `BPLDPSimulability.lean`, `ChebyshevTN.lean`, `AperiodicLattice.lean`, `ChernBridge.lean`, `AnalogHawkingDemarcation.lean`.
- **Infrastructure / utilities** — `Basic.lean`, `ArrayHelpers.lean`, `ExtractDeps.lean` (environment walker), `BundleRiemannAux.lean`, `RiccatiComparison.lean`, `LaplaceMethod.lean`, `MatrixBCH.lean`, `MatrixBCHCubic.lean`, `MatrixTaylor.lean`, `FermiHubbardDimer.lean`, `RouabahExplicit.lean`.

For a fully alphabetized list, see `docs/counts.json` field `lean.module_names` (378 entries).

---

## 4. Headline theorem index

Load-bearing top-level theorems. Each row: fully-qualified name + module path + one-line statement. For the full theorem list, use `grep "^theorem " lean/SKEFTHawking/<Module>.lean` per module, or the upstream `extract_lean_deps.py` outputs in `lean/lean_deps.json`.

### 4.1 Solovay-Kitaev / FKLW topological-QC density (Phase 5–7)

| Theorem | Module | One-line |
|---|---|---|
| `fibonacci_density_F21_unconditional` | `FKLW/SU2BCHBracketClosure.lean` | F.21 Fibonacci density in SU(3)_2 ↪ SU(2) — kernel-only, zero tracked Props (2026-05-22). |
| `SkApproxCSuperQuadraticBound_holds` | `FKLW/SolovayKitaevPathA.lean` (line 1716) | Unconditional super-quadratic convergence of the Dawson-Nielsen compiler at K_compose = 1024 (2026-05-23). |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` | `FKLW/SolovayKitaevPathA.lean` (line 2523) | Unconditional Path A strict headline for ε ∈ (0, ε₀] bundling error + length (2026-05-23). |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci` | `FKLW/SolovayKitaevQuantitative.lean` | First kernel-verified quantitative Solovay-Kitaev length bound (conditional on `SolovayKitaevQuantitativeContract`). |
| `bridge_FKLW_unitary_hom` | `FKLW/AharonovAradBridgeIteration.lean` | Aharonov-Arad bridge from accumulation-at-1 to closure-equals-univ. |
| `H_Fib_v4_witness_unconditional` | `FKLW/OneParameterSubgroupSU2.lean` | Unconditional v4 anchor for Phase 5 Step 13. |

### 4.1b Verified universal quantum compilation (Phase 6u–6z, bundle D8)

| Theorem | Module | One-line |
|---|---|---|
| `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional` | `FKLW/CliffordT*.lean` | UNCONDITIONAL Clifford+T quantitative SK; first machine-verified ⟨H,T⟩ density in SU(2) (Niven). Phase 6u. |
| `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight` | `FKLW/GenericSUdSkHeadlineCascadeConcrete.lean` | First kernel-verified Solovay-Kitaev at **arbitrary dimension SU(d)**. Phase 6y. |
| `matrixMercatorLog` / `exp_matrixMercatorLog` | `FKLW/GenericSUdMatrixMercatorLog.lean` | Concrete-radius matrix logarithm (named convergence radius) — removes the existential blocker; Mathlib-PR candidate. Phase 6y. |
| `cliffordCCZLiteral_dense` | `FKLW/CliffordCCZSU8LiteralHeadline.lean` | First **T-free, CCZ-essential** density in SU(8): literal ⟨H,S,CNOT,CCZ⟩ dense, no T gate. Phase 6z. |
| `cliffordOnly_not_dense` | `FKLW/MukhopadhyayCliffordNotDense.lean` | Clifford-alone generates a finite group ⟹ CCZ essential (converse of 6z). Phase 6x′. |
| `channelSde2_le_toffoliCost` | `FKLW/MukhopadhyayToffoliUnconditional.lean` | First **unconditional** machine-checked Toffoli-count lower bound `T^of(U) ≥ sde₂(Û)` (Mukhopadhyay 2024). Phase 6x′. |
| Read-Rezayi `SU(2)_5` / `SU(2)_7` headlines | `FKLW/ReadRezayiK5ClosureDenseWitness.lean`, `ReadRezayiK7ClosureDenseWitness.lean` | Unconditional SK headlines for two more universal anyon alphabets. Phase 6x. |
| `trappedIonSU4_solovayKitaev_headline_unconditional` | `FKLW/TrappedIonSU4FullHeadlineForm.lean` | SU(4) Mølmer-Sørensen instance of the SU(d) headline. Phase 6y. |

### 4.1c Fault-tolerant QC + classical-simulability (Phase 6v / 6w, bundles D6 / D7)

| Theorem | Module | One-line |
|---|---|---|
| Williamson-Yoder overhead + `quadraticOverhead_not_linear` | `FaultTolerance/GaugingQEC.lean` | `W·polylog(W)` gauging-QEC auxiliary-qubit count; polylog factor provably unavoidable (class-separation). |
| Shor ECC-256 T-count bound | `FaultTolerance/ShorTGateCount.lean` | 630M / 490M T-gates (1200 / 1450-qubit configs), inside the 1-gigagate envelope. First kernel-verified end-to-end. |
| APM-LDPC hashing-bound predicate | `FaultTolerance/APMLdpcHashingBound.lean` | `[[1152,580]]` rate > 1/2 vs rate-exactly-1/2 falsifier class; hashing bound non-vacuously witnessed. |
| `analog_hawking_quantum_advantage_demarcation` | `AnalogHawkingDemarcation.lean` | Classical-simulability ↔ quantum-advantage demarcation (belief-propagation + categorical-Chern bridge). |
| `surface_gravity_bounds_kzm_exponent` | `KibbleZurekUnruh.lean` | KZM-Unruh bridge: SK-EFT surface gravity κ bounds the universal KZM exponent (D-Wave-measurable). |

### 4.2 Standard-Model anomaly / chirality / Z₁₆

| Theorem | Module | One-line |
|---|---|---|
| `generation_constraint_iff` | `GenerationConstraint.lean` | 3 ∣ N_f ↔ 24 ∣ 8·N_f (three generations from anomaly + modular invariance). |
| `c_minus_eight_N_f` | `WangBridge.lean` | c₋ = 8·N_f from SM Weyl fermion content. |
| `modular_invariance_24` | `ModularInvarianceConstraint.lean` | Framing anomaly 24 ∣ c₋ ↔ phase = 1. |
| `tpf_outside_gs_scope_main` | `TPFEvasion.lean` | Master TPF-evasion theorem: 5-of-9 Golterman-Shamir conditions violated. |
| `anomaly_free_implies_chiral_gauge` | `SPTClassification.lean` | Anomaly-free ⟹ chiral-gauge (consumes `TPFConjecture` tracked Prop). |
| `rokhlin_sixteen` | `RokhlinBridge.lean` | The "16 convergence" — SM Weyl / ℤ₁₆ / Rokhlin / Kitaev DIII all the same 16. |

### 4.3 Quantum groups / MTCs / TQFT

| Theorem | Module | One-line |
|---|---|---|
| `Uqsl2` (HopfAlgebra instance) | `Uqsl2Hopf.lean` | First Hopf-algebra instance on a quantum group in any proof assistant (66 thms, 0 sorry). |
| `Uqsl3` (HopfAlgebra instance) | `Uqsl3Hopf.lean` | First rank-2 quantum-group Hopf algebra in any proof assistant (189 thms, 0 sorry). |
| `QuantumGroup k A` (HopfAlgebra instance) | `QuantumGroupHopf.lean` | First generic parameterized U_q(𝔤) HopfAlgebra in any proof assistant. |
| `kacWaltonFusion` | `KacWaltonFusion.lean` | First Kac-Walton fusion algorithm in any proof assistant (SU(5)₁ Z₅, SU(2)/SU(3)/SU(4)/G₂/B₂ verified). |
| `trefoil_eq_neg_one` | `IsingBraiding.lean` | Trefoil knot Jones polynomial = -1 — first machine-verified knot invariant. |
| `fibonacci_universality` | `FibonacciUniversality.lean` | Fibonacci braiding generates SU(2)_3 image dense in SU(2) (Lie-algebra spanning). |
| `wrt_S3` / `wrt_S2_S1` / `wrt_figure_eight_complement` | `WRTComputation.lean` | First WRT TQFT invariants of canonical 3-manifolds in any proof assistant. |
| `wittEquivalentMTC_braided_implies_wittClass_eq` | `SymTFTAudit/DrinfeldCenter.lean` | Davydov-Müger-Nikshych-Ostrik 2010 braided-Witt equivalence ⟹ integer-mod-24 Witt-class equality. |
| `stage5_11_pseudoUnitary_closure` | `SymTFTAudit/PseudoUnitary.lean` | DMNO 2010 Theorem 5.2 pseudo-unitary subclass discharge. |

### 4.4 Gravity / black holes / cosmology

| Theorem | Module | One-line |
|---|---|---|
| `G_N_emerg_eq_alpha_ADW_times_Sakharov` | `LinearizedEFE.lean` | Emergent Newton constant `G_N^emerg = α_ADW · 12π / (N_f · Λ²)` from ADW microscopic theory. |
| `c_GW_equals_c_iff_chi_vest_eq_one` | `GravitationalWaves.lean` | GW170817 falsifies the vestigial-second-sound graviton identification by 7×10¹⁴ (under `H_VestigialModeIsGraviton`). |
| `BHEntropy_eq_area_minus_three_halves_log` | `BHEntropyMicroscopic.lean` | `S = A/(4G_N) − (3/2)log(A/(4G_N))` with Kaul-Majumdar SU(2)_k decomposition. |
| `four_laws_consistent_with_adw_bhs_cool_toward_extremality` | `BHThermodynamicsFourLaws.lean` | BCH four laws partitioned by regime at `M_c = (N_f · Λ_UV) / (12π · α_ADW)`. |
| `penrose_singularity_curve_theoretic` | `PenroseSingularityCurveTheoretic.lean` | Curve-theoretic Penrose composition theorem. |
| `raychaudhuri_focusing_ineq_under_NEC` | `RaychaudhuriEquation.lean` | Raychaudhuri focusing inequality `dθ/dλ ≤ -θ²/(n−1)` under NEC. |
| `hubbleSquared_ADW_pos` | `FLRWDynamics.lean` | ADW emergent-gravity Friedmann positivity. |
| `vestigial_w_eq_one_minus_tau_sq_over_5tau_sq_minus_one` | `VestigialEOS.lean` | First closed-form vestigial-gravity EOS `w_vest(τ) = (1−τ²)/(5τ²−1)`. |
| `gibbs_duhem_locks_w_vac_eq_neg_one` | `GibbsDuhemTheorem.lean` | First machine-checked emergent-vacuum obstruction (any single-scalar self-tuning ⟹ w_vac ≡ -1). |
| `q_theory_no_go_main` | `QTheoryNoGoTheorem.lean` | Klinkhamer-Volovik q-theory NO-GO across all 4 realizations. |

### 4.4a SymTFT formalization (Phase 6r + Phase 6r-prime)

| Theorem | Module | One-line |
|---|---|---|
| `phase_6r_prime_substantive_closure` | `SymTFT/Phase6rPrimeClose.lean` | **68-conjunct consolidated substantive-content closure** bundling all post-audit-remediation Phase 6r/6r' content. Single anchor for the M-R dual-phase adversarial-review reviewer. |
| `IsKirbyTaylorPinPlusBordism` (tracked Prop) | `SymTFT/PinBordism.lean` | Pin⁺ bordism group at dimension 4 is isomorphic to ℤ/16 (Kirby-Taylor 1990). Substrate-discharged via W1.2 Quotient construction `Omega4PinPlusBordism ≃+ ZMod 16`; full geometric ISO discharge requires Stiefel-Whitney + Pin group reductions absent in Mathlib. |
| `omega4PinPlusBordismEquivZMod16` | `SymTFT/PinPlusBordism4.lean` | **Substantive `AddEquiv`**: the Setoid-quotient `Omega4PinPlusBordism` is `≃+` to `ZMod 16` (W1.2 substrate; consumed by `IsKirbyTaylorPinPlusBordism` substrate-discharge). |
| `IsAndersonDualPinPlus` | `SymTFT/PinBordism.lean` | TP_5(Pin⁺) ≅ ℤ/16 via Anderson-dual (Freed-Hopkins arXiv:1604.06527). Post-A1 substantive Pontryagin discharge: `TP5PinPlus := AddChar (ZMod 16) Circle`; iso via Mathlib `circleEquivComplex` + `zmodAddEquiv.symm`. |
| `IsDMNOBiconditional` (tracked Prop) | `SymTFT/LagrangianAlgebra.lean` | DMNO 2010 main theorem: `Is3DTQFTBraided B ↔ HasLagrangianAlgebra B` carried at predicate-body level. Forward direction (Witt-trivial → has-Lagrangian-algebra) requires MTC typeclass + Lagrangian-algebra construction infrastructure absent in Mathlib. |
| `IsPinPlusObstruction RP4` | `SymTFT/StiefelWhitney.lean` | M4-narrow substantive Pin⁺ obstruction: `w 2 = 0` on RP⁴ (Karoubi 1968 §5 mod-2 binomial computation; **corrected** from prior docstring bug `w_2 = w_1²` which was the Pin⁻ obstruction). Pin⁻ falsifier `RP4_not_isPinMinusObstruction` ships substantively. |
| `karoubi_RP4_w2_eq_zero_mod_2` / `karoubi_RP4_w_values` / `karoubi_RP4_instance_consistent` | `SymTFT/StiefelWhitney.lean` | **Round-3 remediation 2026-05-26**: substantive Karoubi 1968 §5 mod-2 binomial computation `Nat.choose 5 2 % 2 = 0` + full 5-coefficient table `(1, 1, 0, 0, 1)` + instance-bridge lemma. Decide-proved primary-source content underlying the `HasStiefelWhitney RP4` instance encoding; addresses R-1 P5 anti-pattern by making the Karoubi substantive content visible at the Lean-theorem level (was previously hidden in the instance data). |
| `RP4.instIsManifold` | `SymTFT/RP4IsManifold.lean` | M3 Layer B-4d substantive `IsManifold (𝓡 4) ω RP4` instance via chart-transition piecewise decomposition (id-piece via sphere chart-transition + `.congr`; neg-piece via `contMDiff_neg_sphere` + chart-conjugate; union via `ContDiffOn.union_of_isOpen`). |
| `IZOmega_PinPlus_5 ≃+ TP5PinPlus` | `SymTFT/AndersonDualFunctor.lean` | M5 generic Anderson-dual functor recovers TP_5(Pin⁺) substantively (composes W1.2 substantive `omega4PinPlusBordismEquivZMod16` + AddChar precomposition functoriality; NOT P5 refl). |
| `electric_squared_iso_vacuum` | `SymTFT/A5VacuumPlusElectric.lean` | **Session 5 ship (2026-05-26)**: first object-level Z₂ fusion-rule iso `e ⊗ e ≅ 𝟙` in `Center (VecG_Cat k G2)`. Closes long-standing A5(c) cross-iso gap. |
| `electric_tensor_electric_β_hom_eq_vacuum` | `SymTFT/A5VacuumPlusElectric.lean` | Load-bearing categorical-coherence identity underlying `electric_squared_iso_vacuum`: 5-step proof via `Center.tensor_β` unfold → `signHalfBraiding` substitution → whiskering distribution → `signEndo_sq` cancellation via helper `sign_factors_cancel`. |
| `diagBiprodHalfBraiding` | `SymTFT/CenterBiproductsHalfBraiding.lean` | A5(b)-pt2 full `HalfBraiding` instance on the diagonal biproduct, monoidal + naturality axioms discharged via per-summand `biprodTensor_hom_ext` Mathlib-PR-quality lemma + 7-step rewrite chain. |
| `vacuum_tensor_vacuum_iso` | `SymTFT/A5VacuumPlusElectric.lean` | A5(c) Center C lift: `vacuumAnyon ⊗ vacuumAnyon ≅ vacuumAnyon` (substantive idempotency of the Z₂-MTC vacuum). |
| `IsToricCodeTwoLagrangianAlgebraStructure` | `SymTFT/ToricCodeLagrangian.lean` | Substantively discharged via C1 anyon-set classification (`ToricCodeLagrangianAnyons.lean`): exactly two Lagrangian anyon sets up to equivalence (electric `{1, e}` + magnetic `{1, m}`); third candidate `{1, f}` falsified by braiding-non-triviality. **First substantively-formalized two-Lagrangian-algebra classification for toric code MTC** at anyon-set level. |
| `IsDarkSectorTopologicalBoundary` | `SymTFT/AlternativeBoundaries.lean` | Substantively discharged post-A3 via hidden-sector witness conjunct `∃ hidden_charge ≠ 0, s.z16_class = (-3) + hidden_charge`; cross-bridge to Phase 5x `HiddenSectorClassification.three_singlets_satisfy_hidden_sector`. |
| `substrateEtaInvariant` | `SymTFT/SubstrateEtaInvariant.lean` | Substantive Witten-Yonekura η-invariant via `ZMod.toAddCircle s.z16_class` (composition of substantive Mathlib character-theory functions); biconditional `η = 0 ↔ z16 = 0`. |
| `sm_matter_as_symtft_boundary_closure` | `CrossBridges/SMMatterAsSymTFTBoundary.lean` | Wave 3a.3 substantive cross-bridge: SM 3-generation matter content as topological-boundary data on Drinfeld-center bulk via `generation_constraint_iff` recovery. |
| `wave_3b_1_substrate_to_bulk_identification` | `SymTFT/SubstrateToBulkIdentification.lean` | Wave 3b.1 program-D-class substrate-to-bulk identification: BEC/ADW/³He-A all Z₁₆-trivial-lift; `IsSKEFTHawkingSymTFTBoundary` substantive definition reclassified from tracked Prop (A4). |

### 4.4b DKM transport bootstrap on SK-EFT-Hawking (Phase 6q)

| Theorem | Module | One-line |
|---|---|---|
| `kms_replaces_unitarity_thm` | `DKMBootstrap/KMSConsistency.lean` | Substantive resolution of Phase 6o Wave 1c Obstruction (I): CGL `hasReflectionPositivity` + `hasDynamicalKMS_algebraic` produces CHHK F4 positivity at 2-pt-function level. |
| `vertical_bootstrap_bypasses_crossing` | `DKMBootstrap/NoCrossing.lean` | Substantive resolution of Phase 6o Wave 1c Obstruction (II): vertical bootstrap + F4/F5/F6 ⇒ full CHHK axiom set without any crossing identity. |
| `dkm_axiom_set_iff_vertical_plus_f4f5f6` | `DKMBootstrap/NoCrossing.lean` | Equivalence: `IsDKMAxiomSet ↔ IsVerticalBootstrap ∧ F4 ∧ F5 ∧ F6`. |
| `dkm_rate_function_is_LDPRateFunction` | `DKMBootstrap/LDPBridge.lean` | **Highest-leverage cross-bridge of Phase 6q**: Phase 6n abstract `IsLDPRateFunction` class instantiated on Phase 6q DKM substrate via FDT-pinned variance `σ²:=χ·D`. |
| `chhk_F4_existence_iff_LDP_rate_function_holds` | `DKMBootstrap/LDPBridge.lean` | Substrate-level biconditional closure of the Wave 2a.1 DR §6 cross-bridge (Wave 2b.2 substantive lift 2026-05-25). |
| `horizon_transport_uniqueness_graphene_witness_one_half` | `DKMBootstrap/HorizonTransportBootstrap.lean` | **Positive uniqueness half of Phase 6q bimodal outcome** — graphene Dirac fluid substrate's collective mean free path bounded below by `mirConst = 1/2` (substantive constant `(2·β_2/(4π))^(1/3) ≈ 0.0756` ships Python-side in `src/dkm_bootstrap/graphene_mir.py`; the Lean `1/2` placeholder is a safe upper bound). |
| `sharpened_no_go_super_factorial` | `DKMBootstrap/HorizonTransportBootstrap.lean` | **Sharpened NO-GO half of Phase 6q bimodal outcome** — CHHK bootstrap inapplicable to super-factorial-unbounded commutator-norm substrates (BEC Bogoliubov case via Yin-Lucas/Kuwahara-Saito Lieb-Robinson-for-bosons). |
| `becBogoliubovCommutatorNorm_isSuperFactorialUnbounded` | `DKMBootstrap/BECBogoliubovBosonicGrowth.lean` | **Wave 2b.4 substantive lift (2026-05-25)** — concrete BEC Bogoliubov-bosonic commutator-norm sequence `(2κ)!` substantively instantiates the `IsSuperFactorialUnbounded` predicate, witnessing the sharpened-NO-GO half at concrete-substrate-instance level. |
| `bec_falls_under_sharpened_no_go` | `DKMBootstrap/BECBogoliubovBosonicGrowth.lean` | Wave 2b.4 cross-bridge: BEC platform fails CHHK F3 operator-growth axiom for any positive microscopic constants. |
| `platform_kms_qualities_pairwise_distinct` | `DKMBootstrap/E1E2CrossBridge.lean` | Classifier-level distinctness: graphene (Strong) / BEC (Approximate) / polariton (EffectiveOnly) KMS-quality classifications are pairwise-distinct. Substantive companion: `bec_distinguishes_from_graphene_super_factorial` in `BECBogoliubovBosonicGrowth.lean`. |
| `f2_orthogonal_to_skeft_axioms`, `f3_orthogonal_to_skeft_axioms` | `DKMBootstrap/AxiomSet.lean` | Substantive structural finding: CHHK F2 (f-sum rule) and F3 (operator-growth) microscopic axioms are NOT implied by CGL `SKEFTAxioms` — they carry genuinely new microscopic-lattice content. |

### 4.5 Hawking pipeline / SK-EFT

| Theorem | Module | One-line |
|---|---|---|
| `count_N_eq_floor_plus_one` | `SecondOrderSK.lean` | Transport-coefficient counting `count(N) = ⌊(N+1)/2⌋ + 1`. |
| `parity_alternation_general_N` | `ThirdOrderSK.lean` | Parity alternation theorem for SK-EFT gradient expansion. |
| `wkb_connection_unitarity_broken` | `WKBConnection.lean` | Exact WKB through complex turning point — modified unitarity. |
| `hawking_universality_main` | `HawkingUniversality.lean` | Hawking universality theorem (BEC/polariton/graphene). |
| `dispersion_within_ligo_iff` | `GravitationalWaves.lean` | SK-EFT dispersion biconditional vs LIGO. |
| `dirac_fluid_block_diagonal` | `DiracFluidMetric.lean` | 3×3 graphene Dirac-fluid acoustic metric block-diagonalizes for quasi-1D (92% theorem reuse). |

### 4.6 Statistical / numerical estimators

| Theorem | Module | One-line |
|---|---|---|
| `jackknifeVariance_nonneg` | `VerifiedJackknife.lean` | First verified jackknife variance non-negativity in any proof assistant. |
| `sampleVariance_nonneg` | `VerifiedStatistics.lean` | Sample variance non-negativity. |
| `intAutocorrTime_bounds` | `VerifiedJackknife.lean` | Integrated autocorrelation time bounds. |
| `multi_shift_cg_correctness` | `HubbardStratonovichRHMC.lean` | Multi-shift CG correctness for RHMC. |

### 4.7 Topological quantum gates (Fermi-Hubbard + Berry phase)

| Theorem | Module | One-line |
|---|---|---|
| `swap_unitary_minus_one_sign` | `FermiHubbardDimer.lean` | First formally verified symmetry-protected (non-topological) two-qubit gate. |
| `berry_phase_geometric_at_kernel_angle` | `FermiHubbardDimer.lean` | Berry phase is purely geometric under kernel-angle condition. |

### 4.8 Dark sector

| Theorem | Module | One-line |
|---|---|---|
| `sfdm_merger_signature` | `SFDMMergerForecast.lean` | SFDM Rankine-Hugoniot density jump closed form γ=2; sonic-boom step at Mach transition. |
| `fracton_dm_viable_in_p_wave_dipole_superfluid` | `FractonDarkMatter.lean` | Fracton DM viable in p-wave dipole superfluid at MeV–TeV. |
| `fg_cdm_obstruction` | `FangGuTorsionDM.lean` | Fang-Gu torsion DM kinematically excluded at CDM level (traceless T_μν ⟹ w = 1/3). |
| `hidden_sector_minimal_singlet_count` | `HiddenSectorClassification.lean` | ℤ₁₆-classified hidden sector — T-0 TQFT candidate invisible to direct detection. |

---

## 5. Tracked Props (load-bearing hypotheses)

Project posture: **axioms are temporary scaffolding, not permanent commitments** (Pipeline Invariant #15). The constructive alternative is a tracked `def`-Prop that propagates explicitly through every consumer's type signature. Project axiom count is **0** (counts.json `axiom_names: []`, last 2026-05-23 regen; provisional verification post-Phase-6r-prime via `grep -rn "^axiom " lean/SKEFTHawking/` → 0 real declarations).

Full catalogue: `docs/PERMANENT_TRACKED_HYPOTHESES.md`. **Phase 6r-prime Session 2 audit (2026-05-25)**: the original Phase 6r 12 tracked Props were reduced to **2 legitimate** (KT 1990 + DMNO 2010) via P5 identity-wrapper + P2 bundle-redundancy anti-pattern remediation (A1-A4 audit). The 5 audit-pattern items (#4/#5/#7/#8/#12) were DELETED; 3 items (#2/#9/#11) were RESTRUCTURED to substantive content; 1 item (#10) was RECLASSIFIED as a substantive definition.

| Tracked Prop | Status | Module | Discharge LoE |
|---|---|---|---|
| `H_VestigialModeIsGraviton` | KEEP (permanent) | `GravitationalWaves.lean:326` | N/A — requires different microscopic substrate (out of project scope). |
| `H_DESICompatibility` | DISCHARGE_FUTURE_PHASE | `FLRWDynamics.lean:272` | ~50 person-hours; Phase 6b.2 (not active). |
| `H_RT_Formula_Valid` | KEEP (permanent) | `RTCasiniHuertaBounds.lean:87` | N/A — project-scope boundary (RT formula is AdS/CFT holographic working assumption). |
| `TPFConjecture` | KEEP (permanent; converted from `axiom gapped_interface_axiom` on 2026-05-19) | `SPTClassification.lean:254` | N/A — open at literature frontier in 3+1D / 4+1D (proven in 1+1D + 2+1D). |
| `SolovayKitaevQuantitativeContract` | DISCHARGE_IN_PROGRESS | `FKLW/SolovayKitaevQuantitative.lean` | Phase 6t Path A Option C tight-ε regime SHIPPED 2026-05-23; loose-ε bundled headline also SHIPPED. Substantive remaining: K-margin tightening as Mathlib-PR-quality follow-on. |
| `IsKirbyTaylorPinPlusBordism` (Phase 6r legitimate; Phase 6r-prime substrate-discharged via W1.2 Quotient) | KEEP (Kirby-Taylor 1990) | `SymTFT/PinBordism.lean` | Substrate ships `Omega4PinPlusBordism ≃+ ZMod 16` substantively; full geometric ISO (η-invariant on RP⁴ + AHSS) deferred — requires Stiefel-Whitney + Pin group reductions absent in Mathlib (>1 year). |
| `IsDMNOBiconditional` (Phase 6r legitimate; renamed from `IsDMNOWittTrivialIffLagrangianAlgebra` in W2.3 v2) | KEEP (DMNO 2010) | `SymTFT/LagrangianAlgebra.lean` | Body IS the biconditional `Is3DTQFTBraided B ↔ HasLagrangianAlgebra B`; substantive DMNO categorical-algebra proof requires MTC typeclass + Lagrangian-algebra construction (>1 year) — Phase 7+ Mathlib upstream. |

Search live: `grep -rn "H_VestigialModeIsGraviton\|H_DESICompatibility\|H_RT_Formula_Valid\|TPFConjecture\|SolovayKitaevQuantitativeContract\|IsKirbyTaylorPinPlusBordism\|IsDMNOBiconditional" lean/`.

---

## 6. Pipeline invariants (15)

Authority: `docs/WAVE_EXECUTION_PIPELINE.md` §"Pipeline Invariants". One-line summary each:

1. **`formulas.py` is canonical** — only place physics formulas live; all other code imports from it.
2. **`constants.py` is canonical** — only place experimental parameters, physical constants, and the Aristotle theorem registry live.
3. **`visualizations.py` is canonical** — only place figure functions live; notebooks reference via `# viz-ref:` tags.
4. **Every formula has a Lean theorem** with zero sorry.
5. **Every computed quantity has bounds** enforced by CHECK 12.
6. **Every paper claim traces to computation** within 0.5%, enforced by CHECK 14.
7. **Narrative derives from data** — feasibility claims need computed support.
8. **Every experimental parameter has verified provenance** in `src/core/provenance.py`, enforced by CHECK 15.
9. **Placeholder theorems are non-load-bearing** — `True := trivial` theorems are doc markers only; substantive count = total − placeholders.
10. **No heartbeat overrides in proof bodies** (exception: metaprograms like `ExtractDeps.lean` walking O(project-size)).
11. **Every external bibitem has a primary-source cache file** under `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,abstract.txt,json}`, enforced by CHECK 19.
12. **Provenance DOIs resolve to the registry** — every DOI in `PARAMETER_PROVENANCE` must resolve to a `CITATION_REGISTRY` bibkey (CHECK 20).
13. **Stage 14 QI register is auto-regen + manually-curated** — open items regenerated; closed items preserved verbatim across regens.
14. **Every paper-shaped output lifts into a `PAPER_STRATEGY.md` bundle** (F, D1–D5, L1–L3, I1, I2, I3, E1, E2) — recorded in `docs/PAPER_DRAFT_MAPPING.md`.
15. **Every new project-local `axiom` requires explicit user sign-off** + discharge plan or no-feasible-proof argument; `AXIOM_METADATA` registration mandatory.

---

## 7. Bundle status (17 publication targets)

Authority: `docs/PAPER_STRATEGY.md` (architecture) + `docs/PAPER_DRAFT_MAPPING.md` (per-draft → per-bundle assignment) + `docs/BUNDLE_READINESS_HEATMAP.md` (per-bundle Stage-13 readiness, auto-regen via `scripts/bundle_readiness.py --heatmap`).

Per the auto-generated heatmap (2026-05-31), **all 17 bundles show 0 blockers (🟢 GREEN) post-supersession.** The heatmap aggregates existing per-paper findings; a fresh-context bundle Stage-13 sweep is user-triggered, and D8's dedicated reviewer triple is the next operational step.

| Bundle | Tier | Title | Status (2026-05-31) |
|---|---:|---|:---:|
| **F** | 0 (flagship review) | "Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey" | 🟢 GREEN. |
| **D1** | 1 (deep) | Formally Verified Analog Hawking Radiation Across Three Platforms | 🟢 GREEN. |
| **D2** | 1 (deep) | Anomaly Constraints on Standard-Model Particle Content | 🟢 GREEN. |
| **D3** | 1 (deep) | Emergent Gravity from Microscopy — Linearized EFE through BH Thermodynamics | 🟢 GREEN. |
| **D4** | 1 (deep) | Topological Quantum Computation — First Machine-Verified Foundations | 🟢 GREEN. |
| **D5** | 1 (deep) | The Dark Sector under Substrate Constraints | 🟢 GREEN. |
| **D6** | 1 (deep) | Formally Verified Fault-Tolerant Quantum Computation Substrate | 🟢 GREEN. |
| **D7** | 1 (deep) | Classical Simulability and Quantum Advantage via Tensor Networks | 🟢 GREEN. |
| **D8** | 1 (deep) | Kernel-Verified Universal Quantum Gate Compilation | 🟢 GREEN (content complete; bundle-paper lift pending). |
| **L1** | 2 (PRL letter) | GW170817 vs Vestigial-Graviton — 7×10¹⁴ Falsification | 🟢 GREEN. |
| **L2** | 2 (PRL letter) | Three Generations from Modular Invariance | 🟢 GREEN. |
| **L3** | 2 (PRL letter) | BCH Four Laws by Regime | 🟢 GREEN. |
| **I1** | 3 (infrastructure) | Verification Methodology + Lean Tooling | 🟢 GREEN. |
| **I2** | 3 (infrastructure) | Sentence-Level Paper Provenance Pipeline | 🟢 GREEN. |
| **I3** | 3 (infrastructure) | Verified Stochastic Calculus for Mathlib4 | 🟢 GREEN. |
| **E1** | 4 (experimental letter) | Paris-LKB Polariton Analog-Hawking Detection Path | 🟢 GREEN. |
| **E2** | 4 (experimental letter) | Dean-Kim-Lucas Graphene Bilayer Sonic Horizon | 🟢 GREEN. |

**Bundle directories:** `papers/{F,D1,D2,D3,D4,D5,D6,D7,D8,L1,L2,L3,I1,I2,I3,E1,E2}/`. Bundle architecture canon: `docs/PAPER_STRATEGY.md` (17 targets); `docs/PAPER_DRAFT_MAPPING.md` (per-existing-draft → bundle table); `docs/BUNDLE_LIFT_PROCEDURE.md` (14-step lift workflow); `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (absorbing late-phase waves into already-drafted bundles).

---

## 8. Python source modules

132 Python modules under `src/`. Grouped by sector. For per-module docstrings + signatures, browse `src/<sector>/` directly or read `SK_EFT_Hawking_Inventory.md` Section 1.

### 8.1 Core (canonical singletons)

| File | Purpose |
|---|---|
| `src/core/constants.py` | Physical constants, experimental params, `ARISTOTLE_THEOREMS` registry, `AXIOM_METADATA`, `PLACEHOLDER_THEOREMS`. Pipeline Invariant #2. |
| `src/core/formulas.py` | Canonical physics formulas with Lean + Aristotle refs (~137 functions). Pipeline Invariant #1. |
| `src/core/visualizations.py` | All Plotly figure functions + `COLORS` palette. Pipeline Invariant #3. |
| `src/core/transonic_background.py` | 1D BEC transonic flow solver. |
| `src/core/aristotle_interface.py` | Aristotle API + sorry-gap registry. |
| `src/core/sm_anomaly.py` | SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint. |
| `src/core/provenance.py` | `PARAMETER_PROVENANCE` registry (tiers + verification dates). |
| `src/core/citations.py` | `CITATION_REGISTRY` (DOI + arXiv + primary-source-path tracking). |

### 8.2 Phase 1–2: dissipative SK-EFT

| Directory | Modules |
|---|---|
| `src/first_order/` | (empty — content moved to `formulas.py`). |
| `src/second_order/` | `enumeration.py` (count(N) = ⌊(N+1)/2⌋+1), `coefficients.py`, `wkb_analysis.py`, `cgl_derivation.py` (CGL dynamical KMS → FDR). |

### 8.3 Phase 3: gauge erasure / WKB / ADW

| Directory | Modules |
|---|---|
| `src/gauge_erasure/` | `erasure_theorem.py` (non-Abelian gauge erasure → U(1) survives). |
| `src/wkb/` | `connection_formula.py`, `bogoliubov.py`, `spectrum.py`, `backreaction.py`. |
| `src/adw/` | `wen_model.py`, `hubbard_stratonovich.py`, `gap_equation.py`, `fluctuations.py`, `ginzburg_landau.py`, `tetrad_gap_solver.py`, `tetrad_observables.py`. |

### 8.4 Phase 4: experimental / chirality / fracton / vestigial

| Directory | Modules |
|---|---|
| `src/experimental/` | `predictions.py`, `kappa_scaling.py`, `polariton_predictions.py`, `doublon_gate.py`. |
| `src/chirality/` | `gioia_thorngren.py`, `tpf_gs_analysis.py`. |
| `src/fracton/` | `sk_eft.py`, `information_retention.py`, `gravity_connection.py`, `non_abelian.py`. |
| `src/vestigial/` | `mean_field.py`, `lattice_model.py`, `monte_carlo.py`, `phase_diagram.py`, `finite_size.py`, `su2_integration.py`, `grassmann_trg.py`, `lattice_4d.py`, `fermion_bag.py`, `wetterich_model.py`, `phase_scan.py`, `quaternion.py`, `so4_gauge.py`, `gauge_fermion_bag.py`, `gauge_fermion_bag_majorana.py`, `hs_rhmc.py`, `hs_rhmc_jax.py`, `hs_rhmc_torch.py`, `stencil_dirac.py`, `verified_analysis.py`. |

### 8.5 Phase 5 sectors

| Directory | Topic |
|---|---|
| `src/graphene/` | Bilayer-graphene Dirac fluid (Phase 5w): `bilayer_eos.py`, `hawking_predictions.py`, `platform_comparison.py`, `transport_counting.py`, `wkb_spectrum.py`. |
| `src/dark_sector/` | Phase 5x dark-sector: `adw_cosmological_constant.py`, `fracton_dm.py`, `sfdm_merger_forecast.py`, `sfdm_sk_eft.py`, `synthesis.py`, `z16_hidden_sector.py`. |
| `src/scalar_rung/` | Phase 5z scalar-rung Higgs prediction: `bhl_embedding.py`, `ew_mass_matrix.py`, `higgs_prediction.py`. |
| `src/fermi_hubbard/` | Phase 5t Fermi-Hubbard doublon: `dimer.py`. |
| `src/vestigial_inflation/` | Phase 6b vestigial-inflation NO-GO: `ns_r_prediction.py`, `planck_bicep_check.py`, `slow_roll.py`. |

### 8.6 Phase 6 sectors

| Directory | Topic |
|---|---|
| `src/emergent_gravity/` | Phase 6a Track A: `G_N_emerg.py`, `linearized_efe.py`, `vergeles_unitarity.py`. |
| `src/gravitational_waves/` | Phase 6a Track B: `c_GW_computation.py`, `dispersion_relation.py`, `ligo_constraint_check.py`. |
| `src/bh_entropy/` | Phase 6a Track C: `entropy_coefficient.py`, `horizon_spectrum.py`, `mtc_state_counting.py`. |
| `src/bh_thermodynamics/` | Phase 6a Wave 5: `acoustic_evolution.py`, `falsifier_checks.py`, `four_laws_data.py`, `regime_classifier.py`. |
| `src/cosmological_perturbations/` | Phase 6b: `cmb_spectrum.py`, `linear_perturbations.py`, `planck_comparison.py`. |
| `src/bbn/` | Phase 6c BBN: `abundances.py`, `candidate_checker.py`. |
| `src/equivalence_principle/` | Phase 6c: `mechanism_classifier.py`. |
| `src/qec_holography/` | Phase 6c: `code_distance.py`, `scrambling_time.py`. |
| `src/center_symmetry/` | Phase 6d: `eta_over_s_prediction.py`, `polyakov_loop.py`, `svetitsky_yaffe.py`. |
| `src/chiral_ssb/` | Phase 6d GMOR: `gmor_check.py`, `quark_condensate.py`, `tetrad_ratio.py`. |
| `src/cfl/` | Phase 6d CFL: `cfl_lagrangian.py`, `topological_order_check.py`, `z3_one_form_action.py`. |
| `src/strong_cp_de/` | Phase 6e: `combined_de_consistency.py`, `zhitnitsky_eval.py`. |
| `src/heat_kernel/` | Phase 6e: `a2_computation.py`, `a4_computation.py`, `seeley_dewitt.py`. |
| `src/higher_curvature/` | Phase 6e: `curvature_basis.py`, `gauss_bonnet_check.py`, `observational_bound_check.py`. |
| `src/einstein_cartan/` | Phase 6e: `ec_residual_assessment.py`, `observational_bounds.py`, `torsion_amplitude.py`. |
| `src/nonlinear_efe/` | Phase 6f: `T_emerg_vs_matter.py`, `efe_solver.py`, `observable_prediction.py`. |
| `src/diff_invariance/` | Phase 6f: `anomaly_hunt.py`, `variational_check.py`. |
| `src/micro_macro_match/` | Phase 6f: `cc_problem_assessment.py`, `g_n_emerg_from_micro.py`, `lambda_emerg_from_micro.py`. |
| `src/rt_ch_bounds/` | Phase 6j: `ch_bound_check.py`, `rt_comparison.py`. |
| `src/ew_phase_transition/` | Phase 6g/6k: `baryogenesis_compatibility.py`, `order_classifier.py`, `potential.py`. |
| `src/ew_baryogenesis/` | Phase 6g: `bridge_check.py`, `sphaleron_computation.py`. |
| `src/resurgence/` | Phase 6n: `bdg_self_energy.py`, `borel.py`. |
| `src/dkm_bootstrap/` | Phase 6q Wave 2b numerical companion (2026-05-25 strengthening close): `graphene_mir.py` — CHHK MIR constant `(2·β_2/(4π))^(1/3) ≈ 0.0756` with Crossno 2016 graphene-data confrontation. Canonical formulas in `src/core/formulas.py` (`chhk_beta_d`, `chhk_mir_constant`, `graphene_mir_constant`, `graphene_mir_constant_mpmath`, `unit_sphere_surface`); platform-specific specialization here. |

---

## 9. Aristotle integration

**322 theorems machine-proved across 44 runs.** Authority: `ARISTOTLE_THEOREMS` registry in `src/core/constants.py`. Run table in `SK_EFT_Hawking_Inventory.md` Section 3.

**Submission tooling:**
- `scripts/submit_to_aristotle.py` — `--dry-run` previews; `--submit --priority N` submits; `--retrieve <ID> --integrate` integrates returned proofs.
- `docs/references/Theorm_Proving_Aristotle_Lean.md` — mandatory pre-read.
- `docs/references/aristotle_batch_plan.md` — current batch plan.

**Posture:** Aristotle is Stage-4 fallback in the wave pipeline. As of Phase 6, MCP-interactive proving via `lean-lsp-mcp` is the primary loop; Aristotle reserved for (i) sorries that survive interactive decomposition, or (ii) batch submissions. No Aristotle runs in any 6-prefix phase as of 2026-05-23 — all Phase 6n/6o/6p/6t ships MCP-proven.

**Toolchain caveat:** Aristotle runs on Lean 4.28.0 + earlier Mathlib pin; project is on 4.29.1 + `5e932f97`. Use sparingly when project uses 4.29-specific features.

---

## 10. Other docs (pointers)

### 10.1 `docs/` reference

| File | Purpose |
|---|---|
| `docs/ARCHITECTURE_SCOPE.md` | Layer 3 scope statement (what is and is not predicted under the project's mechanisms). |
| `docs/BUNDLE_DIRECTORY_SCHEMA.md` | Per-bundle file layout. |
| `docs/BUNDLE_LIFT_PROCEDURE.md` | 14-step procedure for lifting per-paper drafts into a publication bundle. |
| `docs/BUNDLE_READINESS_HEATMAP.md` | Per-bundle Stage-13 readiness, auto-regen via `scripts/bundle_readiness.py`. |
| `docs/DASHBOARD.md` | Provenance command-center documentation (`scripts/provenance_dashboard.py`, localhost:8050). |
| `docs/KNOWLEDGE_GRAPH.md` | Project knowledge-graph schema + Postgres+AGE setup. |
| `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` | Stage A–G protocol for absorbing late-phase waves into already-drafted bundles. |
| `docs/PAPER_DRAFT_MAPPING.md` | Per-existing-draft → per-bundle assignment table. |
| `docs/PAPER_STRATEGY.md` | 17-bundle publication architecture (canonical). |
| `docs/PAPER_TABLES_STATUS.md` | Per-paper LaTeX table generation status. |
| `docs/PERMANENT_TRACKED_HYPOTHESES.md` | 5-Prop catalogue (tracked-Prop posture, status, discharge LoE). |
| `temporary/working-docs/PHASE5_STEP13_COMPLETE.md` | Phase 5 Step 13 (F.21 unconditional) ship summary. |
| `temporary/working-docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md` | Phase 6t quantitative Solovay-Kitaev ship summary. |
| `docs/QI_REGISTER.md` | Stage 14 quality-improvement register (auto-regen + manually-curated). |
| `docs/READINESS_GATES.md` | Per-paper Stage-13 readiness companion to bundle heatmap. |
| `docs/RESEARCH_STATUS_OVERVIEW.md` | High-level research-status overview. |
| `docs/WAVE_EXECUTION_PIPELINE.md` | 14-stage wave protocol + 15 pipeline invariants. |
| `docs/counts.json` | Live counts ground truth (regen via `scripts/update_counts.py`). |
| `docs/counts.tex` | LaTeX `\input{}` counts macros for papers. |

### 10.2 `docs/roadmaps/` — phase roadmaps

Per-phase roadmaps (Phase 1 through Phase 7a) in `docs/roadmaps/Phase<N>_Roadmap.md`. Active roadmaps as of 2026-05-26:
- **Phase 6r** (SymTFT substrate-to-bulk unification, 8 Waves, **SUBSTANTIVELY CLOSED 2026-05-25**; bundle absorption HELD for unified event).
- **Phase 6r-prime** (substantive discharge of Phase 6r tracked Props, 4 Wedges + 3 carryovers + W5 cross-bridge integration + R dual-phase adversarial review, **SUBSTANTIVELY CLOSED at Session 5 2026-05-26** with 68-conjunct closure; ADV-3 MonObj/ComonObj axiom-instance follow-on flagged as next-session Mathlib-PR-quality strengthening, NOT blocking).
- **Phase 6v** (external-substrate alignment + creates D6 bundle, 7 waves NOT STARTED).
- **Phase 6w** (classical-simulability + tensor-network substrate, 7 waves NOT STARTED).
- **Phase 6t** (quantitative SK — Path A Option C close 2026-05-23).
- **Phase 7a** (paper-bundle architecture freeze).

Phase 6u (Generic-Alphabet SK substrate) is a NOT-STARTED planning skeleton with T-A2 / T-B tracks re-slotted from "(likely Phase 6w)" to Phase 6x or later per ADR 008. All Phase 5+ phases through 6p are substantively closed.

### 10.3 `docs/references/` — manuals

- `docs/references/Theorm_Proving_Aristotle_Lean.md` — mandatory Aristotle pre-read.
- `docs/references/Datastar_Dashboard_Reference.md` — provenance-dashboard reference.
- `docs/references/production_rhmc.md` — RHMC production reference.

### 10.4 `docs/adrs/` — architecture decision records

- `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md`.

### 10.5 `docs/agents/` — agent prompts

- `docs/agents/claims-reviewer-bundle-prompts.md` — Stage-13 anchor list per bundle.
- `docs/agents/claims_reviewer.md` — claims-reviewer agent prompt.

### 10.6 `docs/stakeholder/` — per-phase stakeholder docs

Implications + strategic-positioning notes per phase, `docs/stakeholder/Phase<N>_*.md` (~22 docs).

### 10.7 `docs/analysis/` and `docs/validation/`

- `docs/analysis/` — cross-cutting analysis docs.
- `docs/validation/` — validation reports.

---

## 11. Scripts (53 in `scripts/`)

**Validation + counts:**
- `scripts/validate.py` — full validation suite (21 checks); `--list` enumerates; `--check <name>` runs one.
- `scripts/update_counts.py` — regenerates `docs/counts.json` (re-runs `extract_lean_deps.py` if Lean source hashes changed).
- `scripts/extract_lean_deps.py` — extracts Lean declaration taxonomy + axiom dependencies (via `ExtractDeps.lean`).
- `scripts/graph_integrity.py` — graph-integrity checks for the knowledge graph.
- `scripts/build_graph.py` — builds the project knowledge graph (Postgres + AGE).
- `scripts/last_modified.py` — sentence-level freshness propagation.
- `scripts/sentence_state.py` — sole-writer sentence-state CLI (paper-provenance v2).
- `scripts/verification_state.py` — verification-state cross-tab change-bus.

**Bundle ops (Phase 7a):**
- `scripts/bundle_append.py` — append-and-supersede across bundles.
- `scripts/bundle_clusters.py` — claim-cluster bundle projection.
- `scripts/bundle_migration.py` — bundle migration tooling.
- `scripts/bundle_readiness.py` — regenerates `docs/BUNDLE_READINESS_HEATMAP.md`.
- `scripts/bundle_source_manifest.py` — bundle source manifest.
- `scripts/check_bundle_source_freshness.py` — freshness check.
- `scripts/datastar_bundles.py` — provenance-dashboard Bundles-tab JSON.

**Citation + provenance:**
- `scripts/back_fill_primary_sources.py` — populates `Lit-Search/Phase-X/primary-sources/` cache files.
- `scripts/promote_primary_sources.py` — writes successful fetches back into `CITATION_REGISTRY`.
- `scripts/extract_missing_bibkeys.py` — extracts `\bibitem` stubs from modified papers.
- `scripts/citation_cache.py` — citation cache management.
- `scripts/audit_paper_lean_refs.py` — auditor for paper ↔ Lean references.

**Aristotle:**
- `scripts/submit_to_aristotle.py` — submission + retrieval + integration.
- `scripts/review_runner.py` — review-runner orchestration.

**Figures + papers:**
- `scripts/review_figures.py` — generates PNGs + structural figure checks.
- `scripts/render_paper_tables.py` — paper-table rendering.
- `scripts/paper_tables/` — per-bundle table generators.
- `scripts/templates/` — paper templates.

**MC production:**
- `scripts/run_rhmc_production.py`, `scripts/run_rhmc_epochs.sh`, `scripts/run_majorana_production.py`, `scripts/run_vestigial_production.py`, `scripts/run_vestigial_inflation_preliminary.py`, `scripts/analyze_majorana_results.py`, `scripts/view_vestigial_mc.py`, `scripts/benchmark_rust_parallel.py`.

**T-gate compilers (Phase 6p):**
- `scripts/phase6p_tgate_compiler.py` (+ `_v4`, `_v6`, `_v7`, `_v8`), `scripts/phase6p_tgate_exact_frob.py`.

**Other:**
- `scripts/extract_sigma_symbolic.py`, `scripts/generate_a1_resolution.py`, `scripts/wave2_flip_provenance.py`, `scripts/sync_graph_to_pg.py`, `scripts/cluster_detect.py`, `scripts/qi_register.py`, `scripts/readiness_gates.py`, `scripts/datastar_helpers.py`, `scripts/provenance_dashboard.py`, `scripts/test_helpers.py`, `scripts/test_pseudofermion_convention.py`, `scripts/pre-commit-notebooks.sh`.

---

## 12. Cross-references

- **Memory (per-conversation):** `~/.claude/projects/-Users-johnroehm-Programming-PythonEnvironments-Physics-Fluid-Based-Physics-Research/memory/MEMORY.md` — index of topic files (project ships, feedback notes, next-session openers).
- **Lit-Search deep research:** `Lit-Search/` workspace-level — phase-specific deep-research deliverables (`Phase-5*/`, `Phase-6*/`, `Phase-7*/`); primary-source cache at `Lit-Search/Phase-X/primary-sources/`; pending tasks at `Lit-Search/tasks/`.
- **Workspace docs:** `../CLAUDE.md` — workspace-level agent guidance.
- **Working docs (transient):** `temporary/working-docs/` — proof-state notes, per-wave working memos, archive of misplaced narrative.
- **Archived old Inventory_Index:** `temporary/working-docs/inventory_index_handoff_archive_2026-05-23.md` — the previous 488KB session-log-style index, preserved for audit.

---

## 13. Maintenance protocol

**When to update this file:**
- New top-level theorem ships → add to §4.
- New tracked Prop → add to §5 (after `PERMANENT_TRACKED_HYPOTHESES.md` is updated).
- New subdirectory in `lean/SKEFTHawking/` → add to §3.1.
- Bundle status change (RED ↔ GREEN) → update §7 (or re-regen heatmap and link to it).
- Counts move ≥1% → refresh §1 from `docs/counts.json`.

**What NOT to put here:**
- Per-session ship narrative (belongs in `temporary/working-docs/` or `MEMORY.md` topic files).
- Per-commit changelog (belongs in git history).
- Per-wave deep prose (belongs in `SK_EFT_Hawking_Inventory.md`).
- Full theorem statements (belongs in `.lean` files; this index gives names + one-line).

**Size budget check after edit:** `wc -c SK_EFT_Hawking_Inventory_Index.md` — keep under 100,000 bytes. Current target: ~50–80 KB.
