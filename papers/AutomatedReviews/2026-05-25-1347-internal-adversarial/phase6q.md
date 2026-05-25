---
target: phase6q_dkm_transport_bootstrap
target_kind: substrate
reviewer: adversarial-reviewer (general-purpose dispatch)
review_date: 2026-05-25T13:47:00Z
readiness_gates_version: 1
---

# Adversarial Review — Phase 6q DKM Transport Bootstrap (substrate-level)

## Summary

Twenty findings: 1 BLOCKER, 12 REQUIRED, 7 RECOMMENDED. The substantive math is sound — Python MIR constant 0.0756 is correctly computed from CHHK eq. (9) + (12) at d=2, the Lean theorem `becBogoliubovCommutatorNorm_isSuperFactorialUnbounded` is genuinely substantive (factorial-dominates-exponential composed via central-binomial), the F2/F3 orthogonality theorems honestly anchor "new microscopic content," and the kernel-only axiom posture is intact (0 axioms project-wide). The findings cluster on documentation drift after the 2026-05-25 strengthening-close: the stale "(2β₂/4π)^{1/3} ≈ 0.6" estimate still appears in two Lean docstrings, the closing working doc, and the project-complete memory; CITATION_REGISTRY is missing 5 secondary bibkeys cited inside Phase 6q Lean docstrings (Yin-Lucas, Kuwahara-Saito, Abanin-De Roeck-Huveneers, Toledo-Tude & Eastham, Parker-et-al.); CHHK eq. references repeatedly cite "eq. (29)" for the MIR bound which is actually CHHK eq. (12); Crossno's representative ℓ value (80 nm) is a fabricated central-window number, not a paper-anchored value (Crossno's three samples have l_m = 1500, 600, 34 nm at 60 K — none ~80 nm); the working-doc claim "First formally-verified analog" is an unbacked Gate-10 first-claim; the Lean substrate-level "graphene witness at mirConst=1/2" uses a=1 normalized substrate, so what's "formally verified" is ℓ/a≥1/2 at τ=D=a=1 — i.e., 1 ≥ 1/2 — not the substantive geometric inequality (this is acknowledged in newer prose but the working doc's L2-entry framing overclaims). The single BLOCKER (Crossno value) is mechanical to fix; everything else is REQUIRED docstring/registry consistency. Gates affected: 1 (citation registry holes + stale eq. labels), 3 (Crossno value provenance), 5 (borderline structural-tautology biconditional, honestly disclosed), 7 (working-doc 0.6 stale + first-claim), 9 (module count + LoC drift in inventory/roadmap/memory). Overall: not "publishable" in current state, but resolvable in a small consistency-pass.

## Findings

### 1.1 — 🟡 REQUIRED — 5 secondary bibkeys cited in Lean docstrings absent from CITATION_REGISTRY
- **Gate:** CitationIntegrity
- **Location:** Multiple — see Evidence
- **Observed:** Five external references appear in Phase 6q DKMBootstrap Lean module docstrings without corresponding `CITATION_REGISTRY` entries in `src/core/citations.py`:
  - **Yin-Lucas arXiv:2106.09726** — cited in `BECBogoliubovBosonicGrowth.lean:60` and `HorizonTransportBootstrap.lean:48`, `E1E2CrossBridge.lean` (referenced indirectly). Load-bearing as the Lieb-Robinson-for-bosons substrate for the sharpened-NO-GO half.
  - **Kuwahara-Saito arXiv:2103.11592** — same modules. Load-bearing as the bosonic Lieb-Robinson substrate.
  - **Abanin-De Roeck-Huveneers PRL 115, 256803 (arXiv:1507.01474)** — cited in `Predicates.lean:182`, `NoCrossing.lean:42`, `BECBogoliubovBosonicGrowth.lean:65`. Load-bearing as the fermionic factorial-exponential bound that CHHK F3 is built on.
  - **Toledo-Tude & Eastham APL Quantum 1, 036108 (2024)** — cited in `E1E2CrossBridge.lean:47`. Load-bearing for the polariton-non-equilibrium classification.
  - **Parker-Cao-Avdoshkin-Scaffidi-Altman PRX 9, 041017 (arXiv:1812.08657)** — cited in `Predicates.lean:184`, `NoCrossing.lean:43-44`. Load-bearing as the universal operator-growth hypothesis behind CHHK F3.
- **Evidence:** `grep -i "Yin\|Kuwahara\|Abanin\|Toledo.*Tude\|Parker.*Cao" src/core/citations.py` returns no matching keys (only an unrelated `Ying-Degenne` martingale entry). The READINESS_GATES.md Gate-1 rule states: "Every bibkey in the .tex has a matching CITATION_REGISTRY entry … A bibkey that is not in the registry [blocks]." Lean docstrings are not `.tex`, but per the adversarial-reviewer.md gate-1 expansion the same rule applies for load-bearing-citation-in-substrate: the registry is "how the pipeline tracks what has been verified."
- **Expected:** Each of the 5 references either (a) has a `CITATION_REGISTRY` entry with primary-source PDF cached, or (b) is demoted from "load-bearing substrate reference" to "informal pointer" with an explicit disclaimer in the docstring.
- **Fix:** Add the 5 entries to `CITATION_REGISTRY` (use existing `CHHK2025DKMTransport` as the template); back-fill primary-source PDFs via `scripts/back_fill_primary_sources.py`; run `validate.py --check citation_primary_sources_present`.

### 1.2 — 🔵 RECOMMENDED — CHHK equation-label citations are inconsistent and likely wrong
- **Gate:** CitationIntegrity
- **Location:** Multiple — see Evidence
- **Observed:** The Python formulas + Lean predicates that implement the MIR-style master bound `(d·β_d/(4π))^{1/(d+1)} ≤ ℓ/a` and the prefactor `β_d = (1/π)·V_{d-1}/(2π)^d·(1−π/4)/(d+2)` repeatedly cite "CHHK eq. (29)" or "eq. (26)/(29)" as the source. Verified against the v2 PDF (arXiv:2509.18255v2, 14 May 2026, cached at `Lit-Search/Phase-1-and-Background/primary-sources/CHHK2025DKMTransport.pdf`): the prefactor β_d is introduced at **eq. (9)** in §5 ("Bounds on the collective mean free path"); the super-Planckian MIR bound `(d·β_d/(4π))^{1/(d+1)} ≤ ℓ/a` is **eq. (12)**. The paper's eq. (29) is in §7.2 ("Second bound") and is the operator-norm bound on the nested-commutator squared expectation value — *not* the MIR bound. Eq. (26) is in §7.1 and is the same intermediate step. Possible explanation: v1 of the paper (22 Sep 2025) may have had different equation numbering and the original Wave 1a.1 DR was written against v1.
- **Evidence:**
  - `formulas.py:10684,10707,10711,10734,10759` cite "CHHK eq. (29)".
  - `SKEFTSpecialization.lean:23,46` cite "CHHK eq. (29)" for `(d·β_d/4π)^{1/(d+1)}`.
  - `HorizonTransportBootstrap.lean:33,45` cite "CHHK eq. (26)/(29)".
  - The cached v2 PDF page 8 explicitly shows: "obtain from (2) that β_d/(1−e^{−1/(Tτ)}) ≤ (ℓ/a)^d (τ/χa^d)⟨n₀²⟩_T, **where β_d ≡ (1/π) V_{d-1}/(2π)^d (1−π/4)/(d+2)**" (eq. (9)).
  - Page 9: "(d β_d/4π)^{1/(d+1)} ≤ ℓ/a (super-Planckian Tτ ≪ 1)" (**eq. (12)**).
- **Expected:** Either cite eq. (9)+(12) (the v2 numbering, which is what the cached PDF shows) or explicitly note the v1/v2 mismatch.
- **Fix:** Global replace "CHHK eq. (29)" → "CHHK eq. (12) [v2; eq. (29) in v1]" and "CHHK eq. (26)" → "CHHK eq. (9) [v2]" across formulas.py, the four DKMBootstrap modules referencing the MIR bound, and the working doc. Note that the *substantive formula* is correctly implemented — this is a citation-label-only fix.

### 1.3 — 🔵 RECOMMENDED — Dispatch's author-name error noted but project still has stale CHHK citation in dispatch chain
- **Gate:** CitationIntegrity
- **Location:** `lean/SKEFTHawking/DKMBootstrap/Predicates.lean:12-17`
- **Observed:** The docstring honestly flags the "Christ-Hartman-Hartman-Kologlu" error in the original DR dispatch and corrects to "Chowdhury, Hartnoll, Hebbar, Khondaker". CITATION_REGISTRY has the correct author list. WebFetch of arXiv:2509.18255 confirms: Subham Dutta Chowdhury, Sean A. Hartnoll, Aditya Hebbar, Ruby Khondaker. **Citation match verified.** This is a recommendation only: the authorial flagging is a strength — recommend adding a one-line provenance note to the citation registry's `notes` field documenting that the prior DR dispatch had the wrong name list, to prevent future re-introduction.
- **Evidence:** `Predicates.lean:12-17` carries the explicit "naming flagged per Wave 2a.1 dossier" annotation.
- **Expected:** No content fix required. Optionally, push the provenance note into the registry `notes` for posterity.
- **Fix:** Optional — append to `CITATION_REGISTRY['CHHK2025DKMTransport']['notes']`: "Author-name verification: prior Wave 1a.1 dispatch contained the wrong author string 'Christ-Hartman-Hartman-Kologlu'; verified via arXiv abs page 2026-05-25 to be correct as listed (Chowdhury / Hartnoll / Hebbar / Khondaker)."

### 2.1 — 🔴 BLOCKER — Crossno representative mean-free-path 80 nm is not anchored to the primary source
- **Gate:** ParameterProvenance
- **Location:** `src/dkm_bootstrap/graphene_mir.py:38-43`
- **Observed:** `CROSSNO_GRAPHENE_MEAN_FREE_PATH_M = 80e-9` is documented as: "Source: Crossno et al. Science 351, 1058 (2016). The reported ℓ is in the 50-100 nm range in the Dirac fluid window; 80 nm is the central-window representative value." The Crossno 2016 cached PDF (page 4) reports: "Fig 3C taken at 60 K. l_m is estimated to be **1.5, 0.6, and 0.034 μm** for samples S1, S2, and S3, respectively." None of these three values is in the 50-100 nm range. The cleanest sample S1 has l_m ≈ 1500 nm at 60 K — ~19× larger than the claimed "representative 80 nm." The paper also mentions ~0.1 μm = 100 nm as a theoretical estimate of the electron-electron scattering length, but that's a *theoretical scattering length* not the *measured momentum-relaxation length* l_m. The "50-100 nm" + "80 nm representative" appear to be fabricated central-window prose, not paper-derived. This is a Gate-3 BLOCKER per the adversarial-reviewer.md rule: "drift and missing are BLOCKER" — the value is not paper-anchored.
- **Evidence:** Crossno 2016 page 4 (`primary-sources/Crossno2016GrapheneWF.pdf`): "l_m is estimated to be 1.5, 0.6, and 0.034 μm for samples S1, S2, and S3, respectively." Table S.I (page 5) confirms samples are mobility-distinct (S1 cleanest at 3·10^5 cm²/V·s). The Phase 6q test `tests/test_dkm_bootstrap.py:170-171` "Crossno measures ℓ ~ 50-100 nm at T ~ 75 K; representative 80 nm" propagates the unsourced number into a passing assertion.
- **Expected:** Either (a) anchor the constant to a specific Crossno sample (e.g., S1's l_m = 1.5 μm at 60 K), with explicit citation, or (b) document the constant as an order-of-magnitude representative chosen for illustration with the explicit Crossno-sample range cited.
- **Fix:** Replace `CROSSNO_GRAPHENE_MEAN_FREE_PATH_M = 80e-9` with one of:
  - `= 1.5e-6  # Crossno 2016 sample S1, l_m at 60K`, or
  - `= 6e-7   # Crossno 2016 sample S2, l_m at 60K`, or
  - keep an illustrative range but make the docstring honest: "Order-of-magnitude representative; Crossno 2016 reports l_m = 1.5, 0.6, 0.034 μm for S1/S2/S3 at 60K." The downstream `crossno_graphene_satisfies_chhk_bound()` ℓ/a margin claim ("~4300×") needs recomputation if the value changes.

### 2.2 — 🟡 REQUIRED — Castro Neto a = 0.246 nm anchoring is informal
- **Gate:** ParameterProvenance
- **Location:** `src/dkm_bootstrap/graphene_mir.py:36`
- **Observed:** `GRAPHENE_LATTICE_SPACING_M = 0.246e-9` cites Castro Neto et al. RMP 81, 109 (2009) eq. (4). The Castro Neto registry entry `CastroNeto2009RMPGraphene` exists in `CITATION_REGISTRY`, primary-source PDF cached. WebSearch confirms the paper exists. The value 0.246 nm = √3 × 0.142 nm is the standard graphene lattice constant (where 0.142 nm is the C-C bond length). This is a well-known number, but the docstring's claim of "eq. (4)" was not verified against the cached PDF page 4 in this review.
- **Evidence:** `CITATION_REGISTRY['CastroNeto2009RMPGraphene']` is present with cached primary source.
- **Expected:** A note in the docstring confirming the precise equation reference, OR a structural primary-source-link via a regenerated `validate.py --check parameter_provenance` pass on this specific parameter.
- **Fix:** Verify against page 4 of `Lit-Search/Phase-1-and-Background/primary-sources/CastroNeto2009RMPGraphene.pdf`; if eq. (4) is indeed the lattice constant equation, the docstring is fine; if not, correct the reference.

### 3.1 — 🟡 REQUIRED — B.2 reverse-direction biconditional is a structural tautology (honestly disclosed but borderline)
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/DKMBootstrap/LDPBridge.lean:188-214`
- **Observed:** The Wave 2b.2 reverse direction `LDP_rate_function_yields_F4_compatible_correlator_existence` has proof body `⟨zeroCorrelator, zeroCorrelator_isImGRetardedNonneg⟩`. The biconditional `chhk_F4_existence_iff_LDP_rate_function_holds` packages this with the forward direction. The hypothesis `IsLDPRateFunction β (dkm_rate_function β p)` is never consumed (its position in the signature has an underscore: `_h_ldp`). Both sides of the biconditional are unconditionally satisfiable on any DKM substrate via the zero correlator + the construction-by-decree DKM rate function — neither direction has substantive bite.
- **Evidence:** Line 191: `⟨zeroCorrelator, zeroCorrelator_isImGRetardedNonneg⟩`. The docstring (lines 168-175) explicitly discloses this: "the substantive 'under action-correlator link' form … is **deferred** to the D1 lift-to-Lean wave," and "both sides hold unconditionally on every DKM substrate via the zero correlator, so the biconditional is structurally complete at substrate level."
- **Expected:** The docstring honesty saves this from being a BLOCKER. The remaining ask: tag the headline theorem name or docstring more bluntly that this is *substrate-only* — e.g., rename to `chhk_F4_existence_iff_LDP_rate_function_holds_substrate_level` or add a `@[deprecated "..."]`-style banner pointing at the D1-deferred substantive form. The current name implies more than the body delivers.
- **Fix:** Rename to make the substrate-only scope explicit, OR add an explicit "SUBSTRATE LEVEL ONLY — both sides hold via zero witness" line at the top of the docstring.

### 3.2 — 🔵 RECOMMENDED — `IsDKMFeasibleSDPCandidate := True` placeholder retained — KEEP verdict honest
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/DKMBootstrap/SDPStructure.lean:133-141`
- **Observed:** The strengthening pass KEPT this as a "research-frontier scaffold." Body is `Prop := True`. The trivial witness `trivial_sdp_candidate` is a `trivial`. Per the docstring (lines 125-132): "The placeholder explicitly *advertises* the future work to downstream readers."
- **Evidence:** No downstream Lean module CONSUMES this predicate as a load-bearing hypothesis (grep confirms only self-references in SDPStructure.lean). Used only in the cosmetic `analytic_independent_of_sdp_candidate` (line 158) which trivially packages it with an analytic-bootstrap hypothesis.
- **Expected:** Keep as is — KEEP verdict is justified given (a) no load-bearing consumer, (b) honest docstring, (c) explicit "Phase 7+ research-frontier" framing.
- **Fix:** None required. Optionally: surface this in a `placeholder_markers` audit file so the Gate-5 evaluator does not need to discover it as a candidate.

### 3.3 — 🟡 REQUIRED — `becBogoliubovCommutatorNorm := (2κ)!` is honest substrate substitution but docstring borders on overclaim
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/DKMBootstrap/BECBogoliubovBosonicGrowth.lean:96-103, 196-219`
- **Observed:** The theorem `becBogoliubovCommutatorNorm_isSuperFactorialUnbounded` is genuinely substantive: it composes the central-binomial identity `(κ!)² ≤ (2κ)!` (via Mathlib `Nat.factorial_mul_factorial_dvd_factorial_add`) with factorial-dominates-exponential (`FloorSemiring.tendsto_pow_div_factorial_atTop`) to discharge the abstract `IsSuperFactorialUnbounded` predicate on the concrete sequence `(2κ)!`. The MATH is real. However, the docstring at lines 28-43 frames this as "the substantive **second NO-GO** structural finding: the BEC Bogoliubov platform fails the CHHK F3 operator-growth axiom irrespective of the (ε, n0Norm) microscopic constants" — and the title section calls this "Substantive BEC Bogoliubov-bosonic unbounded-norm proof." This is *true at the substrate level* but **untrue** of the BEC Bogoliubov Hamiltonian itself: the proof does not derive `(2κ)!` from the Bogoliubov-bosonic operator-norm structure; it postulates the sequence and shows the postulated sequence satisfies the abstract predicate. The actual derivation from a BEC Hamiltonian is explicitly noted as "multi-session out-of-scope" (lines 331-339).
- **Evidence:** Line 102: `becBogoliubovCommutatorNorm := fun κ => (Nat.factorial (κ + κ) : ℝ)`. Line 207: the proof uses `unfold becBogoliubovCommutatorNorm` to expose the postulated form. The disclosure at lines 331-339 is honest but appears *after* the main headline's prose framing.
- **Expected:** The headline name `becBogoliubovCommutatorNorm` itself is the source of the framing overclaim — it asserts the sequence IS the BEC Bogoliubov commutator norm, when in fact it is a *postulated substrate stand-in*. Either (a) rename to e.g. `becBogoliubovBosonicStandInSequence` or `superFactorialBosonicWitness`, or (b) move the "physical-stand-in" disclaimer to the *top* of the module docstring (before the substantive prose).
- **Fix:** Reframe headline naming OR top-of-file disclaimer move.

### 3.4 — 🔵 RECOMMENDED — `bec_distinguishes_from_graphene_super_factorial` substantive companion is genuinely substantive
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/DKMBootstrap/BECBogoliubovBosonicGrowth.lean:300-305`
- **Observed:** This A.3 substantive-companion theorem returns a pair `⟨zero_seq_hasOperatorGrowthBound …, bec_falls_under_sharpened_no_go …⟩`. The first conjunct says the graphene zero-sequence satisfies F3 (true: 0 ≤ κ!·ε^κ·n0Norm for nonneg n0Norm); the second says BEC's `(2κ)!` does not. The pairing is genuinely substantive — it ties classifier-distinctness to operator-growth-behaviour distinctness, exactly as the docstring claims. **Honest substantive companion.** Caveat: the second-conjunct distinction is BEC-vs-zero, not BEC-vs-graphene-real-substrate (graphene's actual commutator-norm sequence is not modeled here; the zero sequence is a placeholder for "graphene-compatible-with-F3").
- **Evidence:** Lines 287-305 + 277-285.
- **Expected:** Docstring already honest about the substrate posture.
- **Fix:** None required.

### 4.1 — 🟡 REQUIRED — Working doc + memory cite stale 0.6 estimate inconsistent with shipped Python value
- **Gate:** CrossPaperConsistency
- **Location:**
  - `temporary/working-docs/phase6q/wave_2c_positioning.md:12, 75`
  - `memory/project_phase6q_complete_2026_05_23.md:45`
  - `lean/SKEFTHawking/DKMBootstrap/HorizonTransportBootstrap.lean:23-24`
  - `lean/SKEFTHawking/DKMBootstrap/E1E2CrossBridge.lean:80`
- **Observed:** Four distinct artifacts still cite the stale "(2β₂/4π)^{1/3} ≈ 0.6" estimate, even after the 2026-05-25 strengthening pass corrected the Python and roadmap docs to the actual value 0.0756:
  - Working doc line 12: "(2β₂/4π)^{1/3} ≈ 0.6 per Wave 2a.1 DR §5, Python-numerical-companion-deferred"
  - Working doc line 75: "compute the substantive graphene MIR constant `(2β₂/4π)^{1/3} ≈ 0.6` per Wave 2a.1 DR §5"
  - Memory file line 45: "substantive `(2β₂/4π)^{1/3} ≈ 0.6` ships Python-side in deferred Wave 2b numerical companion"
  - `HorizonTransportBootstrap.lean` line 22-24: "the bound reads `0.6 ≤ √(τ·D) / a` (substrate-level — Python numerical side for the 0.6 constant)"
  - `E1E2CrossBridge.lean` line 80: "the MIR-bound discharge (`(2β₂/4π)^{1/3} ≈ 0.6` graphene MIR constant per Wave 2a.1 DR §5)"
  The Python source (`graphene_mir_constant() = 0.07562892800257`) and the Python docstring + tests + the roadmap §B.1 + the inventory at line 106 all agree the value is 0.0756. The Lean Python-anchor docstrings on lines 36-37 of `HorizonTransportBootstrap.lean` and elsewhere agree on 0.0756. So inside the same module, the *prose intro* says 0.6 and the *theorem docstring* says 0.0756.
- **Evidence:** `grep -n "0\.6" lean/SKEFTHawking/DKMBootstrap/HorizonTransportBootstrap.lean lean/SKEFTHawking/DKMBootstrap/E1E2CrossBridge.lean temporary/working-docs/phase6q/wave_2c_positioning.md` returns 5 sites of the stale value.
- **Expected:** Single canonical value 0.0756 (or its `0.0757` rounding) across all four artifacts. The 0.6 number is wrong by ~8× and must not appear in any post-strengthening-close documentation.
- **Fix:** Global replace `≈ 0.6` → `≈ 0.0756` (or `≈ 0.0757`) in the five sites above, then re-grep for any remaining 0.6 references to confirm no missed instances.

### 4.2 — 🟡 REQUIRED — Module count drift: roadmap + memory say "9 new modules", inventory says "10" or "11", actual is 11
- **Gate:** CrossPaperConsistency
- **Location:**
  - `docs/roadmaps/Phase6q_Roadmap.md:9, 424` ("9 new modules")
  - `memory/project_phase6q_complete_2026_05_23.md:10, 53, 60` ("9 Lean modules")
  - `SK_EFT_Hawking_Inventory_Index.md:56` ("10 new Lean modules"); line 106 ("11 modules")
  - Actual filesystem count: 11 .lean files in `lean/SKEFTHawking/DKMBootstrap/`
- **Observed:** Session 1 of the roadmap log enumerates 10 modules (Wave 1a.2/1b.1/1b.2/1b.3/1c.1/1c.2/1c.3/2a.2/2a.3/2b). Session 2 adds BECBogoliubovBosonicGrowth.lean → 11 total. The strengthening-close section of the memory file correctly says "now 11 modules total" (line 37) but the leading bullet says "9 new Lean modules" (line 10). The roadmap's Session-1 bullet at line 9 + line 424 says "9 new Lean modules" but enumerates 10 in its content. The inventory's recent-changes log (line 56) says "10 new Lean modules" referring to the 2026-05-23 ship (which was the pre-Session-2 state, but 10, not 9), and the module-map (line 106) correctly says "11 modules" referring to the current state.
- **Evidence:** `ls lean/SKEFTHawking/DKMBootstrap/*.lean | wc -l` = 11. `wc -l lean/SKEFTHawking/DKMBootstrap/*.lean` total = 2709 lines (inventory says ~2050 LoC — ~30% undercount).
- **Expected:** Three-way consistency: roadmap, memory, inventory all agree (a) Session 1 shipped 10 modules, (b) Session 2 added 1 module, (c) current total = 11 modules, ~2709 LoC.
- **Fix:** Edit roadmap line 9 + 424 "9 new" → "10 new (Session 1) + 1 new (Session 2) = 11 total"; edit memory line 10 + 53 + 60; edit inventory line 56 "10 new" → "11 modules (Session 1 + Session 2)"; correct LoC claim from "~2,050" to "~2,710" (or accept ~2,700 round).

### 4.3 — 🔵 RECOMMENDED — Roadmap claims "10 Lean modules" under Session 1 close
- **Gate:** CrossPaperConsistency
- **Location:** `docs/roadmaps/Phase6q_Roadmap.md:424`
- **Observed:** The roadmap's Session 1 log header says "9 new modules under lean/SKEFTHawking/DKMBootstrap/" but then enumerates 10 modules (Wave 1a.2 + Wave 1b.1/1b.2/1b.3 + Wave 1c.1/1c.2/1c.3 + Wave 2a.2/2a.3 + Wave 2b). The number "9" appears to be an off-by-one in the count, but the enumeration is correct.
- **Evidence:** Count of bullets in lines 426-438 = 10.
- **Expected:** "10 new modules" in the Session 1 header.
- **Fix:** Replace "9 new modules" with "10 new modules" in line 424 of the roadmap.

### 5.1 — 🟡 REQUIRED — "First formally-verified analog" first-claim not ledger-backed
- **Gate:** NarrativeGrounding / FirstClaimVerification
- **Location:** `temporary/working-docs/phase6q/wave_2c_positioning.md:29`
- **Observed:** The L2-entry prose says "First formally-verified analog of the CHHK 2509.18255 transport-bootstrap MIR-style master bound on an analog-gravity substrate (graphene Dirac fluid)." This is a Gate-10 first-claim ("first formally verified X"). CHHK arXiv:2509.18255v1 was September 2025; v2 was 14 May 2026. The bound itself has been in the published literature for ~8 months. A FirstClaimLedger entry is not present (the gate is `needs-recheck` for all first-claims per READINESS_GATES.md §Gate-10 status).
- **Evidence:** No `FirstClaimLedger` node exists yet (per gate doc); no documented prior-work search appears in the working doc, the Lit-Search dispatches, the roadmap, or the strengthening-close memory.
- **Expected:** Either (a) demote to "first formally-verified analog known to the authors" / "to our knowledge, first formally-verified analog", or (b) document a prior-work search of Mathlib / Coq / Agda / Rocq before keeping the unqualified "first" claim.
- **Fix:** Add a hedge to the L2-entry prose, OR add a ledger entry documenting the prior-work search (Lean's Mathlib has no CHHK transport-bootstrap formalization; Coq/Rocq/Agda likewise — but this requires explicit verification before the unqualified "first" claim).

### 5.2 — 🟡 REQUIRED — Working doc's "graphene witness substantively non-trivial" framing overclaims relative to Lean substrate
- **Gate:** NarrativeGrounding
- **Location:** `temporary/working-docs/phase6q/wave_2c_positioning.md:12`; `lean/SKEFTHawking/DKMBootstrap/HorizonTransportBootstrap.lean:103-111`
- **Observed:** Working doc says: "graphene's collective mean free path √(τD) is bounded below by a geometric constant." The actual Lean theorem `horizon_transport_uniqueness_graphene_witness_one_half` shows `IsMIRBound grapheneDKMParameters (1/2)`, which unfolds to `1/2 ≤ √(1·1)/1 = 1` — i.e., `1/2 ≤ 1`, discharged by `norm_num`. The Lean substrate uses `grapheneDKMParameters` with τ = D = a = 1 (normalized), so what's verified is `1/2 ≤ 1` at the unit-substrate, NOT the CHHK substantive bound `0.0756 ≤ ℓ/a` on physical graphene with a = 0.246 nm. The Lean theorem is honestly substrate-level non-vacuity, but the working doc prose elides this. The HorizonTransportBootstrap.lean docstring (line 91-98) does honestly disclose "The Lean substrate-level `mirConst = 1/2` is a *safe upper bound* on the substantive Python-computed constant: `(2·β_2/(4π))^(1/3) ≈ 0.0756`."
- **Evidence:** `grapheneDKMParameters` at `E1E2CrossBridge.lean:83-93` has all five fields = 1. `IsMIRBound p mirConst := mirConst ≤ p.collectiveMeanFreePath / p.a` unfolds to `1/2 ≤ Real.sqrt(1·1)/1 = 1` — `norm_num` discharges trivially.
- **Expected:** Working doc prose explicitly notes that the Lean theorem is at the *normalized substrate* (τ = D = a = 1) and the substantive physical claim is the Python-side `0.0756 ≤ ℓ/a` against Crossno's measured value.
- **Fix:** Edit the L2-entry prose (line 29 + line 12 in the working doc) to add the qualifier "(Lean substrate at normalized parameters; substantive physical value `0.0756 ≤ ℓ/a` ships Python-side)" or similar.

### 5.3 — 🔵 RECOMMENDED — "Highest-leverage cross-bridge of Phase 6q" is interpretive
- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/DKMBootstrap/LDPBridge.lean:4`, `SK_EFT_Hawking_Inventory_Index.md:196`
- **Observed:** "HIGHEST-LEVERAGE CROSS-BRIDGE OF PHASE 6Q" is asserted multiple times. The claim is from Wave 2a.1 DR §6 (a research-intern dispatch) — not a formal-theorem result. It's an interpretive framing claim about substrate ordering.
- **Evidence:** No formal metric of "leverage" exists in the pipeline; the claim is editorial.
- **Expected:** Keep as is (it's clearly framing) but consider toning down ALL-CAPS to less assertive phrasing in the docstrings.
- **Fix:** Optional — `HIGHEST-LEVERAGE CROSS-BRIDGE` → `the load-bearing LDP cross-bridge` or similar.

### 5.4 — 🔵 RECOMMENDED — Memory file's "graphene MIR constant ≈ 0.6" prose contradicts strengthening section
- **Gate:** NarrativeGrounding / CrossPaperConsistency
- **Location:** `memory/project_phase6q_complete_2026_05_23.md:45`
- **Observed:** The memory file's "Bimodal outcome BOTH halves shipped substantively" section line 45 says "substantive `(2β₂/4π)^{1/3} ≈ 0.6` ships Python-side in deferred Wave 2b numerical companion." The same file's strengthening-close section line 21 says "the prior memo's `(2β₂/4π)^{1/3} ≈ 0.6` estimate was inaccurate by ~8×; actual value is ~0.076." Same file, two contradicting values, both visible to future readers.
- **Evidence:** Single-file inconsistency.
- **Expected:** Remove/correct the line-45 stale claim.
- **Fix:** Edit memory line 45: "≈ 0.6" → "≈ 0.0756" (or add a strikethrough/note pointing to the strengthening-section correction).

### 6.1 — 🟡 REQUIRED — IsLDPCompatibleCorrelator forward direction's "F4 positivity → LDP" claim is rate-function-by-decree
- **Gate:** AssumptionDisclosure / LeanProofSubstance
- **Location:** `lean/SKEFTHawking/DKMBootstrap/SKEFTSpecialization.lean:220-224`
- **Observed:** `chhk_positivity_yields_LDP_compatible` body: `⟨h_pos, chhk_positivity_yields_LDP_rate_function h_pos β hβ p⟩`. The IsLDPRateFunction witness for `dkm_rate_function β p` is built from `DKMParameters` alone (FDT-pinned σ² = χ·D > 0 from positivity), NOT from the F4 positivity input `h_pos`. The `h_pos` is preserved in the output pair (first component) but never used by the second component. So the "F4 positivity → LDP rate function" implication is true but the *substantive step* is "DKMParameters positivity → LDP rate function" (no F4 needed). The docstring lines 219 honestly disclose "The DR §6 Gaussian-fluctuation-regime condition is automatically satisfied at substrate level by `DKMParameters` positivity" — which means the F4 input is **not load-bearing** for the rate-function conclusion. The theorem name `chhk_positivity_yields_LDP_compatible` implies F4 is the engine, when the engine is actually `DKMParameters.χ_pos + DKMParameters.D_pos`.
- **Evidence:** Lines 220-224 show `h_pos` passed-through but unused in `chhk_positivity_yields_LDP_rate_function`'s body (LDPBridge.lean:143-147 has `_h_pos` underscore).
- **Expected:** Rename or restructure to make the substantive engine explicit: e.g., `dkm_parameters_yield_LDP_compatible` taking `(h_pos, β, hβ, p)` and producing `IsLDPCompatibleCorrelator G β p` — with a docstring note that the F4 input is bundled-only-for-output, not load-bearing.
- **Fix:** Either rename, or add a docstring sentence: "Substantive note: the F4 positivity hypothesis `h_pos` is preserved in the output pair but does not enter the rate-function discharge — the rate function is `DKMParameters`-determined."

### 6.2 — 🔵 RECOMMENDED — Phase 6q axiom-set bridges (F4/F5/F6) require the action-correlator link as undisclosed in roadmap
- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/DKMBootstrap/AxiomSet.lean:88-104, 111-124, 129-142`
- **Observed:** The bridge theorems `dkm_positivity_from_skeft_axioms`, `dkm_uhp_analyticity_from_skeft_axioms`, `dkm_pt_symmetry_from_skeft_axioms` all require an `IsDKMSpectralFunction action G` hypothesis (the action-correlator link) in addition to the SKEFTAxioms input. The link itself is a substantial structural assumption — it bundles the F4/F5/F6 implications. In the roadmap Session 1 entry (line 427), this is summarized as "F4 / F5 / F6 bridges from SKEFTAxioms" without explicitly flagging the link hypothesis. The Lean docstrings (lines 67-72 of AxiomSet.lean) DO disclose it; the roadmap and inventory do not.
- **Evidence:** AxiomSet.lean lines 73-81 define `IsDKMSpectralFunction` as a 3-conjunct structure. The bridge theorems consume this as a hypothesis. The only non-trivial witness is `trivialLink : IsDKMSpectralFunction zeroAction zeroCorrelator` (line 229), which has all three conjuncts vacuous on the zero substrate.
- **Expected:** Roadmap Session 1 + inventory summary acknowledge that the F4/F5/F6 bridges are conditional on the action-correlator link, NOT free reductions from SKEFTAxioms.
- **Fix:** Add a sentence to roadmap line 427 + inventory line 187: "Bridge theorems require an additional action-correlator link hypothesis (`IsDKMSpectralFunction`) which carries the spectral-function-of-action content; trivially-discharged on the zero substrate."

### 7.1 — 🟡 REQUIRED — Inventory LoC undercount ~2,050 vs actual 2,709 for DKMBootstrap
- **Gate:** NumericalFreshness
- **Location:** `SK_EFT_Hawking_Inventory_Index.md:106`
- **Observed:** Inventory line 106 says DKMBootstrap is "11 modules (~2,050 LoC)". Actual: 11 modules, 2,709 LoC (computed by `wc -l lean/SKEFTHawking/DKMBootstrap/*.lean`). Drift: 2709/2050 = 32% undercount.
- **Evidence:** `wc -l lean/SKEFTHawking/DKMBootstrap/*.lean` total = 2709.
- **Expected:** Match within ~5%.
- **Fix:** Update inventory line 106 to "~2,710 LoC".

### 7.2 — 🟡 REQUIRED — Pytest count: roadmap + memory + inventory say 4149; counts.json says 4218
- **Gate:** NumericalFreshness
- **Location:** `docs/counts.json` (4218); `docs/roadmaps/Phase6q_Roadmap.md:486`, memory line 35, inventory line 55 — all say "pytest 4149/0"
- **Observed:** `counts.json` `pytest_cases: 4218`; the roadmap, inventory, and memory all say "4149". Live `pytest --collect-only` reports "4150/4218 tests collected (68 deselected)" — i.e., default run collects 4150 (4218 total minus 68 deselected slow tests). The 4149 number may come from a per-marker count that excluded one borderline case, or it's stale from before B.1's 23 new tests landed but counts.json was regenerated. Either way: the three text artifacts and the canonical `counts.json` disagree on a load-bearing pytest count.
- **Evidence:** `counts.json` line 414: `"pytest_cases": 4218`. Live collection: 4150 collected. Roadmap line 486 + memory line 35 + inventory line 55: "pytest 4149/0".
- **Expected:** Single canonical pytest count, sourced from `counts.json`, reported consistently across the three text artifacts.
- **Fix:** Decide canonical reporting convention (e.g., "4218 total / 4150 default-run / 68 slow-deselected") and propagate.

### 7.3 — 🔵 RECOMMENDED — Roadmap "~1,800 LoC" → actual Session 1 LoC ≈ 2,368 (=2709 − 341 BEC)
- **Gate:** NumericalFreshness
- **Location:** `docs/roadmaps/Phase6q_Roadmap.md:9, 424`
- **Observed:** Roadmap claims "9 new Lean modules (~1,800 LoC)" for Session 1. Session 1 shipped 10 modules totalling 2368 LoC (2709 - 341 LoC for BECBogoliubovBosonicGrowth shipped in Session 2). Drift: 2368/1800 = ~32% undercount, consistent with the inventory's ~30% undercount.
- **Evidence:** `wc -l lean/SKEFTHawking/DKMBootstrap/*.lean` (minus BEC) = 2368.
- **Expected:** Match within ~5%.
- **Fix:** Update roadmap to "~2,370 LoC" for Session 1 + "~340 LoC" for Session 2 + "~2,710 LoC total".

### 8.1 — 🔵 RECOMMENDED — No production-run claims in Phase 6q — Gate 8 vacuously passes (confirmation)
- **Gate:** ProductionRunHealth
- **Location:** All Phase 6q artifacts
- **Observed:** `grep -rn "ProductionRun\|Monte Carlo\|numerical evidence\|MC evidence" lean/SKEFTHawking/DKMBootstrap/ src/dkm_bootstrap/ temporary/working-docs/phase6q/` returns nothing. The Python `crossno_graphene_satisfies_chhk_bound()` reports a measured-data check but it's not "MC evidence." Gate 8 passes vacuously.
- **Evidence:** No production-run claims in the substrate-level Phase 6q artifacts.
- **Expected:** Gate 8 status `passed` (vacuously).
- **Fix:** None.

## QI Candidate

**Pattern: post-strengthening documentation drift.** The 2026-05-25 strengthening pass correctly updated the Python source, the canonical roadmap section §B.1, the inventory module-map, and the strengthening-close section of the project-complete memory — but left stale `0.6` references in (a) the working doc body (`wave_2c_positioning.md`), (b) the project-complete memory's "Bimodal outcome BOTH halves" section, (c) two Lean module docstrings (`HorizonTransportBootstrap.lean` lines 22-24, `E1E2CrossBridge.lean` line 80). The stale references cluster at "intro prose" / "TL;DR" sections that were authored at Phase 6q-close (2026-05-23) and not revisited by the strengthening pass. A QI register entry: "Strengthening-pass remediation of numerical values should sweep ALL docstrings/working-docs/memory files in scope, including intro prose, not just the targeted strengthening items." Suggested mitigation: `scripts/validate.py --check phase_value_freshness` that scans for known-stale numerical literals in the Phase-X working-doc set after a closing-update.

**Pattern: 5 secondary bibkeys in load-bearing Lean docstrings without `CITATION_REGISTRY` backing.** The DKMBootstrap modules cite five external papers in their `References:` blocks (Yin-Lucas, Kuwahara-Saito, Abanin-De Roeck-Huveneers, Toledo-Tude & Eastham, Parker-et-al.) that are load-bearing substrate references for the F3 bound's underlying physics. None of these have CITATION_REGISTRY entries. The current pipeline's `validate.py --check citation_primary_sources_present` covers paper `.tex` bibkeys but not Lean docstring references. Suggested mitigation: extend the citation-registry-presence check to scan `lean/SKEFTHawking/**/*.lean` `References:` blocks for `arXiv:<id>` patterns and report missing-registry-entry findings.
