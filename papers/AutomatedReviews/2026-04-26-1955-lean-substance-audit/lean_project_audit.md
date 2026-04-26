---
audit: lean-project-substance
date: 2026-04-26
auditor: lean-substance-auditor
scope: full lean/SKEFTHawking/ (172 modules, 4115+ theorems, 0 sorry, 1 axiom)
---

## Summary

Project compiles clean and the build invariants (zero sorry, exactly one
registered axiom `gapped_interface_axiom`) hold. The audit nevertheless
surfaces **substantial substance debt** concentrated in three systemic
patterns:

1. ~98 placeholder `theorem … : True := trivial` "module-summary" markers.
   Most are docstring-as-theorem; harmless on their own but they masquerade
   as theorem-count contributions and hide a few load-bearing placeholders
   (e.g. `equivalence_is_monoidal`, `equivalence_is_braided`,
   `ocneanu_rigidity_placeholder`, `fusion_to_tqft_placeholder`,
   `tpf_c3_conditional`).
2. ~13 numeric/arithmetic-tautology theorems whose statement reads as a
   physics or category-theory result but whose body is `:= rfl` on a
   syntactic identity (`(16 : ℕ) = 16`, `(1 : ℝ) = 1`, `g₁ * g₂ = g₁ * g₂`,
   `Fintype.card G = Fintype.card G`, `n_transport = n_transport`,
   `ddMul_one_left k G = ddMul_one_left k G`).
3. **24 explicit `set_option maxHeartbeats N` overrides on theorem bodies**
   in `Uqsl3Hopf.lean`, `Uqsl2AffineHopf.lean`, `QuantumGroupCoproduct.lean`,
   and `QuantumGroupAntipode.lean` — direct violation of CLAUDE.md pipeline
   invariant 10 (the `ExtractDeps.lean` carve-out does not apply here;
   these are `theorem`/`private theorem` bodies).

Aggregate severity counts (one finding per anti-pattern instance class,
not per occurrence):

- **BLOCKER:** 4
- **REQUIRED:** 9
- **RECOMMENDED:** 7

No new axioms beyond the registered one. No Class 4 paper-staleness
discovered in the spot-check sample of 16 `formulas.py` Lean refs (all
resolved). One `.backup` and one `.aristotle` file present in the source
tree (build artifacts that should not ship).

---

## Findings

### 1. Class 6 BLOCKER — 14 heartbeat overrides on `Uqsl3Hopf.lean` theorem bodies

- **Module/Lines:** `lean/SKEFTHawking/Uqsl3Hopf.lean:1108, 1391, 1667, 1955, 2565, 2949, 3294, 3633` (and 6 more — 14 total per `grep`)
- **Pattern:** `set_option maxHeartbeats 800000 in\nprivate theorem …`
- **Issue:** Pipeline invariant 10 explicitly forbids `set_option maxHeartbeats N` on `theorem` / `private theorem` / `lemma` bodies — "a proof hitting the heartbeat limit is evidence of a wrong proof architecture, not a compute shortage." The exemption documented in CLAUDE.md is for `ExtractDeps.lean` only (metaprograms walking the env). Hopf-algebra coproduct/antipode proofs are not metaprograms and can be decomposed into `have` sub-lemmas — the precedent in `QuantumGroupCoproduct.lean:786` says exactly this in the comment introducing its decomposed approach: "Decomposed into sub-lemmas (Phase 1 expand + per-sector hypotheses + final assembly) to stay within default heartbeat budget, **unlike Uqsl3Hopf's monolithic 800k-heartbeat proof**." The author already knew this was a debt.
- **Fix:** Decompose each 800k-heartbeat coproduct/antipode lemma in `Uqsl3Hopf.lean` along the same Phase-1-expand → per-sector → final-assembly pattern used in `QuantumGroupCoproduct.lean`. Remove the `set_option maxHeartbeats` lines.

### 2. Class 6 BLOCKER — 9 heartbeat overrides on `Uqsl2AffineHopf.lean` theorem bodies

- **Module/Lines:** `lean/SKEFTHawking/Uqsl2AffineHopf.lean:2061, 2330, 3282, 4148, 4945, 5080, 5198, 5311, 5627, 5705`
- **Pattern:** `set_option maxHeartbeats 400000 in` (and 800k/2M on the larger ones), each immediately followed by `private theorem affComulFreeAlg_Serre…`/`private theorem affAntipode…`. The file's own header comment at line 1518 explicitly lists `set_option maxHeartbeats N` as a pipeline-violating anti-pattern, then 500 lines later violates it 9 times.
- **Issue:** Same as finding 1 — Serre-relation respect proofs at 4 generators (E0, E1, F0, F1) and 4 K-elements should decompose into sector helpers, not bump heartbeats up to 2M.
- **Fix:** Apply the same decomposition the author committed to in the file's own anti-pattern-warning comment. Each 4-generator Serre identity has 4 obvious sub-cases that can be pre-proved as `have` sub-lemmas with default heartbeat budget.

### 3. Class 6 BLOCKER — 3 heartbeat overrides + 1 maxRecDepth in `QuantumGroup{Coproduct,Antipode}.lean`

- **Module/Lines:** `QuantumGroupCoproduct.lean:789, 1125`; `QuantumGroupAntipode.lean:353, 541, 714` (the last is `set_option maxRecDepth 8000 in` inside a tactic block).
- **Pattern:** identical to findings 1–2.
- **Issue:** `QuantumGroupCoproduct.lean:789` says in a comment that it was specifically decomposed to stay within budget, then the next line sets `maxHeartbeats 800000`. The decomposition succeeded structurally but did not eliminate the budget lift — finish the job.
- **Fix:** Either reduce the 800k lift to default by completing decomposition, or document the exception with a structural justification matching `ExtractDeps`-style metaprogram carve-out (decomposition is exhausted). Currently the comment claims the former but the code asserts the latter.

### 4. Class 1 BLOCKER — `RotorModesGapped : Prop := True` is vacuous

- **Module/Line:** `lean/SKEFTHawking/TPFEvasion.lean:53`
- **Pattern:** `def RotorModesGapped : Prop := True  -- axiomatized: open question in TPF paper`
- **Issue:** This is exactly the failure pattern called out in `feedback_tracked_hypothesis_nontrivial.md`: an "axiomatized" Prop body of `True`. The downstream theorem `tpf_c3_conditional : ¬RotorModesGapped → True := by intro _; trivial` (line 59-61) is therefore inhabited by any inhabitant of `False → True` — i.e. discharges no obstruction. It claims to formalize "if rotor modes are gapless, C3 is violated" but actually formalizes nothing. The MajoranaRung.lean header comment at line 213 says the Stage-13 review caught this exact pattern there ("the prior encoding `: Prop := True` was vacuous"), then re-parameterized it. TPFEvasion.lean did not get the same treatment.
- **Fix:** Parameterize `RotorModesGapped` over a spectral-gap predicate (e.g. `RotorModesGapped (rotorSpec : ℝ → ℂ) : Prop := ∃ Δ > 0, ∀ ω ∈ spec, Δ ≤ |ω|`) following the `H_LeptonNumberViolated`/`H_PMNSAnglesFromSubstrate_eps` parameterization pattern. Then re-state `tpf_c3_conditional` so its hypothesis bites.

### 5. Class 1 REQUIRED — `MinimalModularExtension` structure: 3 of 3 fields are `: True`

- **Module/Line:** `lean/SKEFTHawking/Z16Classification.lean:107-113`
- **Pattern:**
  ```
  structure MinimalModularExtension (B : SuperModularCategoryData) where
    dim_doubled : True  -- formal: D²(C) = 2 · D²(B)
    is_modular : True
    fermion_absorbed : True
  ```
- **Issue:** Every field of this load-bearing structure is `True`. Any inhabitant of the structure (including `⟨trivial, trivial, trivial⟩`) "satisfies" all three constraints. The 16-fold way result `sixteen_fold_way_conditional : (16 : ℕ) = 16 := rfl` (line 130) is then a tautology that says nothing about modular extensions.
- **Fix:** Replace the three `True` fields with concrete propositions over the `B : SuperModularCategoryData` carrier (dimension doubling: `globalDim C = 2 * globalDim B`; modularity: `Nonempty (NonDegenerateBraided C)`; fermion absorption: a specific inclusion property). Until these are typeable, mark the file `WIP` and remove the misleading `sixteen_fold_way_conditional` headline.

### 6. Class 1 REQUIRED — `GappedInterfaceConjecture` structure: 3 of 3 conjectural fields are `: True`

- **Module/Line:** `lean/SKEFTHawking/SMGClassification.lean:159-169`
- **Pattern:**
  ```
  structure GappedInterfaceConjecture where
    smg_data : SMGSymmetryData
    anomaly_free : smg_data.anomaly_free
    gap_exists : True  -- formal: ∃ H_int, HasSpectralGap H_int
    symmetry_preserved : True
    chiral_boundary_gapless : True
  ```
- **Issue:** The conjecture's three load-bearing claims (gap exists, symmetry preserved, chiral boundary gapless) are all encoded as `True`. The companion `class HasSpectralGap` (line 126-134) has the same problem on `unique_ground_state : True` and `uniform_in_volume : True`. The structure is non-empty and all consequences derived from it are vacuous in those fields.
- **Fix:** Either (a) lift the three conjectural fields to genuine Props (e.g. `gap_exists : ∃ H : InteractionHamiltonian, HasSpectralGap H`), or (b) collapse the structure into the existing `gapped_interface_axiom` in `SPTClassification.lean` so it doesn't compete with the registered axiom.

### 7. Class 1 REQUIRED — `ChiralityWall3DStatus` four "gap status" fields are `: True`

- **Module/Line:** `lean/SKEFTHawking/GaugingStep.lean:234-244`
- **Pattern:**
  ```
  structure ChiralityWall3DStatus where
    gap1_axiomatized : True
    gap2_conditional : True
    gap3_mod8_proved : True
    gap3_mod16_hypothesis : True
    three_gaps : (3 : ℕ) = 3
  ```
- **Issue:** The four gap-status fields form a meaningless conjunction; `chirality_wall_status` (lines 247-252) constructs an inhabitant trivially. The bridge theorem `gap1_enables_disentangler : True := trivial` (line 260) and the surrounding "Bridge Theorems" section then derive a chain of trivial implications.
- **Fix:** Each "gap status" field should reference an actual Prop or Lean theorem witnessing its content (e.g. `gap1_axiomatized := SPTClassification.gapped_interface_axiom`'s registered status; `gap3_mod8_proved := AlgebraicRokhlin.<theorem-name>`). If the goal is a documentation summary, write a Lean string-literal docstring, not a structure.

### 8. Class 1 REQUIRED — `ChevalleyInvolution`/`LoopAlgebraSl2` 4 fields are `: True`

- **Module/Line:** `lean/SKEFTHawking/OnsagerAlgebra.lean:185-203`
- **Pattern:** `is_involution : True`, `negates_cartan : True`, `swaps_roots : True`, `infinite_dim : True`
- **Issue:** The Chevalley involution θ of sl₂ has concrete finite content (θ² = id, θ(h) = -h, θ(e) = f, θ(f) = e); the loop-algebra dimension is provable from Mathlib's Laurent polynomial machinery. None of these are encoded — all four are `True`. The downstream consequences (Onsager → su(2) contraction) therefore rest on an empty foundation in this module's part of the chain.
- **Fix:** Use the existing Mathlib `LieAlgebra.Sl2` infrastructure (or define θ on `Matrix (Fin 2) (Fin 2) ℂ` directly) and prove the involution/negation/swap properties. The `infinite_dim` field follows from `LaurentPolynomial` being infinite-dimensional over its base.

### 9. Class 2 REQUIRED — Six `:= rfl` theorems whose statement reads as physics but body is a pure identity

- **Modules/Lines:**
  - `lean/SKEFTHawking/Z16Classification.lean:96` `theorem sVec_fermion_dim : (1 : ℝ) = 1 := rfl` ("The fermion f in sVec has quantum dimension 1")
  - `Z16Classification.lean:130` `theorem sixteen_fold_way_conditional : (16 : ℕ) = 16 := rfl` ("16-fold way theorem (conditional on existence)")
  - `lean/SKEFTHawking/DrinfeldCenterBridge.lean:240` `theorem anomaly_matching_untwisted : ddMul_one_left k G = ddMul_one_left k G := rfl` ("Anomaly matching through the Drinfeld double")
  - `DrinfeldCenterBridge.lean:296` `theorem vecG_simples_count : Fintype.card G = Fintype.card G := rfl` ("The number of simple objects in Vec_G ... equals |G|")
  - `lean/SKEFTHawking/GaugeEmergence.lean:172` `theorem abelian_dw_fusion ... : g₁ * g₂ = g₁ * g₂ := rfl` ("The fusion rules of Z(Vec_G) for abelian G are completely determined by ...")
  - `lean/SKEFTHawking/DiracFluidSK.lean:136` `theorem fdr_preserves_transport_count (n_transport : ℕ) : n_transport = n_transport := rfl` ("the CGL FDR constraint preserves the transport coefficient count")
- **Issue:** Each docstring claims a non-trivial physical or categorical result; each body is a syntactic identity. None of these theorems use the named hypothesis or carry physical content. They look like real theorems in `lean_deps.json` and skew the 4115 count.
- **Fix:** For each one, either (a) restate with content (e.g. `vecG_simples_count` should equate the simple-object count of `VecG_Cat` to `Fintype.card G` via the actual GradedObject machinery), or (b) demote to `example` with a docstring explaining the pending formalization, or (c) delete and link the docstring narrative to the genuinely-proved upstream theorem (e.g. `sVec_global_dim`).

### 10. Class 2 REQUIRED — `equivalence_simples_via_functor` proof bypasses the named functor

- **Module/Line:** `lean/SKEFTHawking/CenterFunctor.lean:104-107`
- **Pattern:**
  ```
  /-- The equivalence implies |G|² simples (proved independently). -/
  theorem equivalence_simples_via_functor :
      Fintype.card G ^ 2 = Fintype.card G * Fintype.card G :=
    center_simples_count G
  ```
- **Issue:** The name asserts `via_functor` but the statement is `pow_two`-equivalent and the body invokes `center_simples_count` (a counting fact, not the functor). The docstring even admits "(proved independently)." The accompanying `equivalence_is_monoidal : True := trivial` and `equivalence_is_braided : True := trivial` (lines 110, 113) on the same module then complete the placeholder cluster.
- **Fix:** Rename to `centerFunctor_simples_count_squared` or merge into the existing `dz2_simple_count` / S₃CenterAnyons direct proofs. Promote `equivalence_is_monoidal` / `equivalence_is_braided` to genuine statements once `H_CF2` is discharged, or remove them with a "see H_CF2 hypothesis" docstring.

### 11. Class 2 REQUIRED — `pillar3_onsager_dg`, `pillar3_contraction_target` headline `:= rfl` identities

- **Module/Line:** `lean/SKEFTHawking/ChiralityWallMaster.lean:107, 110`
- **Pattern:**
  ```
  theorem pillar3_onsager_dg : DG_COEFF = 16 := rfl
  theorem pillar3_contraction_target : sl2_dim = 3 := rfl
  ```
- **Issue:** `DG_COEFF` and `sl2_dim` are `def`s whose definitions are `16` and `3` respectively (verified upstream). The "Pillar" naming convention is paper-prose-load-bearing — paper8_chirality_master uses the Pillars as headline contributions. Stating `DG_COEFF = 16` as a theorem proves `16 = 16` — the actual content (DG/Onsager has 16-coefficient, Onsager contracts to 3-dimensional sl₂) lives in upstream modules.
- **Fix:** Replace these with theorems that quote the actual upstream content via name (e.g. `pillar3_onsager_dg : OnsagerAlgebra.DG_coeff = AlgebraicRokhlin.cobordism_classification_value := rfl_or_real_proof`), so the master theorem references substantive names rather than pre-evaluated literals.

### 12. Class 1/2 RECOMMENDED — 96+ `theorem <module>_summary : True := trivial` placeholders

- **Modules/Lines:** 96 instances across `DrinfeldDoubleRing.lean:194`, `Uqsl3.lean:391`, `SU3kFusion.lean:300`, … (full list in grep output: every module ending with a `*_summary : True := trivial`).
- **Pattern:** `theorem <module>_summary : True := trivial`
- **Issue:** Each is a docstring-as-theorem; on its own each is harmless and serves as a documentation hook. In aggregate they (a) inflate the 4115-theorem count by ~2.3% with content-free entries, (b) violate Gate 5 LeanProofSubstance for any paper that cites a `*_summary` theorem (none currently do, but adversarial reviewers have flagged this pattern before — `feedback_strengthening_pass_paper_drift.md`), and (c) create 96 false hits when grep-checking for "all theorems compile" green.
- **Fix:** Choose one of:
  - Convert all `*_summary : True := trivial` to `/-! ## Summary` markdown blocks (no theorem) — preferred.
  - Promote a meaningful per-module headline theorem (e.g. `DrinfeldDoubleRing.summary : DG.IsRing := DG.ring_struct`) so the summary is non-vacuous.
  - Tag each as `private` and exclude from the 4115 count via `validate.py` — preserves the documentation hook without paper-substance contamination.

### 13. Class 1 RECOMMENDED — `gap1_enables_disentangler : True := trivial`

- **Module/Line:** `lean/SKEFTHawking/GaugingStep.lean:258-260`
- **Pattern:**
  ```
  theorem gap1_enables_disentangler :
      -- gapped_interface_axiom → disentangler exists (conditional chain)
      True := trivial
  ```
- **Issue:** Header section "8. Bridge Theorems" advertises a chain from the registered `gapped_interface_axiom` to disentangler existence. Body is `True`. This is the kind of "Bridge" theorem that an adversarial reviewer would point at first — the semantic claim is in the comment, the formal claim is `True`.
- **Fix:** State the actual implication (`SPTClassification.gapped_interface_axiom spt h_free → ∃ W : SymmetryDisentangler, …`). Or delete and reference the upstream axiom directly.

### 14. Class 1 RECOMMENDED — `ocneanu_rigidity_placeholder`, `fusion_to_tqft_placeholder`

- **Module/Line:** `lean/SKEFTHawking/FusionCategory.lean:150, 153`
- **Pattern:** `theorem ocneanu_rigidity_placeholder : True := trivial` and `theorem fusion_to_tqft_placeholder : True := trivial`
- **Issue:** These two theorems are named after major mathematical results (Ocneanu rigidity, Fusion → TQFT) but bodies are `True`. The docstring is "(placeholder for Wave 4C)." Naming a theorem after a real theorem and proving it `True := trivial` is exactly the substance failure that Gate 5 exists to catch — a paper citing `FusionCategory.ocneanu_rigidity_placeholder` would textually claim Ocneanu rigidity is formalized.
- **Fix:** Rename to `wave4C_ocneanu_rigidity_TODO` (no risk of looking proved), or move the `True` placeholders out of the `theorem` namespace into a `def TODOMarker` registry. Search for any paper reference to these names before changing — `gh grep` `papers/` came up empty for both.

### 15. Class 3 RECOMMENDED — `ADW_emerges_linearized_EFE_under_Vergeles` extracts its conclusion from its hypothesis

- **Module/Line:** `lean/SKEFTHawking/LinearizedEFE.lean:411-431`
- **Pattern:**
  ```
  def H_VergelesNGModeProjection (Λ N_f α_ADW : ℝ) : Prop :=
    0 < α_ADW ∧ 0 < Λ ∧ 0 < N_f ∧
    G_N_emerg Λ N_f α_ADW = α_ADW * (12 * Real.pi / (N_f * Λ ^ 2))

  theorem ADW_emerges_linearized_EFE_under_Vergeles
      {Λ N_f α_ADW : ℝ}
      (h : H_VergelesNGModeProjection Λ N_f α_ADW) :
      G_N_emerg Λ N_f α_ADW =
        α_ADW * (12 * Real.pi / (N_f * Λ ^ 2)) :=
    h.2.2.2
  ```
- **Issue:** The author's docstring is honest: "This is a tautology by construction of `G_N_emerg`; it serves as the formal statement of the bridge ..." The conclusion is literally a conjunct of the hypothesis. The pattern is structurally identical to the Phase 5w W10c failure documented in `feedback_subagent_lean_quality.md` ("∃-C-absorption made them vacuous"). The bridge theorem encodes no transport from microscopic → macroscopic — the equality is asserted as part of the hypothesis itself.
- **Fix:** Restructure: the hypothesis should encode "the NG-mode two-point function has spin-2 KG tensor structure" (a Prop on a function), and the theorem should *derive* `G_N_emerg = α_ADW · 12π/(N_f Λ²)` from that structural assumption + the canonical Sakharov–Adler integral. If the integral derivation is not yet in scope, tag the theorem `_DEFINITIONAL` to match `feedback_tracked_hypothesis_nontrivial.md` precedent.

### 16. Class 5 RECOMMENDED — `.aristotle` and `.backup` files in source tree

- **Module/Lines:** `lean/SKEFTHawking/Uqsl2AffineHopf.lean.aristotle` (1111+ lines; contains `theorem uqsl2_affine_hopf_summary : True := trivial`); `lean/SKEFTHawking/Uqsl2Hopf.lean.backup` (427 lines; contains `theorem uqsl2_hopf_summary : True := trivial`).
- **Pattern:** Build artifacts shipped in source tree.
- **Issue:** These are excluded from `lake build` by extension but may pollute grep, count audits, and downstream tooling. The `.aristotle` file likely represents an Aristotle-batch export awaiting integration.
- **Fix:** Move both to `temporary/working-docs/` per `reference_working_docs.md`, or add a `.gitignore` rule for `*.lean.{backup,aristotle}` and remove from working tree.

### 17. Class 7 RECOMMENDED — `private theorem` count in `Uqsl3Hopf.lean` is 189 with monolithic 800k-budget bodies

- **Module/Line:** `lean/SKEFTHawking/Uqsl3Hopf.lean` (5235 lines, 189 theorem-keyword declarations, 14 heartbeat-bumped bodies)
- **Pattern:** Multiple `private theorem` bodies of 50–200+ lines under `set_option maxHeartbeats 800000 in`.
- **Issue:** Decomposition gap (Class 7) compounding Class 6. The pattern of one big proof with 800k heartbeats instead of 5 sub-proofs each at default budget is the architecture-shortcut signature CLAUDE.md invariant 10 was written to prevent.
- **Fix:** This is the same as findings 1–3 but recorded as a separate Class-7 systemic finding so the QI register has a "decomposition-debt" entry distinct from the "heartbeat-policy-violation" entry.

---

## Stretch QI candidates

1. **`validate.py --check vacuous_summary_theorems`** — flag any `theorem.* : True := trivial` whose name does not match a documented allowlist (e.g. `*_summary` markers may be acceptable; everything else is not). Alerts on findings 4, 12, 13, 14.

2. **`validate.py --check rfl_identity_theorems`** — flag any `theorem … : x = x := rfl` or `theorem … : N = N := rfl` (where N is a numeric literal) outside an explicit-test context. Alerts on finding 9.

3. **`validate.py --check heartbeat_policy`** — extend the existing pipeline-invariant-10 check to flag any `set_option maxHeartbeats N in` immediately preceding a `theorem`/`lemma`/`example` declaration (excluding the documented `ExtractDeps.lean` carve-out). Alerts on findings 1–3, 17.

4. **`validate.py --check structure_field_substance`** — flag any structure declaration with ≥1 field of type `True`. Alerts on findings 5, 6, 7, 8.

5. **`validate.py --check hypothesis_used_in_proof`** — flag any theorem whose declared hypotheses do not appear in the proof body's identifier set. Alerts on finding 10. (This is hard; a coarse approximation is "no hypothesis name appears as a token in the proof body.")

6. **Adversarial-reviewer rule update.** Add the patterns "every-field-of-structure-is-`True`" and "conclusion-is-conjunct-of-hypothesis" to the Gate 5 LeanProofSubstance reviewer's heuristic checklist. Both surfaced multiple times in this audit and neither is currently caught at the syntactic-extractor level.

7. **Working-doc cleanup.** Move `.lean.{backup,aristotle}` out of the source tree and add a `lake exec check` step that rejects them.
