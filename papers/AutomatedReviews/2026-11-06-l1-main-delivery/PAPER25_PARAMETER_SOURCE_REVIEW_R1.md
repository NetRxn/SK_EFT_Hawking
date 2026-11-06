# Paper25 parameter/source review R1

Verdict: ACCEPT within source, consumer-mapping and original finding-control repair scope. No introduced blocking discrepancy found. Candidate baseline a3ceb535231b54d82a751a0a0509521ff08f76d6; exact three-file dirty diff SHA256 df50bbd54a92350186e49b1b833903d1621d5825f4465fd210bf329ac31104e3. This is independent review of the actual frozen source, not a full sentence-walker, full graph execution, project-gate pass, scientific BUILD acceptance, human approval or canonical finding closure.

## Actual consumer mapping

All fourteen declared identities are unique and present as actual PARAMETER_PROVENANCE keys. The first seven also remain in the accepted L1 declaration. The mapping is justified by actual manuscript/helper bodies, not merely the registry's new key_claims.

| Existing key | Actual Paper25 consumer |
|---|---|
| GW.C_GW_DEVIATION_UPPER_BOUND | paper_draft.tex:89 asymmetric +7e-16 source bound. |
| GW.C_GW_DEVIATION_LOWER_BOUND | paper_draft.tex:89 asymmetric -3e-15 source bound. |
| GW.C_GW_TWO_SIDED_CAP | paper_draft.tex:90-93 adopts symmetric3e-15; tables.py:20-27 uses the canonical cap in stable width; ligo_constraint_check.py:66-77 uses it in endpoint ratios. |
| GW.CHI_VEST_NATURAL_LOWER | paper_draft.tex:126-129 adopts0.1; tables.py:40-53 passes the exact canonical endpoint to the ratio helper. |
| GW.CHI_VEST_NATURAL_UPPER | Same actual consumers for10. |
| GW.GW170817_PEAK_FREQ_HZ | paper_draft.tex:339-344 uses numerical probe100; retained legacy key identifies the actual adopted model input, without a measured peak or physical-band claim. |
| GW.GAMMA_H_VESTIGIAL_DEFAULT | Same paragraph assumes coefficient1e-30 before multiplication to obtain bound1e-28. |
| GRAV.N_F_PER_GEN_NO_NU_R | paper_draft.tex:427-444 imports the companion's count choices behind its0.40–1.27 comparison; companion paper23_linearized_efe/paper_draft.tex:343-348 explicitly lists15. |
| GRAV.N_F_PER_GEN_WITH_NU_R | Same comparison and companion passage explicitly lists16. |
| GRAV.N_F_THREE_GEN_NO_NU_R | Same comparison and companion passage explicitly lists45. |
| GRAV.N_F_THREE_GEN_WITH_NU_R | Same comparison and companion passage explicitly lists48. |
| GRAV.ALPHA_ADW_LOWER | Paper25:435-444 compares the conditional matching values with adopted lower endpoint0.1. |
| GRAV.ALPHA_ADW_UPPER | Same passage compares with adopted upper endpoint10. |
| GRAV.SAKHAROV_COEFFICIENT | Paper25:429-435 uses12pi explicitly in induced coupling and alpha*=Nf/(12pi). |

The final seven are separate whole-manuscript Newton-coupling comparison coverage, not extra requirements invented for original finding2.3. Paper25:438-444 explicitly leaves the kernel's Dirac versus companion Weyl-count convention unreconciled, distinguishes alpha_ADW from chi_vest, and makes the Planck-anchor matching conditional. Their matching numerical windows do not identify the physical responses or derive either window.

No operational GW.CHI_VEST_DEFAULT is needed for the exact algebraic unity witness. No GW.GW_FREQ_HZ_LOWER/UPPER is used: the manuscript does not consume the10–10000Hz scan, and its correction supplies no physical band. The probe alias is not counted twice. No numerical C_LIGHT_M_S is used in the relative-speed law: symbolic c cancels. Likewise symbolic Planck-anchor cancellation yields Nf/(12pi) without numerical G_N_OBS_GEV_M2 or M_PLANCK_GEV. These exclusions preserve the distinction between numerical inputs and symbolic hypotheses; this is not a census of every plotting-grid or proof numeral.

## Producer and control contract

Read actual scripts/build_graph.py:400-455: extract_parameter_nodes unconditionally constructs id param:<key> with type Parameter for every provenance entry; status affects verification metadata, not target existence/type. Read extract_paper_nodes:1005-1086: filesystem discovery plus the actual Paper25 registry entry constructs paper:paper25_gravitational_waves of type Paper. Read extract_depends_on_edges:3769-3815: it emits one DEPENDS_ON for each explicit existing target, deduplicates pairs, and has no approval test that could hide an unverified dependency. platforms=[] contributes no additional platform-derived dependencies. Consequently all fourteen identities are supported by the current producer's source contract; none is an unknown or duplicate target.

I did not execute these extractors. Their normal registry imports traverse src.core.__init__ into scientific and Aristotle modules; preserving this assignment's no-native/no-evaluator boundary takes priority over an additional execution witness. This is a static producer/key/type proof, not independent dynamic graph output. ROOT's actual original-control terminal receipts provide separate dynamic evidence for the seven GW targets across both papers; they do not by themselves test the seven GRAV edges.

The strengthened original2.3 Verify now asserts the complete seven-key cross-product for BOTH papers and filters actual target-node type Parameter. It retains the original finding heading/identity, infra lane, recommended severity and ParameterProvenance gate. Location now names actual registry and both graph identities. Expected/Fix and historical Observed/Evidence are conserved; no weaker passing condition replaces the original repair.

I read exact command and red/green stdout/stderr/JSON receipts. RED return1 reports exactly seven missing Paper25 GW targets; GREEN return0 prints the complete fourteen original GW cross-paper edges message. The receipts are ROOT execution evidence, not reviewer reruns. The command checks dependency visibility, not scientific parameter verification or provenance approval. Gate3 may now honestly surface unverified/projected inputs.

## Exact preservation and accepted source lineage

Independent read-only git-show/AST comparisons against the exact baseline establish PARAMETER_PROVENANCE AST identity in full: values, human nulls/history, tiers and notes are conserved. Only PAPER_DEPENDENCIES.paper25_gravitational_waves differs; L1 and every other entry are AST-identical. CITATION_REGISTRY changes only Abbott2017GW170817Detection, and only its provides field. The actual git diff bytes equal the supplied patch exactly, and only the three assigned paths differ.

I read actual archived l1-main-composed-source-review-r1.md inside INDEPENDENT_MAIN_REVIEWS_AND_CLAIMS.zip associated with accepted69f92d1ee. It accepts L1 dependency metadata and conditional Paper25 consumer substance at source scope, while retaining original physical BUILD. I read actual l1-gw-provenance-independent-r3.md and actual-application-independent-r4.md inside GW_PROVENANCE_R3_EVIDENCE.zip associated with9d645b887. R3 examines the detection paper's real time-frequency representation, source table and30–2048Hz analysis and supports event context rather than a measured scalar100Hz peak; R4 independently accepts the actual complete corrected provenance fixture and null-date/history preservation. Earlier drift rejection and failed global gates are explicitly retained in those receipts.

Current citations.py:8145-8151 correctly carries that already accepted distinction into its active provides surface. Its100Hz wording describes the project's retained legacy-unit probe label; it supplies no measured peak, physical band or frequency-convention calibration. Physical interpretation as100Hz still requires the matching stated in current provenance.py:3021-3063 and Paper25's dispersion section. DOI, source path, notes and all other citation entries remain unchanged. This review reuses the accepted primary-source analysis; it does not claim a new independent signal analysis or new PDF research.

Paper25's new title/topic/key_claims accurately summarize the actual corrected manuscript: assumed scalar law, finite interval and endpoint constraints, conditional scalar witness, prior-dependent probability, unmatched product correction, and separate conditional Newton comparison. Removed prose incorrectly suggesting vanishing measure under any prior, a matched Gamma_H bridge, exact luminality as a hypothesis clause or a derived physical graviton is not required by the current manuscript. This factual metadata synchronization does not narrow the owning original physical objectives.

## Acceptance limits and custody

Original2.1 remains OPEN: actual lower and upper endpoint human_verified_date fields are both None. No reviewer approval, invented date, closure or blanket waiver is authorized. No existing writer, planner/ledger, notebook, index, slot, build, scientific evaluator, tests, validator, GraphIndex or full graph was executed or mutated by this reviewer. Only the assigned /tmp report pair was written. Read-only shell/Python source inspection, zip reads, AST comparison, git show/diff and continuity-check commands were used.

The owning primary roadmap:146-153 retains full-strength B3/L1-02/Phase6a/5y/6e BUILD: actual metric/source/projector/multiplicity/regulator/subtraction and numerator/normalization, coupling/domain, original O(Lambda²/16pi²) normalization and[0.1,10] AS A RESULT, positive physical state, tensor dynamics and same matter/light reference, transport/units/frequency/error-controlled band. Metadata, adopted inputs and conditional kinematics construct none of these. No old-charter reduction or physical impossibility/closure follows.

Initial manual packet-owned/reference SHA checks returned no drift; the canonical same R1 packet check returned fresh=true, changed=[] after source assessment. Final same-packet result is recorded below. ROOT owns actual-change gates, independent acceptance integration and any canonical closure; neither this source ACCEPT nor ROOT's narrow original-control GREEN establishes full-profile or publication acceptance.

Final canonical check of the SAME R1 packet after report creation: fresh=true, changed=[]. No drift.
