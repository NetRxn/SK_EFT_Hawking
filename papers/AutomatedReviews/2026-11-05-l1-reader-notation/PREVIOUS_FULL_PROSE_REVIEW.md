# L1 full prose readthrough, 5 November 2026, r1

**Verdict: BLOCK on reader outcome.** The present four-page manuscript does not yet carry its original physical argument for a PRL reader. This is a prose/structure verdict, not independent physics certification, and it does not promote or overturn scientific acceptance records. The useful interval result is clear; its physical subject and significance are still supplied as assumptions. Rewriting those assumptions truthfully has repaired overclaiming but has not completed the original construction.

## Review boundary and sources

Repository reviewed: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103`; bundle: its `papers/L1`. Manuscript SHA256 verified at readthrough: `224b4b4917c7fd00eff5d2b11369c5c79e9c48963fac93eb5439fff7800871e2`. Read all 535 lines in sequence, including bibliography and comments, through `\end{document}` at line 535. All manuscript line numbers below refer to that file.

Read the full repository prose-reviewer role and its prohibited-patterns reference, bundle metadata, the L1 charter in `docs/PAPER_STRATEGY.md` §2.3 and its sequencing context, primary `docs/roadmaps/Phase6a_Roadmap.md` current overlay and Wave 2, the primary `REPAIR_DISPOSITION_MAP.md` priority/ownership and L1 obligations, current publication notebook around the Executor handoff and manuscript/figure increments, and the PR115-associated successor `L1_Physical_Bridges_Roadmap.md` at `/Users/johnroehm/Documents/Codex/2026-11-05/task-2/research/docs/roadmaps/`. Read the candidate retarded spectral interface's statement, finite-sample countercontrol and physical acceptance boundary. The successor roadmap is research sequencing, not independent acceptance of a physical bridge or a slot grant.

No compile, tests, scientific calculation, Lean proof search, slot operation, source/notebook edit or Git mutation was performed. In particular this review makes no claim that a stronger theorem is absent: there was no live Lean LSP/type/import/dependency/history examination. A text or roadmap statement cannot establish that absence or an upgrade. New substrate proposed for the paper must undergo that examination separately. The supplied four-page clean-compile result and prior focused figure repair remain narrower evidence than this readthrough. No Stage 9, 10 or 13 green follows.

## Where the PRL reader stops

**Lines 86–90, especially 87–89.** After the opening has introduced spinor gravity, a vestigial phase and second sound, the manuscript says it supplies neither the microscopic mode, its propagator nor its matter coupling. A PRL reader now needs a reason that constraining this particular free susceptibility teaches something about a physical theory. The manuscript instead proceeds to a familiar arrival-time bound and its square-root inversion. At lines 130–144 the justification becomes explicitly that the earlier Letters constrained theories whereas this Letter constrains an identification with no microscopic coefficients. That difference explains the limitation but supplies no new physical leverage.

The opening result itself may cause an earlier skim rejection at lines 33–41: the abstract displays a narrow allowed interval and immediately says both the mode and comparison range are not derived. That is honest. The necessary next authorial action is to make the original required physical construction carry the significance, not to remove the qualification or present the missing derivation as novelty.

**What the manuscript is actually about:** Given the stipulated speed law `c_GW = c sqrt(chi_vest)` and an adopted order-unity comparison interval, it inverts a GW170817 speed bound, records that elementary interval algebra in Lean, and inventories what the calculation cannot establish about a graviton model.

This matches the corrected charter's conditional confinement calculation, but falls short of the current owning roadmap and repair queue's full physical B3 normalization/window, tensor-mode/matter bridge and transport/observational requirements. It cannot discharge those by becoming a shorter conditional note.

## The five questions

### 1. Does the abstract lead with the result? NO, narrowly but consequentially

Lines 33–34 begin with the action “We constrain our assumed leading-order graviton speed,” followed by the ansatz. The actual finding begins at line 35. This is a short delay, not an incomprehensible abstract; nevertheless the first sentence does not state what was found. More consequentially, the title's “its natural range” (24–25) is stronger reader framing than the abstract's “our adopted range” (38). The title suggests that the paper has established a natural physical domain; the abstract tells the reader it has not.

Authorable change now: put the conditional interval consequence in the first sentence, define the susceptibility and light-speed reference compactly, and retain the explicit present construction boundary. Do not turn the result into a microscopic finding by deleting “assumed.” The final title/abstract must be rebuilt from the independently accepted physical outcome when that construction returns; an interim accurately conditional title is not publication acceptance.

### 2. Does each section advance one connected argument? NO

There are only three numbered sections, but their paragraph architecture contains several competing papers.

- **Introduction, 50–156:** useful motivation, equation and observation at 50–110; an extended literature catalogue at 115–128; a justification for why the work lacks the earlier papers' operator-level content at 130–144; and repeated qualification at 146–156. The reader reaches the end still asking why this susceptibility and range are physical. The catalogue and second qualification block postpone the answer rather than form a step toward it.
- **Formal setup and result, 162–333:** the range provenance at 162–185 is necessary to understand the headline denominator. The interval theorem at 194–221 carries the calculation. The remaining theorem/proof identifiers at 187–192, 207–210, 224–261 and 286–333 largely organize a source module rather than advance a physics argument. In particular, the tracked-hypothesis paragraph admits that P2 implies the other conditions at the chosen tolerance (299–304), then spends another paragraph distinguishing how its falsifiers fail (306–319). The reader has already learned the full allowed set from Theorem 1. This audit adds no new physical restriction.
- **Discussion, 339–433:** the small-versus-zero-width interpretation at 339–349 is useful. The three proposed recovery paths at 351–405 become a research agenda. The third path develops an unnormalized numerical ansatz at much greater length than the main result, ending by saying its actual coefficient remains open. The comparison to a separate in-preparation linearized-EFE programme at 408–423 adds another provisional normalization instead of resolving this one's. Reproducibility at 425–433 is appropriate support but currently reads as counts and implementation inventory, not a usable data/code citation.

The manuscript's main scientific chain should be physical response/domain → tensor speed relative to matter/light → controlled arrival-time inference → surviving parameter interval. Current prose provides only the last arrow and several honest statements that the preceding arrows are missing.

### 3. Is every symbol defined before use? NO

First literal lapse: **line 34**, `c` in `c_GW = c sqrt(chi_vest)` is not defined as the electromagnetic/light reference speed. `c_GW` is called a graviton speed; chi is only called a susceptibility at 35–36 and first described as a normalized metric response at 77–79. Standard reader inference makes the abstract readable, but the matter/light reference is especially substantive here because its derivation is one of the open bridges.

Additional concrete repairs:

- Line 67: `H` is never identified as the de Sitter Hubble parameter in the manuscript.
- Line 112: `ADW` is never expanded for the new reader. This is an acronym, but it obstructs following the physical chain just as an undefined symbol does.
- Line 165: `gamma_star` enters the RPA formula without an explicit mathematical or physical definition. Earlier “coupling inputs” at 81 is not an identification of this symbol, sign, normalization or domain. State what input it denotes; derivation of the physical coupling stays a BUILD.
- Line 174: `Lambda_UV` is used before an explicit definition of the regulator/cutoff scale or units. Line 183's `alpha_ADW` is named a coefficient but its distinct relation to chi is not explained; do not invite the reader to identify the two because their chosen intervals coincide.
- Lines 374–379: define `omega`, `gamma`, `Gamma_H` and their units before discussing physical frequency. The text correctly warns that “100” has not been physically normalized; keep that warning until actual matching exists. Writing Hz beside it cannot repair the missing map.
- Line 398: `tol` appears without a definition or relation to the previously fixed `tau`.
- Lines 412–414: define `N_f`, `M_Pl` and `G_N,emerg` if this comparison survives restructuring; “SM N_f” does not state the count convention.

Do not merely add a notation table: introduce the relevant object in the argument where the reader first needs it, and keep physical units/source correspondence as scientific work rather than treating a verbal definition as their derivation.

### 4. Is every sentence addressed to a reader of the literature? NO

Deletion/move list below removes process narration from the main argument. Preserve scientific qualifications in reader-facing form; no removal of an adverse result, limitation or original obligation is authorized.

- **85–86:** delete “The identification is appealing in its brevity.” It offers taste instead of a physical reason to study the ansatz.
- **112–113:** delete the project-specific “ADW program” defense and “three Phase 6 recovery paths” navigation; retain the precise scope statement, with ADW expanded if needed.
- **135:** remove “As the Introduction notes.” The paragraph is already in the Introduction; it exposes assembled rather than authored structure.
- **151–156:** delete this repeated tour of recovery mechanisms after condensing their actual scientific possibilities once in the conclusion.
- **182–185:** move the “linearized-EFE wave” and “project-internal anchor” provenance to an appropriate reproducibility/source note, preserving the factual absence of a derived physical range. This provenance does not become a physical justification when renamed.
- **187–192, 207–210, 238–244:** move implementation inventory and tactic narration to supporting methods; keep the equation, elementary proof argument and actual hypotheses in the Letter.
- **280–282:** move raw Lean witness names out of the figure caption into supporting provenance. They are not needed to read the observable or compatible interval.
- **286–289:** delete “Per the project's discipline” and the process reason for creating a Prop. Move the full tracked-hypothesis/falsifier audit (286–315) to supporting methods, preserving the redundancy and independence caveats there.
- **303–304:** move the bookkeeping sentence that the recorded Prop keeps its definition. It addresses source maintenance.
- **351–352, 360–361, 368–369:** delete Phase labels and instructions to future project phases; retain only scientific mechanisms warranted by the result.
- **381–403:** move the placeholder theorem inventory and numerical-probe algebra out of the main Discussion. Preserve its assumption/units/physical-matching limitations in the supporting record and preserve the open transport requirement in the conclusion/roadmap. This is not evidence to replace the required matched transport calculation.
- **408–409, 415–418:** remove “wave,” “ships,” and the programme-asymmetry rationale if a short physically relevant comparison remains; otherwise move 408–423 to supporting context. Do not import an unreviewed stronger companion claim as the new spine.
- **425–433:** replace theorem/test counts and local implementation-path inventory in the Letter with an exact public reproducibility citation after the appropriate evidence is available. Preserve formal hypotheses and accepted boundaries in the supporting methods.

The commented lift history at 518–533 is not rendered manuscript prose and is not a reader-facing deletion finding. This report does not re-run or infer deterministic prose gates.

### 5. Is compiled length within the charter budget? PASS for the four-page charter; metadata word-equivalent compliance UNVERIFIED here

`bundle_metadata.json` records `compiled_pages: 4`, matching `PAPER_STRATEGY.md`'s four-page L1 charter. It also declares a **3750-word-equivalent** ceiling, not a page ceiling. Four pages alone cannot establish that measurement, and this readthrough did not execute a word-equivalent counter. The metadata separately says its approximate 600-character abstract guide is not primary-source verified. I do not convert either into confirmed venue conformance. No new compile or external venue-policy verification was performed.

The problem is not that the current draft needs more pages to discuss all its theorem names. Its four pages overallocate scarce space to bookkeeping and underdeliver the required physical chain. A concise physical Letter with longer supporting derivations is a viable architecture only after those derivations actually exist and pass independent review.

## Ordered restructuring instruction

1. **Freeze the original acceptance contract before rewriting the spine.** ROOT retains the entire L1 manuscript, claims, figures, citations, canonical review/closure and integration. Agree bounded physical deliverables with Executor and the existing PR115 successor; do not transfer “the rest of L1” or create a competing construction campaign. The current draft cannot be made publication-ready by rebranding the absent physics as optional future work.
2. **Create a reader-facing physical-model step from accepted construction, not a longer caveat.** For the intended Letter this step must identify the microscopic source/state and normalized metric response, its independently justified physical domain and original normalization/window; a stable tensor pole/polarizations and matter/light reference; and a controlled transport/arrival-time map. Put only the decisive equations, assumptions and validity band in the main text, with the actual derivation in supporting methods. If these results are not yet delivered, keep this step an explicit construction dependency outside publishable prose, never fill it with a stipulated positive state, a chosen chi=1 or tiny gamma.
3. **Rewrite Introduction to one question and one answer.** Present the physical identification, explain what its newly established dynamics predicts for the observable, introduce the datum, then state the surviving interval and what it teaches about that physical model. Compress the four 2017 papers to the comparison needed to explain the new physical target. Remove the second introduction at 130–156. Preserve correct attribution that Volovik's own de Sitter result is luminal; this manuscript's susceptibility law cannot be attributed to him.
4. **Rebuild “Formal setup and result” around the physical-to-observational chain.** Define c, chi, normalization and units; give the physically derived law or precisely delimited alternative outcome; state the finite-tolerance interval theorem once, with a short readable proof; compare to the independently derived physical domain. Use endpoint deviations as checks or figure annotations, not three coequal theorem statements. Move tactics, source identifiers and the tracked-Prop audit into methods. Keep the interval's nonzero width, its unity anchor and prior dependence.
5. **Make the figure and caption display that one comparison.** Retain the finite interval versus adopted/derived domain distinction and unresolved-scale disclosure. Remove Lean-name lists. Caption wording must follow the exact plotted artifact and integrated physical result. Existing focused figure acceptance does not settle this whole prose review.
6. **Replace Discussion's research agenda with an implication and a validity boundary.** Explain what observation selects or excludes in the actual model and how errors/transport affect it. One concise limitation paragraph can preserve the missing or conditional bridges without repeating them in every section. Retain only mechanisms the accepted dynamics actually motivates; remove Phase instructions, placeholder gamma arithmetic and unrelated programme comparison. Keep substantive negative/conditional results in supporting methods and their canonical scientific records, not buried by deletion.
7. **Reauthor title and abstract last, then repeat independent full readthrough and actual applicable gates.** Lead with the strongest accepted physical outcome. If construction yields another speed law, luminality, instability or a scoped obstruction, ROOT and Executor must reconcile that outcome with the original contract and operator disposition rather than force it into the present fine-tuning headline. A stronger result must be checked in actual Lean types/imports/dependencies/history before promoting it. Refresh affected claim/figure/prose/consumer records together; this report grants no stage closure.

## Construction dependencies that prose cannot discharge

- **B3 / W1–W2:** actual source, state, projector, multiplicity, contact/subtraction and regulator/volume matching to a dimensionless chi; original `O(Lambda^2/(16 pi^2))` normalization and `[0.1,10]` derived as a result. Scalar bubble, positivity and selected finite coefficients are supporting milestones, not that result. Different interval/obstruction requires its specified disposition.
- **W3:** constrained quadratic/retarded tensor dynamics, stable residues and polarizations, relation between static response and kinetic/gradient ratio, universal matter/EM reference. Calling a mode second sound or defining its speed does not provide this bridge.
- **W4:** causal matched retarded response, real transport coefficients, units and Hz/angular-frequency conversion, controlled band and arrival-time/error map. The accepted conditional transport construction separates linear attenuation from real dispersion; the paper's linear gamma-times-omega placeholder must not be promoted to that physical result. The finite-sample spectral countercontrols explicitly delimit inference from Euclidean samples.
- **W5 / ROOT:** integrate accepted outcomes across paper25/L1/D3 and other actual consumers, then complete independent review, canonical closure, current-candidate qualification and final human publication review. Executor supplies bounded construction packages; ROOT remains accountable for end-to-end L1.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

1. The brief's full-strength physical B3/mode/matter/transport requirements agree with the current primary Phase6a overlay, repair queue and PR115 successor. They conflict with the **historical strategy rationale** that L1 has no open Phase-6 dependency and depends on no uncertain content. Treat that rationale as historical, not as a waiver. The strategy itself reserves a confinement-letter portfolio decision for the operator.
2. The brief reports a four-page clean PDF; metadata also says four pages, and the notebook records focused zero-overfull layout acceptance. This read-only prose review does not independently recompile or certify the PDF. The metadata's actual length target is word equivalents, so “four pages” is not full evidence for that separate ceiling.
3. The current title says “its natural range,” while the manuscript calls that range adopted and not physically derived. The original current acceptance contract requires deriving it. Truthful body qualifications resolve overstatement locally but do not resolve the title-to-physical-delivery gap or complete B3.
4. Metadata contains historical green/submission-ready narration alongside current RED/pending stage fields. Neither those histories nor the brief's repaired figure/propagation milestone authorizes Stage 9/10/13 green from this review.
5. No contradiction supports moving all remaining L1 work to Executor: the latest notebook explicitly retains ROOT's end-to-end L1 responsibility. The PR115-associated roadmap is a bounded successor sequencing document and preserves original acceptance, source ownership reconciliation and controller admission.
