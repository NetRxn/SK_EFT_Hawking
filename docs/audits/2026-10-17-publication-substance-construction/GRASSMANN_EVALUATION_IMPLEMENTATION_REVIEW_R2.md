# Independent actual C1 source, mathematics and kernel review R2

Verdict: **ACCEPT_C1_SOURCE_AND_KERNEL_WITH_EXPLICIT_SCAN_DISPOSITION**.

Task publication-eq7-c1-independent-review-r2; parent publication-remediation. Different reviewer from the C1 author. ROOT remains acceptance/integration owner and sole writer of primary notebook `.codex/continuity/publication-eq7-c1-independent-review-r2-notebook.md`. Owning roadmap is primary `docs/roadmaps/Phase6a_Roadmap.md`. This review owns ONLY `/tmp/publication-eq7-c1-independent-review-r2.md` and `.json`; R1 evidence is preserved without edits.

Candidate: public wt1 at `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/wt1`, commit `e0a45f209fcff9dcaf3bb02d59e7f2a2900d7820`, base `f2ee5854ecd8f6b6aca3ab7a63650f5b92e0f3de`. Sole candidate addition: 603-line `lean/SKEFTHawking/ADW/FiniteGrassmannEvaluation.lean`. Before/after SHA256 is identically `5f8f6d3b844d7b286a2b00606b50dd0b779999f2cbb5cd98f80c3fc7e51f60ee`.

The FIRST R2 action checked the new assigned SAME packet; exit0, fresh=true, changed=[]. I read its ROOT notebook and the continuity contract. The final identical packet check again exited0, fresh=true, changed=[]. R1's initial packet check was also fresh. Its report was left incomplete after actual transport errors, never accepted by inference. Read-only primary slotctl status pinned ACTIVE/public/codex wt1 and exact candidate; sandbox ps/loopback observations were unavailable, not healthy or failed backend evidence. ROOT's current reconciliation receipt separately reports complete capacity, no conflicts/errors and running/present backend/proxy; its serial failed-line132 probe returned goals_after=[] without reset/restart/cache changes.

## Actual evidence and exact coverage

The R1 independent matching-wt1 `lean_run_code` request contained the complete exact source plus all78 named `#print axioms` commands in ONE compilation. Actual success=true, timed_out=false, 78 info diagnostics, no non-info diagnostics; EVERY declaration depends only on propext/Classical.choice/Quot.sound. This is reused unchanged under R2's matching source hash, not rerun or claimed new.

Independent source regex enumeration now confirms exactly78 public declarations and61 theorems; its sets exactly match the batch and closing-goal rosters. All61 correct theorem endings have actual independent goals_after=[]:46 successful R1 calls plus15 successful R2 serial retries. Initial R1 file diagnostics were clean; final actual R2 file diagnostics return success=true, timed_out=false, items=[], failed_dependencies=[]. Static candidate scan found no sorry/native_decide/axiom/unsafe/maxHeartbeats. No theorem is omitted because it carries a simp attribute.

Three new actual serial headline `lean_verify(scan_source=true)` calls cover `local_coframeGrassmann_formalExp`, `eval_positive_mixed_zero` and `nilExp_linear_multinomial`. Each returns the standard three axioms and the SAME warnings below, retained verbatim:

```json
[
  {"line":33,"pattern":"scoped instance"},
  {"line":36,"pattern":"scoped instance"},
  {"line":39,"pattern":"scoped instance"},
  {"line":45,"pattern":"scoped instance"}
]
```

The JSON companion embeds full exact requests/responses, the entire source, all62 R1 batch/goal calls including15 errors, and all21 R2 calls. R1's separately issued initial diagnostic response is recorded in the session, while the final diagnostic raw response is embedded in R2. Source and input hashes, declaration rosters, individual axiom outputs and successful closing coverage are retained.

### Transport and reviewer-probe disclosures

The first61 closing-goal RPCs were launched concurrently through Promise.allSettled in one functions.exec.46 succeeded and15 returned HTTP transport errors at `http://127.0.0.1:8761/mcp?client=codex`. I stopped and reported them. High concurrency is observed; it is NOT a proved root cause. ROOT reconciled the endpoint and issued the new packet. All15 missing requests then succeeded sequentially, one awaited call at a time. No successful original goal or original78-export batch was repeated. No slot repair or reset occurred.

Two supplemental full-source consumer probes test scope and inherited operations, not a repeat of the completed kernel batch. The first incorrectly opened the evaluation namespace before expecting norm synthesis to fail; opening that namespace legitimately activates its scoped instances, so that reviewer expectation failed. Its captured class-definition lints also concern reviewer scratch definitions only. The corrected probe moves the negative test before namespace activation and uses abbreviations. It succeeds, timed_out=false, with only one unused-variable linter warning in the reviewer probe. Both full requests/responses remain in JSON. Candidate final diagnostics remain clean.

## Mathematical review

**Genuine carrier, norm and separation.** B1 defines G as ExteriorAlgebra over the complex coordinate module on Site×(Fin4⊕Fin4), card8V. Its coordinateBasis is the actual reindexed Pi coordinate basis. C1 uses coordinateBasis.ExteriorAlgebra indexed by all finite subsets of Fin(8V), then basis.equivFun. Thus coordinates see the entire exterior algebra, not a scalar diagonal image or assumed target. The norm is exactly the finite complex Pi sup norm transported through an injective linear equivalence. The norm equality is definitional, norm-zero separation and coordinate norm bound are proved. Actual finite dimension derives from this basis and supplies completeness.

**Independent finite exponential and formal evaluation.** nilExp is defined directly by Σk≤M (k!)⁻¹ • z^k for any complex algebra with Ring, independently of the desired integral. map_nilExp works through actual algebra homomorphisms even when the target is noncommutative. JointZero universally quantifies all monomials with total coframe degree>M. The discarded-monomial proof splits every polynomial coefficient at that bound. seriesEval is a proved unital AlgHom from formal series: multiplication combines low-coefficient agreement with the pinned actual truncation convolution-locality theorem. Exclusive truncTotal uses M+1. Ordinary truncation itself is never called an AlgHom.

The arbitrary-complex zero-constant source theorem permits ANY polynomial degree. Its finite/formal exp agreement calls accepted A at every retained coefficient. Positive-power and mixed-power vanishing use formal-series lower order, not a totalDegree upper bound or a restricted degree-four source. Higher-degree monomial source control is explicit.

**Common ideal, cutoff and multiplication.** nilExp_eq_exp identifies the independently defined finite sum with Mathlib's actual algebraic nilpotent exponential only after z^(M+1)=0 is established. nilExp_cutoff proves stability under larger cutoff. The add theorem proves hp,hq and hs for P,Q,P+Q from the SAME JointZero family and zero-constant premises before calling exp_add_of_commute. Consequently a shared budget is justified; it is not inferred from separate nilpotence of two arbitrary elements. The mixed-power theorem independently proves a^k b^l=0 when k+l>M.

**Actual local/global premise discharge.** grade_two_jointZero uses B1's weighted_product_grade in actual G, grade2|β|, and grade_above_dimension at8V; Subtype.ext discharges the equality in C. Actual coframe_grade supplies the condition for every global and local coframe, arbitrary actual links. The common cutoff is always4V, including a local family whose vectors still live on the global regulator. The actual APIs expose no assumed nilpotence, commutation or integrability premise.

**Exact multinomial and target typing.** The polynomial coefficient proof uses the actual ordinary complex multinomial coefficient theorem. It establishes β!·multinomial=|β|! and separately proves factorial nonvanishing before complex cancellation. Thus the denominator is coordinate product factorial β!, not |β|!. Finite coefficient extensionality yields the complete expansion; aeval moves it into proved commutative bilinear C. The real-auxiliary specialization is then explicitly included in actual local/global G. The arbitrary complex G version is directly obtained by applying the included algebra homomorphism to nilExp_linear_multinomial and using map_nilExp/map_sum/map_smul; no new premise is needed. Finite commutative products remain inside C. No CommRing/CommMonoid or Finset.prod is installed on full G.

**Controls and meaningfulness.** M0, empty coordinates and zero families are admitted. M0 JointZero iff every generator value is zero is proved. The actual pair-sum control has a surviving exterior square term under an injective four-generator map; B1 supplies genuine nonzero four-generator words, so this is not a scalar or vacuous control. The mixed(2,2) control gives degree4, factorial4 and normalized coefficient1/4, distinguishing the wrong total factorial24. Formal monomial source control permits arbitrary positive degree and complex coefficient. The one-site identity-link result simplifies only the vector exponential; its comment correctly retains the positive-cutoff scalar weighted-mean obligation for C2. No pointwise W=1 claim appears.

## Semantic disposition of the four scan warnings

I directly read the pinned fork scanner `.../1359978/src/lean_lsp_mcp/verify.py`: its comment says “Patterns that may affect soundness - all warnings, LLM decides risk”; its unconditional scoped-instance regex and raw-line rg scan perform no semantic assessment. This review uses that actual scanner contract, not a replacement checker or a new waiver.

- Line33 registers only NormedAddCommGroup.induced along the actual injective coordinate linear equivalence. Mathlib's induced construction retains the original group and adds the separated coordinate metric/norm. The independent corrected consumer probe proves original additive-group compatibility by rfl.
- Line36 registers NormedSpace.induced along the SAME linear map/norm. Its original complex module is preserved; the independent probe proves equality to the pre-scope original Module by rfl. It neither changes ring multiplication nor imposes commutativity.
- Line39 restricts scalars from that complex normed space along ℝ→ℂ. Pinned Mathlib restrictScalars uses Module.restrictScalars and the inherited algebraMap norm law on this same space. No altered Grassmann/scalar algebra is introduced.
- Line45 derives CompleteSpace through FiniteDimensional.complete ℂ on this constructed finite-dimensional normed G. Completeness is proved, not postulated, and is not a False instance.

The corrected consumer probe verifies no normed additive-group synthesis before activating the evaluation scope, successful NormedAddCommGroup/complex NormedSpace/real NormedSpace/CompleteSpace synthesis after activation, and failure to synthesize CommRing on full G. Opening the namespace can activate these scoped instances as intended; imports alone do not install the norm globally. The global finite-dimensional instance is a proved algebraic property, independent of norm choice.

Disposition: **benign constructed scoped norm/space/completeness registrations**. All four lexical warnings remain present and explicitly accepted on these actual semantics. This is NOT warnings=[] or a warning-free scanner result. No code was changed to evade regex matching; no logical-purity, heartbeat or scientific bar was reduced. Pipeline Invariant10 itself permits local instance caching, so lexical instance declarations are not automatically prohibited.

## Usability and exact acceptance boundary

C1 provides the actual complete complex/real normed G target, explicit bounded-index finite sums, exact scalar-monomial/fixed-vector expansion, algebraic J bridge, inclusion transport and actual common-budget coframe discharge needed for C2 finite-sum Bochner proofs. No normed multiplication or analytic exponential is required. I found no mathematical or API correction necessary within the approved C1 package.

This acceptance is C1 SOURCE/MATHEMATICS/KERNEL ONLY. C2 actual integrability/integrals/local Eq7 and genuine variance/complex/nonzero/high-degree integral controls, including positive-cutoff zero-coframe weighted mean, remain OPEN. C3 literal/closed source polynomials, source-specialized identities, original independent-site product and single global integral/reindexing remain OPEN. Full C/Eq7 is not accepted here. ROOT owns native importability, absorption, authoritative builds/extraction and full required Wave gates.

B2 physical action correspondence; original Eq9–11 matrix/Berezin/determinant/Haar/compact-link Fubini/nonzero Z/phase; physical B3 source/state/response/modes/matter/transport/limits/simulation; and publication remain OPEN. No source/Git/notebook/controller/build/cache/dependency/aggregate/registry edit was performed.

The installed lean4 skill was applied in review_only mode under the stricter project/assignment restrictions. Memory informed only discovery/evidence-boundary discipline; all current conclusions above were checked against actual files and tools.

