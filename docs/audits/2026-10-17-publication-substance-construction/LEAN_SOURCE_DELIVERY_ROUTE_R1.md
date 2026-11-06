# Existing Lean delivery route audit

Current conclusion: a separate accepted dependency-closed L1 source increment EXISTS as source, and the existing process supports pure-Lean substrate wave review. It does NOT make that increment merge qualified or waive current merge pytest/canonical failures. No existing general scoped-main merge route or L1 exception was found. The smallest source-only candidate has not been constructed or qualified here.

## Exact base and source cutset
Live GitHub main (connector fetch_commit with ref main): `ce194cdc4bf939b108c17edc9530a7f0a14565f9`, matching origin/main. Local main `90e39dc7d627c0f31d495a3111ca52b0e04da710` is stale and must not be used. MAIN HEAD `42037383847cc7fa5a3e3761032456fe3050f653`; PRIMARY HEAD `450710b86adfec7a9adf7c43178d26e421bbbd18`. No remote writes/fetch or source mutation performed.

All nine modules below are absent from actual main. The eight pre-C2 modules are byte-identical across MAIN420 and PRIMARY450. Recursive project imports beyond these nine are byte-identical to actual main (full list in JSON). This includes PauliMatrices, Detection.GaussianThreshold and its QuantumNetwork import closure. No unrelated GravitationalWaves or FKLW changes or constants.py edits are required for this theorem import cutset.

| Exact source file | Last source integration commit | SHA256 |
|---|---|---|
| lean/SKEFTHawking/ADW/FiniteGrassmannSourceAuxiliary.lean | 57f6c2a93 | f4086dd595d0bceec1d1e6ccca1f69b21f3132897895b5a0de055271bb6dfa18 |
| lean/SKEFTHawking/ADW/FiniteGrassmannCoframe.lean | a16af66d1 | 4d9ae0f635b648a88dbd7cdf07ccd2248553057aa12f3633c92ea7657dc35261 |
| lean/SKEFTHawking/ADW/GaussianGrassmannAuxiliary.lean | b392a1e0c | 84c7aa0ecef730f1f29c3ade0ec61eabb107d92b1bbe4b6d9d032609cd675d50 |
| lean/SKEFTHawking/ADW/FiniteGrassmannEvaluation.lean | 4c4a7baa9 | 5f8f6d3b844d7b286a2b00606b50dd0b779999f2cbb5cd98f80c3fc7e51f60ee |
| lean/SKEFTHawking/ADW/GaussianAuxiliaryCompensation.lean | 996fa93a3 | 99a40ad1f4304547b2701845e14f168fd3cfcaf2a7526b07eed4eaa7aaead2b6 |
| lean/SKEFTHawking/ADW/GaussianAuxiliaryComplex.lean | 0e2894344 | 91b9884a4194980538b2889f8b57f6c09cf995dfdfa1db71241c00723472375f |
| lean/SKEFTHawking/ADW/GaussianPolynomialAffine.lean | c9b223abf | 3e6a5a5671a518595571395a2584f3d8794f157aadd3b0d552677dec69b47676 |
| lean/SKEFTHawking/ADW/GaussianPolynomialHermite.lean | d4e4494b8 | 2d4f1dee5432252a28aca49038f870ecdb98ea06122eafa1cfa121d1f27c5893 |
| lean/SKEFTHawking/ADW/GaussianPolynomialIBP.lean | 8ad141152 | ffb651c528b22d256b05e8a5ea5118ff3d6fb5bf917d00cd9544b25daccfb396 |

Preserve actual-main aggregate and add exactly these nine imports. MAIN420 holds eight; PRIMARY450's C2 import is commit450710b86; C2 source b4e603d74 plus corrected docstring b392a1e0c equals SHA84c7aa0ecef730f1f29c3ade0ec61eabb107d92b1bbe4b6d9d032609cd675d50. Do not cherry-pick whole mixed source/paper commits blindly: several source integration commits also change papers/review records. C1+C3-S acceptance/native/canonical provenance remains MAIN420; C2 accepted corrected source/kernel/composition is /tmp/publication-eq7-c2-independent-review-r2.json (verdict ACCEPT_C2_CORRECTED_SOURCE_AND_KERNEL_AND_SOURCE_COMPOSITION), native evidence belongs to ROOT. Full C3 is excluded because ongoing/unaccepted.

MAIN lean-toolchain/lakefile/lake-manifest equal actual main; toolchain leanprover/lean4:v4.32.0, mathlib81a5d257c8e410db227a6665ed08f64fea08e997, PhysLibc4843367 (complete refs in manifest). PRIMARY toolchain/manifest identical; lakefile differs only NavierStokes extra library stanza. Do not copy that unrelated stanza or change pins.

## Canonical dependency closure is candidate-specific
A true source-plus-canonical cutset cannot be copied as existing artifact bytes from MAIN420 or PRIMARY450: they describe different populations and unrelated changes. Existing writers in scripts/sync_manifest.py:126-142 own extraction/hash, counts, atlas and atlas heatmap; scripts/extract_lean_deps.py:62-95 includes aggregate AND all recursive Lean sources in hash. Regenerate through scripts/extract_lean_deps.py, update_counts.py, atlas_view.py --write and atlas_heatmap.py --write for the exact candidate. scripts/render_paper_tables.py is the existing dependent table writer. Inspect its actual output before calling this a no-papers wave: any papers/ modification means plain s13 under topology/gate_precheck. Exact minimal derived byte set remains unmeasured until the candidate exists. No old catalog/count/atlas file should be transplanted.

## Wave, merge, submission and approval are separate
AGENTS.md requires appropriate verification at stated acceptance boundary and preserves scientific/independent review. CLAUDE.md:163-168 names full pytest before PR/submission/wave close and verify_scope --merge-gate as full certification. Pipeline Stage6 (~291-304) requires all tests pass; Stage5 (~260-283) requires native zero-error/zero-sorry build and correct counts; Stage12 full cross-layer sync/validation, Stage13 independent findings-only review with zero outstanding blockers for submission candidates. Pipeline lean routing (~683-689) also requires kernel-purity and axiom allowlist.

Topology docs/architecture/VALIDATION_GATE_TOPOLOGY.md:24-38,50-63 explicitly distinguishes advisory iteration, pure-Lean wave closure, paper wave closure and submission. scripts/gate_precheck.py:49-64,114-122 implements s13-lean as same full measurement with --scope substrate, --force-latex, --no-archive; paper reds remain reported. This is eligibility to dispatch fresh-context Stage13 review, not merge permission. Existing wave-close SKILL steps1-3 require sync, review with zero blockers, then close report including validate result, report path, count and commit range. Its hardcoded s13 conflicts concretely with topology's documented s13-lean selection; the existing s13-lean implementation resolves the no-papers precheck without designing a new mechanism.

Exact actual merge implementation scripts/verify_scope.py:239-260,302-340 requires:

1. Full `uv run python -m pytest -m '' -q` exit0, both repo and plugin testpaths. Paper-corpus pytest failures are NOT scoped away.
2. `validate.py --ci --no-memo` output substring `✓ SUBSTRATE: clean`. Comment says readiness_submission_gate sole expected failure; implementation checks only substring, not rc or failure identity. Do not exploit weaker implementation as authorization.
3. Explicit counts_fresh, tables_fresh, claim_clusters_fresh and notebook_exec together --no-memo exit0. These may fail from paper/canonical state even for no-papers input.
4. `lake build SKEFTHawking.ExtractDeps` exit0, in lean/. Required clean-baseline/ADR008 authority remains ROOT's; this audit ran no builds.
5. No newly added git-porcelain status entry caused by the run. This is a set-difference check, not full byte comparison and not a clean-start check. A clean exact candidate and artifact inspection remain necessary evidence.

There is no merge scope flag in this flow. `verify_scope` ordinary scoped mode deliberately prints NOT CERTIFIED; s13-lean cannot replace it. Any actual ROOT27-node paper/canonical red in full pytest or explicit four-check leg remains merge blocking under this existing process. Their exact current set is ROOT-owned measurement, not duplicated here. Historical b21 failure is not current-head proof.

Actual-main docs/dev-loops/MemoryProcesses/EXECUTION.md expressly says s13-lean does not replace merge-gate/waive failing pytest. Its 2026-09-09 owner acceptance excludes pre-existing corpus failures only for that increment; it is not standing L1 authority. Current live main's existence therefore proves historical integration with disclosed special acceptance, not a general merge exemption.

Submission remains scope-blind: scripts/gate_precheck.py submission:82,120-122 executes --strict --force-latex --no-archive. Strict provenance/source freshness/axiom closure/citation obligations, Stage9/10/13 evidence and GREEN human readiness rule remain; topology:114-122 warns mechanized YELLOW/open is not all P1 passed. QA_QI_INFRASTRUCTURE_MAP §4:514-535 and pipeline:949-950 preserve actual human provenance decisions. Final human publication approval is untouched.

## Existing-process recommendation
Keep accepted source progressing independently of full C3 and paper rewrites: ROOT can assemble the listed exact-base nine-module import-closed package with existing canonical producers under its existing integration authority, obtain independent integrated scientific review and run the existing s13-lean wave precheck if no papers were changed. This preserves useful accepted science without claiming main qualification. ROOT's current red remeasurement determines required merge repair work; use existing remediation planner for actual required failures. Merge only after exact candidate passes existing merge requirements. Do not merge whole MAIN420 or PRIMARY450, copy their derived artifacts, call wave close a merge certificate, add a skip/waiver/ceiling, or infer new owner acceptance from finite-memory history.

No tests, Lean operations, builds, source/Git/controller/cache/registry/notebook edits, PRs or merges were performed. Only these two /tmp report outputs were written. Continuity first check passed fresh; final same-packet result will be supplied separately.
