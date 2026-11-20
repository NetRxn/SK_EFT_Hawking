# Independent C3-S source composition review

**ACCEPT_SOURCE_COMPOSITION.** No required source correction. Acceptance is source composition only.

Task `publication-eq7-c3-source-integration-review-r1`; parent publication-remediation. ROOT owns notebook, integration/native/full gates, acceptance and reset. Owned outputs are only this report and its JSON companion. No source/Git/controller/cache/build/dependency/notebook mutation; no new Lean/MCP/build invocation.

## Exact frozen state and accepted evidence

MAIN at `4c4a7baa90c9164963ad71a3d30f85455bb4ab23` has exactly modified `lean/SKEFTHawking.lean` and untracked `lean/SKEFTHawking/ADW/FiniteGrassmannSourceAuxiliary.lean`; index empty. wt2 is clean at `c5c8605b53c4ed17a2d149772850dd84c5c8ca7a`, directly following source author `8d6b0b99a2c576356c17328364ac889b7f1b1e7e`. Author commit changes only the 550-line source; ROOT's commit changes only the aggregate import.

Exact source equality holds across MAIN, live wt2, author commit, aggregate commit and the accepted independent review's embedded full source: SHA256 `f4086dd595d0bceec1d1e6ccca1f69b21f3132897895b5a0de055271bb6dfa18`, 26377 UTF-8 bytes, 25765 Unicode characters, 550 lines.

The complete prior independent review prose and JSON were read/parsed and are embedded in the companion. Markdown SHA256 `68ffa82f38b2d40098536fc5e7e5371d2e63c22022e9b6d9516b99077d88d7cc`; JSON `d30155b46465de9a82c04cf053dbfc6359d0079b9cfea225560ef456fc0dc464`; verdict `ACCEPT_C3_SOURCE_CONSTRUCTION_ONLY`. Reaudited all 74 recorded raw calls: 84 exact export/axiom records, 62 closing-goal manifests/contexts, seven headline verifies, final clean diagnostics. All actual goal contexts match the exact source. Standard axioms only; warnings empty. This reuses actual independent implemented-source/math/kernel acceptance. No redundant Lean call. Prior first-check ordering disclosure and sandbox process/loopback observer limitations are preserved.

## Complete aggregate conservation

MAIN old SHA256 `8522e2f2cac0605dcf7cb5cdb9e05b7a2cd070f64485f8ca977767cd197d51d5`; new `3347865f88121f85e9bff71c23df987ca85c1010707dc8ec9bab661ffce7c498`. wt2 old `46cf32b684f9ac2691589f867d6023aa546c23fc37b9dae1bd4d6dbbffbdac84`; new `aa7d24f34b03ed6d8e8a9bccdbfa0a5d86a565876aba98d6b7505bc19162980e`. Deleting the SINGLE exact new source import from each candidate recovers its entire own old aggregate byte-for-byte. Every old import/order/comment/theorem/proof body is conserved; nonimport bodies match exactly. MAIN imports 1981→1982; wt2 imports 2086→2087.

MAIN and wt2 aggregates are not globally identical: MAIN has the preexisting FiniteGrassmannEvaluation import, while wt2 has additional frontier imports including NavierStokes. Complete old/new raw aggregates, ordered import manifests and cross-diff are retained. All cross-differences predate the same one-line source import. No unrelated wt2 aggregate history was absorbed into MAIN.

Actual MAIN patch:
```diff
--- MAIN baseline
+++ MAIN candidate
@@ -1,5 +1,6 @@
 import SKEFTHawking.ADW.FiniteGrassmannEvaluation
 import SKEFTHawking.ADW.FiniteGrassmannCoframe
+import SKEFTHawking.ADW.FiniteGrassmannSourceAuxiliary
 import SKEFTHawking.ADW.GaussianAuxiliaryCompensation
 import SKEFTHawking.ADW.GaussianAuxiliaryComplex
 import SKEFTHawking.ADW.GaussianPolynomialAffine

```

## Actual dependency closure and pin differences

Source imports actual B1 FiniteGrassmannCoframe only; B1 imports Mathlib and SKEFTHawking.PauliMatrices; PauliMatrices imports Mathlib. This exhausts the directly parsed local closure. All three actual files match author/wt2/MAIN. B1 SHA256 `4d9ae0f635b648a88dbd7cdf07ccd2248553057aa12f3633c92ea7657dc35261`; PauliMatrices `00af5311e27d83b074fd873e865f0680954a348ee8466b1579677141c770d6c0`. No C1/C2/NavierStokes source dependency or premise. lean_deps extraction was not used as an absence oracle or regenerated.

Toolchain and Lake manifest match exactly across accepted author/wt2/MAIN. All configuration/dependency snapshots are unchanged from their own baselines. The whole lakefile differs: wt2 alone has an appended NavierStokes lean_lib block with autoImplicit=true. MAIN's SHA256 is `236bd415087ae279f8235e19f6c4df7eb6f00a1baa4ca80b1accfe11b03dc602`; wt2's is `7008b3d79ac294f4e822e8c867a326c316e94ff9047c4fd110e66b9cab84e5fe`. The remainder is byte-identical, including project autoImplicit=false and all dependency pins. The extra library is outside this source's actual dependency closure. Exact raw files/diff are retained; no whole-lakefile equality is claimed. lean_deps.json snapshots also differ and remain unchanged per baseline.

Lean and REPL input tag v4.32.0; Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997; Physlib c48433678e8fb6306ebcd48453300c8e16058a62; resolved REPL 68a3b3a059787a7db44fb1e6281e4a657efee470. All transitive resolved package pins are preserved in the JSON manifest. Native target reachability remains ROOT-owned.

Exact source equality preserves printed/closed word separation, fixed-direction quartic/no extra factorial, ordered g2/4 and accumulated -2g2 coefficient control, actual compact links/gamma/coframe carrier, bilinear inclusion/grades, arbitrary couplings, auxiliary sigma/physical spacing separation, identity/nonidentity/zero-coupling controls, a=2 and 1/2 spacing controls, and separate source-family renaming.

## Boundaries and freshness

Source composition only. ROOT retains native/import/build/full-tree qualification, all applicable Wave stages and integration/reset ownership. C2 actual G integral work is separate. Full C3 source-specialized actual Eq7, actual local integrability/integrals, product order/inclusion, original independent-site product weight, single global Gaussian/integrability/common cutoff, nested/uncurried measure transport remain OPEN. B2 action correspondence, B3 physical source/state/adjoint/response, original Eq9–11/Berezin/Haar/Fubini/observables/nonzero normalized Z/phase/sampling/modes/matter/transport/continuum/thermodynamic/simulation/publication gates remain OPEN. C1 warning disposition, all original controls, pipeline stages and human approval gates remain unchanged. Older 4c6 R5/native receipts apply to old source and supply no new native green.

The literal FIRST tool action was the assigned same-packet check: exit 0, fresh=true, changed=[]. Final SAME-packet check also exit 0, fresh=true, changed=[]. `git diff --check` exit 0. Complete raw file/manifests/conservation and accepted evidence are in the JSON companion.

Audit transparency: an initial size assertion confused Unicode characters with UTF-8 bytes; corrected before any output. A strict whole-lakefile-equality assertion then exposed the preexisting extra NavierStokes block, which was inspected and disclosed above. Neither incident changed source or scientific acceptance.

Large raw Git stdout snapshots in the companion use lossless `base64(zlib(UTF-8))`, with original byte length/SHA256 and verified roundtrip. No raw evidence was truncated.
