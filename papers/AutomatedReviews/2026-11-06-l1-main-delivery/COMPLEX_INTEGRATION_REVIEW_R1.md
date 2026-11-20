# Independent exact integration composition review r1

Verdict: **ACCEPT_EXACT_INTEGRATION_COMPOSITION**.

This approves the exact unapplied proposal in /tmp/publication-complex-integration-r1.json and its primary/main patches and postimages. It does not certify application, controller absorption, native build, generated-artifact freshness, whole-project gates, physical acceptance, main readiness or publication.

## Exact source and target composition

I read the complete proposal manifest, proposal Markdown, frozen ROOT integration notebook, complete main and primary patches, and exact postimages. My earlier independent source/kernel review remains the proof authority for the exact source. Independent byte comparisons confirm both proposed 624-line GaussianAuxiliaryComplex.lean postimages equal git-show of author commit e0c51ec2ed709c30a2d331fe0a52edd50a84bc39, SHA256 91b9884a4194980538b2889f8b57f6c09cf995dfdfa1db71241c00723472375f. The forty theorem exports exactly match the manifest.

MAIN remains clean at 91d380f4acd6077e55d24e6f213931497ae39e55. Its patch adds only the exact new source and a single leading import SKEFTHawking.ADW.GaussianAuxiliaryComplex to lean/SKEFTHawking.lean. Every original aggregate byte remains the suffix of the postimage, in exactly its original order. Aggregate before SHA256 e471901c2f91a9866dfcbe012b83452b45f85e5ae0169292b8caf2759f3dc824; after 7c7d45566ba00fb19484821b44d798f15beca139e17b7ec13a3d7c9d58d22952.

Primary remains clean at 2c201cd00cd1d17e7665ea0a6711344abc1c1524. Author e0c51ec2 is its direct child and adds only the source module. The primary integration patch adds only the identical leading aggregate import, so normal author absorption plus this import produces the proposed postimage. Every prior primary aggregate byte is conserved, including peer imports absent from MAIN. Aggregate before SHA256 d1507f92b631eb1627540e375a828daca74f9621d1001583b0e0246dd88029f0; after ab36adc30443e9c0a6a036dadf502809e336f1cc7568c69f511a031960691343.

I independently reconstructed both patch postimages in memory from the unified hunks, and additionally generated unified diffs independently from exact before/after bytes; both patches match exactly. No unlisted path, removed old import or whole-frontier merge is included. Each staged target contains exactly the aggregate and new source.

## Dependency and compiler context

The actual affine, Hermite and IBP source bytes are identical among author, primary and MAIN, including their manifest hashes. I independently traversed the full project import closure of the new module; every preexisting project source in that closure is byte-identical among all three contexts. There is no import of the aggregate from that closure, so adding the aggregate import introduces no aggregate cycle. Existing target Lean source contains no declaration-name collision with the new module's definitions or theorems.

lean/lean-toolchain and lean/lake-manifest.json are identical among author, primary and MAIN and unchanged relative to each target HEAD. The three lakefile require blocks, including Mathlib, REPL and PhysLib revisions, are identical. Every target lakefile is unchanged by this proposal.

The whole lakefile is intentionally not byte-identical across targets: author/primary already contain a separate NavierStokes lean_lib stanza with autoImplicit=true that MAIN already omits. This is the only observed lakefile difference, predates this proposal, is not copied into MAIN, and is outside the new module's full project import closure. It is not a toolchain or dependency-pin difference. The SKEFTHawking package/library settings relevant to this module are preserved.

The new module imports its complete proof context directly rather than relying on the aggregate import order. It is entirely inside SKEFTHawking.ADW with an explicitly closed noncomputable section/namespace. It adds no global attributes, instances, options, syntax or notation declarations. The early aggregate import therefore has no identified declaration or parser conflict. Imported Mathlib modules may expand the aggregate dependency set as expected; actual native compilation and full-project qualification remain required rather than inferred from this source comparison.

## Boundaries and execution

Initial exact packet check returned exit 0, fresh=true, changed=[]. Final identical packet check is recorded below and in the JSON companion. I performed only read-only source/patch/Git inspection and Python in-memory comparisons. No new MCP verification was necessary for this composition-only review; no builds, Lean runs, controller, cache/dependency/process actions, Git mutations, source changes, notebook changes, or MAIN writes were made. Only /tmp/publication-complex-integration-review-r1.md and .json were written. Other reviewers' work was preserved.

No required composition correction found. ROOT retains normal absorption/application after the active MAIN source-record review, actual native/build/extraction/full gates and independent generated-artifact qualification. Eq4 compensation/truncation, actual Grassmann/coframe/Berezin/link/source/C2/positive-phase and physical B3/publication obligations remain OPEN.

Final identical-packet continuity check: exit 0, fresh=true, changed=[]. Proposal and targets remain unchanged.
