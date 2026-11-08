# Scoped D11 backing-reference propagation review

Verdict: **ACCEPT_SCOPED_D11_REFERENCE_PROPAGATION**.

## Scope and conservation

Independent claims-reviewer-role review of exactly two chain targets in `papers/D11/claims_review.json`, at HEAD `bf586aa778ade29970187cb7c3f58eeb5479cf06`. Read the entire ROOT notebook, actual claims-reviewer persona, source contexts, declarations, preserved LSP result and before/after JSON. The complete recursive comparison found only `/sentences/18/chain_proposed/links/2/target` and `/sentences/37/chain_proposed/links/0/target`, each changing `Torus` to `SKEFTHawking.TopologicalBand.Torus`. All other data is conserved across 169 sentence records, including IDs, quotes, original run IDs, notes, verdicts, human-state fields and other backing links.

Before SHA256: `16c3581fc0d9359073d7e202d6c9fe7bdafef9052ef0c378ba5dfd24e012b9ca`.
After SHA256: `921463f00d02849c7ee8c7c00b602d7c1765dc38cb5db9209fbec7cac4b5c846`.

## Source fidelity

The affected IDs are `sentence:D11:introduction:bbc664cf` and `sentence:D11:principal-branches-and-a-finite-torus:83add19b`. Actual manuscript lines 84–90 describe the discretized FHS Brillouin construction; lines 143–146 explicitly identify the product of two cyclic factors and telescoping. Both original notes identify `TopologicalBand/FiniteTorus.lean`, not the new Grassmann coframe carrier.

`TopologicalBand/FiniteTorus.lean` imports Mathlib, defines `Torus N₁ N₂ := ZMod N₁ × ZMod N₂`, and builds two shifts, finite-sum shift invariance and forward-difference telescoping. `FHSLatticeGauge.lean` actually imports it. It is root-imported and unchanged since introduction commit `a9aa94b53c4a4dcfc3edcc2ba354fcc51540c409`. The other declaration really coexists: `ADW/FiniteGrassmannCoframe.lean` defines a structure of positive extents indexed by `Fin 4`, with `Site` a four-coordinate cyclic product. It is root-imported; latest source change is `da589c0cd11df218361e1175ea8c83b9ddcccaea`.

The immutable ROOT LSP evidence has success true and timeout false; its actual #print gives `fun N₁ N₂ => ZMod N₁ × ZMod N₂`. Its SHA256 is `d6c007bf58ea7a652b2a68ad639be420e872e4d7c6f026a8ca7aa3812471caab`. No fresh theorem proof was needed or executed for a target-string repair.

## Resolver and validation evidence

The existing canonicalizer with its actual GraphIndex resolves each edited link to `lean:SKEFTHawking.TopologicalBand.Torus`. Bare `Torus` returns ambiguous/suggested with exactly the two actual declarations; the fully qualified coframe name separately resolves to its own node. Thus the repair restores the intended backing without deleting or conflating either substrate.

Strict sentence schema validation passed for 169 records. `git diff --check` passed. First and final checks of the same continuity packet returned fresh true and no changed inputs. Exact observed paths, hashes, commands and resolver outputs are in the companion JSON.

## Limits and residual debt

The read-only canonical census reproduces the existing check predicate: 2313 Lean links, 111 unresolved against the unchanged ceiling 109, therefore failing. D11 retains six old unresolved links: `propext`, `Classical.choice`, `Quot.sound` in each of two other sentences. Those links and the ceiling were not edited. This review does not turn the overall gate green. Existing historical TeX locators/quotes are conserved; no full sentence refresh is claimed.

No scoped repair is required. This accepts reference propagation only, not the whole D11 claim corpus, a stage verdict, canonical finding closure, full merge gate or publication. The only files touched by this reviewer are `/tmp/publication-d11-torus-reference-review-r1.md` and `/tmp/publication-d11-torus-reference-review-r1.json`; no repository, Git, slot, MCP, Lean, cache or registry changes were made. An initial uv invocation could not access its default cache; the existing virtualenv completed the read-only checks without cache repair.
