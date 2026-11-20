# E1 historical-registration disposition

Assessment base: `6e2642ece56abbbbd9da43f7bb29bd20633c013d`.
Directly read the current E1 manuscript, all three built historical modules,
the relevant KappaScaling carrier/correction/bounds and their module history.
Coordinated imported inspection on 2026-10-15 succeeded in both batches,
without errors or timeout. Source blobs matched the candidate and main
`ce194cdc4bf939b108c17edc9530a7f0a14565f9`.

## Why the registrations are obsolete

| Historical registration | Evidence and disposition |
|---|---|
| PolaritonPhase5u; DispersionAndPolariton | No source file or exact module record in the pinned catalog. Neither is an existing declaration to cite as formal backing. |
| KerrSchild.PolaritonCrossBridge; KerrSchild.SingleCopy | No source file or exact module record; the current manuscript has no single-copy or ringdown argument. |
| GrapheneHawking | Imported signatures state generic correction arithmetic and the defined Hawking-temperature identity. They do not derive the adopted normalization or a polariton device's physical behavior. The graphene comparison is absent from the current argument. |
| SoftTheorems.NoiseFloorPrediction | The strengthened July source computes noiseFloor(delta_k)=delta_k/2, its half-ratio for nonzero delta_k and invariance under changes to Wilson coefficients on an explicit SKConfig. E1 asserts none of these. Its mean-field energy expressed in kelvin is a different observable. |
| WKBConnection | The explicit ExactWKBParams and ModifiedBogoliubov carrier supply a model with modified unitarity as a field. Imported occupation nonnegativity additionally requires decoherence<1; noiseFloor=Gamma_H/kappa belongs to that model. E1 does not assert this occupation model, its spectral floor or complex turning-point results. |

These dispositions remove historical direct registrations, not source modules,
proven results or genuine physical assumptions.

## Stronger backing considered

KappaScaling defines the correction on positive healing length and sound speed
with nonnegative transport coefficients. Its imported correction bound states
an equality to the adopted -(pi/6)D^2, a sharp magnitude bound and nonzero
correction for positive kappa; its scaling result factors the defined
correction quadratically in kappa. This is stronger matching arithmetic than
the graphene-only presentation, but it does not derive a universal coefficient,
a measured correction, or a physical noise budget. E1 already discloses that
pi/6 is an adopted normalization and does not claim formal verification of that
physical choice. No new apex or decorative theorem citation is added.

The retained explicit verification claims continue to cite PolaritonTier1.
The existing `bundle_closure.build_closures` reader, run on the pinned catalog
and current apex metadata, resolves all four apexes, finds only the
PolaritonTier1 module in their closure, and reports zero private-edge
truncations and 19 other leaf-edge truncations. The closure is evidence about
those declared claims, not an assertion that all prose is backed.

## Source pins

| Module | SHA-256 |
|---|---|
| GrapheneHawking | fd51aade3708511b788d5b2dceddf4e867e5621f6f9f36fa5cd07e7d84b91b4b |
| SoftTheorems.NoiseFloorPrediction | f14bc1f40389f2696ac074f6b539b94a99f9f99f3c1262674624b727946a7fd3 |
| WKBConnection | 1bd86425aebc0706dbdfeeacf351c4d410a5dbb7c32723ff83072e2ed1bf1efb |
| KappaScaling | 562f67640d9dbd1b462cf39036a84e592d3cf0f0beb7e5332d325d24f65bc552 |

The eleven inspected theorem axiom closures contain only propext,
Classical.choice and Quot.sound. Ordinary axiom closure alone does not
establish relevance or physical content; the explicit carriers above matter.

## State preservation

The existing deregistration writer appended one event and rationale while
preserving every original event. Its generic bookkeeping changes to last_lift
and freshness_stale were restored. Its manifest-refresh subprocess failed;
a direct invocation of the existing manifest writer then produced an invalid
source-missing measurement under the worktree's hidden ancestor. The previous
manifest and metadata were preserved exactly. This repair claims no manifest
freshness and changes no Stage9/10/13 pending state. The producer defect is a
separate open infra finding in E1.md.

Two unrelated scientific concerns remain for subsequent source-grounded E1
repair: a mean-field energy ratio does not establish background occupation,
and the dimensional half-gain frequency must be distinguished from its
universal dimensionless ratio. This roster correction does not resolve them.
