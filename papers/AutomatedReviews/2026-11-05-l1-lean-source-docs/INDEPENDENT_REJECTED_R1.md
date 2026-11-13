# Independent review: BLOCK exact proposal

Proposal `/tmp/l1-source-docs-proposal-20261105.lean`, SHA256 `695e955a1e7d90db84969dd0677bdb8da3dccc327b4f4d4e90926571aeff3fba`.

The comment-only preservation gate passes. All 49 intervening byte segments around 48 nested-aware block comments are byte-identical; 17 manifest operations reconstruct this exact proposal and change9 block comments. Every import, declaration statement, proof, value, line comment outside a block, whitespace outside a block, and API remains unchanged. Non-block SHA256: `2e84faa34934b06504b5a31ab71dde726b2236706c20bd315a6b02ac1622524d`.

## Required corrections

1. Section3 still says chi is pinned within `~3e-15` of unity. The correct offsets from1 are `-2τ+τ²` and `+2τ+τ²`, approximately `±2τ`. Replace this remaining occurrence. The finding1.2 lexical control misses it because of Markdown backticks/newline; strengthen that control rather than claiming the repair complete.
2. The revised overview RPA locator must be `VestigialSusceptibility.W6Ext.chi_RPA`. Actual source line320 is inside `namespace SKEFTHawking.VestigialSusceptibility.W6Ext`, confirmed by its typed lean_deps record. Its formula is correctly reproduced.

## Fresh source and mathematical review

Read the complete GW proposed source and original changed blocks, actual imports, declarations/proofs, related RPA/GammaH definitions, and actual typed dependency records for GW declarations plus RPA/GammaH. Basic and LinearizedEFE are actual project imports; the GW definitions nevertheless take free real parameters. The scoped claims in the new overview are justified by those definitions and recorded value dependencies. No claim that missing physics is absent globally is warranted or made by the proposed replacement.

The fixed predicate is `Real → Prop`, with `|δ|≤τ` for τ=3e-15. The interval theorem explicitly assumes χ≥0 and yields `[(1−τ)²,(1+τ)²]`. P2 implies P3 because τ<1/2; on the nonnegative carrier the positive lower interval endpoint also yields P1. At χ=1/4, sqrtχ−1=−1/2, so P1 passes and both P2/P3 fail. The revised nonindependence/satisfiability descriptions are correct. The exact interval remains finite and nonempty; the speed tolerance is τ, susceptibility offsets approximately ±2τ, width4τ=1.2e-14. Those statements preserve original theorem strength.

The correction definitions/proofs concern real multiplication. The iff requires positive real ω. The literal100 probe and assumed |γ|≤1e-30 yield at most1e-28, and do not identify Hz, physical Γ_H or a total correction including χ offset. Actual `SecondOrderSK.GammaH` is a four-real-argument function `(γ₁+γ₂)*(κ/c_s)^2`; this alone supplies none of the GW source/state/unit identifications. The revised caution is accurate and the physical BUILD remains owed.

## Actual primary document

Rendered and visually inspected the held Abbott PDF printed page6, reading the entire §4intro and §4.1 through the upper-right continuation before4.2. Eq1 is asymmetric: `−3×10⁻¹⁵≤Δv/v_EM≤+7×10⁻¹⁶`, with Δv=v_GW−v_EM. The distance is conservative26Mpc, lower90% credible luminosity-distance bound. The upper speed limit assumes simultaneous emission and attributes the measured+1.74±0.05s lag to faster GW travel. The lower limit assumes a10s SGRB emission delay. The alternative emission window(−100s,1000s) broadens either side by about2 orders; the continuation discusses future joint detections separating source-emission and distance-dependent propagation delays. The proposal's equation locator, asymmetric source bound, adopted symmetric envelope and alternative-history caveat are correct. This source supplies no susceptibility-speed law.

## Boundary and optional same-scope cleanup

No native check/build/MCP/controller/process-control/Git/notebook/source mutation was performed. Earlier parent-reported baseline build is not native acceptance of this proposal. All four original finding identities and original physical BUILD remain separate and open pending actual qualification. Only /tmp review artifacts were written.

Optional same-scope cleanup: the absolute-bound doc first line says `|γ|·ω` although ω is unrestricted; its next line and theorem correctly use `|γ|·|ω|`. Align the first line. Existing 'half-decade' terminology for[0.1,10] is misleading; avoid it when touching those descriptions.
