# NJL numerical provenance integration

Merge `2e3bc448` reproduces the independently reviewed candidate `451d5e27` at the Git tree level. The pre-existing untracked test stub in the target checkout was preserved.

- D1 `5b65ac5a` binds five displayed values to the three existing BEC benchmark floor evaluations. Expanding the snippets reproduces the original manuscript byte for byte, and PDF text and word positions match. Review report SHA-256 `c091daade898e9b03dac2554688308ab48cc66e4f68464456825d11f9d928f61`.
- D6 `419d10d4` distinguishes the exact inequality from the rounded reciprocal and binds the AGP thresholds and level-one depolarizing estimate to their separate source entries. The protected scalar input renders in the caption. Review report SHA-256 `c9942a9862de19155a0e246ae8ac52499bfa00c7ca154513c8b5b515d2fb068f`.
- D9 `451d5e27` computes the two uniform-prior assignment errors and the two conditional relaxation floors from the published operating points. The 48 ns floor is an approximation and the 88 ns floor rounds down to preserve its inequality. Review report SHA-256 `429ad9d8501c69942dd543b52f7feb9fc55109228fd9b34eb11b383a874fe344`.

The live numerical-literal count fell from 136 to 115, and the ceiling tightened from 117 to 115. Eleven focused numerical and table tests passed together. Canonical D1, D6 and D9 compiles passed, retaining the inherited layout warnings. The fast suite running on the earlier table checkpoint covers that checkpoint's source. The updated composition still requires broad qualification. Finding and module-reach checks remain open. No bundle or submission status was promoted.
