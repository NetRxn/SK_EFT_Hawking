# Independent current-main review of E1 attenuation recovery

2026-11-22. **FIXED** at the original consumer scope of findings 1.1, 1.2,
and 1.3 on public main `818bb45d3c4705b7190dd3c025ccd3cb30a6c9fd`.

The reviewer recomposed the two selected manuscript hunks and two metadata
claim replacements from `c3ce76a10`. The result matches the actual
manuscript SHA-256
`8408835c6347c4acbbb1e825d9afcf8e408b0588b9de638705737ec4bcb34881`
and metadata SHA-256
`9ef8c298a9ebb2dd366737b6b632522ac8e09530c9bdf7d004b7f859b051839a`.
The formal finding and historical review match their donor `2c0b8d8fc`.
The abstract, figures, tables, underlying implementation, and stage flags
are preserved.

For 1.1, the current Python attenuation factor defines the positive
exponential and specifies multiplication for recovery. The manuscript
states both directions. The Lean theorem bounds the factor, and the order
consequence uses nonnegative occupation. For 1.2, zero decay implies a
unit factor, and the admitted zero-distance case gives a unit factor even
at positive decay. For 1.3, the per-healing-length exponent contains
`c_s/v_g`. The table producer specializes to `v_g=c_s`, now stated in
the paper. The weak-loss criterion is necessary, and independent
dispersion, transmission, and readout error control remain required.

The three original Verify commands failed on the base and passed on the
replay. The reviewer reran each declared command successfully. The
unchanged source-matched Lean catalog resolves all three attenuation
declarations, with only the core Lean axioms and complete extraction.
The forced E1 compile produced four pages with zero overfull boxes, TeX
errors, or unresolved rendered references.

Stage 9, 10, and 13 remain pending, with redo required and source freshness
stale. Original finding E1:2.3 remains open, as do the physical transport
derivation, device calibration, and the validated detection band.
