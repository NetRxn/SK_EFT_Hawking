# Independent starred-figure length counter review

The exact candidate base is PR118
9c6d0187f269ed56d865b0835c906ac062f65529. The candidate counter and
L3 figure R2 manifests verify. All replay changes are in a private
archive-based scratch tree. The primary continuity source is
27012c18fa374e8341e124b510abbedeedb18d29.

## Counter regression

I applied the test hunk alone to the exact pinned archive. The added
regression failed with 302 word equivalents instead of 602. The old
substring counter charged the ordinary figure and missed the starred
figure. Applying the source hunk changed the regression to green.
The complete focused manuscript-length class passed 13 of 13 tests.

The implementation reuses the counter's existing TeX comment stripper
and counts both literal figure environment openings in the existing
word-equivalent branch. An independent fixture includes an ordinary
figure, a double-column starred figure with TeX whitespace, both
ordinary and starred commented openings, an escaped percent preceding
a real figure, and an unrelated starred table. Exactly three figures
are charged. The code leaves the rendered PDF word count, PDF age
check, page measurement, figure allowance and configured ceiling logic
in their existing routes.

## Exact L3 R2 readback

I applied the frozen R2 figure candidate on the same base and forced
a native L3 build using the repository's compile_bundle_pdf.py. The
fresh run reports four pages, zero overfull boxes, zero TeX errors,
zero unresolved references and zero dropped class options. The exact
manuscript and figure image match the frozen R2 inputs byte for byte.
The rebuilt PDF's extracted text also matches the R2 author PDF's
extracted text byte for byte.

The independent extraction has 2,663 rendered words and one live
starred figure. On this same fresh PDF, the unpatched counter reports
2,663 word equivalents and the patched counter reports 2,963. The
configured repository ceiling is 3,750 word equivalents, leaving
787 under this counter. This is a native L3 body-length readback.
Venue-policy verification, the abstract limit, publication
acceptance and unrelated bundle gates are outside this verdict.

## Supplemental readiness-file differential

The entire readiness test file on the scratch counter plus R2 candidate
reports 204 passes and seven failures outside the length class. I
replayed all seven exact test IDs on a separate untouched PR118 archive.
All seven already fail there. They concern Lean module coverage and
deregistration, open Stage-13 ratchets, and apex numeral grounding.
The matching failure IDs are frozen in
`supplemental-failure-comparison.json`. This scope does not assign a
current live gate verdict to a different integration candidate.

**Frozen verdict.** Accept the minimal starred-figure counter fix,
focused regression, and native L3 R2 body-length readback at this
exact base. Primary continuity remains fresh and its checkout is
clean. No publication or broader gate closure is implied.
