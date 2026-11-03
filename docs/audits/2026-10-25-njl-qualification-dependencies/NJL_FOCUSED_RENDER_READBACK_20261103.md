# Focused NJL render and regression readback

The focused line starts from main at ce194cdc. The reviewed solver, generated Lean artifacts, and finding record end at b92e8db5. Commit db471628 carries the regenerated Paper 5 PNGs, five-page PDF, and layout adjustment.

The configured Python environment ran the same three modules, tests/test_tetrad_gap.py, tests/test_tetrad_gap_solver.py, and tests/test_adw.py. The main baseline passed 121 tests. The focused solver candidate and the render commit each passed 200. Full fast-suite qualification remains pending.

Both figure producers executed. The gap curve reaches Δ/Λ = 1.1675353693282826 at G/Gc = 4. Independent visual review accepted the revised footer and marker placement and both captions on page 3. The reviewer extracted the PDF images and confirmed exact RGB and alpha agreement with the regenerated PNGs. The compile emitted a nonfatal float-placement warning. The adjacent figures were visible on the reviewed page. The affected notebook cells had empty saved outputs at b92e8db5. Whole-notebook execution and qualified integration into main remain open.

The two Phase 5d notebook sources were corrected and independently reviewed. They separate the scalar result from physical tetrad and phase claims, label the represented critical root and near-critical refusal correctly, and distinguish an uncomputed width from a width unresolved at working precision. Independent review confirmed schema validity and sequential execution of all 13 code cells. The positive sample residuals remained at or below 1.6e−13, and the gap curve reaches the above-cutoff value reported above. The review covers the source and direct cell execution. Saved notebook output, kernel execution and HTML review remain outside this receipt.

## Completed fast-suite differential

The configured `python -m pytest -q` suite ran in the same repository Python environment on isolated checkouts of ce194cdc and b92e8db5. The baseline finished with 6,940 passed, 45 failed, nine skipped and 92 deselected. The focused solver revision finished with 7,021 passed, 44 failed, eight skipped and 92 deselected. Exact terminal failed test IDs show 44 shared failures, one baseline-only external-cache path failure, and zero candidate-only failures. This comparison establishes no added failing test IDs on the measured solver revision. The baseline failures, canonical validator and exact render/notebook head qualification still require disposition.
