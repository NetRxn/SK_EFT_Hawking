# Focused NJL render and regression readback

The focused line starts from main at ce194cdc. The reviewed solver, generated Lean artifacts, and finding record end at b92e8db5. Commit db471628 carries the regenerated Paper 5 PNGs, five-page PDF, and layout adjustment.

The configured Python environment ran the same three modules, tests/test_tetrad_gap.py, tests/test_tetrad_gap_solver.py, and tests/test_adw.py. The main baseline passed 121 tests. The focused solver candidate and the render commit each passed 200. Full fast-suite qualification remains pending.

Both figure producers executed. The gap curve reaches Δ/Λ = 1.1675353693282826 at G/Gc = 4. Independent visual review accepted the revised footer and marker placement and both captions on page 3. The reviewer extracted the PDF images and confirmed exact RGB and alpha agreement with the regenerated PNGs. The compile emitted a nonfatal float-placement warning. The adjacent figures were visible on the reviewed page. The affected notebook cells had empty saved outputs at b92e8db5. Whole-notebook execution and qualified integration into main remain open.
