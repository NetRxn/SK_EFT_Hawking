# Generated table reference reader R4 author checkpoint

R4 is an incremental three-path patch on exact PR118 plus the five-patch
R3 table composition. R3's independent review found a registered checker
false pass on D9 when a literal percent in inline verbatim appeared before
the unresolved theorem that TeX actually rendered.

R4 masks true comments in generated sources while preserving inline
verbatim, escaped control symbols and source offsets. It reuses the
existing inline verbatim matcher and keeps strict renderer ownership,
historical draft/legacy scanning and the existing resolver unchanged.
The targeted regression fails on R3. The isolated focused suite passes
78 tests on R4. A first shared-scratch suite overlapped a journaled seed
and was superseded by the isolated replay.

Actual canonical D9 registered runs now fail for both the literal percent
seed and the previously fixed conditional seed at the exact table line.
Both seeded manuscripts compile and contain the unresolved name in PDF
text. Recorder ownership and exact journal/source restoration pass.
The clean full checker payload equals the pinned baseline byte for byte
after isolating timing. Independent R4 review and the exact merge profile
remain open.
