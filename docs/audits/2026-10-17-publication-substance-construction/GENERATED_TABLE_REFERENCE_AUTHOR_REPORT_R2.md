# Generated-table theorem-reference checker revision 2

Source base ddc320ec365a1f42fd5d8d81796ae07bc0bb029c, composed with frozen
all-11 table patch f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516.
R2 is an author proposal. All writes occurred in a new private scratch
candidate. R1 remains frozen.

- The existing checker now recognizes a leading dot component in literal
  `./tables/...` inputs and still requires confinement under the bundle's
  lexical tables directory. Absolute table paths and table paths containing
  parent traversal return an explicit coverage failure. Ordinary non-table
  inputs stay outside this leg.
- A `\newif` declaration consumes its declared control sequence. Actual use
  of the conditional around a table input still yields an explicit coverage
  failure when the branch cannot be decided. A subsequent unconditional
  input remains reachable.
- Five newly added assertions failed under R1. All 13 focused edge controls
  passed under R2. `root-real-controls-r2.json` replays the four ROOT TeX
  sources and their captured rendered witness results. The canonical,
  dot-prefixed and unrelated post-declaration forms are reached, and the
  known false branch supplies no table read.
- `parity.json` is byte-identical to R1. It records all 21 bundle counters
  and resolver tiers, 2,540 token occurrences and 71 to 82 active direct
  files. `full-focused.txt` records 99 passing tests across the D5 checker,
  registration contract and existing prose checks. Both candidate and
  baseline qualification use the same pinned PhysLib c48433678e8fb6306ebcd48453300c8e16058a62.
- `theorem-ref-reader-r2.patch` contains the four assigned paths. The exact
  base passed Git apply preflight with whitespace errors enabled.
  `continuity.final.json` records an unchanged tracked assignment.
- Registered clean candidate validation returned 0. Its complete checks
  payload is byte-identical to the clean base, with 1,418 bundle
  candidates, 0 unresolved, 2 drift advisories, 1 documented waiver,
  and legacy 90/90. The seed-journaled registered check returned 1 for
  `unresolved:D9:d9_generated_table_reader_missing_probe` at
  `papers/D9/tables/exact.tex:9`. It restored the exact table bytes,
  mtime, and journal. The restored table SHA256 is
  1664f9fedc19d210e60b7af827385ff8e9565e720062bfab33918c4553c83b39.
  `seed-journal-status.txt` confirms no outstanding seeds.
- The added D9 test uses the migrated D9 table and therefore belongs to
  the composed package. Independent acceptance, main integration and
  publication closure remain separate.
