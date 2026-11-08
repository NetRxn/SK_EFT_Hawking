# Existing dependency guard: local namespace repair

Proposed design under [ADR-018](../../adrs/ADR-018-local-namespace-dependency-classification.md).
Original acceptance: do not report the actual local D3 producer as undeclared,
and do not conceal a genuinely undeclared dependency. Current coverage finding1.4
owns this defect. Scientific numerical assertions remain unchanged.

Modify only `_local_module_names` to include the identifier-valued root component
of each discovered nested Python file, alongside existing stems and parent names.
The same `_walk_py` skip rules apply. Root Python files retain stem handling;
data-only directories do not gain local names. Do not execute discovered imports.

Acceptance evidence:

- Existing declaration suite changes from the reproduced papers-only failure to
  passing without changing pyproject, exemptions, scanner roots or the D3 test.
- A real current `papers.D3.tables` path and nested namespace fixture are recognized.
- Data-only and pruned-directory fixtures do not introduce local module names.
- A seed-journal mutation appends a unique absent external import to a real file
  under the existing production scan roots; the actual declaration assertion fails.
  Restore bytes and mtime, clear caches, and show the unseeded assertion passes.
- Exact D3 width and scalar-speed tests still pass. Independent review confirms
  the implementation matches the accepted scope and the population pilot.
- Update the owning architecture mechanism description, regenerate derived counts
  through existing writers if required, verify freshness, record canonical closure,
  and checkpoint normally. Full repository/main gates are not inferred.

No new check registration, gate type, registry or external dependency is introduced.
The registered-surface probe must establish whether any existing registration
sites need an update rather than assuming a new site is required.
