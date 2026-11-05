# ADR-018 — Local namespace identity in dependency declaration checks

Status: design accepted and implementation independently reviewed; canonical
closure and main qualification pending.

## Context and existing coverage

The existing `tests/test_dependency_declaration.py` owns import-versus-declaration
checking. It walks Python sources without importing them, excludes standard-library
and local names, and resolves remaining distribution names against pyproject.
The reviewer-agent layer independently reviews scientific and publication claims;
its acceptance cannot substitute for this deterministic dependency invariant.
No additional gate, registry, dependency exception or import resolver is needed.

At candidate `ff21c0478`, the existing suite reports one failure and four passes:
`papers <- tests/test_gravitational_waves.py`. The consumer imports the real
`papers.D3.tables` producer, whose namespace has no root `__init__.py`.
The current local-name walk collects file stems and immediate parent names,
so it misses a deeper namespace's repository-root component. A read-only
population pilot adds only `docs` and `papers`; only `papers` is an imported
affected name. `find_spec('papers').origin` is None, consistent with a namespace.
This incident is tracked by current computation-coverage finding1.4.

## Decisions

1. Extend the existing local-name walk to include an identifier-valued first
   repository-relative path component whenever it contains a discovered Python
   file below it. This is the namespace importable from the existing root
   pythonpath. Preserve all existing module and bare-script behavior.
2. Derive names from the same pruned source walk. Do not import discovered code,
   consult installed distributions for local identity, hardcode `papers`, add a
   fake external dependency, or relax the exact D3 width regression.
3. Prove both directions: real local nested namespaces are local, while unrelated
   undeclared external imports still fail the existing assertion. A production
   mutation uses the existing seed journal and restores bytes/mtime; clear the
   scanner caches around each mutated measurement.
4. Preserve the existing guard, alias map, exclusions and registration. Record
   closure only through the existing writer after independent implementation
   review and declared verification. Main and publication acceptance stay separate.

## Alternatives and limits

Adding `papers` to an exception list would conceal the shape defect. Adding an
`__init__.py` would change a scientific producer solely to satisfy a broken check.
Runtime import probing can execute package initialization and confuse installed
and local providers. Replacing the exact-width regression weakens scientific
coverage. None is adopted.

This repair does not redesign the pre-existing broad stem/parent-name heuristic,
prove arbitrary installed-package shadowing behavior, or qualify the whole tree.
See the [specification](../superpowers/specs/2026-11-05-local-namespace-dependency-design.md)
and [plan](../superpowers/plans/2026-11-05-local-namespace-dependency-plan.md).
