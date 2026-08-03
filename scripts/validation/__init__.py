"""Validation-suite implementation package — ADR-009 Phase 2.

`scripts/validate.py` remains the module: framework core (result types, the
`_CHECKS` registry, `run_checks`, reporting, the CLI, and the `BUNDLE_CODES`
re-export). This package holds the check bodies, split by domain so every file
fits in a single read.

**Why the package is named `validation`, not `validate`.** A package SHADOWS a
same-named module on the same `sys.path` entry — verified empirically during
Phase-2 planning. `scripts/validate/` alongside `scripts/validate.py` would make
`import validate` resolve to the package and leave the module unreachable, while
still satisfying the roster gate's `import validate` + `BUNDLE_CODES` assertion
via a file nobody realised was live. ADR-009 D1 originally specified exactly that
pairing and was corrected.

**Execution order does not live here.** Which module a check is defined in has no
bearing on when it runs; `validate._CANONICAL_ORDER` declares that separately
(ADR-009 H3). Organise these modules for reading.
"""
