"""Check modules — imported by `scripts/validate.py` for their registration
side-effect. Which module a check lives in has NO bearing on when it runs;
`validate._CANONICAL_ORDER` declares execution order separately (ADR-009 H3),
so organise these files for reading.
"""
