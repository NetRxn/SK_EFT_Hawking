"""Table specs for the I1 bundle.

The finding-class roster is authored data, not derived data: it is the
adversarial reviewer's own class list and the readiness gate each class
backstops, and it changes only when that agent's definition changes. It lives
here rather than as a hand-written tabular in the draft so that the renderer
owns its formatting and the draft carries a single `\\input`, which is what
`validate.py --check bundle_tables_use_pipeline` requires of every bundle.

⚠️ Keep this roster in step with
`.claude/plugins/skeft-qa/agents/adversarial-reviewer.md`, which is the class
list's single owner. The gate NAMES here follow `docs/READINESS_GATES.md`;
note the agent file and that document disagreed on gate 9's name (the agent
said "CountFreshness", the canonical document says "NumericalFreshness" and
widened its scope), and the canonical document wins.
"""

from scripts.paper_tables import Col


# (class, gate backstopped, evidence the class requires)
_FINDING_CLASSES = [
    ('1. Wrong-target citations',
     'Citation integrity (1)',
     'Each bibliographic entry fetched against its arXiv identifier or DOI; '
     'membership in the citation registry'),
    ('2. Parameter drift from primary sources',
     'Parameter provenance (3)',
     'The provenance entry, then the table, figure or equation of the primary '
     'source it names'),
    ('3. Placeholder theorems cited as verified',
     'Lean proof substance (5)',
     "The theorem's declaration site and the tokens of its proof body"),
    ('4. Cross-paper contradictions',
     'Cross-paper consistency (2)',
     'Every companion draft; shared citation keys in particular'),
    ('5. Narrative overclaims',
     'Narrative grounding (7)',
     'Abstract, introduction and conclusion; prior-art searches for priority claims'),
    ('6. Undisclosed assumptions',
     'Assumption disclosure (6)',
     'Hypothesis parameters and structure-field constraints of each cited theorem'),
    ('7. Count-literal drift',
     'Numerical freshness (9)',
     'Canonical count macros and the reported-metric edges of the knowledge graph'),
    ('8. Production-run health',
     'Production-run health (8)',
     'Run status, re-derived from the log tails rather than from a cached status field'),
]


def _finding_class_rows():
    return [{'cls': c, 'gate': g, 'evidence': e} for c, g, e in _FINDING_CLASSES]


TABLES = {
    'table3_finding_classes': {
        'description': 'Adversarial-review finding classes, the gate each backstops, '
                       'and the evidence each requires',
        'rows': _finding_class_rows,
        'columns': [
            Col('cls',      r'\textbf{Finding class}',   align='l'),
            Col('gate',     r'\textbf{Gate backstopped}', align='l'),
            Col('evidence', r'\textbf{Evidence read}',    align='l'),
        ],
    },
}
