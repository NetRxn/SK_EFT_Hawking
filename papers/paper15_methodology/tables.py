"""Table specs for paper15_methodology."""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import pipeline_stages, validation_checks


TABLES = {
    'table1_stages': {
        'description': 'Pipeline stages + gates (parsed from WAVE_EXECUTION_PIPELINE.md)',
        'rows': pipeline_stages,
        'columns': [
            Col('stage', r'\textbf{Stage}', align='c'),
            Col('name',  r'\textbf{Name}',  align='l'),
            Col('gate',  r'\textbf{Gate}',  align='l'),
        ],
    },
    'table2_checks': {
        'description': 'validate.py @register_check decorators',
        'rows': validation_checks,
        'columns': [
            Col('number',      r'\textbf{Check}',             align='c'),
            Col('name',        r'\textbf{Name}',              align='l'),
            Col('description', r'\textbf{What it verifies}',  align='l'),
        ],
    },
}
