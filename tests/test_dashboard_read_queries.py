"""Actual route/admission seam under fake driver controls; no capability claim.

ROOT separately tests the catalog SQL and combined policy in disposable AGE.
These controls prove ordering, non-vacuous refusal, bounded fetch and cleanup.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import provenance_dashboard as dash
from src.core import dashboard_queries as queries

SAFE_DSN = 'host=127.0.0.1 port=65431 dbname=dashboard_fixture user=dashboard_reader password=dummy'
IDENTITY = dict(identity=True, role=True, membership=True, database=True, ownership=True,
                schema_create=True, table_mutation=True, sequence_mutation=True,
                definers=True, server_files=True)
GRAPH = dict(creators=True, graph=True, usage=True, labels=True, owners=True,
             defaults_select=True, defaults_mutation=True)


class Cursor:
    def __init__(self, connection, scenario):
        self.connection = connection
        self.scenario = scenario
        self.calls = []
        self.pending = []
        self.fetches = []
        self.closed = False
        self.user_queries = []

    def execute(self, sql, params=None):
        self.calls.append((sql, params))
        self.pending = []
        if self.scenario.get('raise_at') == sql:
            raise self.scenario['error']
        if sql == queries.IDENTITY_SQL:
            self.pending = [(dict(IDENTITY, **self.scenario.get('identity', {})),)]
        elif sql == queries.FUNCTION_SQL:
            self.pending = [(dict(signatures=True, overloads=True, **{}),)]
            self.pending[0][0].update(self.scenario.get('functions', {}))
        elif sql == queries.CREATOR_SQL:
            self.pending = [(self.scenario.get('creators', 'graph_writer'),
                             self.scenario.get('configured', ['sk_eft.dashboard_label_creators=graph_writer']))]
        elif sql == queries.GRAPH_SQL:
            self.pending = [(dict(GRAPH, **self.scenario.get('graph', {})),)]
        elif sql == queries.INITIALIZATION_SQL:
            self.pending = self.scenario.get('initialization', [(['session_preload_libraries=age'],)])
        elif sql == queries.PROBE_SQL:
            self.pending = self.scenario.get('probe', [('7',)])
        elif sql == queries.SETTINGS_SQL:
            self.pending = self.scenario.get('settings', [('on', '5s', '1s', 'ag_catalog, pg_catalog')])
        elif sql.startswith('SELECT ag_catalog.agtype_out(r) FROM ag_catalog.cypher'):
            self.user_queries.append(sql)
            if 'query_error' in self.scenario:
                raise self.scenario['query_error']
            self.pending = [(str(i),) for i in range(self.scenario.get('rows', 1))]
        if sql == self.scenario.get('replace_at'):
            self.pending = self.scenario['replacement']

    def fetchmany(self, size):
        self.fetches.append(size)
        result = self.pending[:size]
        self.pending = self.pending[size:]
        return result

    def fetchall(self):
        pytest.fail('unbounded result fetch')

    def close(self):
        self.closed = True


class Connection:
    def __init__(self, scenario):
        self.scenario = scenario
        self.cur = Cursor(self, scenario)
        self.closed = False
        self.rollbacks = 0

    def cursor(self): return self.cur
    def rollback(self): self.rollbacks += 1
    def close(self): self.closed = True


@pytest.fixture
def route(monkeypatch, tmp_path):
    import psycopg
    import build_graph
    import readiness_gates
    import sentence_state
    import verification_state
    (tmp_path / 'papers').mkdir()
    monkeypatch.setenv('SK_EFT_GRAPH_SOURCE', 'json')
    monkeypatch.setenv('SK_EFT_DASHBOARD_READ_DSN', SAFE_DSN)
    monkeypatch.setitem(dash.app.config, 'PG_SYNC_ENABLED', False)
    for module in (dash, build_graph): monkeypatch.setattr(module, 'PROJECT_ROOT', tmp_path)
    monkeypatch.setattr(readiness_gates, 'PAPERS_DIR', tmp_path / 'papers')
    monkeypatch.setattr(sentence_state, 'PAPERS_ROOT', tmp_path / 'papers')
    monkeypatch.setattr(verification_state, 'LOG_PATH', tmp_path / 'verification_log.jsonl')
    monkeypatch.setattr(verification_state, 'LOCK_PATH', tmp_path / 'verification_log.jsonl.lock')
    connections, scenarios = [], []
    def connect(dsn, **kwargs):
        assert dsn == SAFE_DSN
        assert kwargs == {'autocommit': True, 'connect_timeout': 5}
        scenario = scenarios.pop(0) if scenarios else {}
        if 'connect_error' in scenario: raise scenario['connect_error']
        conn = Connection(scenario); connections.append(conn); return conn
    monkeypatch.setattr(psycopg, 'connect', connect)
    return dash.app.test_client(), connections, scenarios


def complete(conn):
    assert conn.closed and conn.cur.closed and conn.rollbacks == 1


@pytest.mark.parametrize('body', [None, [], 'RETURN 1', 8, True, {}, {'query': 5}, {'query': []}, {'query': None}])
def test_malformed_body_is_400_before_connect(route, body):
    client, connections, _ = route
    response = client.post('/api/graph/cypher', json=body)
    assert response.status_code == 400
    assert connections == []


def test_invalid_json_is_400_before_connect(route):
    client, connections, _ = route
    assert client.post('/api/graph/cypher', data='{invalid', content_type='application/json').status_code == 400
    assert connections == []


@pytest.mark.parametrize('dsn', ['', 'garbage', 'host=127.0.0.1',
    'host=127.0.0.1 dbname=x user=y', 'host=x port=1 dbname=x',
    'host=x,y port=1 dbname=x user=y', 'host=x port=notaport dbname=x user=y',
    'host=x port=0 dbname=x user=y', 'service=other host=x port=1 dbname=x user=y',
    'host=x port=1 dbname=x user=y options=-crole=writer'])
def test_missing_malformed_or_ambiguous_dsn_never_connects(route, monkeypatch, dsn):
    client, connections, _ = route
    monkeypatch.setenv('SK_EFT_DASHBOARD_READ_DSN', dsn)
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 7'})
    assert response.status_code == 503
    assert response.json == {'error': 'read query service unavailable'}
    assert connections == []


@pytest.mark.parametrize('query', ['', ' ' * 5, 'RETURN '+ 'a'*4001, 'CREATE (n)',
    'RETURN 1; RETURN 2', 'RETURN 1 --comment', 'RETURN 1 /*comment*/'])
def test_original_guards_still_run_before_connect(route, query):
    client, connections, _ = route
    assert client.post('/api/graph/cypher', json={'query': query}).status_code == 400
    assert connections == []


@pytest.mark.parametrize('row_count', [0, 999, 1000, 1001, 2000])
def test_row_ceiling_sentinel_no_partial_response_and_cleanup(route, row_count):
    client, connections, scenarios = route
    scenarios.append({'rows': row_count})
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 7'})
    if row_count <= 1000:
        assert response.status_code == 200
        assert response.json['count'] == row_count
        assert response.json['rows'] == [str(i) for i in range(row_count)]
        assert response.json['query'] == 'RETURN 7'
        assert isinstance(response.json['ms'], (int,float))
    else:
        assert response.status_code == 400
        assert response.json == {'error': 'query exceeds 1000 row limit'}
    conn = connections[0]; complete(conn)
    assert conn.cur.fetches[-1] == 1001
    sql = conn.cur.user_queries[0]
    assert sql.endswith('AS (r ag_catalog.agtype) LIMIT 1001')
    assert conn.cur.calls[:4] == [('BEGIN READ ONLY', None),
        ("SET LOCAL statement_timeout = '5s'", None), ("SET LOCAL lock_timeout = '1s'", None),
        ('SET LOCAL search_path = ag_catalog, pg_catalog', None)]
    assert conn.cur.calls[-2][0] == queries.SETTINGS_SQL


@pytest.mark.parametrize('flag', list(IDENTITY))
def test_unsafe_effective_identity_privilege_metadata_refuses_and_recovers(route, flag):
    client, connections, scenarios = route
    scenarios.extend([{'identity': {flag: False}}, {}])
    refused = client.post('/api/graph/cypher', json={'query': 'RETURN 123456'})
    assert refused.status_code == 503
    assert connections[0].cur.user_queries == []
    complete(connections[0])
    assert client.post('/api/graph/cypher', json={'query': 'RETURN 7'}).status_code == 200
    assert len(connections) == 2
    complete(connections[1])


@pytest.mark.parametrize('scenario', [
    {'functions': {'signatures': False}}, {'functions': {'overloads': False}},
    {'functions': {'signatures': None}}, {'creators': ''}, {'creators': 'a,a'},
    {'creators': 'unknown'}, {'creators': 'a, b'}, {'configured': None}, {'configured': []},
    {'configured': ['sk_eft.dashboard_label_creators=graph_writer']*2},
    {'configured': ['sk_eft.dashboard_label_creators=other']},
    *[{'graph': {flag: False}} for flag in GRAPH],
    {'initialization': []},
    {'initialization': [(None,)]},
    {'initialization': [([],)]},
    {'initialization': [(['session_preload_libraries=age']*2,)]},
    {'initialization': [(['session_preload_libraries='],)]},
    {'initialization': [(['wrong_setting=age'],)]},
    {'initialization': [(['session_preload_libraries=unrelated'],)]},
    {'initialization': [('session_preload_libraries', '', 'default'), ('shared_preload_libraries', '', 'default')]},
    {'initialization': [('session_preload_libraries', 'age', 'client'), ('shared_preload_libraries', '', 'default')]},
    {'probe': []}, {'probe': [('8',)]}, {'probe': [('7',), ('7',)]},
    {'settings': [('on','5s','0','ag_catalog, pg_catalog')]},
    {'settings': [('off','5s','1s','ag_catalog, pg_catalog')]},
    {'settings': [('on','0','1s','ag_catalog, pg_catalog')]},
])
def test_admission_unknown_unsafe_or_missing_never_executes_user_source(route, scenario):
    client, connections, scenarios = route
    scenarios.append(scenario)
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 123456'})
    assert response.status_code == 503
    assert response.json == {'error': 'read query service unavailable'}
    assert connections[0].cur.user_queries == []
    complete(connections[0])


@pytest.mark.parametrize('replacement', [[], [(None,)], [({},)], [({'identity': True},)],
    [(dict(IDENTITY),), (dict(IDENTITY),)]])
def test_incomplete_null_or_truncated_catalog_aggregate_is_not_vacuous(route, replacement):
    client, connections, scenarios = route
    scenarios.append({'replace_at': queries.IDENTITY_SQL, 'replacement': replacement})
    assert client.post('/api/graph/cypher', json={'query': 'RETURN 1'}).status_code == 503
    assert not connections[0].cur.user_queries
    complete(connections[0])


@pytest.mark.parametrize('stage', [queries.IDENTITY_SQL, queries.FUNCTION_SQL, queries.CREATOR_SQL,
                                  queries.GRAPH_SQL, queries.INITIALIZATION_SQL, queries.PROBE_SQL,
                                  queries.SETTINGS_SQL, 'BEGIN READ ONLY'])
def test_denied_metadata_and_setup_errors_are_unavailable(route, stage):
    import psycopg
    client, connections, scenarios = route
    scenarios.append({'raise_at': stage, 'error': psycopg.errors.InsufficientPrivilege('SECRET CATALOG DETAILS')})
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 1'})
    assert response.status_code == 503 and 'SECRET' not in response.get_data(as_text=True)
    assert not connections[0].cur.user_queries
    complete(connections[0])


@pytest.mark.parametrize('error,status,message', [
    ('QueryCanceled',400,'query time limit exceeded'),
    ('LockNotAvailable',400,'query lock wait limit exceeded'),
    ('InsufficientPrivilege',400,'query not permitted'),
    ('ReadOnlySqlTransaction',400,'query not permitted'),
    ('SyntaxError',400,'cypher query failed'),
    ('InvalidTextRepresentation',400,'cypher query failed'),
    ('ConnectionFailure',503,'read query service unavailable'),
])
def test_actual_sqlstate_classification_cleanup_and_fresh_recovery(route, error, status, message):
    import psycopg
    client, connections, scenarios = route
    scenarios.extend([{'query_error': getattr(psycopg.errors,error)('SECRET QUERY DETAILS')}, {}])
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 1'})
    assert response.status_code == status
    assert response.json == {'error': message}
    complete(connections[0])
    assert client.post('/api/graph/cypher', json={'query': 'RETURN 7'}).status_code == 200
    complete(connections[1])


def test_delimiter_refusal_closes_admitted_connection(route, monkeypatch):
    client, connections, _ = route
    monkeypatch.setattr(queries.secrets, 'token_hex', lambda n: 'fixed')
    response = client.post('/api/graph/cypher', json={'query': "RETURN '$cyqfixed$'"})
    assert response.status_code == 400 and response.json == {'error': 'query rejected'}
    assert not connections[0].cur.user_queries
    complete(connections[0])


def test_connect_failure_has_no_fallback_and_fresh_recovery(route):
    import psycopg
    client, connections, scenarios = route
    scenarios.extend([{'connect_error': psycopg.OperationalError('SECRET ENDPOINT')}, {}])
    response = client.post('/api/graph/cypher', json={'query': 'RETURN 1'})
    assert response.status_code == 503
    assert connections == []
    assert client.post('/api/graph/cypher', json={'query': 'RETURN 1'}).status_code == 200
    assert len(connections) == 1
    complete(connections[0])


@pytest.mark.parametrize('query', ["RETURN 'ordinary quote'", r"RETURN 'back\\slash'",
    "RETURN '$other_tag$'", "RETURN 'Unicode λ'", 'MATCH (n) RETURN n LIMIT 1',
    'RETURN null', 'RETURN 7 // permitted Cypher comment'])
def test_supported_free_form_single_agtype_queries_remain_intact(route, query):
    client, connections, _ = route
    response = client.post('/api/graph/cypher', json={'query': query})
    assert response.status_code == 200
    assert response.json['query'] == query
    assert query in connections[0].cur.user_queries[0]
    complete(connections[0])


def test_admission_is_not_cached_across_safe_then_drifted_connection(route):
    client, connections, scenarios = route
    scenarios.extend([{}, {'identity': {'membership': False}}, {}])
    results = [client.post('/api/graph/cypher', json={'query': 'RETURN 7'}) for _ in range(3)]
    assert [r.status_code for r in results] == [200, 503, 200]
    assert [len(c.cur.user_queries) for c in connections] == [1, 0, 1]
    for conn in connections: complete(conn)


@pytest.mark.parametrize('setting', ['PGSERVICE', 'PGSERVICEFILE', 'PGHOSTADDR', 'PGOPTIONS'])
def test_ambient_endpoint_or_source_options_are_not_implicit_defaults(route, monkeypatch, setting):
    client, connections, _ = route
    monkeypatch.setenv(setting, 'unreviewed')
    assert client.post('/api/graph/cypher', json={'query': 'RETURN 1'}).status_code == 503
    assert connections == []
