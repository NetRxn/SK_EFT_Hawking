"""Per-connection admission and bounded reads for the existing AGE console.

Provisioning stays outside this module. All admission SQL is trusted and static;
user Cypher is introduced only after catalog admission and a trusted AGE read.
The finite function policy is not a universal function-purity or image claim.
"""
from __future__ import annotations

import os
import re
import secrets
from dataclasses import dataclass

MAX_ROWS = 1000


class ReadUnavailable(RuntimeError):
    """Missing, unsafe or unknown reader provisioning."""


class QueryOverflow(ValueError):
    pass


class QueryRejected(ValueError):
    pass


@dataclass(frozen=True)
class ReaderEndpoint:
    dsn: str
    user: str
    database: str


def reader_endpoint(psycopg) -> ReaderEndpoint:
    """No libpq endpoint/login/database defaults, service files or source options."""
    dsn = os.environ.get('SK_EFT_DASHBOARD_READ_DSN', '')
    if not dsn or not dsn.strip():
        raise ReadUnavailable('reader DSN absent')
    try:
        if any(os.environ.get(k) for k in ('PGSERVICE', 'PGSERVICEFILE', 'PGHOSTADDR', 'PGOPTIONS')):
            raise ValueError('ambient endpoint or source options')
        values = psycopg.conninfo.conninfo_to_dict(dsn)
        # An explicit single endpoint avoids service/default/failover ambiguity.
        for name in ('host', 'port', 'dbname', 'user'):
            value = values.get(name)
            if not isinstance(value, str) or not value.strip() or value != value.strip():
                raise ValueError('explicit endpoint, database and login required')
            if ',' in value or '\x00' in value:
                raise ValueError('multiple or invalid endpoint values')
        if not values['port'].isascii() or not values['port'].isdigit() or not 1 <= int(values['port']) <= 65535:
            raise ValueError('invalid port')
        if values.get('service') or values.get('options') or values.get('hostaddr'):
            raise ValueError('indirect endpoint or session options')
        if any(k in values for k in ('replication', 'requiressl', 'target_session_attrs', 'load_balance_hosts')):
            raise ValueError('non-reader connection mode')
    except Exception as exc:
        raise ReadUnavailable('invalid reader DSN') from exc
    return ReaderEndpoint(dsn, values['user'], values['dbname'])


# Each query produces exactly one aggregate record. NULL, absent/extra records or
# flags are refused in Python; aggregates inspect the full catalog population.
IDENTITY_SQL = """
SELECT pg_catalog.jsonb_build_object(
 'identity', current_user = %s AND session_user = %s AND pg_catalog.current_database() = %s,
 'role', (SELECT pg_catalog.count(*) = 1 AND pg_catalog.bool_and(r.rolcanlogin AND NOT
     (r.rolsuper OR r.rolcreaterole OR r.rolcreatedb OR r.rolreplication OR r.rolbypassrls))
     FROM pg_catalog.pg_roles r WHERE r.rolname = current_user),
 'membership', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_roles r
     WHERE r.rolname <> current_user AND pg_catalog.pg_has_role(current_user,r.oid,'MEMBER')),
 'database', pg_catalog.has_database_privilege(current_user,pg_catalog.current_database(),'CONNECT')
     AND NOT pg_catalog.has_database_privilege(current_user,pg_catalog.current_database(),'CREATE')
     AND NOT pg_catalog.has_database_privilege(current_user,pg_catalog.current_database(),'TEMP'),
 'ownership', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_shdepend d
     WHERE d.refclassid = 'pg_catalog.pg_authid'::pg_catalog.regclass
       AND d.refobjid = (SELECT oid FROM pg_catalog.pg_roles WHERE rolname=current_user)
       AND d.deptype = 'o' AND (d.dbid = 0 OR d.dbid =
         (SELECT oid FROM pg_catalog.pg_database WHERE datname=pg_catalog.current_database()))),
 'schema_create', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_namespace n
     WHERE pg_catalog.has_schema_privilege(current_user,n.oid,'CREATE')),
 'table_mutation', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_class c
     JOIN pg_catalog.pg_namespace n ON n.oid=c.relnamespace
     WHERE c.relkind IN ('r','p','v','m','f') AND n.nspname NOT IN ('pg_catalog','information_schema')
       AND n.nspname !~ '^pg_(toast|temp)'
       AND (pg_catalog.has_table_privilege(current_user,c.oid,
          'INSERT,UPDATE,DELETE,TRUNCATE,REFERENCES,TRIGGER,MAINTAIN')
         OR pg_catalog.has_any_column_privilege(current_user,c.oid,
          'INSERT,UPDATE,REFERENCES'))),
 'sequence_mutation', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_class c
     WHERE c.relkind='S' AND pg_catalog.has_sequence_privilege(current_user,c.oid,'USAGE,UPDATE')),
 'definers', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_proc p
     WHERE p.prosecdef AND pg_catalog.has_function_privilege(current_user,p.oid,'EXECUTE')),
 'server_files', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_proc p
     JOIN pg_catalog.pg_namespace n ON n.oid=p.pronamespace
     WHERE n.nspname='pg_catalog' AND
       (p.proname ~ '^pg_(read_file|read_binary_file|stat_file|ls_.*|logdir_ls|file_write|file_rename|file_unlink|file_sync)$'
        OR p.proname IN ('lo_import','lo_export'))
       AND pg_catalog.has_function_privilege(current_user,p.oid,'EXECUTE'))
)
"""
IDENTITY_FLAGS = frozenset(('identity', 'role', 'membership', 'database', 'ownership',
                            'schema_create', 'table_mutation', 'sequence_mutation',
                            'definers', 'server_files'))

FUNCTION_SQL = """
WITH expected(signature) AS (VALUES
 ('ag_catalog.load_edges_from_file(name,name,text,boolean)'),
 ('ag_catalog.load_labels_from_file(name,name,text,boolean,boolean)'),
 ('ag_catalog.create_graph(name)'), ('ag_catalog.drop_graph(name,boolean)'),
 ('ag_catalog.alter_graph(name,cstring,name)'),
 ('ag_catalog.create_vlabel(cstring,cstring)'), ('ag_catalog.create_elabel(cstring,cstring)'),
 ('ag_catalog.drop_label(name,name,boolean)'),
 ('ag_catalog.create_complete_graph(name,integer,name,name)'),
 ('ag_catalog.age_create_barbell_graph(name,integer,integer,name,ag_catalog.agtype,name,ag_catalog.agtype)'),
 ('pg_catalog.set_config(text,text,boolean)')
), resolved AS (
 SELECT e.signature,p.*,l.lanname,n.nspname
 FROM expected e LEFT JOIN pg_catalog.pg_proc p ON p.oid=pg_catalog.to_regprocedure(e.signature)
 LEFT JOIN pg_catalog.pg_language l ON l.oid=p.prolang
 LEFT JOIN pg_catalog.pg_namespace n ON n.oid=p.pronamespace
)
SELECT pg_catalog.jsonb_build_object(
 'signatures', (SELECT pg_catalog.count(*)=11 AND pg_catalog.count(oid)=11 AND pg_catalog.count(DISTINCT oid)=11
   AND pg_catalog.bool_and(COALESCE(NOT prosecdef AND prokind='f' AND NOT proretset AND
     NOT pg_catalog.has_function_privilege(current_user,oid,'EXECUTE') AND
     CASE WHEN nspname='pg_catalog' THEN
       lanname='internal' AND prosrc='set_config_by_name' AND prorettype='pg_catalog.text'::pg_catalog.regtype
     ELSE lanname='c' AND prosrc=proname AND prorettype='pg_catalog.void'::pg_catalog.regtype
       AND probin='$libdir/age'
       AND proowner=(SELECT extowner FROM pg_catalog.pg_extension WHERE extname='age')
       AND EXISTS (SELECT 1 FROM pg_catalog.pg_depend d JOIN pg_catalog.pg_extension x ON x.oid=d.refobjid
          WHERE d.classid='pg_catalog.pg_proc'::pg_catalog.regclass AND d.objid=resolved.oid
            AND d.refclassid='pg_catalog.pg_extension'::pg_catalog.regclass AND d.deptype='e' AND x.extname='age')
     END, false)) FROM resolved),
 'overloads', NOT EXISTS (SELECT 1 FROM pg_catalog.pg_proc p
    WHERE p.proname IN (SELECT proname FROM resolved) AND
      pg_catalog.has_function_privilege(current_user,p.oid,'EXECUTE'))
)
"""

# The custom setting is an administrator-provisioned declaration, checked against
# the effective pg_db_role_setting precedence (role+database, role, database).
CREATOR_SQL = """
WITH configured AS (
 SELECT setting, (CASE WHEN s.setrole<>0 THEN 2 ELSE 0 END +
                  CASE WHEN s.setdatabase<>0 THEN 1 ELSE 0 END) AS priority
 FROM pg_catalog.pg_db_role_setting s
 CROSS JOIN LATERAL pg_catalog.unnest(s.setconfig) AS setting
 WHERE s.setrole IN (0,(SELECT oid FROM pg_catalog.pg_roles WHERE rolname=current_user))
   AND s.setdatabase IN (0,(SELECT oid FROM pg_catalog.pg_database WHERE datname=pg_catalog.current_database()))
   AND setting LIKE 'sk_eft.dashboard_label_creators=%%'
)
SELECT pg_catalog.current_setting('sk_eft.dashboard_label_creators',true),
 (SELECT pg_catalog.array_agg(setting) FROM configured
  WHERE priority=(SELECT pg_catalog.max(priority) FROM configured))
"""

GRAPH_SQL = """
WITH creators AS (SELECT oid,rolname FROM pg_catalog.pg_roles WHERE rolname=ANY(%s)),
 graph_schema AS (SELECT oid,nspowner FROM pg_catalog.pg_namespace WHERE nspname='sk_eft'),
 labels AS (SELECT c.* FROM pg_catalog.pg_class c JOIN graph_schema n ON n.oid=c.relnamespace
            WHERE c.relkind IN ('r','p')),
 defaults AS (
   SELECT cr.oid AS creator,a.grantee,a.privilege_type
   FROM creators cr CROSS JOIN graph_schema n
   CROSS JOIN LATERAL pg_catalog.aclexplode(COALESCE(
     (SELECT defaclacl FROM pg_catalog.pg_default_acl
      WHERE defaclrole=cr.oid AND defaclnamespace=0 AND defaclobjtype='r'),
     pg_catalog.acldefault('r',cr.oid))) a
   UNION ALL
   SELECT cr.oid,a.grantee,a.privilege_type
   FROM creators cr CROSS JOIN graph_schema n
   JOIN pg_catalog.pg_default_acl d ON d.defaclrole=cr.oid AND d.defaclnamespace=n.oid AND d.defaclobjtype='r'
   CROSS JOIN LATERAL pg_catalog.aclexplode(d.defaclacl) a
 ), effective AS (SELECT * FROM defaults WHERE grantee IN
    (0,(SELECT oid FROM pg_catalog.pg_roles WHERE rolname=current_user)))
SELECT pg_catalog.jsonb_build_object(
 'creators', (SELECT pg_catalog.count(*)=%s FROM creators),
 'graph', (SELECT pg_catalog.count(*)=1 FROM ag_catalog.ag_graph g JOIN graph_schema n ON g.namespace=n.oid
           WHERE g.name='sk_eft') AND (SELECT pg_catalog.count(*)=1 FROM graph_schema),
 'usage', (SELECT pg_catalog.bool_and(pg_catalog.has_schema_privilege(current_user,oid,'USAGE'))
           FROM pg_catalog.pg_namespace WHERE nspname IN ('ag_catalog','sk_eft'))
           AND (SELECT pg_catalog.count(*)=2 FROM pg_catalog.pg_namespace WHERE nspname IN ('ag_catalog','sk_eft')),
 'labels', (SELECT pg_catalog.count(*)>=2 AND pg_catalog.bool_and(pg_catalog.has_table_privilege(current_user,oid,'SELECT')) FROM labels),
 'owners', (SELECT pg_catalog.bool_and(nspowner IN (SELECT oid FROM creators)) FROM graph_schema)
           AND (SELECT pg_catalog.bool_and(relowner IN (SELECT oid FROM creators)) FROM labels),
 'defaults_select', NOT EXISTS (SELECT 1 FROM creators cr WHERE NOT EXISTS
     (SELECT 1 FROM effective a WHERE a.creator=cr.oid AND a.privilege_type='SELECT')),
 'defaults_mutation', NOT EXISTS (SELECT 1 FROM effective WHERE privilege_type<>'SELECT')
)
"""
GRAPH_FLAGS = frozenset(('creators', 'graph', 'usage', 'labels', 'owners',
                         'defaults_select', 'defaults_mutation'))

# Preload GUC rows can be unavailable to an unelevated reader. Inspect its
# explicit role/database initialization declaration, then observe a tiny AGE
# read on this same fresh connection. Missing metadata never becomes readiness.
INITIALIZATION_SQL = """
WITH configured AS (
 SELECT setting, (CASE WHEN s.setrole<>0 THEN 2 ELSE 0 END +
                  CASE WHEN s.setdatabase<>0 THEN 1 ELSE 0 END) AS priority
 FROM pg_catalog.pg_db_role_setting s
 CROSS JOIN LATERAL pg_catalog.unnest(s.setconfig) AS setting
 WHERE s.setrole IN (0,(SELECT oid FROM pg_catalog.pg_roles WHERE rolname=current_user))
   AND s.setdatabase IN (0,(SELECT oid FROM pg_catalog.pg_database WHERE datname=current_database()))
   AND setting LIKE 'session_preload_libraries=%%'
)
SELECT pg_catalog.array_agg(setting) FROM configured
WHERE priority=(SELECT pg_catalog.max(priority) FROM configured)
"""
SETTINGS_SQL = """
SELECT pg_catalog.current_setting('transaction_read_only'),
       pg_catalog.current_setting('statement_timeout'),
       pg_catalog.current_setting('lock_timeout'),
       pg_catalog.current_setting('search_path')
"""
PROBE_SQL = """SELECT ag_catalog.agtype_out(r) FROM ag_catalog.cypher('sk_eft',
 $dashboard_probe$ RETURN 7 $dashboard_probe$) AS (r ag_catalog.agtype) LIMIT 2"""


def _one(cur, sql, params=None):
    cur.execute(sql, params) if params is not None else cur.execute(sql)
    rows = cur.fetchmany(2)
    if len(rows) != 1:
        raise ReadUnavailable('incomplete or duplicate admission result')
    return rows[0]


def _flags(cur, sql, required, params=None):
    row = _one(cur, sql, params)
    if (len(row) != 1 or not isinstance(row[0], dict) or set(row[0]) != required
            or any(value is not True for value in row[0].values())):
        raise ReadUnavailable('unsafe or unknown catalog evidence')


def _admit(cur, endpoint):
    _flags(cur, IDENTITY_SQL, IDENTITY_FLAGS,
           (endpoint.user, endpoint.user, endpoint.database))
    _flags(cur, FUNCTION_SQL, {'signatures', 'overloads'})
    row = _one(cur, CREATOR_SQL)
    if len(row) != 2:
        raise ReadUnavailable('creator configuration unavailable')
    effective, configured = row
    if (not isinstance(effective, str) or not isinstance(configured, list)
            or configured != ['sk_eft.dashboard_label_creators=' + effective]):
        raise ReadUnavailable('creator configuration provenance unknown')
    creators = effective.split(',')
    if (not creators or len(creators) != len(set(creators))
            or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_$-]{0,62}', name) for name in creators)):
        raise ReadUnavailable('malformed creator configuration')
    _flags(cur, GRAPH_SQL, GRAPH_FLAGS, (creators, len(creators)))
    initialization = _one(cur, INITIALIZATION_SQL)
    if (len(initialization) != 1 or not isinstance(initialization[0], list)
            or len(initialization[0]) != 1 or not isinstance(initialization[0][0], str)):
        raise ReadUnavailable('initialization evidence unavailable')
    name, separator, value = initialization[0][0].partition('=')
    if (name != 'session_preload_libraries' or separator != '='
            or 'age' not in [v.strip().strip('"') for v in value.split(',')]):
        raise ReadUnavailable('AGE preloading not provisioned')
    if _one(cur, PROBE_SQL) != ('7',):
        raise ReadUnavailable('trusted AGE initialization read failed')


def execute_read_query(psycopg, endpoint: ReaderEndpoint, query: str):
    """Fresh connection; fail closed, rollback and close on every path."""
    conn = None
    cur = None
    admitted = False
    try:
        conn = psycopg.connect(endpoint.dsn, connect_timeout=5, autocommit=True)
        cur = conn.cursor()
        try:
            cur.execute('BEGIN READ ONLY')
            cur.execute("SET LOCAL statement_timeout = '5s'")
            cur.execute("SET LOCAL lock_timeout = '1s'")
            cur.execute('SET LOCAL search_path = ag_catalog, pg_catalog')
            _admit(cur, endpoint)
            if _one(cur, SETTINGS_SQL) != ('on', '5s', '1s', 'ag_catalog, pg_catalog'):
                raise ReadUnavailable('execution-point settings unsafe')
        except Exception as exc:
            raise ReadUnavailable('reader admission failed') from exc
        admitted = True
        # This dollar-literal method was measured with AGE/psycopg. It is not
        # bound Cypher source; reject its exact closing delimiter before use.
        tag = 'cyq' + secrets.token_hex(8)
        if f'${tag}$' in query:
            raise QueryRejected('query rejected')
        sql = ("SELECT ag_catalog.agtype_out(r) FROM ag_catalog.cypher('sk_eft', "
               f'${tag}$ {query} ${tag}$) AS (r ag_catalog.agtype) LIMIT 1001')
        cur.execute(sql)
        rows = cur.fetchmany(MAX_ROWS + 1)
        if len(rows) > MAX_ROWS:
            raise QueryOverflow('query exceeds 1000 row limit')
        return rows
    except Exception as exc:
        if not admitted and not isinstance(exc, ReadUnavailable):
            raise ReadUnavailable('reader connection unavailable') from exc
        raise
    finally:
        # Nested finally blocks also close the connection if cursor/rollback
        # cleanup itself fails. No successful request leaves a transaction open.
        try:
            if conn is not None:
                conn.rollback()
        finally:
            try:
                if cur is not None:
                    cur.close()
            finally:
                if conn is not None:
                    conn.close()
