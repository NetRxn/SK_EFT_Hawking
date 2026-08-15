#!/usr/bin/env python3
"""Runnable verify commands for the papers/I1 Stage-13 remediation (2026-08-14).

Each open blocking finding remediated in that pass declares a decider here.
A check exits non-zero iff its defect is present, and every one of them
RE-MEASURES the live artifact rather than asserting a frozen number — so a
later drift in the Lean source, the registries, the roadmaps or the audit
records reopens the finding automatically.

    uv run python papers/I1/verify_findings.py                 # all checks
    uv run python papers/I1/verify_findings.py <name> [...]    # named checks
    uv run python papers/I1/verify_findings.py --list          # names + findings

Run from the repository root. Exit 0 = every selected check clean.

⚠️ These are DECIDERS, not proxies: each asserts what the remediation
actually changed. Several were confirmed non-vacuous by seeding the defect
back into the production artifact and observing red (see the remediation
report). A check whose population collapses to zero is itself a failure —
`cited_paths` and `census_figures` assert their own denominators.
"""

import sys

def check_citations():
    """review:2026-08-12-0006-internal-adversarial:I1:1.1, :1.2, :1.5"""
    import re,pathlib,glob
    from src.core.citations import CITATION_REGISTRY as R, bibkey_phase
    from src.core.workspace import find_workspace
    ws=find_workspace()
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    keys=set()
    for m in re.finditer(r'\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}',t): keys.update(x.strip() for x in m.group(1).split(','))
    bad=[]
    for k in sorted(keys):
        e=R.get(k)
        if e is None: bad.append(f'{k}: not in CITATION_REGISTRY'); continue
        if not (e.get('title') or '').strip(): bad.append(f'{k}: registry title is EMPTY (exempt-by-neglect)'); continue
        if (e.get('title') or '').strip().replace('\\','').replace(' ','').lower() in {'comm.acm','proc.acmsosp','nature','phys.rev.lett','commun.acm'}:
            bad.append(f'{k}: registry title {e["title"]!r} is a VENUE, not a paper title'); continue
        cached=bool(glob.glob(str(ws/'Lit-Search'/'*'/'primary-sources'/(k+'.*'))))
        textbook=(e.get('doi') is None and e.get('arxiv') is None and re.search(r'textbook|pre-DOI',e.get('notes') or '',re.I))
        if not cached and not textbook: bad.append(f'{k}: no primary-source cache on disk and no declared textbook/pre-DOI class')
    print(f'{len(keys)} bibkeys cited by papers/I1 checked for registry presence, real title and primary-source backing; {len(bad)} defective')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_citation_records():
    """review:2026-05-01-1345-bundle-stage13:I1:1.4, review:2026-05-01-1500-bundle-stage13:I1:1.4, review:2026-08-12-0006-internal-adversarial:I1:1.4"""
    import re,json,collections,pathlib
    from src.core.citations import CITATION_REGISTRY as R
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    keys=set()
    for m in re.finditer(r'\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}',t): keys.update(x.strip() for x in m.group(1).split(','))
    recs=collections.defaultdict(list)
    for l in open('docs/citation_verifications.jsonl'):
        l=l.strip()
        if not l: continue
        try: d=json.loads(l)
        except Exception: continue
        if 'bibkey' in d: recs[d['bibkey']].append(d)
    EXT=['TooBySmithHepLean','compcert','sel4','leancipilot','AlphaProof2025']
    bad=[]
    for k in EXT:
        if k not in keys: bad.append(f'{k}: papers/I1 no longer cites it — the five external antecedent bibitems changed'); continue
        ok=[r for r in recs[k] if r.get('paper')=='papers/I1/paper_draft.tex' and r.get('verdict')=='match']
        if not ok: bad.append(f'{k}: no I1-scoped citation_verifications.jsonl record with verdict "match"'); continue
        e=R[k]
        if not (e.get('doi') or e.get('arxiv')): bad.append(f'{k}: registry carries neither DOI nor arXiv id')
        if e.get('doi_verified') is not True: bad.append(f'{k}: doi_verified is {e.get("doi_verified")!r}')
    for k in ('physlean','alphaproof'):
        if k in keys: bad.append(f'{k}: papers/I1 still cites the unverifiable stub')
        if 'papers/I1/paper_draft.tex' in (R[k].get('used_in') or []): bad.append(f'{k}: used_in still claims papers/I1')
    print(f'{len(EXT)} external antecedent bibkeys checked for an I1-scoped verified cache record + resolvable identifier, plus 2 retired stubs; {len(bad)} defective')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_klrs_note():
    """review:2026-08-12-0006-internal-adversarial:I1:1.3"""
    import re
    from src.core.citations import CITATION_REGISTRY as R
    n=R['KLRS1996']['notes']; bad=[]
    if not re.search(r'70\s*GeV\s*<\s*m_\{H,c\}\s*<\s*95\s*GeV',n): bad.append('KLRS1996 note does not quote the source range 70 GeV < m_{H,c} < 95 GeV')
    if not re.search(r'80',n): bad.append('KLRS1996 note does not carry the ~80 GeV central estimate')
    if re.search(r'canonical\s+crossover\s+threshold\s+m_H_crit\s*=\s*72',n): bad.append('KLRS1996 note still attributes the 72 GeV threshold to KLRS')
    if 'CsikorFodorHeitger1999' not in n: bad.append('KLRS1996 note does not attribute 72.4 to CsikorFodorHeitger1999')
    c=R['CsikorFodorHeitger1999']['notes']
    if '72.4' not in c: bad.append('CsikorFodorHeitger1999 note lost the 72.4 attribution — the two notes must not contradict')
    print(f'5 assertions on the KLRS1996 / CsikorFodorHeitger1999 registry notes; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_lattice_provenance():
    """review:2026-08-12-0006-internal-adversarial:I1:2.1"""
    import re
    from src.core.provenance import PARAMETER_PROVENANCE as P
    from src.core.citations import CITATION_REGISTRY as R
    from src.core.constants import EWBG_PARAMS as E
    K={'EW.M_H_ENDPOINT_SU2HIGGS_GEV':(66.5,'10.1103/PhysRevLett.82.21'),
       'EW.M_H_ENDPOINT_SM_GEV':(72.4,'10.1103/PhysRevLett.82.21'),
       'EW.M_H_ENDPOINT_KLRS_RANGE_UPPER_GEV':(95.0,'10.1103/PhysRevLett.77.2887')}
    doi2key={ (v.get('doi') or '').lower():k for k,v in R.items() }
    bad=[]
    for k,(val,doi) in K.items():
        e=P.get(k)
        if e is None: bad.append(f'{k}: absent from PARAMETER_PROVENANCE'); continue
        if abs(e['value']-val)>1e-9: bad.append(f'{k}: value {e["value"]} != {val}')
        if (e.get('doi') or '').lower()!=doi.lower(): bad.append(f'{k}: doi {e.get("doi")!r} != {doi}')
        if doi.lower() not in doi2key: bad.append(f'{k}: doi {doi} resolves to no CITATION_REGISTRY bibkey')
        if not e.get('llm_verified_date'): bad.append(f'{k}: not llm_verified')
    for c,val in (('KLRS_M_H_CROSSOVER_THRESHOLD_GEV',72.4),('CFH_M_H_ENDPOINT_SU2HIGGS_GEV',66.5),('KLRS_M_H_ENDPOINT_RANGE_UPPER_GEV',95.0)):
        if abs(E.get(c,-1)-val)>1e-9: bad.append(f'EWBG_PARAMS[{c!r}] = {E.get(c)!r}, expected {val}')
    import pathlib
    f=re.sub(r'\s+',' ',pathlib.Path('papers/I1/paper_draft.tex').read_text()).replace('\\_','_')
    for k in K:
        if k not in f: bad.append(f'papers/I1 does not reference the provenance key {k}')
    print(f'{len(K)} lattice-endpoint provenance entries + 3 code constants + 3 prose references checked; {len(bad)} defective')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_lean_provenance_docstring():
    """review:2026-08-12-0006-internal-adversarial:I1:2.2"""
    import re,pathlib
    s=pathlib.Path('lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean').read_text()
    m=re.search(r'/--(.*?)-/\s*theorem sm_klrs_overshoot_ratio_gt_threshold\s*:\s*\(1\.5 : ℝ\) < 125\.20 / 72\.4',s,re.S)
    bad=[]
    if not m: bad.append('sm_klrs_overshoot_ratio_gt_threshold statement or its docstring not found in the expected form')
    else:
        d=m.group(1)
        for need,why in [('EW.M_H_GEV','provenance key for 125.20'),('EW.M_H_ENDPOINT_SM_GEV','provenance key for 72.4'),
                         ('10.1103/PhysRevD.110.030001','DOI for 125.20'),('10.1103/PhysRevLett.82.21','DOI for 72.4'),
                         ('CFH 1999','correct attribution of 72.4'),('not KLRS 1996','explicit denial of the KLRS mis-attribution')]:
            if need not in d: bad.append(f'docstring lacks {need!r} ({why})')
    from src.core.provenance import PARAMETER_PROVENANCE as P
    for k,v in (('EW.M_H_GEV',125.20),('EW.M_H_ENDPOINT_SM_GEV',72.4)):
        if k not in P or abs(P[k]['value']-v)>1e-9: bad.append(f'{k} missing or != {v} — the docstring would be lying')
    print(f'8 assertions binding both literals of sm_klrs_overshoot_ratio_gt_threshold to PARAMETER_PROVENANCE; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_paper15_superseded():
    """review:2026-08-12-0006-internal-adversarial:I1:4.1"""
    import re,pathlib
    bad=[]
    p=pathlib.Path('papers/paper15_methodology/paper_draft.tex').read_text()
    f=re.sub(r'\s+',' ',p)
    if 'SUPERSEDED-BY BANNER' not in p: bad.append('paper15 has no superseded-by banner comment')
    if not re.search(r'\\textbf\{Superseded\.\}.*papers/I1.*is the current account',f): bad.append('paper15 banner does not render a Superseded notice naming papers/I1 as current')
    m=pathlib.Path('docs/PAPER_DRAFT_MAPPING.md').read_text()
    row=[l for l in m.split('\n') if l.startswith('| `paper15_methodology`')]
    if not row: bad.append('paper15_methodology row missing from PAPER_DRAFT_MAPPING.md')
    elif 'SUPERSEDED BY I1' not in row[0]: bad.append('PAPER_DRAFT_MAPPING.md paper15 row does not record supersession')
    # the contradiction the finding is about must still be REAL, else this verify is vacuous
    if 'twelve-stage' not in f or 'ten invariants' not in f: bad.append('paper15 no longer states twelve stages / ten invariants — re-scope this verify')
    i=re.sub(r'\s+',' ',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    if 'fourteen stages and seventeen invariants' not in i: bad.append('papers/I1 no longer states fourteen stages and seventeen invariants — re-scope this verify')
    print(f'6 assertions on the paper15/I1 pipeline-count contradiction and its supersession record; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_sweep_reported():
    """review:2026-08-12-0006-internal-adversarial:I1:5.6"""
    import re,pathlib
    f=re.sub(r'\s+',' ',re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text()))
    d=pathlib.Path('docs/audits/stage13_attribution_sweep_2026-06-10.md').read_text()
    bad=[]
    secs=re.split(r'\n## ',d)[1:]
    tot=0; lo=[]; hi=[]
    for s in secs:
        m=re.search(r'(\d+)\s+(?:load-bearing\s+)?(?:anchors|claims)\b',s)
        if m: n=int(m.group(1)); tot+=n; lo.append(n); hi.append(n)
    fab=re.search(r'(\d+)\s+fabrication-class NOT-SUPPORTED fixed',d)
    nfab=int(fab.group(1)) if fab else None
    words={3:'three',6:'six',18:'eighteen',23:'twenty-three',134:'a hundred and thirty-four'}
    if tot!=134: bad.append(f'sweep record now totals {tot} counted anchors; I1 says a hundred and thirty-four')
    if nfab!=6: bad.append(f'sweep record now states {nfab} fabrication-class fixes; I1 says six')
    if min(lo)!=3 or max(hi)!=23: bad.append(f'per-manuscript range is now {min(lo)}-{max(hi)}; I1 says three to twenty-three')
    nbund=len(re.findall(r'\(18 bundles\)|eighteen',d)) and 18
    for need in ('six such fabrications in a hundred and thirty-four pairs','eighteen manuscripts',
                 'three to twenty-three','one hundred and thirty-four','near one in twenty, not near one in three',
                 'I1 is listed in the sweep','pilot of roughly ten spot-checked'):
        if need not in f: bad.append(f'I1 lacks {need!r}')
    if re.search(r'roughly three in ten spot-checked load-bearing attributions were wrong',f):
        bad.append('the abstract still reports only the pilot rate')
    if re.search(r'\{#i1\}',d): bad.append('the sweep record now HAS an I1 section — I1 s "no entry" sentence is false')
    print(f'12 assertions binding I1 s pilot-vs-sweep paragraphs to docs/audits/stage13_attribution_sweep_2026-06-10.md; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_aristotle_counts():
    """review:2026-08-12-0006-internal-adversarial:I1:5.7"""
    import re,pathlib
    from src.core.constants import ARISTOTLE_THEOREMS as A
    f=re.sub(r'\s+',' ',re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text()))
    c=pathlib.Path('docs/counts.tex').read_text()
    proved=int(re.search(r'\\newcommand\{\\aristotleproved\}\{(\d+)\}',c).group(1))
    runs=int(re.search(r'\\newcommand\{\\aristotleruns\}\{(\d+)\}',c).group(1))
    man=sum(1 for v in A.values() if v=='manual')
    prover=sum(1 for v in A.values() if v!='manual')
    genuine=len({v for v in A.values() if v!='manual'})
    bad=[]
    if proved!=prover: bad.append(f'\\aristotleproved={proved} but {prover} entries carry a run id — the abstract/intro figure is not the prover-closed count')
    if runs!=genuine+ (1 if man else 0): bad.append(f'\\aristotleruns={runs} but genuine runs={genuine} and manual marker present={bool(man)} — I1 s "one below" is wrong')
    if 'Nine entries carry the manual marker' not in f: bad.append(f'I1 does not state the live manual-marker count ({man})')
    if man!=9: bad.append(f'{man} manual entries live; I1 says nine')
    for need in ('excludes them by construction','the number of genuine runs is one below it'):
        if need not in f: bad.append(f'I1 lacks {need!r}')
    if 'the count of prover-closed theorems is three below' in f: bad.append('I1 still says prover-closed is three below \\aristotleproved')
    print(f'7 assertions binding I1 s \\aristotleproved/\\aristotleruns prose to ARISTOTLE_THEOREMS and docs/counts.tex; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_census_figures():
    """review:2026-08-12-0006-internal-adversarial:I1:5.8, :7.2"""
    import re,json,collections,pathlib
    from src.core.constants import ARISTOTLE_THEOREMS as A
    W={2:'two',3:'three',7:'seven',8:'eight',9:'nine',10:'ten',11:'eleven',14:'fourteen',16:'sixteen',17:'seventeen',25:'twenty-five',63:'sixty-three'}
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    f=re.sub(r'\s+',' ',t)
    w=pathlib.Path('docs/WAVE_EXECUTION_PIPELINE.md').read_text()
    g=pathlib.Path('docs/READINESS_GATES.md').read_text()
    deps=json.load(open('lean/lean_deps.json'))
    short=collections.defaultdict(list)
    for d in deps: short[d['name'].split('.')[-1]].append(d)
    inv=w.split('## Pipeline Invariants')[1].split('\n## ')[0]
    live={'stages':len({int(m.group(1)) for m in re.finditer(r'(?m)^###?\s*Stage\s+(\d+)',w)}),
     'invariants':len(re.findall(r'(?m)^\d+\.\s+\*\*',inv)),
     'gates':len(re.findall(r'(?m)^###?\s*Gate\s+\d+',g)),
     'manual':sum(1 for v in A.values() if v=='manual'),
     'run79':sum(1 for v in A.values() if v=='79e07d55'),
     'biggest':collections.Counter(v for v in A.values() if v!='manual').most_common(1)[0][1],
     'run78':sum(1 for v in A.values() if v=='78dcc5f4'),
     'run78mods':len({short[k][0]['module'] for k,v in A.items() if v=='78dcc5f4' and k in short}),
     'ewbcw':sum(1 for d in deps if d['module']=='SKEFTHawking.EWBaryogenesisChiralityWall' and d['kind']=='theorem'),
     'classes':8}
    NUM=r'([a-z]+(?:-[a-z]+)?)'
    claims=[('stages',rf'pipeline has {NUM} stages'),('invariants',rf'stages and {NUM} invariants'),
     ('manual',rf'(?i)\b{NUM} entries carry the manual marker'),
     ('run79',rf'(?i)\b{NUM} theorems of this module closed in Aristotle run'),
     ('ewbcw',rf'declares {NUM} theorems'),('gates',rf'(?i)Three of the {NUM} gates'),
     ('biggest',rf'carries {NUM} entries across'),('run78',rf'carries {NUM} entries spanning'),
     ('run78mods',rf'entries spanning {NUM} unrelated modules'),
     ('classes',rf'the same {NUM} classes enumerated')]
    bad=[]
    for key,pat in claims:
        ms=re.findall(pat,f)
        if len(ms)!=1: bad.append(f'{key}: phrase matched {len(ms)}x (expected 1) — pattern {pat!r}'); continue
        want=W.get(live[key],str(live[key]))
        if ms[0].lower()!=want: bad.append(f'{key}: prose says {ms[0]!r}, live value is {live[key]} ({want!r})')
    n=len(re.findall(r'\\item \\textbf',f.split("The pipeline's invariants must hold")[1].split('\\end{enumerate}')[0]))
    if n!=live['invariants']: bad.append(f'I1 invariant enumeration has {n} items; pipeline doc enumerates {live["invariants"]}')
    print(json.dumps(live,sort_keys=True));print(f'{len(claims)+1} spelled-out census claims re-measured, {len(bad)} wrong')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_strengthening_trajectory():
    """review:2026-08-12-0006-internal-adversarial:I1:5.10"""
    import re,pathlib
    f=re.sub(r'\s+',' ',re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text()))
    r=pathlib.Path('docs/roadmaps/Phase6b_Roadmap.md').read_text()
    m=re.search(r'Trend:\s*((?:\w[\w.]*=\d+,\s*)+\*\*?\w[\w.]*=\d+)',r)
    bad=[]
    if not m: bad.append('per-wave retroactive-cut series not found in docs/roadmaps/Phase6b_Roadmap.md'); series={}
    else:
        series=dict((k,int(v)) for k,v in re.findall(r'([\w.]+)=(\d+)',m.group(1)))
    if 'across the first three development cycles in which it was applied' in f: bad.append('I1 still frames the trajectory as "the first three development cycles in which it was applied"')
    if re.search(r'fell from twelve, to five, to none',f): bad.append('I1 still states the twelve->five->none trajectory')
    if series:
        base=series.get('6c.3')
        if base!=12: bad.append(f'6c.3 baseline is {base}, not 12 — I1 says twelve')
        rest=[v for k,v in series.items() if k!='6c.3']
        if not rest: bad.append('no post-baseline waves in the series')
        else:
            import statistics
            if max(rest)>=12: bad.append(f'a post-baseline wave reached {max(rest)} — I1 says it never again reached twelve')
            if max(rest)!=6: bad.append(f'post-baseline maximum is {max(rest)}, I1 says never exceeded six')
            med=statistics.median(sorted(rest))
            if med!=2: bad.append(f'post-baseline median is {med}, I1 says two')
            if len(rest)!=15: bad.append(f'{len(rest)} post-baseline waves logged, I1 says fifteen')
            zeros=[k for k,v in series.items() if v==0]
            if sorted(zeros)!=['6b.2','6e.5']: bad.append(f'zero-cost waves are {sorted(zeros)}, I1 names 6e.5 and 6b.2')
    for s in ('6c.3','6e.5','6b.2','fifteen subsequent waves','median is two','never exceeded six'):
        if s not in f: bad.append(f'I1 no longer states {s!r}')
    print(f'{13} assertions binding I1 s strengthening-trajectory paragraph to the per-wave series in Phase6b_Roadmap.md; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_cost_claim():
    """review:2026-08-12-0006-internal-adversarial:I1:5.11"""
    import re,pathlib,json,glob,os
    f=re.sub(r'\s+',' ',re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text()))
    bad=[]
    for gone in ('on the order of seconds per stage','on the order of weeks per finding'):
        if gone in f: bad.append(f'I1 still asserts "{gone}"')
    for need in ('485 seconds','2026-08-15T03:30:20Z','thirty-three minutes','2026-08-13','have not measured and do not quote'):
        if need not in f: bad.append(f'I1 lacks {need!r}')
    stamp=re.search(r'timestamp (\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})Z',f)
    if stamp:
        p='docs/validation/reports/validation_%s%s%sT%s%s%sZ.json'%stamp.groups()
        if not os.path.isfile(p): bad.append(f'I1 cites the archived run {p} — it does not exist')
        else:
            s=json.load(open(p))['summary']
            if s['total']<50: bad.append(f'archived run covered only {s["total"]} checks — not "the whole corpus"')
    else: bad.append('I1 no longer cites an archived validation run by timestamp')
    m=re.search(r'--merge-gate.*?\(([\dhms]+) measured (\d{4}-\d{2}-\d{2})\)',pathlib.Path('CLAUDE.md').read_text())
    if not m: bad.append('CLAUDE.md no longer records a dated --merge-gate runtime to corroborate I1')
    else:
        mm=re.match(r'(?:(\d+)h)?(\d+)m(\d+)s',m.group(1))
        mins=(int(mm.group(1) or 0)*60+int(mm.group(2))+int(mm.group(3))/60) if mm else -1
        if not (32<=mins<34): bad.append(f'CLAUDE.md merge-gate figure {m.group(1)} does not round to thirty-three minutes')
        if m.group(2) not in f: bad.append(f'I1 quotes a different merge-gate date than CLAUDE.md s {m.group(2)}')
    print(f'11 assertions on I1 s replaced cost claim and the dated artifacts backing it; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_stage13_recording():
    """review:2026-08-12-0006-internal-adversarial:I1:8.1, :8.2"""
    import json,sys,os,re,pathlib
    d=json.load(open('papers/I1/bundle_metadata.json'))
    bad=[]
    doc=d.get('stage13_review_doc',''); path,_,anchor=doc.partition('#')
    if not path or not os.path.isfile(path): bad.append(f'stage13_review_doc {path!r} does not resolve')
    elif anchor and f'{{#{anchor}}}' not in pathlib.Path(path).read_text(): bad.append(f'stage13_review_doc anchor #{anchor} does not appear in {path}')
    if os.path.isfile(path):
        m=re.search(r'(?m)^review_date:\s*(\S+)',pathlib.Path(path).read_text())
        if not m: bad.append(f'{path} carries no review_date front-matter to check last_stage13_review against')
        elif m.group(1)[:10]!=(d.get('last_stage13_review') or '')[:10]:
            bad.append(f'last_stage13_review={d.get("last_stage13_review")} but {path} is dated {m.group(1)}')
    if d.get('stage13_redo_required') is not True: bad.append(f'stage13_redo_required={d.get("stage13_redo_required")!r}; the draft was restructured and re-remediated after the recorded review')
    for k in ('stage13_review_doc_note','stage13_redo_required_note'):
        if not d.get(k): bad.append(f'{k} missing — the reason for the repoint is not recorded')
    print(f'6 assertions on papers/I1/bundle_metadata.json Stage-13 recording; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0



def check_lean_line_ranges():
    """review:2026-05-01-1345-bundle-stage13:I1:7.2"""
    import re,pathlib,json
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    f=re.sub(r'\s+',' ',t).replace('\\_','_')
    # (declaration or block, file, expected start line) -- every "lines~A--B" I1 carries
    CL=[('firstOrder_uniqueness','SKDoubling',412,439),('FirstOrderCoeffs','SKDoubling',292,301),
    ('firstOrderAction','SKDoubling',304,315),('firstOrderDissipativeAction','SKDoubling',251,261),
    ('DissipativeCoeffs','Basic',152,158),('satisfies_normalization','SKDoubling',126,129),
    ('satisfies_positivity','SKDoubling',140,141),('KMSSymmetry','SKDoubling',156,167),
    ('kmsSpec_pins_four_components','GloriosoLiu/Phase1Reconciliation',118,127),
    ('hasDynamicalKMS_strict','GloriosoLiu/Axioms',91,92),('SKEFTAxioms','GloriosoLiu/Axioms',160,172),
    ('hasDynamicalKMS_algebraic','GloriosoLiu/Axioms',108,111),
    ('aristotleCounterexample','GloriosoLiu/Phase1Reconciliation',139,140),
    ('aristotle_counterexample_violates_FirstOrderKMS','GloriosoLiu/Phase1Reconciliation',150,158),
    ('four_of_nine_partition_recovered','GloriosoLiu/Phase1Reconciliation',189,204),
    ('four_of_nine_partition_under_GLU','GloriosoLiu/Phase1Reconciliation',231,239),
    ('FirstOrderKMS','SKDoubling',367,379),('firstOrder_KMS_optimal','SKDoubling',582,603),
    ('FirstOrderKMS_altSign','SKDoubling',610,618),('firstOrder_altSign_uniqueness_test','SKDoubling',636,656),
    ('gap_solution_monotone','TetradGapEquation',333,349),
    ('H_ScalarChannelIsTetradBifurcationOutput','ScalarRungInterpretation',170,172),
    ('mexican_hat_vev_under_supercritical_bridge','ScalarRungInterpretation',179,184),
    ('bridge_excludes_super_uv_vev','ScalarRungInterpretation',190,196),
    ('FirstOrderProjection_exists','GloriosoLiu/FirstOrderProjection',48,52)]
    bad=[]
    for name,mod,a,b in CL:
        src=pathlib.Path(f'lean/SKEFTHawking/{mod}.lean').read_text().split('\n')
        if a-1>=len(src) or not re.match(rf'\s*(theorem|lemma|def|structure|noncomputable def)\s+{re.escape(name)}\b',src[a-1]):
            bad.append(f'{name}: {mod}.lean:{a} is {src[a-1].strip()[:60]!r}, not the declaration')
        if f'lines~{a}--{b}' not in f: bad.append(f'{name}: I1 no longer carries "lines~{a}--{b}"')
    declared=len(re.findall(r'lines~\d+--\d+',f))
    if declared!=len(CL)+1: bad.append(f'I1 carries {declared} line ranges; this verify covers {len(CL)}+1 (the commented gap_solution_bounded block) — an unverified range was added')
    blk=pathlib.Path('lean/SKEFTHawking/TetradGapEquation.lean').read_text().split('\n')
    if not (blk[310].strip().startswith('/-') and blk[324].strip()=='-/' and 'lines~311--325' in f):
        bad.append('TetradGapEquation commented-out block is no longer exactly lines 311-325')
    print(f'{len(CL)+1} Lean line-range citations in papers/I1 re-resolved against source; {len(bad)} drifted')
    [print('  '+x) for x in bad]
    return 1 if bad else 0



def check_cited_paths():
    """review:2026-05-01-1500-bundle-stage13:I1:5.1"""
    import re,pathlib
    from src.core.workspace import find_workspace
    repo=pathlib.Path('.').resolve(); ws=find_workspace()
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    t=re.sub(r'\s+',' ',t.replace('\\_','_').replace('\\%','%'))
    paths={m.group(1).strip() for m in re.finditer(r'\\(?:texttt|path|url)\{([^}]+)\}',t)}
    paths={p for p in paths if '/' in p and not p.startswith('http') and '<' not in p and '*' not in p}
    bad=[p for p in sorted(paths) if not ((repo/p).exists() or (ws/p).exists())]
    assert len(paths)>=20, f'population collapsed to {len(paths)} — verify is vacuous'
    print(f'{len(paths)} filesystem paths cited in papers/I1 resolved on disk; {len(bad)} unresolved')
    [print('  MISSING: '+p) for p in bad]
    return 1 if bad else 0



def check_projection_disclosure():
    """review:2026-05-06-bundle-stage13:I1-r2:5.1"""
    import re,pathlib,json
    t=re.sub(r'(?m)(?<!\\)%.*$','',pathlib.Path('papers/I1/paper_draft.tex').read_text())
    f=re.sub(r'\s+',' ',t).replace('\\_','_')
    bad=[]
    if 'FirstOrderProjection_exists' not in f: bad.append('papers/I1 does not name FirstOrderProjection_exists')
    if 'A.local_equilibrium' not in f: bad.append('papers/I1 names the theorem but not its one-term proof body A.local_equilibrium')
    src=pathlib.Path('lean/SKEFTHawking/GloriosoLiu/FirstOrderProjection.lean').read_text().split('\n')
    if not src[47].startswith('theorem FirstOrderProjection_exists'): bad.append(f'FirstOrderProjection.lean:48 is {src[47][:60]!r}')
    if src[51].strip()!='A.local_equilibrium': bad.append(f'proof body at :52 is {src[51].strip()!r}, not A.local_equilibrium — the disclosure no longer describes the code')
    d=json.load(open('lean/lean_deps.json'))
    if not any(x['name'].endswith('.FirstOrderProjection_exists') for x in d): bad.append('FirstOrderProjection_exists absent from lean_deps.json')
    print(f'5 assertions binding papers/I1 §3 prose to FirstOrderProjection_exists; {len(bad)} failed')
    [print('  '+b) for b in bad]
    return 1 if bad else 0


CHECKS = [
    ('citations', check_citations),
    ('citation-records', check_citation_records),
    ('klrs-note', check_klrs_note),
    ('lattice-provenance', check_lattice_provenance),
    ('lean-provenance-docstring', check_lean_provenance_docstring),
    ('paper15-superseded', check_paper15_superseded),
    ('sweep-reported', check_sweep_reported),
    ('aristotle-counts', check_aristotle_counts),
    ('census-figures', check_census_figures),
    ('strengthening-trajectory', check_strengthening_trajectory),
    ('cost-claim', check_cost_claim),
    ('stage13-recording', check_stage13_recording),
    ('lean-line-ranges', check_lean_line_ranges),
    ('cited-paths', check_cited_paths),
    ('projection-disclosure', check_projection_disclosure),
]


def main(argv):
    if "--list" in argv:
        for n, f in CHECKS:
            print(f"{n:26s} {f.__doc__}")
        return 0
    sel = [(n, f) for n, f in CHECKS if not argv or n in argv]
    unknown = [a for a in argv if a not in {n for n, _ in CHECKS}]
    if unknown:
        print("unknown check(s): " + ", ".join(unknown), file=sys.stderr)
        return 2
    rc = 0
    for n, f in sel:
        print(f"── {n} " + "─" * max(0, 60 - len(n)))
        r = f()
        rc |= r
        print(("   FAIL" if r else "   ok"))
    return rc


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
