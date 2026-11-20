import ast,hashlib,json,re,subprocess,xml.etree.ElementTree as ET
from pathlib import Path
R=Path('/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103'); W=R.parent
out={}
def old(p): return subprocess.check_output(['git','show','HEAD:'+p],cwd=R).decode()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def reg(s):
 for x in ast.parse(s).body:
  if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CITATION_REGISTRY' for t in x.targets): return ast.literal_eval(x.value)
a=reg(old('src/core/citations.py')); b=reg((R/'src/core/citations.py').read_text()); adds=set(b)-set(a); changes=[k for k in a if a[k]!=b.get(k)]
assert len(a)==664 and len(b)==677 and len(adds)==13 and changes==['BarceloLRR2005']
out['registry']={'before':len(a),'after':len(b),'added':sorted(adds),'old_changed':changes,'removed':sorted(set(a)-set(b))}
prep=json.loads(Path('/tmp/l1-citation-adoption-preparation-r2.json').read_text())
for row in prep['focused_paths']:
 if row['path']!='src/core/constants.py': assert sha(R/row['path'])==row['prepared_postimage_sha256']
internal=[k for k in adds if b[k]['inprep']]; assert len(internal)==8
for k in internal: assert all(b[k][f] is None for f in ['doi','arxiv','primary_source_path','doi_verified']) and not b[k].get('citation_class')
companions=json.loads(Path('/tmp/l1-citation-predecessor-companion-identities.json').read_text())
for row in companions:
 assert row['key'] in internal and b[row['key']]['title']==row['donor_title'] and b[row['key']]['authors']==row['donor_authors']
 s=(R/'papers'/row['companion']/'paper_draft.tex').read_text(); assert row['title'] in s and row['author'] in s
out['internal']=sorted(internal)
for p in ['papers/D1/paper_draft.tex','papers/D3/paper_draft.tex','papers/D9/paper_draft.tex','papers/E1/paper_draft.tex']:
 x=old(p); y=(R/p).read_text(); assert x.split(r'\begin{thebibliography}')[0]==y.split(r'\begin{thebibliography}')[0] and x.split(r'\end{thebibliography}')[1]==y.split(r'\end{thebibliography}')[1]
out['manuscript_bodies_unchanged']=True
s0=json.loads(old('docs/primary_sources_state.json')); s1=json.loads((R/'docs/primary_sources_state.json').read_text()); new=set(s1['entries'])-set(s0['entries']); assert new==adds-set(internal)
assert all(s1['entries'][k]==v for k,v in s0['entries'].items()) and s1['_schema_version']==s0['_schema_version']==1
wr=json.loads(Path('/tmp/l1-citation-current-writer.json').read_text()); assert sha(R/'scripts/back_fill_primary_sources.py')==wr['writer_script_sha256']
for p,m in wr['held_metadata'].items():
 p=Path(p); st=p.stat(); assert sha(p)==m['sha256'] and st.st_mode==m['mode'] and st.st_mtime_ns==m['mtime_ns'] and st.st_size==m['size']
for row in wr['actual_main_invocations']: assert row['record']==s1['entries'][row['record']['bibkey']] and row['exit']==0 and "pre-existing': 1" in row['stderr']
v=json.loads((W/b['Verlinde1988']['primary_source_path']).read_text()); assert v['message-type']=='work' and not v['message'].get('abstract')
out['state']={'old_entries_preserved':len(s0['entries']),'new_keys':sorted(new),'writer_script_sha256':wr['writer_script_sha256'],'held_current_metadata_equal':True,'Verlinde_metadata_only':True}
for p,m in json.loads(Path('/tmp/l1-citation-pre-control-source.json').read_text()).items():
 f=R/p; st=f.stat(); assert sha(f)==m['sha256'] and st.st_mode==m['mode'] and st.st_mtime_ns==m['mtime_ns']
out['prepared_source_state_restored']=True
j=ET.parse('/tmp/l1-citation-adopted-full.xml').getroot(); tests=j.findall('.//testcase'); assert len(tests)==89 and all(t.find('failure') is None and t.find('error') is None and t.find('skipped') is None for t in tests)
required=json.loads(Path('/tmp/l1-citation-adopted-full-verification.json').read_text())['required_testcases']; assert set(required)<={t.attrib['name'] for t in tests}
assert sha(Path('/tmp/l1-citation-adopted-full.xml'))=='1258bfe63ba4d268515b9520971b280b4d11fd00fc6c8a50c51bf1dbd7cd3f09'
out['full_affected_tests']={'passed':89,'required_original_controls_present':required,'junit_sha256':sha(Path('/tmp/l1-citation-adopted-full.xml'))}
CITE=re.compile(r'\\cite[a-zA-Z]*\*?(?:\[[^\]]*\])*\{([^}]*)\}'); COMMENT=re.compile(r'(?<!\\)%.*$'); usage={}; allkeys=set()
for p in (R/'papers').glob('*/paper_draft.tex'):
 body='\n'.join(COMMENT.sub('',l) for l in p.read_text().splitlines()); keys={k.strip() for m in CITE.finditer(body) for k in m[1].split(',') if k.strip()}; allkeys|=keys
 if (p.parent/'bundle_metadata.json').exists():
  for k in keys: usage.setdefault(k,[]).append(p.parent.name)
assert len(allkeys)==516 and not allkeys-set(b)
gaps={k for k in usage if not b.get(k,{}).get('primary_source_path') or not (W/b[k]['primary_source_path']).exists() or 'abstract' in (W/b[k]['primary_source_path']).name.lower()}
assert len(gaps)==174
register=(R/'docs/SOURCE_ACQUISITION_REGISTER.md').read_text(); listed=set(re.findall(r'`([^`]+)`',register)); assert gaps<=listed
assert 'Zhao2023' not in usage and usage['Rokhlin1952']==['L2']
assert (R/'docs/source_acquisition_overlay.json').read_text()==old('docs/source_acquisition_overlay.json')
out['derived_register']={'current_bundle_usage_gap_count_own_writer_semantics':174,'all_gap_keys_listed':True,'Zhao2023_current_bundle_citations':[],'Rokhlin1952_current_bundle_citations':usage['Rokhlin1952'],'curated_overlay_unchanged':True,'limits':'Existing generator _holding uses abstract filename; metadata JSON is treated full; route uses Roehm2026 prefix rather than inprep. Current output is faithful to existing generator, not a new fidelity/body acquisition measurement. Rokhlin curated reason retains historical D2 bibitem text; current bundles column correctly L2.'}
assert 'CITATION_UNDECLARED_CLASS_CEILING = 76' in (R/'src/core/constants.py').read_text()
assert '76/76' in Path('/tmp/l1-citation-post-control-presence.txt').read_text()
out['ratchet']={'current_ceiling':76,'postcontrol_measurement':76,'zero_headroom':True}
out['head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(); out['hashes']={p:sha(R/p) for p in subprocess.check_output(['git','diff','--name-only'],cwd=R).decode().splitlines()}
Path('/tmp/publication-citation-adoption-review-r3-audit.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
