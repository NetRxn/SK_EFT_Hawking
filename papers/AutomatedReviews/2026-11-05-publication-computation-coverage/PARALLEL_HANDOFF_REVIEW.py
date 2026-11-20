from pathlib import Path
import hashlib,json,zipfile,zlib,subprocess,re
R=Path.cwd(); A=R/'docs/audits/2026-10-17-publication-substance-construction'; P=Path('/tmp'); out={'checks':{},'limitations':['Byte/provenance/source-only handoff review; no scientific imports, tests, controls, coefficients, state writers or Git mutations.','Historical review bodies retain their historical232 portable scope; current roadmap explicitly records234.','Scratch paths and dependencies need deliberate rebinding before remote execution.']}
def sha(b):return hashlib.sha256(b).hexdigest()
def run(args):
 p=subprocess.run(args,capture_output=True,text=True);out.setdefault('commands',[]).append({'argv':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr});assert p.returncode==0;return p.stdout
head=run(['git','rev-parse','HEAD']).strip();assert head=='cdc75df665dd68f783a49d1ce90969dcff91b7cb';out['head']=head
m=json.loads((A/'l1_k4_two_protected_tori_7981_source_design_manifest.json').read_text());zpath=A/'l1_k4_two_protected_tori_7981_source_design.zip';assert sha(zpath.read_bytes())==m['archive_sha256'];out['archive_sha256']=m['archive_sha256']
rows=[]
with zipfile.ZipFile(zpath) as z:
 assert z.testzip() is None
 assert len(z.namelist())==20==len(set(z.namelist()))==len(m['files'])
 assert set(z.namelist())=={x['name'] for x in m['files']}
 for f in m['files']:
  n=f['name'];b=z.read(n);original=(P/n).read_bytes();info=z.getinfo(n)
  assert b==original and len(b)==f['bytes'] and sha(b)==f['sha256'] and zlib.crc32(b)==info.CRC
  rows.append(dict(name=n,bytes=len(b),sha256=sha(b),crc32=info.CRC,exact_original=True))
 assert sha(z.read('l1-7981-evaluator-draft-r1.py'))=='e4a228c1194e303001edb65ecdb416d3f9067eb90990bb45726bba91613f39e7'
 out['failed_checker_attempts']={n:json.loads(z.read(n)) for n in ['l1-7981-review-attempt1.json','l1-7981-review-attempt2.json']}
 capture=json.loads(z.read('l1-residual38-second-family-geometry.json'))
 out['scientific_preimages']=[]
 for n,h in capture['source_sha256'].items():
  b=(A/n).read_bytes();assert sha(b)==h;out['scientific_preimages'].append({'path':str((A/n).relative_to(R)),'sha256':h})
 assert len(out['scientific_preimages'])==18
out['archive_files']=rows;out['checks']['archive_20_exact_original_bytes_hash_size_crc']=True
D=R/'papers/AutomatedReviews/2026-11-05-publication-computation-coverage';pairs={'review.md':'review.md','review.json':'review.json','populations.json':'populations.json','held_and_preimages.json':'held-and-preimages.json','companion_identities.json':'companion-identities.json'}
out['citation_copies']=[]
for dest,src in pairs.items():
 d=D/('CITATION_PREDECESSOR_'+dest);s=P/('l1-citation-predecessor-'+src);assert d.read_bytes()==s.read_bytes();out['citation_copies'].append({'path':str(d.relative_to(R)),'sha256':sha(d.read_bytes()),'original':str(s)})
out['checks']['five_citation_reports_exact']=True
prov=json.loads((P/'l1-citation-predecessor-held-and-preimages.json').read_text());out['citation_preimages']=[]
for row in prov['preimages']:
 p=R/row['path'];actual=sha(p.read_bytes()) if p.exists() else None;assert actual==row['current_sha256'];out['citation_preimages'].append({'path':row['path'],'sha256':actual})
out['checks']['citation_current_preimages_exact']=True
out['held_sources']=[]
for row in prov['held_sources']:
 p=R.parent/row['path'];b=p.read_bytes();assert sha(b)==row['sha256'] and len(b)==row['size'];out['held_sources'].append({'path':str(p),'sha256':sha(b),'bytes':len(b)})
out['checks']['held_source_hashes_still_match']=True
road=A/'REPAIR_DISPOSITION_MAP.md';text=road.read_text();changed=run(['git','diff','--',str(road.relative_to(R))]);out['roadmap_sha256']=sha(road.read_bytes())
links=[]
# Check every relative Markdown link in changed lines, plus the current resume section.
section=text[text.index('### Frozen16fde9 qualification and current resume state'):]
for link in re.findall(r'\]\(([^)]+)\)',section):
 if '://' not in link:
  target=(road.parent/link.split('#')[0]).resolve();assert target.exists(),str(target);links.append({'link':link,'resolved':str(target)})
out['links']=links;out['checks']['current_resume_relative_links_resolve']=True
assert 'Portable coverage is234/272.' in section and 'coefficients remain unrun' in section and 'Cache1.2 remains open' in section and 'still-owed source body' in section
out['checks']['source_only_and_open_obligations_preserved']=True
expected={str(road.relative_to(R)),str(zpath.relative_to(R)),str((A/'l1_k4_two_protected_tori_7981_source_design_manifest.json').relative_to(R))}|{x['path'] for x in out['citation_copies']}
status=run(['git','status','--porcelain','--untracked-files=all']);actual={line[3:] for line in status.splitlines()};assert actual==expected,(actual,expected)
run(['git','diff','--check']);out['checks']['diff_exact_eight_handoff_paths_only']=True;out['checks']['diff_whitespace']=True
out['verdict']='ACCEPT source-only remote handoff evidence';out['corrections_required']=[]
(P/'l1-parallel-handoff-review-r1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verdict':out['verdict'],'checks':out['checks'],'archive_sha256':out['archive_sha256'],'files':len(rows),'links':len(links)}))
