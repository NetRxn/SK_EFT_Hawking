from pathlib import Path
import hashlib,json,re,zipfile
R=Path('/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103'); D=R/'papers/AutomatedReviews/2026-11-05-publication-computation-coverage'; F=R/'papers/AutomatedReviews/2026-11-05-source-register-fidelity'; sha=lambda b:hashlib.sha256(b).hexdigest(); previous=json.loads(Path('/tmp/publication-citation-adoption-review-r3-audit.json').read_text()); hashes=previous['hashes']; assert len(hashes)==11
for p,h in hashes.items(): assert sha((R/p).read_bytes())==h,p
m=json.loads((D/'CITATION_ADOPTION_ARCHIVE_MANIFEST.json').read_text()); assert len(m['files'])==12
for row in m['files']:
 p=D/row['name']; b=p.read_bytes(); assert len(b)==row['bytes'] and sha(b)==row['sha256']
 if row['name']=='CITATION_ADOPTION_EVIDENCE.zip': source=Path('/tmp/l1-citation-adoption-evidence.zip')
 elif row['name']=='CITATION_ADOPTION_EVIDENCE-manifest.json': source=Path('/tmp/l1-citation-adoption-evidence-manifest.json')
 else: source=Path('/tmp',row['name'].replace('CITATION_ADOPTION_REVIEW','publication-citation-adoption-review-r3'))
 assert b==source.read_bytes(),source
with zipfile.ZipFile(D/'CITATION_ADOPTION_EVIDENCE.zip') as z:
 assert z.testzip() is None
 for row in json.loads((D/'CITATION_ADOPTION_EVIDENCE-manifest.json').read_text())['files']:
  b=z.read(row['name']); assert sha(b)==row['sha256'] and b==Path('/tmp',row['name']).read_bytes()
links=[]
for p in [D/'CITATION_ADOPTION.md',R/'docs/audits/2026-10-17-publication-substance-construction/REPAIR_DISPOSITION_MAP.md']:
 for name,target in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',p.read_text()):
  if ':' not in target and '#' not in target:
   links.append((str(p.relative_to(R)),target)); assert (p.parent/target).exists(),target
assert (F/'CURRENT_RED_REPRODUCTION.txt').read_bytes()==Path('/tmp/l1-source-register-fidelity-reproducer-r2.txt').read_bytes()
assert (F/'ORIGINAL_IMPORT_FAILURE.txt').read_bytes()==Path('/tmp/l1-source-register-fidelity-reproducer.txt').read_bytes()
finding=(F/'source_register_fidelity.md').read_text(); original=Path('/tmp/l1-source-register-fidelity-finding.md').read_text()
verify=lambda s:next(l for l in s.splitlines() if l.startswith('- **Verify:**'))
assert verify(finding)==verify(original)
for token in ['SOURCE-1','**Accepted owner:** ROOT','architecture-change','**Severity:** major','**Lane:** infra','**Gate:** CitationIntegrity','**Gate relationship:** Indirect','canonical `_cache_fidelity','inprep: True']:
 assert token in finding,token
intake=json.loads((F/'CANONICAL_INTAKE.json').read_text()); assert len(intake)==1; n=intake[0]; assert n['id']=='review:2026-11-05-source-register-fidelity:source_register_fidelity:1.1' and n['meta']['status']=='open' and n['meta']['severity']=='major' and n['meta']['lane']=='infra'
ledger=json.loads((R/'docs/review_finding_supersessions.json').read_text()); assert not any(x.get('finding_id')==n['id'] for x in ledger['supersessions'])
x={'reviewed11_postimages_unchanged':hashes,'exact_copied_evidence_files':12,'archive_entries_valid':24,'local_links_checked':len(links),'promoted_finding_id':n['id'],'promoted_finding_status':'open','original_Verify_unchanged':True,'both_actual_red_and_import_failure_preserved':True,'dedup_requiredrepair_ROOTowner_indirect_gate_retained':True,'source_writes_tests_network':False}
Path('/tmp/l1-citation-final-composition-r5.json').write_text(json.dumps(x,indent=2)+'\n'); print(json.dumps(x,indent=2))
