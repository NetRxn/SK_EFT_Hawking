import subprocess,json,time,hashlib,os
from pathlib import Path
root=Path.cwd();stem=Path('/tmp/l1-01d72-fast')
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head == '01d72af223c38b9fc91d7eff685fe65e4aabf230'
assert not any(stem.with_suffix(x).exists() for x in ('.preflight.json','.txt','.xml','.exit.json'))
status=subprocess.check_output(['git','status','--porcelain=v1'],text=True);assert not status,status
command=['uv','run','python','-m','pytest','-q','--junitxml=/tmp/l1-01d72-fast.xml']
start=time.perf_counter()
stem.with_suffix('.preflight.json').write_text(json.dumps({'head':head,'status':status,'command':command,'scope':'Canonical bare fast testpaths, frozen candidate; no live Lean slot operation authorized.'},indent=2)+'\n')
with stem.with_suffix('.txt').open('w') as out:
 r=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONUNBUFFERED':'1'})
finalhead=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
finalstatus=subprocess.check_output(['git','status','--porcelain=v1'],text=True)
receipt={'exit_code':r.returncode,'actual_parent_wall_seconds':time.perf_counter()-start,'head_before':head,'head_after':finalhead,'status_before':status,'status_after':finalstatus,'same_head':head==finalhead,'clean_after':not finalstatus,'command':command,'stdout_sha256':hashlib.sha256(stem.with_suffix('.txt').read_bytes()).hexdigest()}
stem.with_suffix('.exit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
raise SystemExit(r.returncode)
