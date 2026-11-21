"""Necessary parity/saturation counts only; no integrated coefficient or zero inference."""
import sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"2026-10-17-publication-substance-construction"))
from l1_interacting_support import half,match,link
pop=half(3)
uv=[]
for z0 in (0,1):
 for z1 in (0,2):
    count,_=match(pop,link(z0,0)^link(z1,1),(2,7,7,8))
    uv.append({'z0':z0,'z1':z1,'ordered_action_candidates':count})
u2=[]
for z0 in (0,1):
 for z1 in (0,1):
    count,_=match(pop,link(z0,0)^link(z1,0),(2,6,8,8))
    u2.append({'z0':z0,'z1':z1,'ordered_action_candidates':count})
assert [x['ordered_action_candidates'] for x in uv]==[0,5760,5760,11520]
assert [x['ordered_action_candidates'] for x in u2]==[43560,37800,37800,43560]
print(json.dumps({'scope':'necessary action parity/saturation support only; not coefficients',
 'G02_G12':uv,'G02_squared':u2},indent=2))
