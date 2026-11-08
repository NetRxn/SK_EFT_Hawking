from l1_residual_sparse_sources import source_table
from l1_residual_source_contract import source
from itertools import islice
from collections import Counter
p=source_table()
kinds=Counter((bool(r),bool(i)) for r,i in p.values())
reps={}
for key,val in p.items():
    reps.setdefault((bool(val[0]),bool(val[1]),key[3:]),key)
for key in reps.values():
    mask,i,j,a,b=key
    exact=p[key]
    assert source(mask,i,j,a,b)==exact
    assert source(mask,i,j,b,a)==tuple(-x for x in exact)
    assert source(mask,j,i,a,b)==exact
for key in ((15,0,0,0,1),(51,0,0,0,0),(51,0,4,0,1)):
    assert source(*key)==p.get(key,(0,0))
print('direct source moment control',len(reps),'nonzero representatives + 3 probes; populations',kinds)
