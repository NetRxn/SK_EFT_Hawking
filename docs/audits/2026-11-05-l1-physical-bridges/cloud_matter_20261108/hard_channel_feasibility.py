"""Structural N4 feasibility inventory only; no hard-channel amplitude traversal."""
import io,json
from contextlib import redirect_stdout
from collections import Counter
from math import comb
with redirect_stdout(io.StringIO()):
    import remote_source_census as census
S=census.S
TREE={(0,0),(0,1),(1,1)}
records=[]
for item in census.output:
    target=tuple(item['action_degrees']);z0,z1=item['anchors'];name=item['source']
    axis1=0 if name=='G02_squared' else 1
    source_edges=((z0,0),(0,2),(z1,axis1),(0,2))
    parity=S.link(z0,0)^S.link(z1,axis1)
    selected=[]
    for (p,c),lefts in census.triples.items():
        rem=tuple(t-d for t,d in zip(target,c))
        if min(rem)<0:continue
        for a in lefts:
            for b in census.triples.get((p^parity,rem),()):
                if a[-1]<=b[0]:selected.append(a+b)
    assert len(selected)==item['multisets']
    profiles=Counter()
    for word in selected:
        incidences=Counter(source_edges)
        for i in word:
            x,k,l,u,v=S.TERMS[i][2];m,n=(a for a in range(4) if a not in (k,l))
            incidences.update(((x,k),(S.forward(x,k),l),(S.forward(x,l),k),(x,l),(u,m),(v,n)))
        free=[n for edge,n in incidences.items() if edge not in TREE]
        assert all(n%2==0 for n in free)
        profiles[max(free),tuple(sorted(Counter(free).items()))]+=1
    source_degrees=(6,2,0,0) if axis1==0 else (6,1,1,0)
    free_source=sum(edge not in TREE for edge in source_edges)
    coarse=8**free_source
    for degree in source_degrees:coarse*=comb(8,degree)
    records.append({**item,'free_source_occurrences':free_source,
       'coarse_source_rows_upper_bound':coarse,
       'unfixed_link_profiles':[{'max_degree':key[0],'degree_histogram':key[1],'multisets':n} for key,n in sorted(profiles.items())]})
print(json.dumps({'scope':'structural inventory only; no runtime/memory extrapolation from easy channels',
 'admission':'no full harder-channel or larger-lattice traversal before measured runtime, peak memory and representative scaling',
 'existing_caps':{'row':120000,'per_join_compatible_products':3000000},
 'warning':'coarse source bounds exceed caps in some signatures but do not establish actual row counts or infeasibility',
 'source_signatures':records},indent=2))
