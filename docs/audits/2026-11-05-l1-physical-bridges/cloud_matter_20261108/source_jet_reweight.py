"""Exact fixed-bare-D squared source jet, reusing archived Haar kernels.

No original source file is modified. --family bounds a single contraction family;
--assemble performs only the already checked exact arithmetic and census.
The source-function wrappers change only support/orbit weights and population
checks. Haar, wedge, factorial and source-moment formulas are untouched.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from itertools import product
import argparse
import importlib
import inspect
import hashlib
import json
import sys

AUDIT=Path(__file__).resolve().parents[2]/'2026-10-17-publication-substance-construction'
sys.path.insert(0,str(AUDIT))
from l1_equal_time_shared_quartic import same_site_quadratic_support,edges_for
from l1_equal_time_mixed_factor import transform

E=(0,0,1,-1)
def charge(word):
    return sum(-E[k]-E[l] for x,k,l,u,v in word)
def tags(word):
    return tuple(sorted(tuple(sorted(c.values())) for c in edges_for(word).values() if len(c)>1))

FAMILIES={
 'private':((),16,F(93555,4)),
 'quartic':(((2,2),),24,F(168399,4)),
 'double':(((2,2),(2,2)),8,F(1323,2)),
 'pair':(((1,1),(1,1)),12,F(62937,2)),
 'four':(((1,1),(1,1),(1,1),(1,1)),4,F(0)),
 'mixed':(((1,1),(1,1),(2,2)),8,F(567)),
}
WORDS=tuple(tuple(sorted(w)) for w in same_site_quadratic_support())
assert len(WORDS)==len(set(WORDS))==185
assert Counter(map(charge,WORDS))==Counter({0:113,-4:36,4:36})
SUBSETS={name:{w for w in WORDS if charge(w) and tags(w)==spec[0]}
         for name,spec in FAMILIES.items()}
assert all(len(SUBSETS[n])==s[1] for n,s in FAMILIES.items())
assert len(set.union(*SUBSETS.values()))==sum(map(len,SUBSETS.values()))==72

def replace_once(source,old,new):
    assert source.count(old)==1,(old,source.count(old))
    return source.replace(old,new)

def representatives(words):
    remaining=set(words);out={}
    while remaining:
        w=min(remaining)
        orbit={tuple(sorted(transform(t,a,b) for t in w))
               for a,b in product((False,True),repeat=2)}
        assert orbit<=remaining
        # Both generators preserve absolute source charge, including signs.
        assert {abs(charge(z)) for z in orbit}=={4}
        remaining-=orbit;out[w]=len(orbit)
    assert sum(out.values())==len(words)
    return out

def contract_family(name):
    subset=SUBSETS[name];expected=FAMILIES[name][2]
    if name=='private':
        # Existing private evaluator is top-level; only subset/population changes.
        path=AUDIT/'l1_equal_time_private_pairs.py'
        code=path.read_text()
        print('SOURCE_SHA256',path.name,hashlib.sha256(code.encode()).hexdigest(),flush=True)
        code=replace_once(code,'for word in same_site_quadratic_support():',
                          'for word in selected_words:')
        code=replace_once(code,'assert sum(counts.values())==33','assert sum(counts.values())==16')
        code=replace_once(code,'assert counts[122472]==1','assert counts[122472]==0')
        ns={'__name__':'private_source_jet_subset','selected_words':subset}
        exec(compile(code,str(path),'exec'),ns)
        value=ns['total'];hist=ns['counts']
    else:
        modules={'quartic':'l1_equal_time_shared_quartic','double':'l1_equal_time_double_shared',
                 'pair':'l1_equal_time_shared_quadratic_pair','four':'l1_equal_time_four_quadratic_factor',
                 'mixed':'l1_equal_time_mixed_factor'}
        m=importlib.import_module(modules[name]);function='main' if name in ('quartic','double') else 'run'
        code=inspect.getsource(getattr(m,function))
        print('SOURCE_SHA256',Path(m.__file__).name,hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest(),flush=True)
        ns=dict(m.__dict__)
        if name=='mixed':
            ns['same_site_quadratic_support']=lambda:subset
            code=replace_once(code,'assert len(words)==16','assert len(words)==8')
            histogram='result'
        else:
            orbits=representatives(subset)
            print('ORBIT_PREFLIGHT',name,len(orbits),sum(orbits.values()),flush=True)
            ns.update(orbits=orbits,same_site_quadratic_support=lambda:orbits)
            specs={
                'quartic':('out','out[result]+=1','out[result]+=orbits[word]',48),
                'double':('outcomes','outcomes[value]+=1','outcomes[value]+=orbits[word]',16),
                'pair':('sums','sums[(len(history),len(active),value)]+=1',
                        'sums[(len(history),len(active),value)]+=orbits[word]',24),
                'four':('outcomes','outcomes[value]+=1','outcomes[value]+=orbits[word]',8),
            }
            histogram,old,new,original_count=specs[name]
            code=replace_once(code,old,new)
            code=replace_once(code,f'assert sum({histogram}.values())=={original_count}',
                              f'assert sum({histogram}.values())=={len(subset)}')
        code+='\n    return '+histogram+'\n'
        exec(compile(code,str(m.__file__),'exec'),ns)
        hist=ns[function]()
        value=sum((k[2] if name=='pair' else k)*v for k,v in hist.items())
    assert sum(hist.values())==len(subset)
    assert value==expected,(name,value,expected)
    print('FAMILY_RESULT',name,len(subset),value,sorted(hist.items()),flush=True)
    return value

def assemble():
    # Values are regression targets, each independently recomputed by --family.
    charged=sum(v[2] for v in FAMILIES.values())
    assert charged==F(196371,2)
    numerator_second=16*charged
    assert numerator_second==1570968
    Z8=F(1252309350145403,2123366400);same=F(10179913,32)
    logZ_second_j=F(954400425849600,113846304558673)
    # Both first derivatives vanish by exact transverse exchange.
    normalized_second_j=numerator_second/Z8-(same/Z8)*logZ_second_j
    answer={'convention':'fixed bare D=G22-G33; action coframe A=exp(jE), E=(0,0,1,-1)',
        'charge_census':{str(k):v for k,v in sorted(Counter(map(charge,WORDS)).items())},
        'charged_word_count':72,'charged_raw_subtotal':str(charged),
        'raw_numerator_second_j_div_g2_to_6':str(numerator_second),
        'logZ_second_j':str(logZ_second_j),
        'g2_squared_variance_second_j':str(normalized_second_j),
        'g2_squared_variance_second_h':str(normalized_second_j/8),
        'source_conversion':'h=2*sqrt(2)*j; d2/dh2=(1/8)*d2/dj2',
        'g2_squared_Sigma_D_second_h_multiplier':str(-normalized_second_j/64),
        'full_covariance_or_physical_propagation':False}
    # Parent's independently executed transverse_covariances.py supplies the
    # full h=0 H/T numerators. The charged72 source-decoupled words use the
    # exact local moments H²:D²:T²=9:21:129; coupled40 all have zero charge.
    transverse={}
    for name,raw,moment in [('H',F(17419143,128),F(9)),('T',F(31250131,16),F(129))]:
        raw_second=numerator_second*moment/21
        normalized_second=raw_second/Z8-raw/Z8*logZ_second_j
        transverse[name]={'raw_numerator_at_zero':str(raw),
            'raw_numerator_second_j_div_g2_to_6':str(raw_second),
            'g2_squared_variance_second_j':str(normalized_second),
            'g2_squared_variance_second_h':str(normalized_second/8)}
    assert transverse['H']['raw_numerator_second_j_div_g2_to_6']=='673272'
    assert transverse['T']['raw_numerator_second_j_div_g2_to_6']=='9650232'
    answer['additional_fixed_basis_transverse_jets']=transverse
    print(json.dumps(answer,indent=2),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--family',choices=FAMILIES)
    parser.add_argument('--assemble',action='store_true');args=parser.parse_args()
    if args.family:contract_family(args.family)
    elif not args.assemble:
        for name in FAMILIES:contract_family(name)
    if not args.family:assemble()
