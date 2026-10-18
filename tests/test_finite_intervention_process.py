"""Outcome-tree tests against independently multiplied pure-state paths."""
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
import sympy as sp
import pytest
from src.core.formulas import finite_intervention_process as evaluate

I2 = [[1, 0], [0, 1]]
Z = [[[[1, 0], [0, 0]]], [[[0, 0], [0, 1]]]]

def node(next=None):
    return dict(evolution=[I2], instrument=deepcopy(Z), next=[None, None] if next is None else next)

def args():
    return dict(system_dim=2, environment_dim=1, outcome_count=2,
                initial=[[F(9,25),F(12,25)],[F(12,25),F(16,25)]], protocol=node())

def decode(matrix):
    return sp.Matrix([[sp.Rational(a.numerator,a.denominator)+sp.I*sp.Rational(b.numerator,b.denominator)
                       for a,b in row] for row in matrix])

def test_unnormalized_zero_and_prefixes():
    a=args();a['protocol']=node([node(),node()]);r=evaluate(**a)
    assert r['leaf_count']==4 and r['total_probability']==1
    assert r['branches'][(0,1)]['weight']==r['branches'][(1,0)]['weight']==0
    assert decode(r['branches'][(0,0)]['state'])==sp.diag(sp.Rational(9,25),0)
    assert r['prefix_marginals'][(0,)]==F(9,25)
    assert all(item['weight']==r['prefix_marginals'][h] for h,item in r['branches'].items())

def test_unequal_environment_and_feedback_against_pure_paths():
    # Six dimensional joint state; independently propagate amplitudes along paths.
    d=6;eye=sp.eye(d);perm=sp.zeros(d)
    for j in range(d):perm[(j+1)%d,j]=1
    X=sp.Matrix([[0,1],[1,0]])
    psi=sp.zeros(d,1);psi[0]=sp.Rational(3,5);psi[4]=sp.I*sp.Rational(4,5)
    def encode(M):
        return [[(F(sp.re(z)),F(sp.im(z))) for z in list(M.row(i))] for i in range(M.rows)]
    later0=dict(evolution=[encode(eye)],instrument=deepcopy(Z),next=[None,None])
    later1=dict(evolution=[encode(sp.kronecker_product(X,sp.eye(3)))],instrument=deepcopy(Z),next=[None,None])
    root=dict(evolution=[encode(perm)],instrument=deepcopy(Z),next=[later0,later1])
    r=evaluate(system_dim=2,environment_dim=3,outcome_count=2,initial=encode(psi*psi.H),protocol=root)
    for a,b in product(range(2),repeat=2):
        Pa=sp.kronecker_product(sp.diag(int(a==0),int(a==1)),sp.eye(3))
        Pb=sp.kronecker_product(sp.diag(int(b==0),int(b==1)),sp.eye(3))
        future=eye if a==0 else sp.kronecker_product(X,sp.eye(3))
        v=Pb*future*Pa*perm*psi
        assert decode(r['branches'][(a,b)]['state'])==v*v.H
        assert r['branches'][(a,b)]['weight']==F((v.H*v)[0])
    root['next']=[later0,later0]
    changed=evaluate(system_dim=2,environment_dim=3,outcome_count=2,initial=encode(psi*psi.H),protocol=root)
    assert r['prefix_marginals'][(0,)]==changed['prefix_marginals'][(0,)]
    assert r['prefix_marginals'][(1,)]==changed['prefix_marginals'][(1,)]
    assert r['branches'][(1,0)]['weight']!=changed['branches'][(1,0)]['weight']

def test_leaf_and_nonmutation():
    a=args();before=deepcopy(a);r=evaluate(**a);assert a==before
    a['protocol']=None;r=evaluate(**a)
    assert r['depth']==0 and r['leaves']==((),) and r['total_probability']==1

@pytest.mark.parametrize('change',[
 dict(system_dim=True),dict(environment_dim=0),dict(outcome_count=-1),
 dict(initial=[[1.0,0],[0,0]]),dict(initial=[[True,0],[0,0]]),
 dict(initial=[[1,1],[0,0]]),dict(initial=[[2,0],[0,-1]]),
 dict(initial=[[1,1],[1,0]]),dict(initial=[[1,0],[0,1]]),
 dict(initial=[[1]]),dict(initial=[[(0,1),0],[0,0]]),
 dict(protocol={}),dict(protocol=[]),
])
def test_invalid_inputs(change):
    a=args();a.update(change)
    with pytest.raises((TypeError,ValueError)):evaluate(**a)

def test_invalid_kraus_tree_and_cycles():
    bad=[]
    p=node();p['evolution']=[];bad.append(p)
    p=node();p['evolution']=[[[2,0],[0,2]]];bad.append(p)
    p=node();p['instrument']=[[[[1,0],[0,1]]],[[[1,0],[0,1]]]];bad.append(p)
    p=node();p['instrument'][1]=[];bad.append(p)
    p=node();p['next']=[None,node()];bad.append(p)
    p=node();p['next'][0]=p;bad.append(p)
    p=node();p['next']=[None];bad.append(p)
    for p in bad:
        a=args();a['protocol']=p
        with pytest.raises((TypeError,ValueError)):evaluate(**a)

def test_three_outcomes_and_complex_initial():
    initial=[[(F(1,2),0),(0,F(-1,2)),0],[(0,F(1,2)),(F(1,2),0),0],[0,0,0]]
    projectors=[[[int(i==j==a) for j in range(3)] for i in range(3)] for a in range(3)]
    p=dict(evolution=[[[int(i==j) for j in range(3)] for i in range(3)]],
           instrument=[[m] for m in projectors],next=[None]*3)
    r=evaluate(system_dim=3,environment_dim=1,outcome_count=3,initial=initial,protocol=p)
    assert [r['branches'][(a,)]['weight'] for a in range(3)]==[F(1,2),F(1,2),0]
    assert r['leaf_count']==3 and r['total_probability']==1
