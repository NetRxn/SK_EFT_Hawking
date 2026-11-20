"""Exact matrix collision checks independent of the scalar trajectory."""
from fractions import Fraction as F
from itertools import product
import pytest
from src.core.formulas import memory_history_approximation as approx


def collision(rho,bit,retention):
    # Tensor |bit><bit| with arbitrary real rational density rho, then mix
    # identity/SWAP on the joint matrix and explicitly trace out the system.
    joint=[[rho[i%2][j%2] if i//2==j//2==bit else F(0) for j in range(4)] for i in range(4)]
    perm=[0,2,1,3]
    mixed=[[retention*joint[i][j]+(1-retention)*joint[perm[i]][perm[j]] for j in range(4)] for i in range(4)]
    return [[sum(mixed[2*s+i][2*s+j] for s in range(2)) for j in range(2)] for i in range(2)]

@pytest.mark.parametrize('bits',list(product((0,1),repeat=3)))
@pytest.mark.parametrize('cutoff',range(4))
def test_exact_joint_matrix_trajectory(bits,cutoff):
    lambdas=[F(1,2),F(2,3),F(3,4)]
    r=approx(inputs=bits,retentions=lambdas,initial=F(3,8),cutoff=cutoff,reference=F(1,4))
    rho=[[F(5,8),F(1,8)],[F(1,8),F(3,8)]]
    for b,l in zip(bits,lambdas):rho=collision(rho,b,l)
    assert rho[1][1]==r['full_probability']
    assert rho[0][1]==F(1,8)*F(1,2)*F(2,3)*F(3,4)
    sigma=[[F(3,4),F(0)],[F(0),F(1,4)]]
    for b,l in zip(bits[3-cutoff:],lambdas[3-cutoff:]):sigma=collision(sigma,b,l)
    assert sigma[1][1]==r['truncated_probability']
    assert r['absolute_error']==r['exact_error_from_prefix']<=r['error_bound']

def test_sharp_forgetting_and_no_forgetting():
    r=approx(inputs=[0]*8,retentions=[F(1,2)]*8,initial=1,reference=0,cutoff=8)
    assert r['absolute_error']==r['error_bound']==F(1,256)
    assert r['suffix_pair_minimax_lower_bound']==F(1,512)
    for length in (0,1,8,100):
        r=approx(inputs=[0]*length,retentions=[1]*length,initial=1,cutoff=length)
        assert r['absolute_error']==1 and r['suffix_pair_minimax_lower_bound']==F(1,2)
    r=approx(inputs=[1,0],retentions=[1,0],initial=1,cutoff=1)
    assert r['error_bound']==r['absolute_error']==0

def test_empty_and_replay_cost():
    r=approx(inputs=[],retentions=[],initial=F(1,2),reference=0,cutoff=0)
    assert r['full_probability']==F(1,2) and r['error_bound']==1
    r=approx(inputs=[0]*100,retentions=[F(1,2)]*100,initial=1,cutoff=8)
    assert r['full_updates']==100 and r['suffix_updates']==8
    assert r['absolute_error']<=F(1,256)

@pytest.mark.parametrize('kwargs',[
    dict(inputs=[True]),dict(inputs=[2]),dict(retentions=[]),dict(retentions=[0.5]),
    dict(retentions=[-1]),dict(initial=True),dict(initial=2),dict(reference=-1),
    dict(cutoff=True),dict(cutoff=2),dict(cutoff=-1),dict(inputs=iter([0]))])
def test_strict_inputs(kwargs):
    args=dict(inputs=[0],retentions=[F(1,2)],initial=0,cutoff=1)
    args.update(kwargs)
    with pytest.raises((TypeError,ValueError)):approx(**args)
