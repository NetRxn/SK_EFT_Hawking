"""Coherent amplitudes, discarded interference and intervention histories."""
from fractions import Fraction as F
import pytest
from src.core.formulas import coherent_memory_process

def test_resolved_history_and_interference():
    r=coherent_memory_process()
    table=[[r['measured']['branches'][(a,b)]['weight'] for b in (0,1)] for a in (0,1)]
    assert table==[[F(144,625),F(256,625)],[F(144,625),F(81,625)]]
    assert r['uninterrupted_one']==F(49,625)
    assert r['measured_one']==F(337,625) and r['interference_contrast']==F(288,625)
    for a,p in [(0,F(16,25)),(1,F(9,25))]:
        assert r['measured']['prefix_marginals'][(a,)]==p
        assert r['future_identity']['prefix_marginals'][(a,)]==p
    assert r['retained_one']==(0,F(256,625)) and r['control_one']==(0,0)
    assert all(x['total_probability']==1 for x in [r['uninterrupted'],r['measured'],r['future_identity'],*r['retained'],*r['control'],r['feedback']])
    assert [r['feedback']['branches'][h]['weight'] for h in [(0,0),(0,1),(1,0),(1,1)]]==[F(1,2),0,0,F(1,2)]

@pytest.mark.parametrize('c,s',[(1,0),(0,1),(F(3,5),F(-4,5)),(F(5,13),F(12,13))])
def test_independent_amplitude_paths(c,s):
    r=coherent_memory_process(c=c,s=s)
    # Amplitude of |10> after U twice is c*c + (-i*s)*(-i*s).
    # Resolving the middle Z outcome discards the cross term between these paths.
    assert r['uninterrupted_one']==(c*c-s*s)**2
    assert r['measured_one']==c**4+s**4
    assert r['interference_contrast']==2*c*c*s*s
    assert r['retained_one']==(0,s**4)

@pytest.mark.parametrize('c,s',[(True,0),(.6,.8),(1,1),('3/5',F(4,5))])
def test_invalid_coefficients(c,s):
    with pytest.raises((TypeError,ValueError)):coherent_memory_process(c=c,s=s)
