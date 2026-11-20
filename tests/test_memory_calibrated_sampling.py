"""Calibration confidence and strict boundary tests; no hardware claims."""
from copy import deepcopy
from fractions import Fraction as F
import pytest
from src.core.formulas import memory_calibrated_sampling_certificate as certify

NAMES = ('false_positive','false_negative','reset0','reset1','main0','main1')

def example():
    return {name: {'n':81920 if i<4 else 20480,'count':count,
                   'radius':F(1,128 if i<4 else 64)}
            for i,(name,count) in enumerate(zip(NAMES,[320,320,320,10480,80,6430]))}

def test_reviewed_example_and_combined_confidence():
    r=certify(groups=example(),alpha=F(1,64))
    for key,value in dict(false_positive_upper=F(3,256),false_negative_upper=F(3,256),
        eps0=F(3,128),eps1=F(151,1024),memoryless_bound=F(199,1024),
        empirical_gap=F(635,2048),strict_margin=F(173,2048),
        calibration_failure_bound=F(1,128),sampling_failure_bound=F(1,256),failure_bound=F(3,256)).items():
        assert r[key]==value
    assert r['reject_common_channel']
    inadequate=certify(groups=example(),alpha=F(1,128))
    assert inadequate['sampling_failure_bound']<=inadequate['alpha']
    assert not inadequate['confidence_sufficient'] and inadequate['positive_margin']
    assert not inadequate['reject_common_channel']

def test_threshold_equality_is_not_rejection():
    g=example()
    # Threshold 231/1024; denominator 20480, zero-history count 80.
    g['main1']['count']=80+4620
    r=certify(groups=g,alpha=F(1,64))
    assert r['strict_margin']==0 and not r['reject_common_channel']
    g['main1']['count']+=1
    assert certify(groups=g,alpha=F(1,64))['reject_common_channel']

def test_caps_and_asymmetric_false_negative():
    g=example();g['false_negative']['count']=81920
    r=certify(groups=g,alpha=F(1,64))
    assert r['false_negative_upper']==r['readout_bias_bound']==r['eps0']==r['eps1']==1
    assert not r['reject_common_channel']
    g=example();g['false_negative']['count']=640
    r=certify(groups=g,alpha=F(1,64))
    assert r['false_negative_upper']==F(1,64)
    assert r['eps0']==F(7,256)
    r=certify(groups=example(),alpha=F(1,64),exponent_cap=0)
    assert r['failure_bound']==1 and not r['reject_common_channel']
    assert all(x['exponent_capped'] for x in r['groups'].values())

@pytest.mark.parametrize('name',NAMES)
@pytest.mark.parametrize('field,value', [('n',True),('n',0),('count',-1),('count',1000000),('count',1.0),('radius',0),('radius',0.01),('radius',True)])
def test_invalid_group_inputs(name,field,value):
    g=example();g[name][field]=value
    with pytest.raises((ValueError,TypeError)):
        certify(groups=g,alpha=F(1,64))

@pytest.mark.parametrize('alpha',[True,0,1,-1,0.1,'1/64'])
def test_invalid_alpha(alpha):
    with pytest.raises((ValueError,TypeError)):
        certify(groups=example(),alpha=alpha)

def test_protocol_schema_and_nonmutation():
    g=example();before=deepcopy(g)
    certify(groups=g,alpha=F(1,64));assert g==before
    g['extra']={}
    with pytest.raises(ValueError):certify(groups=g,alpha=F(1,64))
    g=example();g['main0']['extra']=0
    with pytest.raises(ValueError):certify(groups=g,alpha=F(1,64))

def test_worst_coverage_power_arithmetic():
    # Calibration averages can each exceed their true means by one radius.
    g=example()
    for name in NAMES[:4]:g[name]['count']+=640
    r=certify(groups=g,alpha=F(1,64))
    assert r['memoryless_bound']==F(247,1024)
    assert F(635,2048)-r['memoryless_bound']-F(4,64)==F(13,2048)>0
