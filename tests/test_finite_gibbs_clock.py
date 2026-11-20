"""Independent finite spectral diagnostics, not certified floating bounds."""
import numpy as np
import pytest
from scipy.linalg import expm
from src.core.formulas import finite_gibbs_clock as clock

def run(H,X,s=.7,beta=.4,hbar=1.3):
    return clock(hamiltonian=H,observable=X,beta=beta,hbar=hbar,modular_time=s)

def test_sign_and_independent_exponential():
    H=np.diag([0.,2.]);X=np.array([[0,1],[1,0]])
    r=run(H,X)
    assert r['physical_time']==pytest.approx(-.4*1.3*.7)
    assert r['modular_observable'][0,1]==pytest.approx(np.exp(1j*.4*.7*2))
    wrong=expm(1j*.4*.7*H)@X@expm(-1j*.4*.7*H)
    assert np.linalg.norm(wrong-r['modular_observable'])>.1
    boltz=expm(-.4*H);np.testing.assert_allclose(r['gibbs_state'],boltz/np.trace(boltz))
    assert r['comparison_residual']<1e-12

@pytest.mark.parametrize('n',[1,2,3,5])
def test_random_conjugations_group_star_and_energy_shift(n):
    rng=np.random.default_rng(419+n)
    Q,_=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))
    H=Q@np.diag(np.arange(n)/3)@Q.conj().T
    X=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
    before=H.copy();r=run(H,X)
    expected=expm(1j*r['physical_time']/1.3*H)@X@expm(-1j*r['physical_time']/1.3*H)
    np.testing.assert_allclose(r['modular_observable'],expected,atol=2e-12)
    np.testing.assert_array_equal(H,before)
    np.testing.assert_allclose(run(H+7*np.eye(n),X)['modular_observable'],r['modular_observable'],atol=2e-12)
    np.testing.assert_allclose(run(H+7*np.eye(n),X)['gibbs_state'],r['gibbs_state'],atol=2e-12)
    first=run(H,X,s=.2)['modular_observable']
    np.testing.assert_allclose(run(H,first,s=.5)['modular_observable'],r['modular_observable'],atol=2e-12)
    np.testing.assert_allclose(run(H,X.conj().T)['modular_observable'],r['modular_observable'].conj().T,atol=2e-12)
    for key in ['comparison_residual','matrix_log_residual','normalization_residual','modular_unitarity_residual','heisenberg_unitarity_residual']:
        assert r[key]<2e-12

def test_degenerate_scalar_and_zero_time():
    X=np.array([[0,1,0],[2j,0,0],[0,0,1]])
    H=np.diag([1.,1.,2.])
    np.testing.assert_allclose(run(H,X)['modular_observable'],X,atol=1e-12)
    np.testing.assert_allclose(run(3*np.eye(3),X)['gibbs_state'],np.eye(3)/3,atol=1e-12)
    np.testing.assert_allclose(run(H,X,s=0)['modular_observable'],X,atol=1e-12)

@pytest.mark.parametrize('change',[
 dict(beta=0),dict(beta=-1),dict(hbar=0),dict(hbar=True),dict(beta=float('inf')),
 dict(modular_time=float('nan')),dict(modular_time=1j),dict(hamiltonian=[]),
 dict(hamiltonian=[[0,1],[0,0]]),dict(hamiltonian=[[0,float('nan')],[0,0]]),
 dict(observable=[[1]]),dict(observable=[[float('inf'),0],[0,1]]),
 dict(hamiltonian=np.diag([0,1000.])),dict(hamiltonian=np.diag([0,100.])),
])
def test_invalid_and_rank_loss(change):
    a=dict(hamiltonian=np.diag([0.,1.]),observable=np.eye(2),beta=1.,hbar=1.,modular_time=.5)
    a.update(change)
    with pytest.raises((ValueError,TypeError)):clock(**a)

def test_nonfinite_output_diagnostics_refused():
    # Finite entries can still overflow matrix products or residual norms.
    with np.errstate(over='ignore',invalid='ignore'):
        with pytest.raises(ValueError):
            run(np.diag([0.,2.]),np.array([[0.,1.e300],[1.e300,0.]]))
