#!/usr/bin/env python3
"""Is the L=8 near-zero fermion mode (kappa~1e7) a property of the OPERATOR or
induced by the (trapped) CONFIG?

Decisive cheap measurement: compute kappa = lam_max/lam_min of A†A = -A^2 for a
ladder of configurations:
  - the g=2.0 warm config scaled by s in {0, 0.25, 0.5, 1.0}  (s=0 = free operator)
  - the g=0.5 deep-symmetric config
If kappa stays ~1e7 even at s=0 (free operator), deflation is a HARD requirement
for L=8. If s=0 is well-conditioned and kappa grows with the h-amplitude, the
near-zero mode is the trap signature and deflation is an escape backstop.

Read-only. Records JSON under data/rhmc/force_decomp/.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
import sk_eft_rhmc

OUT_DIR = Path("data/rhmc/force_decomp")


def build_cg_entries():
    CG = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])
    cg_a, cg_i, cg_j, cg_val = [], [], [], []
    for a in range(4):
        for I in range(8):
            for J in range(8):
                v = CG[a, I, J]
                if abs(v) > 1e-15:
                    cg_a.append(a); cg_i.append(I); cg_j.append(J); cg_val.append(v)
    return (np.array(cg_a, dtype=np.int64), np.array(cg_i, dtype=np.int64),
            np.array(cg_j, dtype=np.int64), np.array(cg_val, dtype=np.float64))


def kappa_of(h, L, cg, n_low=8):
    cg_a, cg_i, cg_j, cg_val = cg
    NF = 8 * L**4
    def A(v):
        return np.asarray(sk_eft_rhmc.apply_fermion_matrix_py(h, v, L, cg_a, cg_i, cg_j, cg_val))
    Op = LinearOperator((NF, NF), matvec=lambda v: -A(A(v)), dtype=np.float64)
    hi = float(eigsh(Op, k=1, which='LA', tol=1e-3, return_eigenvectors=False)[0])
    # SA on clustered near-zero modes needs a generous Lanczos subspace (ncv) to
    # converge; k=8/ncv~64 is the regime that worked in the force-decomp probe.
    low = np.sort(eigsh(Op, k=n_low, which='SA', tol=5e-2, maxiter=6000,
                        ncv=min(NF - 1, 6 * n_low + 24), return_eigenvectors=False))
    lo = float(low[0])
    return lo, hi, [float(x) for x in low]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--configs', type=str,
                    default='data/rhmc/L8_v1/L8_g2.0000.npz,data/rhmc/L8_v1/L8_g0.5000.npz',
                    help='comma-separated real configs (the trapped ones)')
    ap.add_argument('--n-random', type=int, default=3,
                    help='# random-h configs at matched amplitude (the generic-config control)')
    args = ap.parse_args()

    L = args.l
    V = L**4
    cg = build_cg_entries()
    rng = np.random.default_rng(20260625)

    # The fermion matrix A[h] is h-LINEAR (A[0]=0), so amplitude rescaling leaves
    # kappa invariant — only the config SHAPE matters. Compare real (trapped)
    # configs against random configs of matched norm.
    real_hs = []
    norm_ref = None
    for path in args.configs.split(','):
        if not path:
            continue
        h = np.asarray(np.load(path)['h_final'], dtype=np.float64).reshape(V, 4, 4)
        real_hs.append((Path(path).stem, h))
        if norm_ref is None:
            norm_ref = float(np.linalg.norm(h))
    print(f"L={L}  matched ||h|| ref = {norm_ref:.2f}", flush=True)

    configs = list(real_hs)
    for r in range(args.n_random):
        hr = rng.standard_normal((V, 4, 4))
        hr *= norm_ref / np.linalg.norm(hr)
        configs.append((f"random#{r+1}", hr))

    rows = []
    for label, h in configs:
        t0 = time.time()
        try:
            lo, hi, low = kappa_of(h, L, cg)
            kap = hi / lo if lo > 0 else float('inf')
        except Exception as e:
            print(f"  {label:14s}: eigsh FAIL {type(e).__name__}: {str(e)[:60]}", flush=True)
            continue
        rows.append(dict(label=label, kind=('real' if 'random' not in label else 'random'),
                         h_norm=float(np.linalg.norm(h)), lam_min=lo, lam_max=hi,
                         kappa=kap, low=low))
        print(f"  {label:14s} ||h||={np.linalg.norm(h):8.2f}  lam_min={lo:.3e} "
              f"lam_max={hi:.2f}  kappa={kap:.3e}   ({time.time()-t0:.0f}s)", flush=True)

    print("\n" + "=" * 64)
    print("VERDICT")
    print("=" * 64)
    rand_k = [r['kappa'] for r in rows if r['kind'] == 'random']
    real_k = [r['kappa'] for r in rows if r['kind'] == 'real']
    if rand_k and real_k:
        med_rand = float(np.median(rand_k))
        print(f"  real (trapped) configs: kappa = {[f'{k:.1e}' for k in real_k]}")
        print(f"  random configs (matched norm): kappa = {[f'{k:.1e}' for k in rand_k]}")
        if med_rand > 1e6:
            print(f"  -> random-h ALSO kappa~{med_rand:.0e} >> 1e6: near-zero modes are GENERIC")
            print(f"     to L={L} at this amplitude. DEFLATION IS A HARD REQUIREMENT.")
        elif real_k and max(real_k) > 30 * med_rand:
            print(f"  -> random-h well-conditioned (~{med_rand:.0e}) but trapped configs are")
            print(f"     >>30x stiffer: the near-zero mode is CONFIG-INDUCED (trap signature).")
            print(f"     Deflation is an escape backstop; good thermalization may avoid it.")
        else:
            print(f"  -> comparable kappa; near-zero modes are a generic feature of typical")
            print(f"     configs. Deflation strongly recommended.")

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%S")
    out = OUT_DIR / f"conditioning_L{L}_{stamp}.json"
    out.write_text(json.dumps(dict(L=L, configs=args.configs, n_random=args.n_random,
                                   rows=rows, timestamp=stamp), indent=2))
    print(f"\n  recorded -> {out}")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
