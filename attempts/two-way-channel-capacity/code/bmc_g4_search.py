#!/usr/bin/env python3
"""k = 4 search for sym(G_4) of the BMC (1806 reduced strategies per user).

Initialisations:
  'iid'   : product-form strategies, every node Bern(x*), x* = argmax x h(x) (value g*);
  'lift'  : the k = 3 optimum (bmc_gk_k3_seed2.npz from `bmc_gk.py 3 1500 300 2`)
            followed by one fresh Bern(x*) letter at every depth-4 node;
  'liftT' : one fresh Bern(x*) letter first, then the k = 3 optimum in each branch;
  'rand'  : Dirichlet(0.3) random starts.
Each start runs ITERS alternations of 3+3 Blahut-Arimoto half-steps (bmc_gk.Problem),
then the best one is polished.  Returned values are attained by explicit distributions
(lower bounds on sym(G_4)); no global-optimality certificate.

  'liftmix<eps>': (1-eps) * (lift+liftT)/2 + eps * iid  (full support);
  'lifteps<eps>': (1-eps) * lift + eps * iid            (full support).

Usage: python bmc_g4_search.py ITERS N_RAND SEED [mixonly|epsonly]
Runs reported in the attempt file:
  python bmc_g4_search.py 60 20 4            (log: g4_run_seed4.log)
  python bmc_g4_search.py 200 0 5 mixonly    (log: g4_run_seed5.log)
  python bmc_g4_search.py 250 0 6 epsonly    (log: g4_run_seed6.log)
"""
import sys
import json
import time
import numpy as np
import bmc_gk as G

XSTAR = 0.7035062


def leaves_inputs(t, depth):
    """Inputs used at the last level (depth 1 below `depth`) of reduced tree t."""
    x, ch = t
    if depth == 1:
        return [x]
    out = []
    for c in ch:
        out += leaves_inputs(c, depth - 1)
    return out


def truncate(t, depth):
    x, ch = t
    if depth == 1:
        return (x, (None,) if x == 0 else (None, None))
    return (x, tuple(truncate(c, depth - 1) for c in ch))


def iid_weight(t, depth):
    x, ch = t
    w = XSTAR if x == 1 else 1 - XSTAR
    if depth == 1:
        return w
    for c in ch:
        w *= iid_weight(c, depth - 1)
    return w


def main():
    iters, n_rand, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(seed)
    t0 = time.time()
    trees4 = G.reduced_trees(4)
    T = G.outcome_table(trees4, 4)
    assert G.dedup(T).shape == T.shape   # no duplicates: index = tree order
    prob = G.Problem(T, 16)
    probT = prob.transpose()

    trees3 = G.reduced_trees(3)
    idx3 = {t: i for i, t in enumerate(trees3)}
    d3 = np.load("bmc_gk_k3_seed2.npz")
    assert d3["T"].shape == (42, 42)
    inits = {}
    inits["iid"] = [np.array([iid_weight(t, 4) for t in trees4])] * 2
    lift = []
    for p3 in (d3["p1"], d3["p2"]):
        w = np.array([p3[idx3[truncate(t, 3)]] *
                      np.prod([XSTAR if x else 1 - XSTAR for x in leaves_inputs(t, 4)])
                      for t in trees4])
        lift.append(w / w.sum())
    inits["lift"] = lift
    liftT = []
    for p3 in (d3["p1"], d3["p2"]):
        w = np.zeros(len(trees4))
        for i, t in enumerate(trees4):
            x, ch = t
            wt = XSTAR if x == 1 else 1 - XSTAR
            for c in ch:
                wt *= p3[idx3[c]]
            w[i] = wt
        liftT.append(w / w.sum())
    inits["liftT"] = liftT
    # full-support perturbations (multiplicative BA updates cannot revive zero weights)
    iid = inits["iid"][0]
    for eps in (0.02, 0.1, 0.3):
        inits[f"liftmix{eps}"] = [(1 - eps) * (0.5 * l + 0.5 * lt) + eps * iid
                                  for l, lt in zip(lift, liftT)]
    for eps in (0.01, 0.05):
        inits[f"lifteps{eps}"] = [(1 - eps) * l + eps * iid for l in lift]
    if len(sys.argv) > 4 and sys.argv[4] == "mixonly":
        inits = {k_: v_ for k_, v_ in inits.items() if k_.startswith("liftmix")}
    if len(sys.argv) > 4 and sys.argv[4] == "epsonly":
        inits = {k_: v_ for k_, v_ in inits.items() if k_.startswith("lifteps")}

    results = []
    for name, (p1, p2) in inits.items():
        a, b = prob.value(p1, p2)
        v, q1, q2 = G.optimise(prob, probT, rng, iters, init=(p1.copy(), p2.copy()))
        results.append((v / 8, name, q1, q2))
        print(json.dumps({"init": name, "init_value": (a + b) / 8, "after": v / 8,
                          "t": round(time.time() - t0)}), flush=True)
    for r in range(n_rand):
        p1 = rng.dirichlet(np.full(prob.n1, 0.3))
        p2 = rng.dirichlet(np.full(prob.n2, 0.3))
        v, q1, q2 = G.optimise(prob, probT, rng, iters, init=(p1, p2))
        results.append((v / 8, f"rand{r}", q1, q2))
        print(json.dumps({"init": f"rand{r}", "after": v / 8, "t": round(time.time() - t0)}), flush=True)
    results.sort(key=lambda z: -z[0])
    v, name, q1, q2 = results[0]
    v2, q1, q2 = G.optimise(prob, probT, rng, 4 * iters, init=(q1, q2))
    a, b = prob.value(q1, q2)
    print(json.dumps({"best_init": name, "sym_rate_G4": (a + b) / 8, "R1": a / 4, "R2": b / 4,
                      "support": [int((q1 > 1e-6).sum()), int((q2 > 1e-6).sum())],
                      "t": round(time.time() - t0)}), flush=True)
    np.savez(f"bmc_gk_k4_seed{seed}.npz", p1=q1, p2=q2, T=T)


if __name__ == "__main__":
    main()
