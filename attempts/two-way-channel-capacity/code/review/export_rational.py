# Reviewer helper (2026-11-27): exports the author's rational k = 3 law (../bmc_gk_k3_seed2.npz, rounded
# by the author's floor/argmax rule via ../bmc_gk.py) with the reduced trees and outcome table to JSON.
# Run: python3 export_rational.py [out.json]   (default: g3_rational.json next to this script)
# Runtime: about 1 s. Needs numpy.
"""Export the author's rational k=3 distribution (their rounding rule) as integer numerators
plus the reduced trees as plain nested lists. Reads the author's files from ../ (the attempt's code/ folder).
This is the only place the author's code/data are touched (to fix WHICH distribution is meant)."""
import json, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.join(HERE, '..')  # author's code/
sys.path.insert(0, CODE)
import bmc_gk

d = np.load(os.path.join(CODE, "bmc_gk_k3_seed2.npz"))
D = 10 ** 9


def rationalise(p):
    q = np.floor(np.asarray(p) * D).astype(np.int64)
    q[np.argmax(q)] += D - q.sum()
    assert q.min() >= 0 and q.sum() == D
    return [int(v) for v in q]


trees = bmc_gk.reduced_trees(3)


def tolist(t):
    if t is None:
        return None
    return [t[0], [tolist(c) for c in t[1]]]


out = {"D": D, "p1": rationalise(d["p1"]), "p2": rationalise(d["p2"]),
       "trees": [tolist(t) for t in trees], "T": d["T"].tolist()}
json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "g3_rational.json"), "w"))
print("supports:", sum(v > 0 for v in out["p1"]), sum(v > 0 for v in out["p2"]))
