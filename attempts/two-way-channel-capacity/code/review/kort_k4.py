# Reviewer check (2026-11-27, Claim 8): parses Kort 1997 App. A.4/A.6 K4 strategies from a pdftotext
# extract of the thesis (not committed: paper text) and writes kort_k4_sym.npz / kort_k4_asym.npz here.
# Run: python3 kort_k4.py path/to/kort.txt   (the two npz outputs are committed, so certify_k4.py runs without it)
# Runtime: about 2 s. Needs numpy.
"""Evaluate Kort's (1997, App. A.4 / A.6) K4 strategies under our behavioural evaluator.
Kort's index order (inferred from App. A.2 vs. the K3 optimum): depth by depth; within a depth,
sort own histories by (y-history, own (x,y)-history) lexicographically.
Usage: kort_k4.py path/to/kort.txt"""
import os, re, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import Evaluator, own_nodes

txt = open(sys.argv[1], encoding="utf-8", errors="replace").read().splitlines()
here = os.path.dirname(os.path.abspath(__file__))


def grab(start_pat, end_pat):
    s = next(i for i, l in enumerate(txt) if re.search(start_pat, l) and i > 2400)
    e = next(i for i, l in enumerate(txt) if re.search(end_pat, l) and i > s)
    vals = {}
    for l in txt[s:e]:
        m = re.match(r"^\s*>\s*(\d+)\s+(\S+)\s*$", l)
        if m:
            raw = m.group(2).replace("O", "0").replace("o", "0").replace("l", "1")
            mm = re.match(r"^(\d\.\d{10})[D0E]([+-]\d\d)$", raw)
            assert mm, raw
            vals[int(m.group(1))] = float(mm.group(1) + "E" + mm.group(2))
    return [vals[i] for i in sorted(vals)]


nodes = own_nodes(4)
kort_order = sorted(nodes, key=lambda v: (len(v), tuple(s[1] for s in v), v))
pos = {v: i for i, v in enumerate(nodes)}
E = Evaluator(4)


def to_mine(alpha):
    b = np.empty(len(nodes))
    for i, v in enumerate(kort_order):
        b[pos[v]] = alpha[i]
    return b


a4 = grab(r"A\.4\s+Symmetric maximum for K 4", r"A\.5\s+NEOS input")
assert len(a4) == 40, len(a4)
b = to_mine(a4)
print("A.4 symmetric K4 (Kort final 0.6208791030): ours =", E.F(b, b) / 8)
np.savez(os.path.join(here, "kort_k4_sym.npz"), b1=b, b2=b)
x = grab(r"A\.6\s+Asymmetric maximum for K 4", r"^References")
assert len(x) == 80, len(x)
al, be = to_mine(x[0::2]), to_mine(x[1::2])
print("A.6 asymmetric K4 (Kort final 0.6214031155): ours =", E.F(al, be) / 8)
np.savez(os.path.join(here, "kort_k4_asym.npz"), b1=al, b2=be)
# sanity: K3 order on A.2
n3 = own_nodes(3)
k3o = sorted(n3, key=lambda v: (len(v), tuple(s[1] for s in v), v))
print("K3 Kort order:", k3o)
