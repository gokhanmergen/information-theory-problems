# Reviewer helper (2026-11-27): 'k = 3 optimum + one i.i.d. letter' behavioural k = 4 strategy from
# g3_behav.npz; writes k4_lift.npz (certified in certify_k4_lift.out).
# Run: python3 make_lift.py
# Runtime: about 1 s. Needs numpy.
"""Behavioural 'k=3 optimum + one i.i.d. letter' for k=4 (test input for certify_k4.py)."""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import own_nodes, Evaluator

here = os.path.dirname(os.path.abspath(__file__))
g3 = np.load(os.path.join(here, "g3_behav.npz"))
n3, n4 = own_nodes(3), own_nodes(4)
assert n4[:len(n3)] == n3
b1 = np.full(len(n4), 0.703506); b2 = np.full(len(n4), 0.703506)
b1[:len(n3)] = g3["b1"]; b2[:len(n3)] = g3["b2"]
E = Evaluator(4)
print("float value of lift:", E.F(b1, b2) / 8)
np.savez(os.path.join(here, "k4_lift.npz"), b1=b1, b2=b2)
