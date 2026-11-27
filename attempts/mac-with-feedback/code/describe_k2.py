"""Print the k=2 strategy distribution saved by opt_cl.py in readable form.
A 2-step strategy is written  x0 | f(0) f(1)  : first input x0, second input f(y1)."""
import sys
import numpy as np
from mac_cl import super_channel, bross_lapidoth_mac, cl_quantities

qq = float(sys.argv[1]) if len(sys.argv) > 1 else 0.5
D = np.load(f"opt_q{qq}.npz")
S1, S2, V = super_channel(bross_lapidoth_mac(qq), 2)
name = lambda s: f"{s[0][()]}|{s[1][(0,)]}{s[1][(1,)]}"
pu, P1, P2 = D["pu2"], D["P12"], D["P22"]
for u in range(len(pu)):
    if pu[u] < 1e-4:
        continue
    t1 = ", ".join(f"{name(S1[a])}:{P1[u, a]:.4f}" for a in np.argsort(-P1[u]) if P1[u, a] > 1e-3)
    t2 = ", ".join(f"{name(S2[b])}:{P2[u, b]:.4f}" for b in np.argsort(-P2[u]) if P2[u, b] > 1e-3)
    print(f"u={u} p(u)={pu[u]:.4f}\n   user1: {t1}\n   user2: {t2}")
A1, A2, B = cl_quantities(pu, P1, P2, V)
print(f"A1/2={A1/2:.6f} A2/2={A2/2:.6f} B/2={B/2:.6f} sum-rate={min(A1+A2, B)/2:.8f}")
