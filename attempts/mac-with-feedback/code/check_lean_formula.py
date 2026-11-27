"""Independent check of cl_quantities against the Lean definitions (condMutualInfo = H(XZ)+H(YZ)-H(XYZ)-H(Z),
mutualInfo = H(X)+H(Y)-H(XY)) evaluated on the full joint table J(u, s1, s2, y^k) of
coverLeungKLetterRegion, for the saved k=2 optimum at q=0.5."""
import numpy as np
from mac_cl import super_channel, bross_lapidoth_mac, cl_quantities

def H(p):
    p = p.ravel(); p = p[p > 0]; return float(-(p * np.log2(p)).sum())

D = np.load("opt_q0.5.npz")
_, _, V = super_channel(bross_lapidoth_mac(0.5), 2)
pu, P1, P2 = D["pu2"], D["P12"], D["P22"]
J = np.einsum("u,ua,ub,aby->uaby", pu, P1, P2, V)          # axes: u, s1, s2, y
assert abs(J.sum() - 1) < 1e-12
# I(S1;Y|S2,U): X = s1, Y = y, Z = (s2,u)
I1 = H(J.sum(3)) + H(J.sum(1)) - H(J) - H(J.sum((1, 3)))
I2 = H(J.sum(3)) + H(J.sum(2)) - H(J) - H(J.sum((2, 3)))
I12 = H(J.sum((0, 3))) + H(J.sum((0, 1, 2))) - H(J.sum(0))
print("Lean-formula:", I1 / 2, I2 / 2, I12 / 2)
print("cl_quantities:", [x / 2 for x in cl_quantities(pu, P1, P2, V)])
