#!/usr/bin/env python3
"""Evaluate the EGN upper bound (with P(V|X,Z) depending on X) for the BEC-BSC PRC.

EGN Proposition 1:
    B = max_{p(x), p(v|x,z)} min( I(X; Y, V) - I(V; X | Z), I(X; Y) + R0 - I(V; Z | X) )
We optimize this over all transitions P(V|X,Z) with |V| = 3.
By symmetry, we assume uniform X.
"""
import math
import numpy as np
from scipy.optimize import minimize

def h(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)

def H_entropy(prob_dist):
    s = 0.0
    for p in prob_dist:
        if p > 1e-15:
            s -= p * math.log2(p)
    return s

def evaluate_egn_bound(p_val, e_val, R0, num_restarts=30):
    ixy = 1 - h(p_val)
    
    # P(V | X, Z) has size 2 x 3 x 3.
    # For each (x, z), P(V | x, z) is a probability distribution over {0, 1, 2}.
    # So 6 distributions of size 3. 12 parameters.
    
    def objective(params):
        P_V_given_XZ = np.zeros((2, 3, 3))
        idx = 0
        for x in (0, 1):
            for z in (0, 1, 2):
                ea = np.exp(params[idx])
                eb = np.exp(params[idx+1])
                denom = ea + eb + 1.0
                P_V_given_XZ[x, z, 0] = ea / denom
                P_V_given_XZ[x, z, 1] = eb / denom
                P_V_given_XZ[x, z, 2] = 1.0 - P_V_given_XZ[x, z, 0] - P_V_given_XZ[x, z, 1]
                idx += 2
                
        # Joint distribution P(x, y, z, v)
        P_xyzv = np.zeros((2, 2, 3, 3))
        for x in (0, 1):
            for y in (0, 1):
                p_y_given_x = p_val if y != x else 1 - p_val
                for z in (0, 1, 2):
                    if z == 2:
                        p_z_given_x = e_val
                    else:
                        p_z_given_x = (1 - e_val) if z == x else 0.0
                    for v in (0, 1, 2):
                        P_xyzv[x, y, z, v] = 0.5 * p_y_given_x * p_z_given_x * P_V_given_XZ[x, z, v]
                        
        # 1. I(X; Y, V) - I(V; X | Z)
        P_x = np.sum(P_xyzv, axis=(1, 2, 3))
        P_yv = np.sum(P_xyzv, axis=(0, 2))
        P_xyv = np.sum(P_xyzv, axis=2)
        h_yv = H_entropy(P_yv.flatten())
        h_yv_given_x = 0.0
        for x in (0, 1):
            h_yv_given_x += P_x[x] * H_entropy((P_xyv[x] / P_x[x]).flatten())
        ix_yv = h_yv - h_yv_given_x
        
        # I(V; X | Z) = H(V | Z) - H(V | X, Z)
        P_z = np.sum(P_xyzv, axis=(0, 1, 3))
        P_zv = np.sum(P_xyzv, axis=(0, 1))
        h_v_given_z = 0.0
        for z in (0, 1, 2):
            if P_z[z] > 1e-15:
                h_v_given_z += P_z[z] * H_entropy(P_zv[z] / P_z[z])
                
        # H(V | X, Z)
        h_v_given_xz = 0.0
        P_xz = np.sum(P_xyzv, axis=(1, 3)) # size 2 x 3
        for x in (0, 1):
            for z in (0, 1, 2):
                if P_xz[x, z] > 1e-15:
                    h_v_given_xz += P_xz[x, z] * H_entropy(P_V_given_XZ[x, z])
                    
        iv_x_given_z = h_v_given_z - h_v_given_xz
        term1 = ix_yv - iv_x_given_z
        
        # 2. I(X; Y) + R0 - I(V; Z | X)
        # I(V; Z | X) = H(V | X) - H(V | X, Z)
        h_v_given_x = 0.0
        P_xv = np.sum(P_xyzv, axis=(1, 2))
        for x in (0, 1):
            h_v_given_x += P_x[x] * H_entropy(P_xv[x] / P_x[x])
            
        iv_z_given_x = h_v_given_x - h_v_given_xz
        term2 = ixy + R0 - iv_z_given_x
        
        return -min(term1, term2)

    best_val = 0.0
    for _ in range(num_restarts):
        init_params = np.random.uniform(-2, 2, 12)
        res = minimize(objective, init_params, method='BFGS')
        if res.success:
            best_val = max(best_val, -res.fun)
            
    return best_val

if __name__ == "__main__":
    p_val = 0.1
    e_val = 0.3
    print(f"EGN Upper Bound for BEC-BSC Primitive Relay Channel (p={p_val}, e={e_val}):")
    print(f"{'R0':>5} {'EGN':>8}")
    for R0 in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8]:
        egn = evaluate_egn_bound(p_val, e_val, R0)
        print(f"{R0:5.2f} {egn:8.5f}")
