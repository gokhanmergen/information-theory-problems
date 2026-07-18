#!/usr/bin/env python3
"""Symmetric numerical evaluation of the BEC-BSC Primitive Relay Channel (fixed indices).

Symmetric parametrization of P(T|Z) where T has outcomes {0, 1, 2}:
  - T=0 is "definitely 0"
  - T=1 is "uncertain"
  - T=2 is "definitely 1"
Transitions:
  - For Z=0: P(T=0) = a, P(T=1) = b, P(T=2) = 1-a-b
  - For Z=1: P(T=2) = a, P(T=1) = b, P(T=0) = 1-a-b
  - For Z=?: P(T=0) = c, P(T=2) = c, P(T=1) = 1-2c
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

def evaluate_symmetric(p_val, e_val, R0, num_restarts=30):
    ixy = 1 - h(p_val)
    ixyz = 1 - e_val * h(p_val)
    cutset = min(ixyz, ixy + R0)
    df = min(1 - e_val, ixy + R0)
    
    best_rate = ixy
    
    def objective(params):
        # softmax to ensure P(T|Z) is valid
        # For Z=0: [a, b, 1-a-b]
        ea = np.exp(params[0])
        eb = np.exp(params[1])
        denom = ea + eb + 1.0
        a = ea / denom
        b = eb / denom
        
        # For Z=?: [c, c, 1-2c] where c in (0, 0.5)
        c = 0.5 / (1.0 + np.exp(-params[2]))
        
        P_T_given_Z = np.zeros((3, 3))
        P_T_given_Z[0, 0] = a
        P_T_given_Z[0, 1] = b
        P_T_given_Z[0, 2] = 1 - a - b
        
        P_T_given_Z[1, 2] = a
        P_T_given_Z[1, 1] = b
        P_T_given_Z[1, 0] = 1 - a - b
        
        P_T_given_Z[2, 0] = c
        P_T_given_Z[2, 2] = c
        P_T_given_Z[2, 1] = 1 - 2*c
        
        P_xyzt = np.zeros((2, 2, 3, 3))
        for x in (0, 1):
            for y in (0, 1):
                p_y_given_x = p_val if y != x else 1 - p_val
                for z in (0, 1, 2):
                    if z == 2:
                        p_z_given_x = e_val
                    else:
                        p_z_given_x = (1 - e_val) if z == x else 0.0
                    for t in (0, 1, 2):
                        P_xyzt[x, y, z, t] = 0.5 * p_y_given_x * p_z_given_x * P_T_given_Z[z, t]
                        
        P_x = np.sum(P_xyzt, axis=(1, 2, 3))
        P_yt = np.sum(P_xyzt, axis=(0, 2))
        P_xyt = np.sum(P_xyzt, axis=2)
        h_yt = H_entropy(P_yt.flatten())
        h_yt_given_x = 0.0
        for x in (0, 1):
            P_yt_given_x = P_xyt[x] / P_x[x]
            h_yt_given_x += P_x[x] * H_entropy(P_yt_given_x.flatten())
        ix_yt = h_yt - h_yt_given_x
        
        h_t_given_y = 0.0
        P_y = np.sum(P_xyzt, axis=(0, 2, 3))
        P_t_given_y = np.zeros((2, 3))
        for y in (0, 1):
            P_t_given_y[y] = P_yt[y] / P_y[y]
            h_t_given_y += P_y[y] * H_entropy(P_t_given_y[y])
            
        h_t_given_z = 0.0
        P_z = np.sum(P_xyzt, axis=(0, 1, 3))
        P_zt = np.sum(P_xyzt, axis=(0, 1))
        for z in (0, 1, 2):
            if P_z[z] > 1e-15:
                P_t_given_z = P_zt[z] / P_z[z]
                h_t_given_z += P_z[z] * H_entropy(P_t_given_z)
                
        izt_given_y = h_t_given_y - h_t_given_z
        
        penalty = 0.0
        if izt_given_y > R0:
            penalty = 10000.0 * (izt_given_y - R0) ** 2
            
        return -ix_yt + penalty

    for _ in range(num_restarts):
        init_params = np.random.uniform(-2, 2, 3)
        res = minimize(objective, init_params, method='BFGS')
        if res.success:
            params = res.x
            ea = np.exp(params[0])
            eb = np.exp(params[1])
            denom = ea + eb + 1.0
            a = ea / denom
            b = eb / denom
            c = 0.5 / (1.0 + np.exp(-params[2]))
            
            P_T_given_Z = np.zeros((3, 3))
            P_T_given_Z[0, 0] = a
            P_T_given_Z[0, 1] = b
            P_T_given_Z[0, 2] = 1 - a - b
            
            P_T_given_Z[1, 2] = a
            P_T_given_Z[1, 1] = b
            P_T_given_Z[1, 0] = 1 - a - b
            
            P_T_given_Z[2, 0] = c
            P_T_given_Z[2, 2] = c
            P_T_given_Z[2, 1] = 1 - 2*c
            
            P_xyzt = np.zeros((2, 2, 3, 3))
            for x in (0, 1):
                for y in (0, 1):
                    p_y_given_x = p_val if y != x else 1 - p_val
                    for z in (0, 1, 2):
                        if z == 2:
                            p_z_given_x = e_val
                        else:
                            p_z_given_x = (1 - e_val) if z == x else 0.0
                        for t in (0, 1, 2):
                            P_xyzt[x, y, z, t] = 0.5 * p_y_given_x * p_z_given_x * P_T_given_Z[z, t]
            
            P_x = np.sum(P_xyzt, axis=(1, 2, 3))
            P_yt = np.sum(P_xyzt, axis=(0, 2))
            P_xyt = np.sum(P_xyzt, axis=2)
            h_yt = H_entropy(P_yt.flatten())
            h_yt_given_x = 0.0
            for x in (0, 1):
                P_yt_given_x = P_xyt[x] / P_x[x]
                h_yt_given_x += P_x[x] * H_entropy(P_yt_given_x.flatten())
            ix_yt = h_yt - h_yt_given_x
            
            h_t_given_y = 0.0
            P_y = np.sum(P_xyzt, axis=(0, 2, 3))
            P_t_given_y = np.zeros((2, 3))
            for y in (0, 1):
                P_t_given_y[y] = P_yt[y] / P_y[y]
                h_t_given_y += P_y[y] * H_entropy(P_t_given_y[y])
                
            h_t_given_z = 0.0
            P_z = np.sum(P_xyzt, axis=(0, 1, 3))
            P_zt = np.sum(P_xyzt, axis=(0, 1))
            for z in (0, 1, 2):
                if P_z[z] > 1e-15:
                    P_t_given_z = P_zt[z] / P_z[z]
                    h_t_given_z += P_z[z] * H_entropy(P_t_given_z)
                    
            izt_given_y = h_t_given_y - h_t_given_z
            
            if izt_given_y <= R0 + 1e-4:
                best_rate = max(best_rate, ix_yt)
                
    return ixy, df, best_rate, cutset

if __name__ == "__main__":
    p_val = 0.1
    e_val = 0.3
    print(f"BEC-BSC Primitive Relay Channel symmetric evaluation (p={p_val}, e={e_val}):")
    print(f"{'R0':>5} {'DF':>8} {'CF/EGN':>8} {'Cutset':>8} {'Gap':>8}")
    for R0 in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8]:
        ixy, df, cf, cs = evaluate_symmetric(p_val, e_val, R0)
        gap = cs - cf
        print(f"{R0:5.2f} {df:8.5f} {cf:8.5f} {cs:8.5f} {gap:8.5f}")
