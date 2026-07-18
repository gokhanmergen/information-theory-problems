#!/usr/bin/env python3
"""Numerical evaluation and capacity characterization of the BEC-BSC Primitive Relay Channel.

Model:
    X ~ Bern(0.5)  (uniform input)
    Z = X with prob 1-e, and ? with prob e  (BEC(e) relay observation)
    Y = X xor N, N ~ Bern(p)  (BSC(p) direct link)
    Relay -> Destination: noiseless link of capacity R0.

We evaluate:
    1. The Cutset Bound.
    2. The Decode-and-Forward (DF) rate.
    3. The Compress-and-Forward (CF) rate optimized over all transitions P(T|Z) with |T| = 3.
    4. The El Gamal-Gohari-Nair (EGN) upper bound, which simplifies for the primitive relay channel to:
       B = sup_{P(T|Z): I(Z; T|Y) <= R0} I(X; Y, T).
"""
import math
import numpy as np
from scipy.optimize import minimize

def h(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)

def H_entropy(prob_dist):
    """Entropy of a probability distribution (array-like)."""
    s = 0.0
    for p in prob_dist:
        if p > 1e-15:
            s -= p * math.log2(p)
    return s

def evaluate_bounds(p_val, e_val, R0, num_restarts=20):
    """Evaluate Cutset, DF, and optimize CF/EGN over P(T|Z) for |T|=3."""
    # Cutset bound: min( I(X; Y, Z), I(X; Y) + R0 )
    # I(X; Y, Z) = 1 - e * h(p)
    ixy = 1 - h(p_val)
    ixyz = 1 - e_val * h(p_val)
    cutset = min(ixyz, ixy + R0)
    
    # DF rate: min( I(X; Z), I(X; Y) + R0 )
    # I(X; Z) = 1 - e
    df = min(1 - e_val, ixy + R0)
    
    # For CF / EGN, we want to maximize I(X; Y, T) subject to I(Z; T | Y) <= R0.
    # Z has 3 outcomes: 0, 1, ? (erased). Let's represent them as indices 0, 1, 2.
    # T has 3 outcomes: 0, 1, ?. Let's represent them as indices 0, 1, 2.
    # We optimize the transition matrix P(T=t | Z=z) of size 3x3.
    # Each row z of P must sum to 1. So 6 degrees of freedom.
    
    best_rate = ixy  # T = const is always feasible and gives I(X; Y)
    
    # Objective function to MINIMIZE (negative of I(X; Y, T))
    def objective(params):
        P_T_given_Z = np.zeros((3, 3))
        # row 0
        P_T_given_Z[0, 0] = exp_logit(params[0])
        P_T_given_Z[0, 1] = exp_logit(params[1]) * (1 - P_T_given_Z[0, 0])
        P_T_given_Z[0, 2] = 1 - P_T_given_Z[0, 0] - P_T_given_Z[0, 1]
        # row 1
        P_T_given_Z[1, 0] = exp_logit(params[2])
        P_T_given_Z[1, 1] = exp_logit(params[3]) * (1 - P_T_given_Z[1, 0])
        P_T_given_Z[1, 2] = 1 - P_T_given_Z[1, 0] - P_T_given_Z[1, 1]
        # row 2
        P_T_given_Z[2, 0] = exp_logit(params[4])
        P_T_given_Z[2, 1] = exp_logit(params[5]) * (1 - P_T_given_Z[2, 0])
        P_T_given_Z[2, 2] = 1 - P_T_given_Z[2, 0] - P_T_given_Z[2, 1]
        
        # Calculate joint distribution P(x, y, z, t)
        # P(x) = 0.5
        # P(y|x) = BSC(p)
        # P(z|x) = BEC(e)
        # P(t|z) = transition
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
                        
        # Mutual information I(X; Y, T)
        P_x = np.sum(P_xyzt, axis=(1, 2, 3))
        P_yt = np.sum(P_xyzt, axis=(0, 2))
        P_xyt = np.sum(P_xyzt, axis=2)
        
        # I(X; Y, T) = H(Y, T) - H(Y, T | X)
        h_yt = H_entropy(P_yt.flatten())
        h_yt_given_x = 0.0
        for x in (0, 1):
            P_yt_given_x = P_xyt[x] / P_x[x]
            h_yt_given_x += P_x[x] * H_entropy(P_yt_given_x.flatten())
        ix_yt = h_yt - h_yt_given_x
        
        # Constraint: I(Z; T | Y) <= R0
        # I(Z; T | Y) = H(T | Y) - H(T | Z, Y)
        # Since Y -> X -> Z -> T is a Markov chain, T is independent of Y given Z.
        # So H(T | Z, Y) = H(T | Z)
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
        
        # Penalty for violating constraint
        penalty = 0.0
        if izt_given_y > R0:
            penalty = 1000.0 * (izt_given_y - R0) ** 2
            
        return -ix_yt + penalty

    def exp_logit(v):
        # Maps real line to (0, 1)
        return 1.0 / (1.0 + np.exp(-v))

    for _ in range(num_restarts):
        init_params = np.random.uniform(-3, 3, 6)
        res = minimize(objective, init_params, method='BFGS')
        if res.success:
            # check if constraint is satisfied
            # reconstruct transition
            params = res.x
            P_T_given_Z = np.zeros((3, 3))
            P_T_given_Z[0, 0] = exp_logit(params[0])
            P_T_given_Z[0, 1] = exp_logit(params[1]) * (1 - P_T_given_Z[0, 0])
            P_T_given_Z[0, 2] = 1 - P_T_given_Z[0, 0] - P_T_given_Z[0, 1]
            P_T_given_Z[1, 0] = exp_logit(params[2])
            P_T_given_Z[1, 1] = exp_logit(params[3]) * (1 - P_T_given_Z[1, 0])
            P_T_given_Z[1, 2] = 1 - P_T_given_Z[1, 0] - P_T_given_Z[1, 1]
            P_T_given_Z[2, 0] = exp_logit(params[4])
            P_T_given_Z[2, 1] = exp_logit(params[5]) * (1 - P_T_given_Z[2, 0])
            P_T_given_Z[2, 2] = 1 - P_T_given_Z[2, 0] - P_T_given_Z[2, 1]
            
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
            
            if izt_given_y <= R0 + 1e-5:
                best_rate = max(best_rate, ix_yt)
                
    return ixy, df, best_rate, cutset

if __name__ == "__main__":
    p_val = 0.1
    e_val = 0.3
    print(f"BEC-BSC Primitive Relay Channel evaluation (p={p_val}, e={e_val}):")
    print(f"{'R0':>5} {'DF':>8} {'CF/EGN':>8} {'Cutset':>8} {'Gap':>8}")
    for R0 in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8]:
        ixy, df, cf, cs = evaluate_bounds(p_val, e_val, R0)
        gap = cs - cf
        print(f"{R0:5.2f} {df:8.5f} {cf:8.5f} {cs:8.5f} {gap:8.5f}")
