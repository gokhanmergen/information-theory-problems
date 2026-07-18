#!/usr/bin/env python3
import numpy as np
from scipy.optimize import minimize
import math

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

def exp_logit(v):
    return 1.0 / (1.0 + np.exp(-v))

def find_and_print():
    p_val = 0.1
    e_val = 0.3
    R0 = 0.8
    
    def objective(params):
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
        
        penalty = 0.0
        if izt_given_y > R0:
            penalty = 10000.0 * (izt_given_y - R0) ** 2
            
        return -ix_yt + penalty

    best_res = None
    best_rate = -1.0
    for _ in range(50):
        init_params = np.random.uniform(-3, 3, 6)
        res = minimize(objective, init_params, method='BFGS')
        if res.success:
            rate = -res.fun
            if rate > best_rate:
                # check constraint
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
                
                P_yt = np.sum(P_xyzt, axis=(0, 2))
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
                    best_rate = rate
                    best_res = (P_T_given_Z, rate, izt_given_y)
                    
    if best_res:
        print("Best rate:", best_res[1])
        print("Constraint value:", best_res[2])
        print("Optimal transition matrix P(T|Z):")
        print(best_res[0])
    else:
        print("No feasible solution found.")

if __name__ == "__main__":
    find_and_print()
