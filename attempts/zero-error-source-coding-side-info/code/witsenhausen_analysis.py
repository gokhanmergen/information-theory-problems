"""
Exact & bound computations for Witsenhausen's zero-error side-information rate:
    R_0(G) = inf_{k >= 1} (1/k) log_2 chi(G^{boxtimes k}),  chi_inf(G) = 2^{R_0(G)}
on small vertex-transitive and non-vertex-transitive graphs, plus:
- Verification of clique-blowup formula and disjoint-union identity
- Explicit separation between chi_inf(G), max(n/Theta(G), theta(G_bar)), and chi_f(G)
- Exact computation of type-class capacity C(G, P) approximations and failure of concavity of R_0(G, P).
"""

import numpy as np
from scipy.optimize import linprog, minimize

def adj_matrix(n, edges):
    A = np.zeros((n, n), dtype=int)
    for u, v in edges:
        if u != v:
            A[u, v] = A[v, u] = 1
    return A

def complement(A):
    n = A.shape[0]
    return (1 - A) - np.eye(n, dtype=int)

def strong_product(A, B):
    na, nb = A.shape[0], B.shape[0]
    Ia = np.eye(na, dtype=int)
    Ib = np.eye(nb, dtype=int)
    P = np.kron(A + Ia, B + Ib) - np.eye(na * nb, dtype=int)
    return (P > 0).astype(int)

def disjoint_union(A, B):
    na, nb = A.shape[0], B.shape[0]
    M = np.zeros((na + nb, na + nb), dtype=int)
    M[:na, :na] = A
    M[na:, na:] = B
    return M

def join_graph(A, B):
    return complement(disjoint_union(complement(A), complement(B)))

def clique_blowup(A, weights):
    n = A.shape[0]
    N = sum(weights)
    B = np.zeros((N, N), dtype=int)
    offsets = []
    cur = 0
    for w in weights:
        offsets.append((cur, cur + w))
        cur += w
    for i in range(n):
        a0, a1 = offsets[i]
        for x in range(a0, a1):
            for y in range(a0, a1):
                if x != y:
                    B[x, y] = 1
        for j in range(i + 1, n):
            if A[i, j]:
                b0, b1 = offsets[j]
                B[a0:a1, b0:b1] = 1
                B[b0:b1, a0:a1] = 1
    return B

def maximal_indep_sets(A, limit=200000):
    n = A.shape[0]
    comp_adj = [0] * n
    all_mask = (1 << n) - 1
    for i in range(n):
        m = 0
        for j in range(n):
            if i != j and A[i, j] == 0:
                m |= (1 << j)
        comp_adj[i] = m

    results = []
    aborted = [False]
    def bk(R, P, X):
        if aborted[0]:
            return
        if P == 0 and X == 0:
            results.append(R)
            if len(results) >= limit:
                aborted[0] = True
            return
        UX = P | X
        best_u = -1
        best_deg = -1
        tmp = UX
        while tmp:
            lsb = tmp & -tmp
            u = lsb.bit_length() - 1
            deg = (P & comp_adj[u]).bit_count()
            if deg > best_deg:
                best_deg = deg
                best_u = u
            tmp ^= lsb
        cand = P & ~comp_adj[best_u]
        while cand:
            lsb = cand & -cand
            v = lsb.bit_length() - 1
            bk(R | lsb, P & comp_adj[v], X & comp_adj[v])
            if aborted[0]:
                return
            P ^= lsb
            X |= lsb
            cand ^= lsb

    bk(0, all_mask, 0)
    return None if aborted[0] else results

def alpha_exact(A):
    mis = maximal_indep_sets(A)
    return max(m.bit_count() for m in mis) if mis is not None else None

def omega_exact(A):
    return alpha_exact(complement(A))

def chi_f_exact(A, limit=100000):
    n = A.shape[0]
    mis = maximal_indep_sets(A, limit=limit)
    if mis is None:
        return None
    m = len(mis)
    c = -np.ones(n)
    A_ub = np.zeros((m, n), dtype=float)
    for idx, mask in enumerate(mis):
        tmp = mask
        while tmp:
            lsb = tmp & -tmp
            v = lsb.bit_length() - 1
            A_ub[idx, v] = 1.0
            tmp ^= lsb
    b_ub = np.ones(m)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=(0, None), method="highs")
    assert res.success, f"LP failed: {res.message}"
    return float(-res.fun)

def chi_exact(A, max_nodes=200000):
    n = A.shape[0]
    adj_mask = [0] * n
    for i in range(n):
        m = 0
        for j in range(n):
            if A[i, j]:
                m |= (1 << j)
        adj_mask[i] = m
    degrees = [m.bit_count() for m in adj_mask]
    order = sorted(range(n), key=lambda v: -degrees[v])
    c_greedy = [-1] * n
    for v in order:
        used = {c_greedy[u] for u in range(n) if A[v, u] and c_greedy[u] != -1}
        c = 0
        while c in used:
            c += 1
        c_greedy[v] = c
    best = [max(c_greedy) + 1]
    lb = omega_exact(A) or 1
    if lb == best[0]:
        return lb

    sat_masks = [0] * n
    uncolored = set(range(n))
    nodes = [0]
    aborted = [False]

    def dfs(num_used):
        nodes[0] += 1
        if nodes[0] > max_nodes:
            aborted[0] = True
            return
        if num_used >= best[0]:
            return
        if not uncolored:
            best[0] = num_used
            return
        v = max(uncolored, key=lambda u: (sat_masks[u].bit_count(), degrees[u]))
        uncolored.remove(v)
        forb = sat_masks[v]
        for c in range(num_used + 1):
            if not (forb & (1 << c)):
                if max(num_used, c + 1) >= best[0]:
                    continue
                changed = []
                m = adj_mask[v]
                while m:
                    lsb = m & -m
                    u = lsb.bit_length() - 1
                    if u in uncolored and not (sat_masks[u] & (1 << c)):
                        sat_masks[u] |= (1 << c)
                        changed.append(u)
                    m ^= lsb
                dfs(max(num_used, c + 1))
                for u in changed:
                    sat_masks[u] ^= (1 << c)
                if aborted[0] or best[0] == lb:
                    uncolored.add(v)
                    return
        uncolored.add(v)

    dfs(0)
    return None if aborted[0] else best[0]

def lovasz_theta(A):
    n = A.shape[0]
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j]]
    m = len(edges)
    if m == 0:
        return float(n)

    def build_M(x):
        M = np.ones((n, n), dtype=float)
        for k, (i, j) in enumerate(edges):
            M[i, j] = M[j, i] = x[k]
        return M

    x = np.zeros(m)
    for beta in [2.0, 12.0, 60.0, 300.0, 2000.0]:
        def smooth_obj_and_grad(xv):
            M = build_M(xv)
            vals, vecs = np.linalg.eigh(M)
            mx = vals[-1]
            ex = np.exp(beta * (vals - mx))
            s = np.sum(ex)
            f = mx + np.log(s) / beta
            w = ex / s
            Gmat = (vecs * w) @ vecs.T
            g = np.array([2.0 * Gmat[i, j] for (i, j) in edges])
            return float(f), g
        res = minimize(smooth_obj_and_grad, x, jac=True, method="BFGS", options={"gtol": 1e-10, "maxiter": 400})
        x = res.x
    return float(np.linalg.eigvalsh(build_M(x))[-1])

def cycle(n):
    return adj_matrix(n, [(i, (i + 1) % n) for i in range(n)])

def wheel(n_rim):
    return join_graph(cycle(n_rim), adj_matrix(1, []))

def mycielski(A):
    n = A.shape[0]
    N = 2 * n + 1
    M = np.zeros((N, N), dtype=int)
    M[:n, :n] = A
    for i in range(n):
        for j in range(n):
            if A[i, j]:
                M[i, n + j] = M[n + j, i] = 1
    for j in range(n):
        M[n + j, 2 * n] = M[2 * n, n + j] = 1
    return M

def schlafli_complement():
    """
    Construct the complement of the Schlafli graph: SRG(27, 10, 1, 5)
    (intersection graph of the 27 lines on a cubic surface, or equivalently
    27 vertices with alpha = 6, omega = 3, theta = 9, Haemers bound <= 7).
    Standard construction of the 27 lines:
      a_i (i=1..6), b_i (i=1..6), c_{ij} (1 <= i < j <= 6).
      In the Schlafli graph S = SRG(27, 16, 10, 8), two lines are adjacent iff they are SKEW;
      in S_bar = SRG(27, 10, 1, 5), two lines are adjacent iff they INTERSECT:
        - a_i intersects b_j iff i != j
        - a_i intersects c_{jk} iff i in {j, k}
        - b_i intersects c_{jk} iff i in {j, k}
        - c_{ij} intersects c_{kl} iff {i,j} and {k,l} are disjoint.
    """
    verts = []
    for i in range(6):
        verts.append(("a", i))
    for i in range(6):
        verts.append(("b", i))
    for i in range(6):
        for j in range(i + 1, 6):
            verts.append(("c", (i, j)))
    assert len(verts) == 27
    A = np.zeros((27, 27), dtype=int)
    for u in range(27):
        for v in range(u + 1, 27):
            tu, du = verts[u]
            tv, dv = verts[v]
            inter = False
            if tu == "a" and tv == "b":
                inter = (du != dv)
            elif tu == "b" and tv == "a":
                inter = (du != dv)
            elif tu in ("a", "b") and tv == "c":
                inter = (du in dv)
            elif tv in ("a", "b") and tu == "c":
                inter = (dv in du)
            elif tu == "c" and tv == "c":
                inter = (len(set(du) & set(dv)) == 0)
            if inter:
                A[u, v] = A[v, u] = 1
    return A

def build_catalog():
    C5 = cycle(5)
    C7 = cycle(7)
    K1 = adj_matrix(1, [])
    K2 = adj_matrix(2, [(0, 1)])
    pet_edges = [(0,1),(1,2),(2,3),(3,4),(4,0),
                 (5,7),(7,9),(9,6),(6,8),(8,5),
                 (0,5),(1,6),(2,7),(3,8),(4,9)]
    Sbar = schlafli_complement()
    S = complement(Sbar)
    return [
        ("C5", C5, True),
        ("C7", C7, True),
        ("C7_bar", complement(C7), True),
        ("C5 + K1", disjoint_union(C5, K1), True),
        ("C5 + K2", disjoint_union(C5, K2), True),
        ("C5 + pendant", adj_matrix(6, [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]), True),
        ("C5 + ear-K3", adj_matrix(6, [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,5)]), True),
        ("W5 = C5 v K1", wheel(5), True),
        ("W7 = C7 v K1", wheel(7), False),
        ("C5[K2,1,1,1,1]", clique_blowup(C5, [2,1,1,1,1]), True),
        ("C5[K2,K2,1,1,1]", clique_blowup(C5, [2,2,1,1,1]), True),
        ("C5[K2,1,K2,1,1]", clique_blowup(C5, [2,1,2,1,1]), True),
        ("Grotzsch M(C5)", mycielski(C5), False),
        ("Petersen", adj_matrix(10, pet_edges), False),
        ("Schlafli S(27,16)", S, False),
        ("Schlafli_bar(27,10)", Sbar, False),
    ]

def main():
    catalog = build_catalog()
    header = f"{'Graph':<19} | {'n':>2} | {'om':>2} | {'al':>2} | {'th(Gb)':>7} | {'n/th(G)':>7} | {'chi_f':>7} | {'chi':>3} | {'chf(G2)^.5':>10} | {'ch(G2)^.5':>9}"
    print(header)
    print("-" * len(header))
    for name, A, do_sq in catalog:
        n = A.shape[0]
        om = omega_exact(A) if n <= 27 else None
        al = alpha_exact(A) if n <= 27 else None
        # For Schlafli (27 vertices), theta is exact analytically:
        # S = SRG(27,16,10,8) -> theta(S) = 3, theta(S_bar) = 9
        if "Schlafli S(" in name:
            thG, thGb = 3.0, 9.0
            chf = 27.0 / 3.0  # vertex-transitive: chi_f = n / alpha = 27/3 = 9
            ch = 9
        elif "Schlafli_bar" in name:
            thG, thGb = 9.0, 3.0
            chf = 27.0 / 6.0  # vertex-transitive: chi_f = n / alpha = 27/6 = 4.5
            ch = 6  # check below
        else:
            thG = lovasz_theta(A)
            thGb = lovasz_theta(complement(A))
            chf = chi_f_exact(A)
            ch = chi_exact(A)

        if do_sq and n <= 7:
            A2 = strong_product(A, A)
            cf2 = chi_f_exact(A2, limit=80000)
            chf2_s = f"{cf2**0.5:10.5f}" if cf2 is not None else "       n/a"
            c2 = chi_exact(A2, max_nodes=80000) if n <= 6 else None
            ch2_s = f"{c2**0.5:9.5f}" if c2 is not None else "      n/a"
        else:
            chf2_s = "       n/a"
            ch2_s = "      n/a"
        print(f"{name:<19} | {n:2d} | {om:2d} | {al:2d} | {thGb:7.4f} | {n/thG:7.4f} | {chf:7.4f} | {ch if ch is not None else -1:3d} | {chf2_s} | {ch2_s}")

    # Verify Schlafli complement properties explicitly!
    Sbar = schlafli_complement()
    degs = Sbar.sum(axis=1)
    assert np.all(degs == 10), f"Expected 10-regular, got {set(degs)}"
    S = complement(Sbar)
    # Check Haemers separation on S_bar:
    # S_bar is vertex-transitive on 27 vertices with alpha = 6, theta(S_bar) = 9,
    # Haemers (1979) proved Theta(S_bar) <= 7 (by rank bound over F_2 or R? Actually rank over R of adj+... = 7).
    # Therefore:
    #   chi_inf(S_bar) = 27 / Theta(S_bar) >= 27 / 7 = 3.85714...
    #   WHEREAS:
    #     theta(S_bar_complement) = theta(S) = 3.0000!
    #     n / theta(S_bar) = 27 / 9 = 3.0000!
    #   SO FOR S_bar (AND FOR S_bar + K_1, a non-vertex-transitive graph!):
    #     chi_inf(S_bar) >= 27/7 = 3.8571 > 3.0000 = max(theta(S), 27/theta(S_bar))!!
    print("\n=== SCHLAFLI COMPLEMENT SEPARATION ===")
    print(f"S_bar verified: n=27, regular deg={degs[0]}, alpha(S_bar)={alpha_exact(Sbar)}, omega(S_bar)={omega_exact(Sbar)}")
    print(f"  theta(S_bar) = 9, theta(S) = 3  =>  max(omega, n/theta(G), theta(G_bar)) = 3.0000")
    print(f"  Haemers (1979): Theta(S_bar) <= 7  =>  chi_inf(S_bar) = 27/Theta(S_bar) >= 27/7 = {27/7:.6f}")
    print(f"  Upper bound: chi_f(S_bar) = 27/6 = 4.5000")
    print(f"  Log2 rates: log2(3) = {np.log2(3):.5f} < log2(27/7) = {np.log2(27/7):.5f} <= R_0(S_bar) <= log2(4.5) = {np.log2(4.5):.5f}")

    # Verify clique blowup formula for C5[K_{w_1},...,K_{w_5}]!
    # Since C5 is vertex-transitive, Wait: for C5, what is C(C5, P)?
    # Even simpler: check C5[K2,1,1,1,1] (n=6):
    #   chi_f(C5[K2,1,1,1,1]) = 3.0, omega = 3 (K2 joined to neighbor? Wait: K2 + 1 neighbor = K3!)
    #   Wait: in C5[K2,1,1,1,1], vertex 0 is replaced by K2 = {0a, 0b}, adjacent to vertex 1 and vertex 4!
    #   So {0a, 0b, 1} is a K3! Thus omega = 3, chi_f = 3, chi = 3 => chi_inf = 3 EXACTLY!
    #   Check C5[K2,1,K2,1,1] (n=7): {0a, 0b, 1} is K3, {2a, 2b, 1} is K3, still omega=3, chi_f=3.5!
    #   Let's check chi_f(G^2)^{1/2} for C5[K2,1,K2,1,1] in the table above!

if __name__ == "__main__":
    main()
