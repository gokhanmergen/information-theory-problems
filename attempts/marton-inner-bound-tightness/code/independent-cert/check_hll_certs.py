#!/usr/bin/env python3
"""Independent audit of HLL's stored one-letter certificates (*_e5.000e-07.json) from
github.com/yanxiaoliu-mike/Suboptimality_Marton (commit cc33e85).

The JSON files are treated as untrusted DATA (json.load only; none of HLL's code is imported).
All numbers are recomputed with python-flint arb (outward-rounded balls) and exact rationals.

What the stored files contain, and hence what can be checked:
  * per map / branch: one record per face (support set S of the simplex), with the face target,
    the interior branch-and-bound summary (processed boxes, largest pruned upper bound as an exact
    rational, remaining boxes) and a SHA-256 digest of the box transcript;
  * the individual boxes are NOT stored (4.7M boxes would be ~GBs), so a box-by-box re-derivation
    from the stored data is impossible.  The digest can only be compared with a re-run of HLL's
    engine (optional argument --replay DIR; that is replication, not an independent check).

Checks performed (each prints PASS/FAIL):
  1. exact instance (alpha, a, T_Y, T_Z) in every file == HLL paper decimals (14),(15),(17);
     ABCA witness == (19);
  2. HLL's stored witness enclosure contains our arb enclosure of G(19);
  3. target_B: our arb value of B - G(19) and of UB(p*) = alpha H(Y*) + abar H(Z*) + B - a.p*,
     which must be <= printed (25);  B identical in all files;
  4. omega (boundary modulus) >= our upper enclosure of 2h(delta) + delta(2 ln 6 + range a),
     delta = 2^-30 (the lemma itself is re-proved in the attempt file);
  5. structure: for each of the 81 maps all 15 nonempty faces S ⊆ {0,1,2,3} occur once, with
     target_S == B - (4-|S|) omega exactly, boundary children == {S minus i}, interior certified,
     remaining_boxes == 0 and largest_pruned_upper < target_S (exact rationals);
     the same for the two superposition branches with 7 faces of {0,1,2};
  6. vertex values (|S| = 1): HLL's stored upper bound encloses our arb value of
     G(e_x) = a_x - alpha H(T_Y(.|x)) - abar H(T_Z(.|x)), and is < target;
  7. coverage: all 81 maps and both branches; total processed boxes == 4,729,704;
  8. (optional) --replay DIR: every transcript_sha256 / box count equals a re-run's.

Usage: python -I check_hll_certs.py <HLL repo>/data/certificates/fixed_input [--replay DIR]
"""
import argparse
import glob
import itertools
import json
import os
import sys
from fractions import Fraction as Fr

from flint import arb, ctx, fmpq

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model as M  # noqa: E402

ctx.prec = 200
FAILS = []


def A(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


def H(dist):
    s = arb(0)
    for t in dist:
        t = Fr(t)
        if t:
            s += -(A(t) * A(t).log())
    return s


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (("  [" + detail + "]") if detail else ""))
    if not ok:
        FAILS.append(name)


def G19_ball():
    f, P = M.F19, M.P19
    px = [sum(P[i] for i in range(4) if f[i] == x) for x in range(3)]
    pY = [sum(px[x] * M.TY[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(px[x] * M.TZ[x][z] for x in range(3)) for z in range(3)]
    pu = [P[0] + P[1], P[2] + P[3]]
    pv = [P[0] + P[2], P[1] + P[3]]
    cells = [(0, 0), (0, 1), (1, 0), (1, 1)]
    pUY = [sum(P[i] * M.TY[f[i]][y] for i in range(4) if cells[i][0] == u) for u in range(2) for y in range(3)]
    pVZ = [sum(P[i] * M.TZ[f[i]][z] for i in range(4) if cells[i][1] == v) for v in range(2) for z in range(3)]
    al = A(M.ALPHA)
    G = (-al * H(pY) - (1 - al) * H(pZ) + (H(pu) + H(pY) - H(pUY)) + (H(pv) + H(pZ) - H(pVZ))
         - (H(pu) + H(pv) - H(P)) + A(sum(M.AVEC[x] * px[x] for x in range(3))))
    return G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("--replay")
    a = ap.parse_args()
    files = sorted(glob.glob(os.path.join(a.certdir, "cc_cert_*_e5.000e-07.json")))
    check("seven component files present", len(files) == 7, str([os.path.basename(f) for f in files]))
    data = {os.path.basename(f): json.load(open(f)) for f in files}

    # 1. instance
    for fn, d in data.items():
        ei = d["exact_instance"]
        ok = (Fr(ei["alpha"]) == M.ALPHA and [Fr(x) for x in ei["a_x"]] == M.AVEC
              and [[Fr(x) for x in r] for r in ei["t_y"]] == M.TY
              and [[Fr(x) for x in r] for r in ei["t_z"]] == M.TZ
              and [Fr(x) for x in d["abca_witness_prob"]] == M.P19)
        check(f"1. exact instance == paper (14),(15),(17),(19) in {fn}", ok)

    # 2. witness enclosure
    G19 = G19_ball()
    for fn, d in data.items():
        lo, hi = (Fr(x) for x in d["g_star_interval"])
        check(f"2. stored G(19) interval contains our arb enclosure ({fn})",
              A(lo) <= G19.lower() and G19.upper() <= A(hi), f"width {float(hi - lo):.2e}")
    print("   our G(19) =", G19.str(35))

    # 3. target
    Bs = {d["target_B"] for d in data.values()}
    check("3a. one common target_B in all files", len(Bs) == 1)
    B = Fr(Bs.pop())
    print("   target_B =", A(B).str(30), "  B - G(19) =", (A(B) - G19).str(25))
    check("3b. B - G(19) <= 5e-7 + 1e-22", (A(B) - G19) <= A(Fr(5, 10**7) + Fr(1, 10**22)))
    pY = [sum(M.PSTAR[x] * M.TY[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(M.PSTAR[x] * M.TZ[x][z] for x in range(3)) for z in range(3)]
    UB = A(M.ALPHA) * H(pY) + A(M.ABAR) * H(pZ) + A(B) - A(sum(M.AVEC[x] * M.PSTAR[x] for x in range(3)))
    print("   UB(p*) with B_T := target_B :", UB.str(30))
    check("3c. UB(p*) <= printed (25) 0.0916508833913554746710", UB.upper() <= A(Fr(M.UB25_S)))

    # 4. omega
    deltas = {d["boundary_cutoff"] for d in data.values()}
    omegas = {d["omega"] for d in data.values()}
    check("4a. common delta, omega", len(deltas) == 1 and len(omegas) == 1)
    delta, omega = Fr(deltas.pop()), Fr(omegas.pop())
    check("4b. delta == 2^-30 < 1/e", delta == Fr(1, 2**30))
    rng_a = max(M.AVEC) - min(M.AVEC)
    om_true = 2 * (-(A(delta) * A(delta).log())) + A(delta) * (2 * arb(6).log() + A(rng_a))
    check("4c. stored omega >= 2h(delta)+delta(2ln6+range a)", om_true.upper() <= A(omega),
          f"omega={float(omega):.6e}")
    # our sharper modulus (attempt file, Lemma 2): H2(delta) suffices when all vertex values < targets
    H2 = -(A(delta) * A(delta).log()) - (1 - A(delta)) * (1 - A(delta)).log()
    print("   (our sharper modulus H2(delta) =", H2.str(8), ")")

    # 5./6./7. structure, vertices, coverage
    vert = {}
    for x in range(3):
        vert[x] = A(M.AVEC[x]) - A(M.ALPHA) * H(M.TY[x]) - A(M.ABAR) * H(M.TZ[x])
    maps, sups, boxes = {}, {}, 0
    for fn, d in data.items():
        for r in d["map_records"]:
            maps.setdefault(tuple(r["metadata"][1]), []).append((fn, r))
        for r in d["superposition_records"]:
            sups.setdefault(r["metadata"][1], []).append((fn, r))
    check("7a. all 81 maps present exactly once", sorted(maps) == sorted(itertools.product(range(3), repeat=4))
          and all(len(v) == 1 for v in maps.values()), f"{len(maps)} maps")
    check("7b. both one-sided branches present once", sorted(sups) == ["u", "v"] and all(len(v) == 1 for v in sups.values()))

    def check_record(label, r, n, vertex_value):
        nonlocal boxes
        subs = {tuple(s["active"]): s for s in r["subproblems"]}
        want = [S for k in range(1, n + 1) for S in itertools.combinations(range(n), k)]
        ok = sorted(subs) == sorted(want) and len(r["subproblems"]) == len(want) and r["certified"]
        for S, s in subs.items():
            tgt = Fr(s["target_exact"])
            ok &= tgt == B - (n - len(S)) * omega
            ok &= s["certified"] is True
            kids = sorted(tuple(c["active"]) for c in s["boundary_children"])
            ok &= kids == sorted(tuple(i for i in S if i != j) for j in S) if len(S) > 1 else kids == []
            ok &= all(c["certified"] for c in s["boundary_children"])
            it = s["interior"]
            ok &= it["certified"] is True and it["remaining_boxes"] == 0
            ok &= Fr(it["largest_pruned_upper_exact"]) < tgt
            ok &= it.get("largest_remaining_upper") is None
            ok &= it["dimension"] == len(S) - 1
            boxes += it.get("processed_boxes", 0)
            if len(S) == 1:
                v = vertex_value(S[0])
                stored = A(Fr(it["root_upper_exact"]))
                ok &= v.upper() <= stored and stored < A(tgt)
                ok &= (stored - v).upper() < A(Fr(1, 10**40))
        return ok

    all_ok = True
    for f, [(fn, r)] in sorted(maps.items()):
        all_ok &= check_record(str(f), r, 4, lambda i, f=f: vert[f[i]])
    check("5/6. 81 map records: faces, targets, children, pruned uppers, vertex values", all_ok)
    all_ok = True
    for side, [(fn, r)] in sorted(sups.items()):
        all_ok &= check_record(side, r, 3, lambda i: vert[i])
    check("5/6. 2 superposition records: faces, targets, children, pruned uppers, vertex values", all_ok)
    check("7c. total processed boxes == 4,729,704", boxes == 4_729_704, str(boxes))
    worst = max(vert.values(), key=lambda v: v.mid())
    check("   vertex values all < B - 3 omega (needed by our sharper modulus)",
          all(v.upper() < A(B - 3 * omega) for v in vert.values()), f"max vertex {worst.str(10)}")

    # 8. replay comparison
    if a.replay:
        rep = {}
        for fn in glob.glob(os.path.join(a.replay, "*.json")):
            d = json.load(open(fn))
            for r in d.get("map_records", []):
                rep[("map", tuple(r["metadata"][1]))] = r
            for r in d.get("superposition_records", []):
                rep[("sup", r["metadata"][1])] = r
        stored = {("map", k): v[0][1] for k, v in maps.items()}
        stored.update({("sup", k): v[0][1] for k, v in sups.items()})
        same = missing = diff = 0
        for k, r in stored.items():
            if k not in rep:
                missing += 1
                continue
            s1 = [(tuple(s["active"]), s["interior"]["transcript_sha256"], s["interior"].get("processed_boxes"))
                  for s in r["subproblems"]]
            s2 = [(tuple(s["active"]), s["interior"]["transcript_sha256"], s["interior"].get("processed_boxes"))
                  for s in rep[k]["subproblems"]]
            if sorted(s1) == sorted(s2):
                same += 1
            else:
                diff += 1
        check(f"8. replay transcript digests identical ({same} identical, {diff} differ, {missing} not replayed)",
              diff == 0, "")
    print("SUMMARY:", "ALL CHECKS PASSED" if not FAILS else "FAILED: " + "; ".join(FAILS))


if __name__ == "__main__":
    main()
