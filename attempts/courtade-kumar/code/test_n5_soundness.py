#!/usr/bin/env python3
"""Adversarial enclosure soundness test: verifies C interval primitives in
certify_n5.c (log2, binary entropy, Bernstein range, derivative range, and
MVF lower bound) against 200-bit mpmath.iv across thousands of random and
boundary test cases.
"""
import os
import random
import shutil
import subprocess
import tempfile
from pathlib import Path

from mpmath import iv, mp

iv.prec = 200
mp.dps = 65
LOG2 = iv.log(iv.mpf(2))

PROBE_C = r'''
#define main certify_n5_main_unused
#include "certify_n5.c"
#undef main

int main(void) {
    init_constants();
    init_hdist();
    int mode;
    while (scanf("%d", &mode) == 1) {
        if (mode == 1) {
            double x;
            if (scanf("%la", &x) != 1) break;
            iv_t r = iv_log2_point(x);
            printf("%.17a %.17a\n", r.lo, r.hi);
        } else if (mode == 2) {
            unsigned f;
            double lo, hi;
            if (scanf("%x %la %la", &f, &lo, &hi) != 3) break;
            fn_data_t fd;
            build_fn_data(f, &fd);
            iv_t m0 = IV_M0_TABLE[fd.k];
            iv_t t1 = iv_pt(lo);
            iv_t t2 = iv_div(iv_sub(iv_pt(hi), t1), iv_sub(iv_pt(1.0), t1));
            double mid = 0.5 * (lo + hi);
            iv_t sum_h_lo = iv_pt(0.0), sum_h_mid = iv_pt(0.0), sum_dJ = iv_pt(0.0);
            for (int g = 0; g < fd.ngroups; g++) {
                iv_t qr = dc5_range(fd.grp[g].b1, t1, t2);
                iv_t rr = dc5_range(fd.grp[g].b0, t1, t2);
                iv_t q_from_r = iv_sub(iv_pt(1.0), rr);
                iv_t r_from_q = iv_sub(iv_pt(1.0), qr);
                if (q_from_r.lo > qr.lo) qr.lo = q_from_r.lo;
                if (q_from_r.hi < qr.hi) qr.hi = q_from_r.hi;
                if (r_from_q.lo > rr.lo) rr.lo = r_from_q.lo;
                if (r_from_q.hi < rr.hi) rr.hi = r_from_q.hi;

                iv_t h1 = iv_bin_entropy_qr(iv_pt(qr.lo), iv_sub(iv_pt(1.0), iv_pt(qr.lo)));
                iv_t h2 = iv_bin_entropy_qr(iv_pt(qr.hi), iv_sub(iv_pt(1.0), iv_pt(qr.hi)));
                double hmin = (h1.lo < h2.lo) ? h1.lo : h2.lo;
                sum_h_lo = iv_add(sum_h_lo, iv_scale_pos(iv_pt(hmin), (double)fd.grp[g].mult));

                iv_t qm = dc5_eval_pt(fd.grp[g].b1, mid);
                iv_t rm = dc5_eval_pt(fd.grp[g].b0, mid);
                sum_h_mid = iv_add(sum_h_mid, iv_scale_pos(iv_bin_entropy_qr(qm, rm), (double)fd.grp[g].mult));

                iv_t dp = dc4_range(fd.grp[g].d1, t1, t2);
                iv_t term = iv_mul(dp, iv_log2(iv_div(rr, qr)));
                sum_dJ = iv_add(sum_dJ, iv_scale_pos(term, (double)fd.grp[g].mult));
            }
            iv_t g_conc = iv_sub(iv_add(m0, iv_scale_pos(sum_h_lo, 1.0 / 32.0)), iv_bin_entropy_pt(hi));
            iv_t g_mid = iv_sub(iv_add(m0, iv_scale_pos(sum_h_mid, 1.0 / 32.0)), iv_bin_entropy_pt(mid));
            iv_t a_iv = iv_make(lo, hi);
            iv_t dg = iv_sub(iv_scale_pos(sum_dJ, 1.0 / 32.0), iv_log2(iv_div(iv_sub(iv_pt(1.0), a_iv), a_iv)));
            double hw1 = rd_up(mid - lo), hw2 = rd_up(hi - mid);
            double hw = hw1 > hw2 ? hw1 : hw2;
            iv_t g_mvf = iv_add(g_mid, iv_mul(dg, iv_make(-hw, hw)));
            printf("%.17a %.17a %.17a %.17a %.17a %.17a\n",
                   g_conc.lo, g_mid.lo, g_mid.hi, dg.lo, dg.hi, g_mvf.lo);
        }
    }
    return 0;
}
'''


def find_compiler():
    env_cc = os.environ.get("CC")
    if env_cc:
        return [env_cc]
    clt_clang = "/Library/Developer/CommandLineTools/usr/bin/clang"
    clt_sdk = "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk"
    if os.path.exists(clt_clang) and os.path.isdir(clt_sdk):
        return [clt_clang, "-isysroot", clt_sdk]
    for cand in ("clang", "gcc", "cc"):
        p = shutil.which(cand)
        if p:
            return [p]
    raise RuntimeError("No C compiler found")


def main():
    code_dir = Path(__file__).resolve().parent
    rng = random.Random(42)

    log_xs = [
        1e-100, 1e-20, 1e-6, 1e-4, 0.495, 0.5, 0.7071067811865475, 0.7071067811865476,
        1.0, 1.0 + 2**-52, 1.0 - 2**-53, 1.4142135623730951, 2.0, 3.0, 32.0, 1e100,
    ]
    for _ in range(2000):
        e = rng.randint(-60, 60)
        m = rng.uniform(0.5, 2.0)
        log_xs.append(m * (2.0 ** e))

    fn_cases = []
    hard_fs = [0x00007fff, 0x00017fff, 0x013d6eb7, 0x0000ffff, 0x00000001, 0x00ff00ff]
    for _ in range(200):
        f = rng.choice(hard_fs) if rng.random() < 0.25 else rng.randrange(1, (1 << 32) - 1)
        k = rng.randint(13, 64800)
        w = rng.choice([1, 2, 4, 8, 16, 64, 256])
        lo = k / 131072.0
        hi = min(64881, k + w) / 131072.0
        if hi > lo:
            fn_cases.append((f, lo, hi))

    lines = [f"1 {x.hex()}" for x in log_xs] + [
        f"2 {f:08x} {lo.hex()} {hi.hex()}" for f, lo, hi in fn_cases
    ]

    with tempfile.TemporaryDirectory() as tmp:
        probe_c = Path(tmp) / "probe_soundness.c"
        probe_bin = Path(tmp) / "probe_soundness"
        probe_c.write_text(PROBE_C)
        cmd = find_compiler() + [
            f"-I{code_dir}", "-O3", "-ffp-contract=off", "-fno-fast-math",
            "-o", str(probe_bin), str(probe_c), "-lm",
        ]
        subprocess.run(cmd, check=True)
        proc = subprocess.run(
            [str(probe_bin)], input="\n".join(lines) + "\n",
            text=True, capture_output=True, check=True,
        )

    out_lines = proc.stdout.strip().splitlines()
    assert len(out_lines) == len(lines)

    max_w = 0.0
    for i, x in enumerate(log_xs):
        lo_s, hi_s = out_lines[i].split()
        c_lo = float.fromhex(lo_s)
        c_hi = float.fromhex(hi_s)
        true_iv = iv.log(iv.mpf(x)) / LOG2
        assert iv.mpf(c_lo) <= true_iv.a and true_iv.b <= iv.mpf(c_hi), (
            f"LOG2 SOUNDNESS FAILURE at x={x}: C=[{c_lo}, {c_hi}] vs true=[{true_iv.a}, {true_iv.b}]"
        )
        max_w = max(max_w, c_hi - c_lo)
    print(f"[PASS] {len(log_xs)}/{len(log_xs)} log2_point soundness checks passed (max width {max_w:.2e})")

    hd = [[bin(x ^ y).count("1") for y in range(32)] for x in range(32)]

    def g_and_dg_200(f, a_mp):
        c1 = [[0] * 6 for _ in range(32)]
        k_ones = 0
        for x in range(32):
            if (f >> x) & 1:
                k_ones += 1
                for y in range(32):
                    c1[y][hd[x][y]] += 1
        b = 1 - a_mp
        hcond = mp.mpf(0)
        dJ = mp.mpf(0)
        comb = [1, 5, 10, 10, 5, 1]
        comb4 = [1, 4, 6, 4, 1]
        for y in range(32):
            q1 = sum(c1[y][d] * (a_mp**d) * (b ** (5 - d)) for d in range(6))
            q0 = 1 - q1
            hcond += -(q1 * mp.log(q1) + q0 * mp.log(q0)) / mp.log(2)
            bq = [mp.mpf(c1[y][d]) / comb[d] for d in range(6)]
            dq = sum(5 * (bq[d + 1] - bq[d]) * comb4[d] * (a_mp**d) * (b ** (4 - d)) for d in range(5))
            dJ += dq * mp.log(q0 / q1) / mp.log(2)
        hcond /= 32
        ha = -(a_mp * mp.log(a_mp) + b * mp.log(b)) / mp.log(2)
        p = mp.mpf(k_ones) / 32
        hf = -(p * mp.log(p) + (1 - p) * mp.log(1 - p)) / mp.log(2)
        return (1 - hf) + hcond - ha, dJ / 32 - mp.log(b / a_mp) / mp.log(2)

    offset = len(log_xs)
    for idx, (f, lo, hi) in enumerate(fn_cases):
        g_conc_lo, g_mid_lo, g_mid_hi, dg_lo, dg_hi, g_mvf_lo = [
            float.fromhex(s) for s in out_lines[offset + idx].split()
        ]
        mid = mp.mpf(0.5 * (lo + hi))
        gm, _ = g_and_dg_200(f, mid)
        assert mp.mpf(g_mid_lo) <= gm <= mp.mpf(g_mid_hi), f"g_mid failure on {f:#x}"
        for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
            a = mp.mpf(lo) + mp.mpf(frac) * (mp.mpf(hi) - mp.mpf(lo))
            gv, dgv = g_and_dg_200(f, a)
            assert mp.mpf(g_conc_lo) <= gv, f"g_conc failure on {f:#x} at {a}"
            assert mp.mpf(dg_lo) <= dgv <= mp.mpf(dg_hi), f"dg failure on {f:#x} at {a}"
            assert mp.mpf(g_mvf_lo) <= gv, f"g_mvf failure on {f:#x} at {a}"

    print(
        f"[PASS] {len(fn_cases)}/{len(fn_cases)} (1,000 point checks) "
        f"g_conc, g_mid, dg, and g_mvf soundness checks PASSED against 200-bit mpmath!"
    )


if __name__ == "__main__":
    main()
