#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""v3.7 回归: 用户实际遇到的五道题（全部来自真实题面数据）

  s01  15 个 32 bit 素数连乘          -> 多素数分解
  s02  三个模数两两共享素因子          -> 模不互素
  s03  泄露 lcm(p-1, q-1)             -> 泄露 φ/λ 的倍数
  s04  e1·e2 = 3087、e1/e2 未知       -> 共模 · e1·e2 = 常数
  s05  babyrsa 四关（py2 语法 + 多段） -> 多段链式求解
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)  # 仓库根目录（rsa_solver.py 所在）
SOLVER = os.path.join(ROOT, "rsa_solver.py")

CASES = [
    ("s01_multi15_prime32.txt", "flag{us4_s1ge_t0_cal_phI}", "15 个 32 bit 素数连乘"),
    ("s02_three_mod_shared_prime.txt", "flag{G00d_w4y_tO_cR4ck_RS4}", "三模数共享素因子"),
    ("s03_lcm_leak.txt", "NSSCTF{lcm_1eak_2ad1c_attack}", "泄露 lcm(p-1,q-1)"),
    ("s04_e1e2_product_3087.py", "NSSCTF{d64dba66-b608-4255-b888-0b0f25c2f90e}",
     "只给 e1·e2 = 3087"),
    ("s05_babyrsa_multistage.py", "de1ctf{9b10a98b-71bb-4bdf-a6ff-f319943de21f}",
     "babyrsa 四关（py2 + 多段）"),
]


def run(path):
    if len(sys.argv) > 2 and sys.argv[1] == "--exe":
        exe = sys.argv[2]
        if exe == "win":
            cand = [os.path.join(ROOT, "rsa_solver_v4.2.exe"),
        os.path.join(ROOT, "dist", "rsa_solver_v4.2.exe"),
        os.path.join(ROOT, "rsa_solver_v4.1.exe"),
                    os.path.join(ROOT, "rsa_solver_v4.0.exe"),
                    os.path.join(ROOT, "dist", "rsa_solver_v4.1.exe"),
                    os.path.join(ROOT, "dist", "rsa_solver_v4.0.exe")]
            exe = next((c for c in cand if os.path.exists(c)), cand[0])
            base = ["wine", exe]
        else:
            base = [exe]
    else:
        base = [sys.executable, SOLVER]
    try:
        # v3.9: 显式 --offline，避免 exe 启动时弹联网选择把批跑卡住
        r = subprocess.run(base + [path, "--offline"],
                           capture_output=True, text=True, timeout=600,
                           env=dict(os.environ, WINEDEBUG="-all"))
        return r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def main():
    ok = 0
    print("%-34s %-6s %s" % ("样例", "结果", "说明"))
    print("-" * 96)
    for name, want, desc in CASES:
        out = run(os.path.join(HERE, "samples16", name))
        hit = want in out
        ok += hit
        print("%-34s %-6s %s" % (name, "通过" if hit else "失败", desc))
        if not hit:
            tail = "\n".join(out.strip().splitlines()[-4:])
            print("      最后输出: %s" % tail.replace("\n", " | ")[:200])
    print("-" * 96)
    print("通过 %d/%d" % (ok, len(CASES)))
    return 0 if ok == len(CASES) else 1


if __name__ == "__main__":
    sys.exit(main())
