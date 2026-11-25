#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""v4.0 回归：p±q 关系型泄露（samples18/）

覆盖 7 种"p、q 通过和 / 差 / 平方差 / 平方和给出"的题型：
  s01  给了 p+q 和 n              （hint 变量名 p_q_sum）
  s02  给了 p−q 和 n              （hint 变量名 p_q_diff）
  s03  只给 p+q 和 p−q，连 n 都没给
  s04  给了 p²−q² 和 n
  s05  给了 φ 和 p−q，没给 n
  s06  写成 s = p + q 再 print(s) 的形式
  s07  hint 变量名叫 s

用法:
  python3 run_tests18.py
  python3 run_tests18.py --exe win
  python3 run_tests18.py --exe /path/to/rsa_solver_v4.0.exe
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)  # 仓库根目录（rsa_solver.py 所在）
SAMPLES = os.path.join(HERE, "samples18")
PY = os.path.join(ROOT, "rsa_solver.py")

ANS = "flag{leak_p_plus_q_and_p_minus_q_test}"

CASES = [
    ("s01_sum_with_n.py", "给了 p+q 和 n（变量名 p_q_sum）"),
    ("s02_diff_with_n.py", "给了 p−q 和 n（变量名 p_q_diff）"),
    ("s03_sum_and_diff_no_n.py", "只给 p+q 和 p−q，连 n 都没给"),
    ("s04_sq_diff_with_n.py", "给了 p²−q² 和 n"),
    ("s05_phi_and_diff.py", "给了 φ 和 p−q，没给 n"),
    ("s06_expr_then_print.py", "写成 s = p + q 再 print(s)"),
    ("s07_hint_var_s.py", "hint 变量名就叫 s"),
    ("s08_literal_text.txt", "题面用一句话写 p - q = ...（无变量名）"),
]


def build_cmd(exe_arg):
    if not exe_arg:
        return [sys.executable, PY]
    if exe_arg == "win":
        for _nm in ("rsa_solver_v4.2.exe", "rsa_solver_v4.1.exe", "rsa_solver_v4.0.exe"):
            _p = os.path.join(HERE, _nm)
            if os.path.exists(_p):
                return ["wine", _p]
        return ["wine", os.path.join(ROOT, "rsa_solver_v4.2.exe")]
    return [exe_arg]


def main():
    exe_arg = None
    argv = sys.argv[:]
    if len(argv) > 2 and argv[1] == "--exe":
        exe_arg = argv[2]
    base = build_cmd(exe_arg)
    env = dict(os.environ, WINEDEBUG="-all")

    ok = 0
    print("%-32s %-6s %s" % ("样例", "结果", "说明"))
    print("-" * 92)
    for name, desc in CASES:
        try:
            r = subprocess.run(base + [os.path.join(SAMPLES, name), "--offline"],
                               capture_output=True, text=True, timeout=600,
                               env=env, cwd=HERE)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            out = "TIMEOUT"
        hit = ANS in out
        ok += hit
        print("%-32s %-6s %s" % (name, "通过" if hit else "失败", desc))
        if not hit:
            tail = "\n".join(out.strip().splitlines()[-3:])
            print("      最后输出: %s" % tail.replace("\n", " | ")[:220])
    print("-" * 92)
    print("通过 %d/%d" % (ok, len(CASES)))
    return 0 if ok == len(CASES) else 1


if __name__ == "__main__":
    sys.exit(main())
