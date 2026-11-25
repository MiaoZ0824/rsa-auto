#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""v4.1 回归：脏写法 / 链式多模数 / 分段明文拼接（samples19/）

覆盖的真实题面特征（都是"标准样例能过、真实上传文件过不了"的那些点）：
  s01  三模数链 n1=pq / n2=qr / n3=rs，一个 flag 被切成 3 段，
       每段前面套一句废话 + 冒号（真实上传原文件）
  s02  只给 e1·e2 = 3087（e1/e2 根本没定义），密文变量名叫 flag1/flag2
       还带一行 flag = '***' 干扰（真实上传原文件）
  s03  n = 1 初始化后 n *= getPrime(32) 循环 15 次（真实上传原文件）
  s04  四段链 + 中文全角冒号前缀
  s05  两段纯碎片，没有任何前缀，直接拼

用法:
  python3 run_tests19.py
  python3 run_tests19.py --exe win                 # 跑同目录的 v4.1 exe
  python3 run_tests19.py --exe /path/to/xxx.exe
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)  # 仓库根目录（rsa_solver.py 所在）
SAMPLES = os.path.join(HERE, "samples19")
PY = os.path.join(ROOT, "rsa_solver.py")

CASES = [
    ("s01_three_mod_parts.txt", "flag{G00d_w4y_tO_cR4ck_RS4}", "三模数链 + 3 段明文拼接"),
    ("s02_e1e2_3087_flags.py", "NSSCTF{d64dba66-b608-4255-b888-0b0f25c2f90e}", "只给 e1·e2，密文叫 flag1/flag2"),
    ("s03_multi15_n1_init.py", "LitCTF{Mu1tiple_3m4ll_prim5_fac7ors_@re_uns4f5}", "n = 1 初始化 + 15 个 32bit 素数"),
    ("s04_chain4_prefixed.txt", "flag{4_p4rts_ch41n_fr0m_shared_pr1mes}", "四段链 + 中文全角冒号前缀"),
    ("s05_parts_bare.txt", "flag{tw0_p4rts_b4re_p13ces}", "两段纯碎片直接拼接"),
]


def build_cmd(exe_arg):
    if not exe_arg:
        return [sys.executable, PY]
    if exe_arg == "win":
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
    print("-" * 96)
    for name, ans, desc in CASES:
        try:
            r = subprocess.run(base + [os.path.join(SAMPLES, name), "--offline"],
                               capture_output=True, text=True, timeout=600,
                               env=env, cwd=HERE)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            out = "TIMEOUT"
        hit = ans in out
        ok += hit
        print("%-32s %-6s %s" % (name, "通过" if hit else "失败", desc))
        if not hit:
            tail = "\n".join(out.strip().splitlines()[-3:])
            print("      最后输出: %s" % tail.replace("\n", " | ")[:220])
    print("-" * 96)
    print("通过 %d/%d" % (ok, len(CASES)))
    return 0 if ok == len(CASES) else 1


if __name__ == "__main__":
    sys.exit(main())
