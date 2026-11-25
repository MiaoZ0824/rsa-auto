#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""v3.7 真实题面回归（samples17/ 里全部是用户真实发过的题面，未改一个字符）

用法:
  python3 run_tests17.py              # 用本机 python 跑 rsa_solver.py
  python3 run_tests17.py --exe win    # 用 wine 跑 rsa_solver_v4.0.exe（验证打包产物）
  python3 run_tests17.py --exe /path/to/rsa_solver_v4.0.exe
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)  # 仓库根目录（rsa_solver.py 所在）
SAMPLES = os.path.join(HERE, "samples17")
PY = os.path.join(ROOT, "rsa_solver.py")

# 最后一项需要联网查公开分解库（v3.8 起默认纯本地，不会自动联网）
CASES = [
    ("s01_multi15_chat.txt", "LitCTF{Mu1tiple_3m4ll_prim5_fac7ors_@re_uns4f5}",
     "15 个 32bit 素数（聊天里贴的那道）"),
    ("s01b_multi15_upload.py", "flag{us4_s1ge_t0_cal_phI}",
     "15 个 32bit 素数（上传文件那道）"),
    ("s02_three_mod.txt", "flag{G00d_w4y_tO_cR4ck_RS4}", "三模数共享素因子"),
    ("s04_e1e2_3087.py", "NSSCTF{d64dba66-b608-4255-b888-0b0f25c2f90e}",
     "只给 e1·e2 = 3087"),
    ("s05_babyrsa_upload.py", "de1ctf{9b10a98b-71bb-4bdf-a6ff-f319943de21f}",
     "babyrsa 四关（上传的原文件，py2 语法 + 多段）"),
    ("x06_nctf_smallprime_plus1.py", "NCTF{Th3r3_ar3_1ns3cure_RSA_m0duli_7hat_at_f1rst_gl4nce_appe4r_t0_be_s3cur3}",
     "小素数连乘 +1 生成 p/q（上传原文件，需 --online）"),
    ("x07_nctf_d_leak.py", "NCTF{70u2_nn47h_14_v3ry_gOO0000000d}",
     "只给 d 没给 n，q = nextPrime(p)（上传原文件）"),
    ("x08_bjd_common_p.py", "BJD{p_is_common_divisor}",
     "e 未知 + 两组模数共享素因子（上传原文件）"),
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


ONLINE_CASES = {"x06_nctf_smallprime_plus1.py"}


def main():
    exe_arg = None
    allow_online = "--allow-online" in sys.argv
    argv = [a for a in sys.argv if a != "--allow-online"]
    if len(argv) > 2 and argv[1] == "--exe":
        exe_arg = argv[2]
    base = build_cmd(exe_arg)
    env = dict(os.environ, WINEDEBUG="-all")

    ok = 0
    skipped = 0
    print("%-30s %-6s %s" % ("真实题面", "结果", "说明"))
    print("-" * 100)
    for name, want, desc in CASES:
        if name in ONLINE_CASES and not allow_online:
            skipped += 1
            print("%-30s %-6s %s" % (name, "跳过", desc + "（纯本地跑不动，加 --allow-online 复测）"))
            continue
        # v3.9: 显式指定联网开关，免得 exe 启动时停下来问
        extra = ["--online"] if name in ONLINE_CASES else ["--offline"]
        try:
            r = subprocess.run(base + [os.path.join(SAMPLES, name)] + extra,
                               capture_output=True, text=True, timeout=900,
                               env=env, cwd=HERE)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            out = "TIMEOUT"
        hit = want in out
        ok += hit
        print("%-30s %-6s %s" % (name, "通过" if hit else "失败", desc))
        if not hit:
            tail = "\n".join(out.strip().splitlines()[-3:])
            print("      最后输出: %s" % tail.replace("\n", " | ")[:220])
    print("-" * 100)
    print("通过 %d/%d%s" % (ok, len(CASES) - skipped,
                           ("，跳过 %d 项（需联网）" % skipped) if skipped else ""))
    return 0 if ok == len(CASES) - skipped else 1


if __name__ == "__main__":
    sys.exit(main())
