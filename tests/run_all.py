#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""一键跑全部回归（纯标准库，不需要 pytest）。

用法:
  python3 tests/run_all.py                # 用源码跑
  python3 tests/run_all.py --exe win      # 用仓库根目录的 exe 跑（需 wine）
  python3 tests/run_all.py --exe /path/to/rsa_solver.exe

退出码 0 = 全绿，1 = 有失败。
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

SUITES = [
    ("run_tests16.py", "多素数 / 模不互素 / lcm 泄露 / e1·e2 / py2 多段"),
    ("run_tests17.py", "真实上传题面（含需联网的一题）"),
    ("run_tests18.py", "p±q 关系反解系列"),
    ("run_tests19.py", "脏写法 / 链式多模数 / 明文分段拼接"),
]

RE_PASS = re.compile(r"通过\s*(\d+)\s*/\s*(\d+)")
RE_SKIP = re.compile(r"跳过\s*(\d+)")


def main():
    exe = None
    if len(sys.argv) > 2 and sys.argv[1] == "--exe":
        exe = sys.argv[2]

    total_pass = total_all = total_skip = 0
    failed_suites = []
    env = dict(os.environ, PYTHONIOENCODING="utf-8")

    print("=" * 78)
    print("  RSA 自动解题器 · 全量回归")
    print("  目标:", exe if exe else "源码 (rsa_solver.py)")
    print("=" * 78)

    for script, desc in SUITES:
        path = os.path.join(HERE, script)
        if not os.path.exists(path):
            print("  [缺失] %-16s %s" % (script, desc))
            failed_suites.append(script)
            continue
        cmd = [sys.executable, path]
        if exe:
            cmd += ["--exe", exe]
        try:
            r = subprocess.run(cmd, cwd=HERE, env=env, timeout=1800,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            out = r.stdout.decode("utf-8", "replace")
            rc = r.returncode
        except subprocess.TimeoutExpired:
            out, rc = "", 124

        m = RE_PASS.search(out)
        if m:
            p, n = int(m.group(1)), int(m.group(2))
            s = RE_SKIP.search(out)
            k = int(s.group(1)) if s else 0
            total_pass += p
            total_all += n
            total_skip += k
            mark = "通过" if (rc == 0 and p == n) else "有失败"
            if mark != "通过":
                failed_suites.append(script)
            extra = ("  跳过 %d（需联网）" % k) if k else ""
            print("  %-16s %s  %d/%d%s   %s" % (script, mark, p, n, extra, desc))
        else:
            failed_suites.append(script)
            print("  %-16s 解析失败 rc=%d   %s" % (script, rc, desc))
            tail = "\n".join(out.strip().splitlines()[-8:])
            if tail:
                print("    " + tail.replace("\n", "\n    "))

    print("-" * 78)
    print("  合计: 通过 %d/%d，跳过 %d" % (total_pass, total_all, total_skip))
    if failed_suites:
        print("  失败套件: " + ", ".join(failed_suites))
        return 1
    print("  全绿 ✅")
    return 0


if __name__ == "__main__":
    sys.exit(main())
