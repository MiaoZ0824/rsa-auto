#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Windows 双击入口: 联网选择 / 拖拽文件 / 直接粘贴题目 / 命令行参数

v4.0 新增: p+q / p-q 关系型泄露自动反解
  · 双击或拖文件进来 → 先问一句「允许查公开分解库吗」
  · 回车 / n = 纯本地（默认，数据不出本机）
  · y = 本次允许联网
  · 大写 Y / N = 记住这个选择，以后不再问
  · 交互菜单里输入 set 可以随时改
  · 命令行已写 --online / --offline 的不再询问
"""
import os
import sys

_END_TOKENS = {"EOF", "END", "END.", ".", "---", "###", "结束", "完"}


def _pause():
    try:
        import rsa_solver
        if rsa_solver.stdin_is_interactive():
            input("\n按回车退出…")
    except Exception:
        pass


def _looks_like_text(t):
    """判断这一行是题面文本而不是文件路径"""
    s = t.strip()
    if not s:
        return False
    if os.path.isfile(s):
        return False
    marks = ("=", "(", ")", "import ", "from ", "def ", "print", "[", "]", "{", "}")
    return any(m in s for m in marks)


def _read_paste(first):
    """继续读剩下的行, 直到:
       · 单独一行 EOF / END
       · 连续两个空行(粘贴时很难出现两个连续空行, 基本不会误判)
       · Ctrl+Z / Ctrl+C
    """
    buf = [first]
    blanks = 0
    while True:
        try:
            line = input()
        except (EOFError, KeyboardInterrupt):
            break
        if line.strip().upper() in _END_TOKENS:
            break
        if not line.strip():
            blanks += 1
            if blanks >= 2:
                break
            print("   （还有内容就接着粘;已经粘完了再按一次回车 / 输入 EOF 立刻开算）")
            continue
        blanks = 0
        buf.append(line)
    return "\n".join(buf)


def _interactive(net_on=None):
    """返回 [题目/文件] ；输入 set 时返回字符串 "SET" ；没输入返回 None"""
    import rsa_solver
    print("=" * 60)
    print("  %s" % rsa_solver.BANNER)
    print("=" * 60)
    print(rsa_solver.announce_text("  "))
    print()
    print("  联网: %s" % rsa_solver.net_state_text(net_on))
    print("        （输入 set 回车可以改这个设置）")
    print("")
    print("三种用法, 任选一种:")
    print("")
    print("  ① 直接把题目粘进来 —— 粘完连按两次回车(或单独输入 EOF 回车), 立刻开算")
    print("  ② 把题目文件直接拖进这个窗口, 回车")
    print("  ③ 手动输入题目文件的路径, 回车")
    print("")
    print("长数字被聊天框折成好几行也没关系, 会自动接回去。")
    print("-" * 60)
    line = ""
    for _ in range(3):
        try:
            line = input("题目/文件 > ").strip().strip('"').strip("'")
        except (EOFError, KeyboardInterrupt):
            return None
        if line.lower() in ("set", "设置", "net", "联网"):
            return "SET"
        if line:
            break
        print("   还没输入内容。粘贴题目、拖文件进来、或者输入文件路径, 都可以。")
    if not line:
        return None

    # ① 文件
    if os.path.isfile(line):
        return [line]

    # ② 题面文本: 第一行是题面的开头, 继续往下读
    if _looks_like_text(line):
        print("-" * 60)
        print("检测到直接粘贴的题目, 继续粘完;粘完连按两次回车(或输入 EOF 回车):")
        text = _read_paste(line)
        return [text]

    # ③ 既不是文件也不像题目: 当路径试一次, 让主程序报错
    return [line]


def _fix_net_args(args, on):
    """把 --online / --offline 换成当前选择"""
    out = [a for a in args if a not in ("--online", "--offline")]
    return out + ["--online" if on else "--offline"]


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

    import rsa_solver

    argv0 = list(sys.argv[1:])
    explicit = ("--online" in argv0 or "--offline" in argv0
                or os.environ.get("RSA_SOLVER_OFFLINE"))

    # ---- 第一步: 决定这次要不要联网 ----
    if explicit:
        net_on = ("--online" in argv0) and ("--offline" not in argv0)
    else:
        pref = rsa_solver.load_pref()
        if pref is None:
            net_on = rsa_solver.ask_online()        # 没记住过 → 问一句
        else:
            net_on = pref                            # 记住过 → 直接用，不打扰
            print("  " + rsa_solver.net_state_text(pref) + "　（上次记住的设置）")

    args = _fix_net_args(argv0, net_on)

    # ---- 第二步: 没带任何参数(双击)就走交互菜单 ----
    if not argv0:
        while True:
            got = _interactive(net_on)
            if got == "SET":
                net_on = rsa_solver.ask_online()
                args = _fix_net_args(args, net_on)
                print("")
                continue
            if not got:
                return 1
            args += got
            break

    try:
        rc = rsa_solver.main(args)
    except Exception as ex:
        print("[!] 出错了: %s" % ex)
        rc = 2
    _pause()
    return rc


if __name__ == "__main__":
    sys.exit(main())
