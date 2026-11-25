#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
rsa_solver.py - CTF RSA 自动题型判定 + 自动解密

纯标准库，零依赖。用法见 README / --help
"""

import sys
import os
import re
import json
import math
import time
import random
import ast
import hashlib
from fractions import Fraction

__version__ = "4.2"

# 题面原文（用来判断出题人用的是 Python 2 还是 3）
_RAW_SRC = {"text": ""}

# ============================================================
# 1. 基础数论
# ============================================================

_SMALL_PRIMES = []


def _init_small_primes(limit=200001):
    if _SMALL_PRIMES:
        return
    sieve = bytearray([1]) * limit
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    _SMALL_PRIMES.extend([i for i in range(limit) if sieve[i]])


_init_small_primes()


def egcd(a, b):
    """扩展欧几里得 (迭代实现: 2048 位大整数用递归版会爆栈)"""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return (old_r, old_s, old_t)


def modinv(a, m):
    a %= m
    if a == 0:
        raise ValueError("inverse of 0")
    g, x, _ = egcd(a, m)
    if g != 1:
        raise ValueError("not invertible")
    return x % m


def is_perfect_square(n):
    if n < 0:
        return False
    r = math.isqrt(n)
    return r * r == n


def iroot(n, k):
    """整数 k 次根, 返回 (root, exact)"""
    if n < 0:
        if k % 2 == 0:
            raise ValueError("negative even root")
        r, e = iroot(-n, k)
        return (-r, e)
    if n == 0:
        return (0, True)
    if k == 1:
        return (n, True)
    if k == 2:
        r = math.isqrt(n)
        return (r, r * r == n)
    # Newton
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // pow(x, k - 1)) // k
        if y >= x:
            break
        x = y
    while pow(x, k) > n:
        x -= 1
    while pow(x + 1, k) <= n:
        x += 1
    return (x, pow(x, k) == n)


def is_prime(n, rounds=24):
    if n < 2:
        return False
    for p in _SMALL_PRIMES[:200]:
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    # 确定性基底 (n < 3.3e24)
    bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    if n < 3317044064679887385961981:
        test = bases[:12]
    else:
        test = bases + [random.randrange(2, n - 1) for _ in range(rounds)]
    for a in test:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_prime(n):
    if n <= 2:
        return 2
    n |= 1
    while not is_prime(n):
        n += 2
    return n


def gcd(*args):
    r = 0
    for a in args:
        r = math.gcd(r, a)
    return r


# ============================================================
# 2. 分解算法
# ============================================================

def trial_division(n, limit=100000):
    """试除小素数, 返回 (factor, cofactor) 或 None"""
    for p in _SMALL_PRIMES:
        if p > limit:
            break
        if n % p == 0:
            return (p, n // p)
    return None


def fermat(n, max_iter=2000000):
    """费马分解: p, q 相近时极快"""
    if n % 2 == 0:
        return (2, n // 2)
    a = math.isqrt(n)
    if a * a < n:
        a += 1
    for i in range(max_iter):
        b2 = a * a - n
        b = math.isqrt(b2)
        if b * b == b2:
            p = a - b
            if p > 1 and n % p == 0:
                return (p, n // p)
        a += 1
    return None


def pollard_rho(n, max_iter=20000000):
    """Brent 版 Pollard rho"""
    if n % 2 == 0:
        return 2
    for attempt in range(6):
        if attempt == 0:
            c, x = 1, 2
        else:
            c = random.randrange(1, n)
            x = random.randrange(2, n)
        y, d, r = x, 1, 1
        q = 1
        it = 0
        while d == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and d == 1:
                ys = y
                for _ in range(min(128, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                d = math.gcd(q, n)
                k += 128
            r *= 2
            it += r
            if it > max(50000, max_iter // 6):
                break
        if 1 < d < n:
            return d
    return None


def pollard_pm1(n, bound=200000, check=None):
    """Pollard p-1: p-1 (或 q-1) 光滑时秒杀。

    v2.4 两处关键改动:
      1) 素数上限提到 200000 —— CTF 里用 Crypto.Util.number.sieve_base
         (前 10000 个素数, 最大 104729) 造出来的 p, p-1 的最大素因子能到
         104729, 旧的 20000 上限根本够不着。
      2) 每个素数不是一次性乘上它的最高次幂, 而是逐次乘一次、查一次 gcd。
         否则当 p-1 和 q-1 都光滑时, 一次糊到 gcd = n, 两个因子都锁死,
         拿不到真因子; 逐步查能在"只有一个被覆盖"的那一步把它揪出来。
    """
    a = 2
    for p in _SMALL_PRIMES:
        if p > bound:
            break
        pk = p
        while pk * p <= bound:
            pk *= p
        cur = 1
        while cur * p <= pk:
            cur *= p
            a = pow(a, p, n)
            g = math.gcd(a - 1, n)
            if g == n:
                # 这一步两边同时被覆盖, 只能换更大范围再试
                return None
            if g > 1:
                return g
            if check is not None and check():
                return None
    return None


def williams_pp1(n, bound=20000):
    """Williams p+1 (简单版)"""
    for B in (bound, bound * 10):
        a = 3
        for p in _SMALL_PRIMES:
            if p > B:
                break
            pk = p
            while pk * p <= B:
                pk *= p
            # 计算 V_pk(a) via Lucas chain (简化: 反复平方)
            for _ in range(pk):
                a = (a * a - 2) % n
            g = math.gcd(a - 1, n)
            if 1 < g < n:
                return g
    return None


_ONLINE = {"on": False, "fails": 0}   # v3.8: 默认纯本地，不把题目数据发出去；要查库加 --online
_ONLINE_CACHE = {}


def factor_online(n, timeout=10):
    """查公开分解库 (factordb)。

    只接受"完全分解且每个因子确实是素数"的结果, 否则当没查到 ——
    分解库里的部分分解、疑似素数一律不用, 免得拿错因子算出乱码。
    """
    if not _ONLINE["on"] or n.bit_length() < 96:
        return None
    key = str(n)
    if key in _ONLINE_CACHE:
        return _ONLINE_CACHE[key]
    res = None
    try:
        import urllib.request
        url = "https://factordb.com/api?query=%s" % key
        with urllib.request.urlopen(url, timeout=timeout) as r:
            data = json.loads(r.read().decode("utf-8", "replace"))
        if data.get("status") in ("FF", "P"):
            fs = []
            for f, ex in data.get("factors", []):
                fs.extend([int(f)] * int(ex))
            if fs and math.prod(fs) == n and all(is_prime(f) for f in fs):
                res = sorted(fs)
    except Exception:
        _ONLINE["fails"] += 1
        if _ONLINE["fails"] >= 3:
            _ONLINE["on"] = False   # 网络不通就别反复卡超时
    _ONLINE_CACHE[key] = res
    return res


def factor_int(n, effort=2, verbose=None):
    """
    通用整数分解, 返回素因子列表 (含重数)
    effort: 1 快速 / 2 标准 / 3 死磕
    """
    if n < 0:
        return []
    if n in (0, 1):
        return []
    factors = []
    # 小素数
    for p in _SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            factors.append(p)
            n //= p
    if n == 1:
        return sorted(factors)
    # 0) 公开分解库 (大 n 唯一现实出路, 先查一下不亏)
    if _ONLINE["on"] and n.bit_length() >= 160:
        fs = factor_online(n)
        if fs:
            return sorted(factors + fs)
    # 递归分解
    stack = [n]
    budget_end = time.time() + {1: 3.0, 2: 12.0, 3: 60.0}.get(effort, 12.0)
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime(m):
            factors.append(m)
            continue
        if time.time() > budget_end:
            factors.append(m)  # 未能分解, 原样放回
            continue
        f = None
        # 1) 小素数再试一轮 (上面只到 20000)
        t = trial_division(m, limit=1000000)
        if t:
            f = t[0]
        # 2) 完全平方
        if f is None and is_perfect_square(m):
            r = math.isqrt(m)
            stack.append(r)
            stack.append(r)
            continue
        # 3) 费马 (p,q 相近 / nextprime 型)
        if f is None:
            r = fermat(m, max_iter=200000 if effort >= 2 else 20000)
            if r:
                f = r[0]
        # 4) p-1 (大 n 也要试: CTF 的 p-1 光滑题都是几千位的 n)
        if f is None and m.bit_length() <= 8192:
            r = pollard_pm1(m, bound=100000 if effort < 3 else 200000,
                            check=lambda: time.time() > budget_end)
            if r:
                f = r
        # 5) rho (按剩余时间分配迭代次数)
        if f is None and m.bit_length() < 400:
            remain = max(0.1, budget_end - time.time())
            iters = int(min(40000000, max(500000, remain * 2500000)))
            r = pollard_rho(m, max_iter=iters)
            if r:
                f = r
        if f is None or f in (1, m):
            remain = max(0.0, budget_end - time.time())
            if m.bit_length() < 200 and remain > 0.5:
                r = pollard_rho(m, max_iter=int(remain * 2500000))
                if r and r not in (1, m):
                    f = r
        if f is None or f in (1, m):
            factors.append(m)
            continue
        stack.append(f)
        stack.append(m // f)
    return sorted(factors)


def compute_phi_from_factors(factors):
    phi = 1
    for p, cnt in _count(factors).items():
        phi *= (p - 1) * pow(p, cnt - 1)
    return phi


def _count(seq):
    d = {}
    for x in seq:
        d[x] = d.get(x, 0) + 1
    return d


# ============================================================
# 3. Wiener 攻击 / 连分数
# ============================================================

def continued_fraction(num, den):
    cf = []
    while den:
        q = num // den
        cf.append(q)
        num, den = den, num - q * den
    return cf


def convergents(cf):
    h0, h1 = 0, 1
    k0, k1 = 1, 0
    for a in cf:
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        yield (h1, k1)


def wiener_attack(n, e):
    """d 很小时 (d < n^0.25/3) 用连分数恢复 d"""
    for (k, d) in convergents(continued_fraction(e, n)):
        if k == 0 or d == 0:
            continue
        if (e * d - 1) % k != 0:
            continue
        phi = (e * d - 1) // k
        s = n - phi + 1
        disc = s * s - 4 * n
        if disc < 0:
            continue
        t = math.isqrt(disc)
        if t * t != disc:
            continue
        if (s + t) % 2:
            continue
        p = (s + t) // 2
        q = (s - t) // 2
        if p * q == n:
            return d, p, q
    return None


def boneh_durfee_lite(n, e):
    """
    简化版 Wiener 扩展: 尝试连分数邻域 (处理 d < n^0.292 中的一部分)
    真正 Boneh-Durfee 需要格, 这里只做一个可选的启发式扩展
    """
    cf = continued_fraction(e, n)
    for i in range(1, len(cf)):
        for delta in (-1, 0, 1):
            if cf[i] + delta <= 0:
                continue
            cf2 = cf[:i] + [cf[i] + delta]
            for (k, d) in convergents(cf2):
                if k == 0 or d == 0:
                    continue
                if (e * d - 1) % k != 0:
                    continue
                phi = (e * d - 1) // k
                s = n - phi + 1
                disc = s * s - 4 * n
                if disc < 0:
                    continue
                t = math.isqrt(disc)
                if t * t == disc and (s + t) % 2 == 0:
                    p = (s + t) // 2
                    q = (s - t) // 2
                    if p * q == n:
                        return d, p, q

# ============================================================
# 4. 多项式工具
# ============================================================

from decimal import Decimal, getcontext


def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                r[i + j] += x * y
    return r


def poly_pow(a, k):
    r = [1]
    for _ in range(k):
        r = poly_mul(r, a)
    return r


def poly_eval(coeffs, x):
    v = 0
    for c in reversed(coeffs):
        v = v * x + c
    return v


def poly_trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_divmod_int(a, b):
    """整数多项式伪除法后的精确除法 (Fraction)"""
    from fractions import Fraction as F
    a = [F(x) for x in a]
    b = [F(x) for x in b]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    if len(b) == 1 and b[0] == 0:
        raise ZeroDivisionError
    r = list(a)
    q = [F(0)] * max(1, len(a) - len(b) + 1)
    db = len(b) - 1
    while len(r) - 1 >= db and any(x != 0 for x in r):
        d = len(r) - 1 - db
        c = r[-1] / b[-1]
        q[d] = c
        for i in range(len(b)):
            r[d + i] -= c * b[i]
        while r and r[-1] == 0:
            r.pop()
        if not r:
            break
    if not r:
        r = [F(0)]
    return q, r


def poly_deriv(p):
    if len(p) <= 1:
        return [0]
    return [p[i] * i for i in range(1, len(p))]


def _sturm_sequence(coeffs):
    from fractions import Fraction as F
    p0 = [F(x) for x in coeffs]
    while len(p0) > 1 and p0[-1] == 0:
        p0.pop()
    if len(p0) <= 1:
        return [p0]
    p1 = poly_deriv(p0)
    if not any(x != 0 for x in p1):
        return [p0]
    seq = [p0, p1]
    while len(seq) < 60:
        try:
            _, r = poly_divmod_int(seq[-2], seq[-1])
        except ZeroDivisionError:
            break
        r = [-x for x in r]
        if not any(x != 0 for x in r):
            break
        while len(r) > 1 and r[-1] == 0:
            r.pop()
        seq.append(r)
    return seq


def _int_poly(p):
    """Fraction 系数多项式 -> 整数系数多项式 (乘以公分母, 符号不变)"""
    dens = [c.denominator for c in p]
    l = 1
    for d in dens:
        l = l * d // math.gcd(l, d)
    return [int(c * l) for c in p]


def _sign_changes(seq, x):
    signs = []
    for p in seq:
        ip = p if all(isinstance(c, int) for c in p) else _int_poly(p)
        v = 0
        for c in reversed(ip):
            v = v * x + c
        if v == 0:
            continue
        signs.append(1 if v > 0 else -1)
    return sum(1 for i in range(1, len(signs)) if signs[i] != signs[i - 1])


def poly_int_roots(coeffs, bound=None, max_roots=6, quick_limit=30000):
    """整数多项式在 [-bound,bound] 内的整数根"""
    coeffs = [int(c) for c in coeffs]
    poly_trim(coeffs)
    if len(coeffs) < 2:
        return []
    if bound is None:
        bound = 1 << 128
    bound = abs(int(bound))

    roots = []
    quick = min(bound, quick_limit)
    for x in range(-quick, quick + 1):
        if poly_eval(coeffs, x) == 0:
            roots.append(x)
    if quick >= bound:
        return roots[:max_roots]

    try:
        seq = [_int_poly(q) for q in _sturm_sequence(coeffs)]
    except Exception:
        return roots[:max_roots]
    if len(seq) < 2:
        return roots[:max_roots]

    def isolate(seq_, lo_, hi_):
        out = []
        try:
            c_lo = _sign_changes(seq_, lo_)
            c_hi = _sign_changes(seq_, hi_)
        except Exception:
            return out
        total = abs(c_hi - c_lo)
        if total == 0:
            return out
        st = [(lo_, hi_, total)]
        guard = 0
        while st and guard < 4000:
            guard += 1
            a, b, c = st.pop()
            if c <= 0:
                continue
            if b - a <= 2:
                out.append((a, b))
                continue
            mid = (a + b) // 2
            if mid <= a or mid >= b:
                out.append((a, b))
                continue
            cm = _sign_changes(seq_, mid)
            ca = _sign_changes(seq_, a)
            cb = _sign_changes(seq_, b)
            st.append((a, mid, abs(ca - cm)))
            st.append((mid, b, abs(cm - cb)))
        return out

    cands = []
    for (a, b) in isolate(seq, quick, bound):
        cands += [a, a + 1, b, b - 1, (a + b) // 2]
    try:
        neg = [c * ((-1) ** i) for i, c in enumerate(coeffs)]
        seqn = [_int_poly(q) for q in _sturm_sequence(neg)]
        for (a, b) in isolate(seqn, quick, bound):
            for t in (a, a + 1, b, b - 1, (a + b) // 2):
                cands.append(-t)
    except Exception:
        pass
    for cand in cands:
        if abs(cand) <= bound and cand not in roots and poly_eval(coeffs, cand) == 0:
            roots.append(cand)
    return roots[:max_roots]


# ============================================================
# 5. LLL (Decimal 高精度增量版) + Coppersmith
# ============================================================

def lll_reduce(B, delta=0.99, max_dim=40):
    """LLL 约化, 输入行向量整数矩阵, 返回 Decimal 矩阵"""
    getcontext().prec = 90
    B = [[int(x) for x in row] for row in B]
    B = [r for r in B if any(x != 0 for x in r)]
    n = len(B)
    if n <= 1:
        return [[Decimal(x) for x in r] for r in B]
    m = len(B[0])
    dd = Decimal(str(delta))

    Bstar = [None] * n
    Bn = [Decimal(0)] * n
    mu = [[Decimal(0)] * n for _ in range(n)]

    def compute_row(i):
        v = [Decimal(x) for x in B[i]]
        for j in range(i):
            if Bn[j] == 0:
                mu[i][j] = Decimal(0)
                continue
            s = Decimal(0)
            bi = B[i]
            bj = Bstar[j]
            for t in range(m):
                if bi[t] and bj[t]:
                    s += Decimal(bi[t]) * bj[t]
            mu[i][j] = s / Bn[j]
            mij = mu[i][j]
            if mij != 0:
                for t in range(m):
                    if bj[t]:
                        v[t] -= mij * bj[t]
        Bstar[i] = v
        Bn[i] = sum((x * x for x in v), Decimal(0))

    for i in range(n):
        compute_row(i)

    k = 1
    it = 0
    max_it = 4000
    while k < n and it < max_it:
        it += 1
        for j in range(k - 1, -1, -1):
            if abs(mu[k][j]) > Decimal("0.5"):
                q = int(mu[k][j].to_integral_value(rounding="ROUND_HALF_EVEN"))
                if q:
                    for t in range(m):
                        B[k][t] -= q * B[j][t]
                    compute_row(k)
        if Bn[k] >= (dd - mu[k][k - 1] * mu[k][k - 1]) * Bn[k - 1]:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            for i in range(k - 1, n):
                compute_row(i)
            k = max(k - 1, 1)
    return [[Decimal(x) for x in r] for r in B]


def coppersmith_univariate(f_coeffs, N, beta=1.0, X=None, mm=None, tt=None,
                           max_dim=16, time_budget=25.0):
    """
    单变量 Coppersmith: 求 f(x) ≡ 0 (mod b) 的小根, b | N, b >= N^beta
    返回 roots 列表
    """
    t_start = time.time()
    f_coeffs = [int(c) for c in f_coeffs]
    poly_trim(f_coeffs)
    dd = len(f_coeffs) - 1
    if dd < 1:
        return []

    if X is None:
        X = 1 << max(8, int(N.bit_length() * beta / dd) - 1)
    X = int(X)

    def build(mm_, tt_):
        rows = []
        for i in range(mm_):
            fi = poly_pow(f_coeffs, i)
            base = pow(N, mm_ - i)
            for j in range(dd):
                row = [0] * (j + len(fi))
                for kk, c in enumerate(fi):
                    row[j + kk] = c * base
                rows.append(row)
        fm = poly_pow(f_coeffs, mm_)
        for i in range(tt_):
            row = [0] * (i + len(fm))
            for kk, c in enumerate(fm):
                row[i + kk] = c
            rows.append(row)
        width = max(len(r) for r in rows)
        for r in rows:
            r.extend([0] * (width - len(r)))
        return [[r[j] * pow(X, j) for j in range(width)] for r in rows]

    combos = []
    if mm and tt:
        combos = [(mm, tt)]
    else:
        seen = set()
        # 按 m 递增, t 取理论值 t = dd*m*(1/beta - 1)
        for mm_ in range(2, 11):
            base_t = int(round(dd * mm_ * (1.0 / beta - 1.0))) if beta < 1 else 1
            cand = [max(1, base_t), max(1, base_t - 1), max(1, base_t + 1)]
            for tt_ in cand:
                dim = dd * mm_ + tt_
                if dim <= max_dim and (mm_, tt_) not in seen:
                    seen.add((mm_, tt_))
                    combos.append((mm_, tt_))
        combos.sort(key=lambda pr: pr[0] * dd + pr[1])
        # 保证每组 m 的大 t 优先于更小 m 的变体
        combos.sort(key=lambda pr: (pr[0], -pr[1]))

    for (mm_, tt_) in combos:
        if time.time() - t_start > time_budget:
            break
        try:
            rows = build(mm_, tt_)
            red = lll_reduce(rows)
        except Exception:
            continue
        for row in red[:5]:
            coeffs = []
            ok = True
            for j, v in enumerate(row):
                iv = int(v)
                if Decimal(iv) != v:
                    ok = False
                    break
                xj = pow(X, j)
                if iv % xj:
                    ok = False
                    break
                coeffs.append(iv // xj)
            if not ok:
                continue
            poly_trim(coeffs)
            if len(coeffs) < 2:
                continue
            for r0 in poly_int_roots(coeffs, bound=X):
                val = poly_eval(f_coeffs, r0)
                if val == 0 or (N % max(1, math.gcd(val, N)) == 0 and math.gcd(val, N) > 1):
                    return [r0]
    return []


# ============================================================
# 6. 模素数 n 次开根
# ============================================================

def _small_factorize(n, bound=1 << 22):
    fs = {}
    for p in _SMALL_PRIMES:
        if p * p > n or p > bound:
            break
        while n % p == 0:
            fs[p] = fs.get(p, 0) + 1
            n //= p
    if n > 1:
        fs[n] = fs.get(n, 0) + 1
    return fs


def tonelli_shanks(n, p):
    n %= p
    if n == 0:
        return 0
    if p == 2:
        return n
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    mm, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
            if i > mm:
                return None
        b = pow(c, 1 << (mm - i - 1), p)
        mm, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def nth_root_mod_prime_all(r, e, p, limit=1 << 20):
    """求 x^e ≡ r (mod p) 的所有解 (p 素数)"""
    r %= p
    if r == 0:
        return [0]
    if e == 1:
        return [r]
    fs = _small_factorize(e)
    if any(not is_prime(k) for k in fs):
        # e 里剩下的部分不是素数(如两个大素数之积): 先拆开, 拆不动就放弃
        fs2, ok = {}, True
        for k, cnt in fs.items():
            if is_prime(k):
                fs2[k] = cnt
                continue
            sub = factor_int(k, effort=1)
            if not sub:
                ok = False
                break
            for sp in sub:
                fs2[sp] = fs2.get(sp, 0) + 1
        if not ok:
            return []
        fs = fs2
    if len(fs) > 1:
        ks = sorted(fs)
        first = ks[0] ** fs[ks[0]]
        rest = e // first
        out = []
        for y in nth_root_mod_prime_all(r, rest, p, limit):
            out.extend(nth_root_mod_prime_all(y, first, p, limit))
        return sorted(set(out))
    q, ee = list(fs)[0], list(fs.values())[0]
    return _prime_root_all(r, q, ee, p, limit)


def _prime_root_all(r, q, ee, p, limit=1 << 20):
    """解 x^(q^ee) ≡ r (mod p)，q 为素数，返回全部根"""
    r %= p
    if r == 0:
        return [0]
    if ee <= 0:
        return [r]
    n = q ** ee
    if (p - 1) % q != 0:
        try:
            d = modinv(n, p - 1)
        except ValueError:
            return []
        x = pow(r, d, p)
        return [x] if pow(x, n, p) == r else []

    t, s = 0, p - 1
    while s % q == 0:
        s //= q
        t += 1
    if pow(r, (p - 1) // q, p) != 1:
        return []
    if ee > t:
        # v3.6 修复: ee > t 时旧版直接 return []（例: e=9 而 p-1 只含 3^1），
        # 实际根数 = gcd(q^ee, p-1) = q^t，是有解的。降幂递归:
        #   x^(q^ee) = r  <=>  (x^(q^(ee-t)))^(q^t) = r
        out = []
        for y in _prime_root_all(r, q, t, p, limit):
            out.extend(_prime_root_all(y, q, ee - t, p, limit))
        return sorted({x % p for x in out if pow(x, n, p) == r})

    z = None
    for a in range(2, 500):
        if pow(a, (p - 1) // q, p) != 1:
            z = a
            break
    if z is None:
        return []
    rho = pow(z, s, p)
    if q == 2:
        # v3.5 修复: e = 2^ee 时开 ee 次平方根; 旧版只开一次就当成解(错),
        # gcd(e,p-1)=2 的题(如 De1CTF 末段)因此永远返回空 -> 报"分解跑不动"
        cur = [r]
        for _ in range(ee):
            nxt = []
            for v in cur:
                sv = tonelli_shanks(v, p)
                if sv is None:
                    continue
                nxt.extend((sv, (-sv) % p))
            cur = nxt
            if not cur:
                return []
        return sorted({x % p for x in cur if pow(x, n, p) == r})
    else:
        if q ** t > limit:
            return []
        d = modinv(q, s)
        x0 = pow(r, d, p)
        delta = pow(x0, q, p) * modinv(r, p) % p
        # 需要 alpha^q = delta^-1
        delta_inv = modinv(delta, p) if delta % p else 0
        alpha = None
        cur = 1
        for _ in range(q ** t):
            if pow(cur, q, p) == delta_inv:
                alpha = cur
                break
            cur = cur * rho % p
        if alpha is None:
            return []
        base = x0 * alpha % p
        if pow(base, q, p) != r:
            return []
    roots = [base]
    w = pow(rho, q ** (t - ee), p) if t >= ee else 1
    cur = 1
    for _ in range(q ** ee):
        cur = cur * w % p
        roots.append(base * cur % p)
    return sorted(set(roots))

# ============================================================
# 7. 结果与格式
# ============================================================

class Result(object):
    def __init__(self, ok, m=None, name="", detail="", extra=None, cands=None):
        self.ok = ok
        self.m = m
        self.name = name
        self.detail = detail
        self.extra = extra or {}
        self.cands = cands or []

    def __repr__(self):
        return "<Result %s ok=%s>" % (self.name, self.ok)


PRINTABLE = set(range(0x20, 0x7f)) | {0x09, 0x0a, 0x0d}


def int_to_bytes(x):
    if x is None:
        return b""
    if x < 0:
        return b""
    if x == 0:
        return b"\x00"
    return x.to_bytes((x.bit_length() + 7) // 8, "big")


def bytes_to_int(b):
    return int.from_bytes(b, "big")


def score_bytes(b):
    """给一段 bytes 打分, 越高越像真明文"""
    if not b:
        return 0
    score = 0
    printable = sum(1 for c in b if c in PRINTABLE)
    score += printable * 10 // len(b)
    if re.search(rb"[A-Za-z0-9_]{2,24}\{[^}\r\n]{2,300}\}", b):
        score += 200
    if b.startswith(b"flag") or b"flag{" in b:
        score += 150
    if not any(c < 0x09 for c in b):
        score += 30
    return score


def pick_flag(cands):
    """从候选 m 里挑最像明文的"""
    best = None
    best_score = -1
    for m in cands:
        b = int_to_bytes(m)
        s = score_bytes(b)
        if s > best_score:
            best_score = s
            best = m
    return best, best_score


# ============================================================
# 8. 通用解密工具
# ============================================================

def phi_from_factors(factors):
    phi = 1
    for p, cnt in _count(factors).items():
        phi *= (p - 1) * pow(p, cnt - 1)
    return phi


def decrypt_standard(n, e, c, factors):
    """标准 RSA 解密 (e 与 phi 互素)"""
    phi = phi_from_factors(factors)
    try:
        d = modinv(e, phi)
    except ValueError:
        return None
    return pow(c, d, n), {"d": d, "phi": phi}


def decrypt_general(n, e, c, factors, max_cands=20000):
    """
    通用解密: e 与 phi 可能不互素
    返回候选明文列表
    """
    fdict = _count(factors)
    # v3.5 修复: 原来是拿"所有素数的 gcd"整体判断能不能求逆 —— 只要有一个素数
    # 的 (p-1) 和 e 不互素（如 q-1 被 65537 整除），整题就被判成"不能求逆"直接返回空。
    # 正确做法是逐素数判断: 每个都互素才能走标准解密，否则逐素数开 e 次根再 CRT。
    if all(math.gcd(e, (p - 1) * pow(p, cnt - 1)) == 1 for p, cnt in fdict.items()):
        r = decrypt_standard(n, e, c, factors)
        return [r[0]] if r else []

    # e 与 phi 不互素: 分素数幂求 e 次根 + CRT
    per_prime = []
    moduli = []
    for p, cnt in fdict.items():
        pk = pow(p, cnt)
        moduli.append(pk)
        cp = c % pk
        if cnt > 1:
            # 只处理 p^1 的简单情况, 高阶用 Hensel 简化
            sols = _roots_mod_prime_power(cp, e, p, cnt)
        else:
            sols = nth_root_mod_prime_all(cp, e, p)
        if not sols:
            return []
        per_prime.append(sols)

    # CRT 组合
    cands = [0]
    cur_mod = 1
    for mod, sols in zip(moduli, per_prime):
        new = []
        for base in cands:
            for s in sols:
                # 解 x ≡ base (mod cur_mod), x ≡ s (mod mod)
                try:
                    inv = modinv(cur_mod % mod, mod)
                except ValueError:
                    continue
                t = ((s - base) % mod) * inv % mod
                new.append(base + cur_mod * t)
                if len(new) > max_cands:
                    break
            if len(new) > max_cands:
                break
        cands = new
        cur_mod *= mod
        if len(cands) > max_cands:
            break
    return cands


def _roots_mod_prime_power(c, e, p, k):
    """解 x^e ≡ c mod p^k (Hensel 提升, 简化版)"""
    sols = nth_root_mod_prime_all(c % p, e, p)
    if not sols:
        return []
    pk = p
    cur = [s % p for s in sols]
    for _ in range(k - 1):
        pk *= p
        nxt = []
        for x in cur:
            fx = (pow(x, e, pk) - c) % pk
            # 在 x + t*p 里搜索
            for t in range(p):
                if p > 1000 and t > 1000:
                    break
                xx = x + t * pk // p
                if (pow(xx, e, pk) - c) % pk == 0:
                    nxt.append(xx)
        cur = nxt
        if not cur:
            return []
    return cur


def crt_pair(a1, m1, a2, m2):
    g, x, _ = egcd(m1, m2)
    if (a2 - a1) % g:
        return None, None
    lcm = m1 // g * m2
    t = ((a2 - a1) // g * x) % (m2 // g)
    return (a1 + m1 * t) % lcm, lcm


# ============================================================
# 9. 攻击模块
# ============================================================

ATTACKS = []


def attack(name, desc):
    def deco(fn):
        ATTACKS.append({"name": name, "desc": desc, "fn": fn})
        return fn
    return deco


def _ctx(ctx, key):
    v = ctx.get(key)
    return v


# ---------- A. 直接密钥 ----------

def recover_n_from_d(d, e, window=8):
    """题目只给 d、连 n 都没打印时，靠 p、q 挨着把 n 反推出来。

    原理：
        e·d - 1 = k·φ(n)，0 < k < e
        φ = (p-1)(q-1) = n - (p+q) + 1
        令 t = p+q-2、Δ = |p-q|，则   t² - 4φ = Δ²
    p、q 挨着（q = nextPrime(p) 这类题）时 Δ 很小，t 就贴在 isqrt(4φ) 附近，
    于是不用扫除数，每个 k 只试几格就能定死。
    """
    K = e * d - 1
    lim = e if e <= (1 << 20) else (1 << 20)
    out = []
    for k in range(1, lim):
        if K % k:
            continue
        phi = K // k
        if phi % 4:                      # p-1、q-1 都是偶数 → φ 必被 4 整除
            continue
        t0 = math.isqrt(4 * phi)
        for t in range(t0 - window, t0 + window + 2):
            if t < 4:
                continue
            dd = t * t - 4 * phi
            if dd < 0:
                continue
            D = math.isqrt(dd)
            if D * D != dd or (t + D) % 2:
                continue
            p = (t + D) // 2 + 1
            q = (t - D) // 2 + 1
            if p < 3 or q < 3:
                continue
            if p * q != phi + (p + q) - 1:   # n = φ + (p+q) - 1
                continue
            if (e * d) % phi != 1:
                continue
            out.append((k, phi, p, q))
    seen, good = set(), []
    for k, phi, p, q in out:
        key = (p, q) if p <= q else (q, p)
        if key in seen:
            continue
        seen.add(key)
        good.append((k, phi, p, q))
    return good


@attack("只给 d、没给 n（p、q 挨着 / nextPrime 型）",
        "e·d-1 = k·φ（k<e）；p、q 相邻时 (p+q-2)² - 4φ = (p-q)² 是小平方，"
        "从 √(4φ) 附近试几格即可还原 n、p、q")
def a_d_without_n(ctx):
    d, e, n = ctx.get("d"), ctx.get("e"), ctx.get("n")
    c = ctx.get("c")
    if not d or not e or n or c is None:
        return None
    if ctx.get("factors") or ctx.get("phi") or ctx.get("p"):
        return None
    cands = recover_n_from_d(d, e)
    if not cands:
        return None
    # 素数校验最贵，放最后；有素数对就只用素数对
    prime_c = [t for t in cands if is_prime(t[2]) and is_prime(t[3])]
    use = prime_c or cands
    best = None
    for k, phi, p, q in use:
        nn = p * q
        try:
            m = pow(c, d, nn)
        except Exception:
            continue
        sc = score_bytes(int_to_bytes(m))
        if best is None or sc > best[0]:
            best = (sc, k, phi, p, q, nn, m)
    if best is None:
        return None
    sc, k, phi, p, q, nn, m = best
    ctx["n"], ctx["p"], ctx["q"] = nn, p, q
    ctx["factors"] = [p, q]
    ctx["phi"] = phi
    detail = ("e·d−1 = k·φ 反推（k=%d）：t² − 4φ = (p−q)² 解出 p、q，再回推 n = p·q" % k)
    cands_m = []
    for k2, phi2, p2, q2 in use:
        try:
            cands_m.append(pow(c, d, p2 * q2))
        except Exception:
            pass
    return Result(True, m, "只给 d、没给 n（p、q 挨着）", detail,
                  {"n": nn, "p": p, "q": q, "d": d, "k": k,
                   "p-q": abs(p - q)}, cands=cands_m)


@attack("已知私钥 d", "题目直接给了 d，pow(c,d,n) 即可")
def a_direct_d(ctx):
    n, e, c, d = ctx.get("n"), ctx.get("e"), ctx.get("c"), ctx.get("d")
    if not (n and c is not None and d):
        return None
    m = pow(c, d, n)
    extra = {}
    # 顺便暴露 p,q
    pq = factor_with_d(n, e, d)
    if pq:
        extra["p"], extra["q"] = pq
    return Result(True, m, "已知私钥 d", "m = c^d mod n", extra)


@attack("p±q 两个未命名大数（无 n）",
        "题面只甩出两个大整数、没给 n：逐对当 p+q / p−q 联立，素数校验 + 解密回代确认")
def a_pq_pair(ctx):
    e, c = ctx.get("e"), ctx.get("c")
    if not (e and c is not None):
        return None
    if ctx.get("factors"):
        return None
    spare = [v for v in (ctx.get("spare_ints") or []) if isinstance(v, int) and v > 1]
    if len(spare) < 2:
        return None
    vals = sorted(set(spare), reverse=True)[:6]
    for i, S in enumerate(vals):
        for j, T in enumerate(vals):
            if i == j or S <= T:
                continue
            if (S + T) % 2 or (S - T) % 2:
                continue
            p, q = (S + T) // 2, (S - T) // 2
            if p <= 1 or q <= 1 or p == q:
                continue
            if not (is_prime(p) and is_prime(q)):
                continue
            n = p * q
            m, info = decrypt_standard(n, e, c, [p, q])
            if m is None:
                cands = decrypt_general(n, e, c, [p, q])
                m = cands[0] if cands else None
                info = {}
            if m is None or pow(m, e, n) != c or not int_to_bytes(m):
                continue
            ctx["p"], ctx["q"], ctx["n"] = p, q, n
            ctx["factors"] = [p, q]
            ctx["leak_pq_kind"] = ("题面两个大整数其实就是 p+q 和 p−q："
                                   "p=(S+T)/2、q=(S−T)/2（两边都是素数），n=p·q 回推")
            return Result(True, m, "p±q 两个未命名大数（无 n）",
                          "两个大整数当 p+q / p−q 联立 → p、q 均通过素性校验 + 解密回代 "
                          "pow(m,e,n)==c 确认", {"p": p, "q": q, "d": info.get("d")})
    return None


@attack("已知 p±q 关系（和 / 差 / 平方差 / 平方和）",
        "题面给 p+q、p−q、p²−q²、p²+q² 这类关系，联立 n 反解 p、q 后常规解密")
def a_pq_relation(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    kind = ctx.get("leak_pq_kind")
    if not (n and e and c is not None and kind):
        return None
    fs = ctx.get("factors") or []
    if len(fs) < 2:
        return None
    p, q = fs[0], fs[1]
    if p * q != n:
        return None
    m, info = decrypt_standard(n, e, c, [p, q])
    if m is None:
        info = {}
        # e 与 φ 不互素时退回通用解密
        cands = decrypt_general(n, e, c, [p, q])
        m = cands[0] if cands else None
        if m is None:
            return None
    if pow(m, e, n) != c:
        return None
    return Result(True, m, "已知 p±q 关系", kind, {"p": p, "q": q, "d": info.get("d")})


@attack("已知 p、q", "有素因子直接算 phi 解密")
def a_pq(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    fs = ctx.get("factors")
    if not fs:
        return None
    if len(fs) < 2 and not (is_prime(fs[0]) and fs[0] < n):
        return None
    m, info = decrypt_standard(n, e, c, fs)
    if m is None:
        return None
    return Result(True, m, "已知素因子", "phi = ∏(p-1)·p^(k-1)，d = e⁻¹ mod phi", info)


@attack("已知 phi", "给了 phi 直接求 d")
def a_phi(ctx):
    n, e, c, phi = ctx.get("n"), ctx.get("e"), ctx.get("c"), ctx.get("phi")
    if not (n and e and c is not None and phi):
        return None
    try:
        d = modinv(e, phi)
    except ValueError:
        return None
    return Result(True, pow(c, d, n), "已知 phi", "d = e⁻¹ mod phi", {"d": d, "phi": phi})


def factor_from_multiple(n, M, bases=(2, 3, 5, 7, 11, 13, 17, 19)):
    """已知 λ(n) 或 φ(n) 的倍数 M，用 Miller-Rabin 见证提取法劈开 n。

    原理: λ(n) | M，所以对任意 a 有 a^M ≡ 1 (mod n)。把 M 写成 2^s·d，
    沿 a^d, a^2d, a^4d … 往上平方，一旦出现 x² ≡ 1 且 x ≢ ±1，gcd(x−1, n) 就是因子。
    """
    if not (n and isinstance(M, int) and M > 1):
        return None
    d, s = M, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
        g = math.gcd(a, n)
        if 1 < g < n:
            return g, n // g
        if g == n:
            continue
        try:
            x = pow(a, d, n)
        except Exception:
            continue
        if x in (0, 1):
            continue
        for _ in range(s):
            y = x * x % n
            if y == 1:
                g = math.gcd(x - 1, n)
                if 1 < g < n:
                    return g, n // g
                break
            x = y
        if x != 1:
            g = math.gcd(x - 1, n)
            if 1 < g < n:
                return g, n // g
    return None


@attack("泄露 φ/λ 的倍数（lcm 型）", "给了 lcm(p−1,q−1) 或 φ 的倍数，见证提取法劈开 n 再常规解密")
def a_phi_multiple(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and c is not None):
        return None
    if ctx.get("factors") and math.prod(ctx["factors"]) == n:
        return None
    cands, seen = [], set()

    def _add(tag, v):
        if not isinstance(v, int) or isinstance(v, bool) or v <= 1 or v in seen:
            return
        seen.add(v)
        cands.append((tag, v))

    for key in ("lcm", "lam", "lambda", "phi_multiple", "phimul", "euler_multiple",
                "lambda_n", "car"):
        _add(key, ctx.get(key))
    lim = math.isqrt(n)
    for v in (ctx.get("leak_vals") or []):
        if isinstance(v, int) and v > lim:
            _add("题面泄露值", v)
    if not cands:
        return None
    # 大一点的先试(倍数越大越可能是 lcm/φ 本身)
    cands.sort(key=lambda kv: -kv[1])
    nb = n.bit_length()
    for tag, M in cands[:16]:
        # λ(n) 的合理解释: 不超过 n 的 4 倍。大出好几个数量级的肯定不是, 别浪费模幂
        if isinstance(M, int) and M.bit_length() > nb + 2:
            continue
        pq = factor_from_multiple(n, M)
        if not pq:
            continue
        p, q = pq
        m, info = decrypt_standard(n, e, c, [p, q])
        if m is None:
            m, info = decrypt_general(n, e, c, [p, q])
        if m is None:
            continue
        if n.bit_length() >= 1000 and _looks_garbage(m):
            continue
        if e and pow(m, e, n) != c:
            # 解出来的明文重新加密对不上密文 → 这个"倍数"是假线索，别当命中
            continue
        return Result(True, m, "泄露 φ/λ 的倍数（lcm 型）",
                      "%s 是 λ(n) 的倍数 → 见证提取法劈开 n（%d bit / %d bit）→ 常规解密"
                      % (tag, p.bit_length(), q.bit_length()),
                      {"p": p, "q": q, "d": info.get("d")})
    return None


@attack("素因子偏移泄露 (p±a)(q±a)", "给了 (p-2)(q-2) 这类式子，先还原 p+q 再解二次方程")
def a_phi_shift(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    leak = ctx.get("phishift")
    if not (n and e and c is not None and leak):
        return None
    a, L = leak
    if a == 0:
        return None
    num = n + a * a - L
    if num % a:
        return None
    s = num // a
    disc = s * s - 4 * n
    if disc < 0:
        return None
    t = math.isqrt(disc)
    if t * t != disc:
        return None
    p = (s + t) // 2
    q = (s - t) // 2
    if p * q != n or q <= 1:
        return None
    m, info = decrypt_standard(n, e, c, [p, q])
    if m is None:
        return None
    return Result(True, m, "素因子偏移泄露",
                  "(p%+d)(q%+d) = n - a(p+q) + a² → 还原 p+q → 解二次方程拿到 p、q" % (-a, -a),
                  {"p": p, "q": q, "d": info.get("d")})


@attack("已知 dp、dq / CRT 参数", "用 CRT 解密，不需要 n 分解")
def a_dp_dq(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and c is not None):
        return None
    dp, dq, p, q = ctx.get("dp"), ctx.get("dq"), ctx.get("p"), ctx.get("q")
    if dp and dq and p and q:
        m1 = pow(c, dp, p)
        m2 = pow(c, dq, q)
        m, mod = crt_pair(m1, p, m2, q)
        if m is not None and mod == n:
            return Result(True, m, "已知 dp/dq", "CRT: m = c^dp mod p ∩ c^dq mod q", {"p": p, "q": q})
    # 只有 dp: 反推 p
    if dp and p is None:
        p = factor_from_dp(n, e, dp)
        if p:
            q = n // p
            d = modinv(e, (p - 1) * (q - 1))
            return Result(True, pow(c, d, n), "已知 dp 泄露", "e·dp ≡ 1 mod (p-1) → 恢复 p", {"p": p, "q": q, "d": d})
    return None


def factor_from_dp(n, e, dp):
    """由 dp 恢复 p: gcd(a^(e·dp) - a, n)"""
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        try:
            g = math.gcd(pow(a, e * dp, n) - a, n)
        except Exception:
            continue
        if 1 < g < n:
            return g
    return None


def factor_with_d(n, e, d):
    """由 d 分解 n (标准算法)"""
    k = e * d - 1
    if k <= 0 or k % 2:
        return None
    t = k
    while t % 2 == 0:
        t //= 2
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        x = pow(a, t, n)
        if x in (1, n - 1):
            continue
        for _ in range(64):
            y = x * x % n
            if y == 1:
                g = math.gcd(x - 1, n)
                if 1 < g < n:
                    return g, n // g
                break
            if y == n - 1:
                break
            x = y
    return None


# ---------- B. 分解 n ----------

@attack("模下幂泄露 (P≡p^k mod n)",
        "题面给了 p、q 的幂取模 n 的结果（如 P=p² mod n / Q=q² mod n）："
        "p | P，所以 gcd(P, n) 直接把 n 劈成素数因子")
def a_mod_pow_leak(ctx):
    n, c = ctx.get("n"), ctx.get("c")
    if not n or c is None:
        return None
    if n.bit_length() < 200:
        return None
    vals = [v for v in (ctx.get("leak_vals") or []) if 1 < v < n]
    if not vals:
        return None
    parts = [n]
    for v in vals:
        nxt, split = [], False
        for m in parts:
            g = math.gcd(v, m)
            if 1 < g < m:
                nxt.extend([g, m // g])
                split = True
            else:
                nxt.append(m)
        parts = nxt
        # 不 break: 多个泄露值要依次把每块继续劈开（P 给 p, Q 给 q）
    if len(parts) < 2:
        return None
    factors = []
    for m in parts:
        if is_prime(m):
            factors.append(m)
        else:
            sub = factor_int(m, effort=2)
            if not sub or len(sub) < 2:
                return None
            factors.extend(sub)
    uniq = sorted(set(factors))
    if len(uniq) < 2:
        return None
    e = ctx.get("e") or 65537
    # 候选规模太大（多处 e | p-1，动辄上千万组）时别在这里硬啃，
    # 交给专门的多根/线性组合攻击，免得截断后挑出个错明文当答案
    total = 1
    for pr in uniq:
        total *= max(1, math.gcd(e, pr - 1))
        if total > 200000:
            return None
    try:
        cands = decrypt_general(n, e, c, factors, max_cands=150000)
    except Exception:
        return None
    if not cands:
        return None
    best, sc = pick_flag(cands)
    if best is None or _plaintext_ratio(best) < 0.85:
        return None
    return Result(True, best, "模下幂泄露 (P≡p^k mod n)",
                  "gcd(泄露值, n) 劈开 n → %d 个素因子 %s；e=%d，共 %d 个候选明文"
                  % (len(uniq), "/".join(str(x.bit_length()) + "bit" for x in uniq),
                     e, len(cands)),
                  cands=cands)


@attack("n 可分解", "试除 / 费马 / Pollard rho / p-1 / 公开分解库 自动分解 n")
def a_factor_n(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and c is not None):
        return None
    if ctx.get("factors"):
        return None
    bits = n.bit_length()
    if bits > 1400:
        # 大 n 不走 rho(白跑): 先费马(相邻素数), 再 p-1(光滑), 最后查公开分解库
        # v3.7: 超过 2048 bit 的 n 费马迭代和 p-1 都收着点, 这几步本来就没戏,
        #       白跑十几秒会拖垮整道题的体验
        fs = None
        r = fermat(n, max_iter=200000 if bits <= 2048 else 4000)
        if r:
            fs = [r[0], r[1]]
        if fs is None and bits <= 2048:
            g = pollard_pm1(n, bound=200000)
            if g:
                fs = [g, n // g]
        if fs is None:
            fs = factor_online(n)
        if fs is None:
            return None
    else:
        effort = 2 if bits <= 320 else 3
        fs = factor_int(n, effort=effort)
    if not fs or len(fs) < 2:
        return None
    if math.prod(fs) != n or not all(is_prime(f) for f in fs):
        return None
    ctx["factors"] = fs
    ctx["p"], ctx["q"] = fs[0], fs[-1]
    if not e:
        return None
    m, info = decrypt_standard(n, e, c, fs)
    if m is not None:
        if bits >= 1000 and _looks_garbage(m):
            ctx["__garbled"] = True      # e 多半用错了, 别当命中
            return None
        det = "n = " + " × ".join(str(x) for x in sorted(set(fs)))
        return Result(True, m, "n 可分解", det, info)
    return None


@attack("两段明文 (和 / 立方和)", "m1 = (F1+F2)^e, m2 = (F1³+F2³)^e: 分解 n 后解出两段明文再拼回")
def a_two_pieces(ctx):
    n, e = ctx.get("n"), ctx.get("e")
    m1, m2 = ctx.get("m1"), ctx.get("m2")
    if not (n and e and m1 and m2):
        return None
    if m1 >= n or m2 >= n:
        return None
    fs = ctx.get("factors")
    if not fs or math.prod(fs) != n:
        fs = None
        r = fermat(n, max_iter=300000)      # nextprime 型: p、q 相邻
        if r:
            fs = [r[0], r[1]]
        if fs is None and n.bit_length() <= 1400:
            fs = factor_int(n, effort=3)
        if fs is None:
            fs = factor_online(n)
        if not fs:
            return None
        ctx["factors"] = fs
    if len(fs) < 2 or math.prod(fs) != n or not all(is_prime(f) for f in fs):
        return None
    try:
        d = modinv(e, compute_phi_from_factors(fs))
    except ValueError:
        return None
    c1 = pow(m1, d, n)      # = F1 + F2
    c2 = pow(m2, d, n)      # = F1³ + F2³
    # F1·F2 = (c1³ - c2) / (3·c1)
    num, den = c1 ** 3 - c2, 3 * c1
    if not c1 or num % den:
        return None
    prod_ = num // den
    disc = c1 * c1 - 4 * prod_
    if disc < 0:
        return None
    s = math.isqrt(disc)
    if s * s != disc or (c1 + s) % 2:
        return None
    F1, F2 = (c1 + s) // 2, (c1 - s) // 2
    best = None
    for shift in range(8, 8 * 400, 8):
        lim = 1 << shift
        for x, y in ((F1, F2), (F2, F1)):
            if y >= lim or x <= 0:
                continue
            m = (x << shift) | y
            if m % n == 0:
                continue
            b = int_to_bytes(m)
            sc = score_bytes(b)
            if best is None or sc > best[0]:
                best = (sc, m, b)
    if best is None or best[0] < 100:
        return None
    det = ("F1+F2 = %d, F1³+F2³ = %d, n = %s" %
           (c1, c2, " × ".join(str(x) for x in sorted(set(fs)))))
    return Result(True, best[1], "两段明文 (和 / 立方和)", det,
                  {"d": d, "F1": F1, "F2": F2, "c1": c1, "c2": c2,
                   "plain": best[2]})


@attack("n 为素数", "n 本身是素数，phi = n - 1")
def a_n_prime(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    if n.bit_length() < 64 or not is_prime(n):
        return None
    phi = n - 1
    try:
        d = modinv(e, phi)
    except ValueError:
        return None
    return Result(True, pow(c, d, n), "n 为素数", "phi(n) = n - 1", {"d": d, "phi": phi})


@attack("n 为素数 · e 与 n−1 不互素", "模本身就是素数, gcd(e,p−1)>1: 列出全部 e 次根, 按可打印性挑")
def a_n_prime_noninv(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    if n.bit_length() < 64 or not is_prime(n):
        return None
    g = math.gcd(e, n - 1)
    if g == 1:
        return None
    roots = nth_root_mod_prime_all(c % n, e, n)
    if not roots:
        return None
    best, sc = pick_flag(roots)
    if best is None:
        return None
    return Result(True, best, "n 为素数 · e 与 n−1 不互素",
                  "gcd(e, n−1) = %d，共 %d 个 e 次根，取最可读的一个" % (g, len(roots)),
                  cands=roots)


@attack("n 为素数幂", "n = p^k，直接开方分解")
def a_prime_power(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    for k in range(2, 8):
        r, exact = iroot(n, k)
        if exact and is_prime(r):
            factors = [r] * k
            m, info = decrypt_standard(n, e, c, factors)
            if m is not None:
                return Result(True, m, "n 为素数幂", "n = %d^%d" % (r, k), info)
    return None


@attack("多素数 RSA", "n = p·q·r…，分解后按通用公式解密")
def a_multi_prime(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    fs = ctx.get("factors")
    if not fs or len(set(fs)) < 3:
        return None
    m, info = decrypt_standard(n, e, c, fs)
    if m is None:
        return None
    return Result(True, m, "多素数 RSA", "%d 个素因子" % len(set(fs)), info)


# ---------- C. 小 e ----------

@attack("低加密指数 · 小明文", "m^e < n，密文直接开方")
def a_small_e_root(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e and c is not None):
        return None
    if e > 64:
        return None
    if c >= n:
        return None
    r, exact = iroot(c, e)
    if exact:
        return Result(True, r, "低加密指数 · 小明文", "m^e = c < n，直接开 %d 次方" % e)
    # 尝试 c + k·n
    for k in range(1, 30000):
        r, exact = iroot(c + k * n, e)
        if exact:
            return Result(True, r, "低加密指数 · 小明文",
                          "m^%d = c + %d·n，直接开方" % (e, k), {"k": k})
    return None


@attack("低加密指数 · 多组广播 (Håstad)", "同一明文用不同模数、相同小 e 加密，CRT 后开方")
def a_hastad(ctx):
    ns = ctx.get("ns") or []
    cs = ctx.get("cs") or []
    es = ctx.get("es") or []
    if len(ns) < 2 or len(cs) < 2 or len(ns) != len(cs):
        return None
    if len(set(es)) > 1:
        return None
    if len(set(ns)) < len(ns):
        return None
    # 指数候选: 题目明写的小 e 优先, 没写/写了默认 65537 时再自动试常见小指数
    cands = []
    if es:
        cands.append(es[0])
    e0 = ctx.get("e")
    if e0 and e0 <= 64 and e0 not in cands:
        cands.append(e0)
    if not es:
        for ce in (3, 5, 7, 11, 13, 17):
            if ce not in cands:
                cands.append(ce)
    # CRT 只需要算一次
    x, mod = 0, 1
    for ni, ci in zip(ns, cs):
        if math.gcd(mod, ni) != 1:
            return None
        x, mod = crt_pair(x, mod, ci % ni, ni)
        if x is None:
            return None
    for e in cands:
        if not e or e > 64:
            continue
        r, exact = iroot(x, e)
        if exact:
            return Result(True, r, "低加密指数 · 多组广播",
                          "CRT 组合 %d 组密文后开 %d 次方" % (len(ns), e), {"e": e})
    return None


def _common_modulus_recover(n, e1, e2, c1, c2, k_max=20000):
    """共模攻击通用版：gcd=1 直接还原 m；gcd=g>1 先得 m^g 再对 c+k·n 试 g 次开方"""
    g, s1, s2 = egcd(e1, e2)
    if g <= 0:
        return None, None
    try:
        if s1 < 0:
            c1 = modinv(c1, n)
            s1 = -s1
        if s2 < 0:
            c2 = modinv(c2, n)
            s2 = -s2
    except ValueError:
        return None, None
    base = pow(c1, s1, n) * pow(c2, s2, n) % n
    if g == 1:
        return base, {"e1": e1, "e2": e2, "g": 1, "k": 0}
    for k in range(0, k_max):
        r, exact = iroot(base + k * n, g)
        if exact and r > 0:
            return r, {"e1": e1, "e2": e2, "g": g, "k": k}
    return None, None


@attack("共模攻击", "同一 n，不同 e 加密同一明文；gcd(e1,e2)=g 时先取 m^g 再开 g 次方")
def a_common_modulus(ctx):
    n = ctx.get("n")
    es = ctx.get("es") or []
    cs = ctx.get("cs") or []
    if not n or len(es) < 2 or len(cs) < 2:
        return None
    for i in range(len(es)):
        for j in range(i + 1, len(es)):
            e1, e2 = es[i], es[j]
            c1, c2 = cs[i], cs[j]
            m, info = _common_modulus_recover(n, e1, e2, c1, c2)
            if m is None:
                continue
            if info.get("g") == 1:
                return Result(True, m, "共模攻击",
                              "e1·s1 + e2·s2 = 1 → m = c1^s1 · c2^s2 mod n",
                              {"e1": e1, "e2": e2})
            if n.bit_length() >= 1000 and _looks_garbage(m):
                continue
            return Result(True, m, "共模攻击",
                          "gcd(e1,e2)=%d → 先恢复 m^%d，再对 c+%d·n 开 %d 次方"
                          % (info["g"], info["g"], info["k"], info["g"]),
                          {"e1": e1, "e2": e2, "g": info["g"]})
    return None


@attack("共模 · e1·e2 = 常数", "只给了 e1·e2 的乘积（e1、e2 未知）：枚举约数对 → 共模攻击 → 开 g 次方")
def a_e_product(ctx):
    n = ctx.get("n")
    cs = ctx.get("cs") or []
    prod = ctx.get("e_product")
    if not n or len(cs) < 2 or not prod:
        return None
    c1, c2 = cs[0], cs[1]
    pairs = []
    for d in range(1, math.isqrt(prod) + 1):
        if prod % d:
            continue
        for e1, e2 in ((d, prod // d), (prod // d, d)):
            if e1 > 1 and e2 > 1:
                pairs.append((e1, e2))
    pairs.sort(key=lambda p: abs(p[0] - p[1]))
    # 先小 k 扫一遍所有约数对, 都没中再放开 k —— 免得一对一对地白跑两万次开方
    hits = []
    for k_lim in (256, 20000):
        for e1, e2 in pairs:
            m, info = _common_modulus_recover(n, e1, e2, c1, c2, k_max=k_lim)
            if m is not None:
                hits.append((e1, e2, m, info))
                break
        if hits:
            break
    for e1, e2, m, info in hits:
        if m is None:
            continue
        if n.bit_length() >= 1000 and _looks_garbage(m):
            continue
        if not int_to_bytes(m):
            continue
        return Result(True, m, "共模 · e1·e2 = 常数",
                      "e1·e2 = %d → 枚举出 e1=%d, e2=%d（gcd=%d），共模攻击得 m^%d 后 k=%d 处开方命中"
                      % (prod, e1, e2, info["g"], info["g"], info["k"]),
                      {"e1": e1, "e2": e2, "g": info["g"]})
    return None


_FLAG_TOKEN = re.compile(rb"[A-Za-z0-9_]{2,24}\{[\x20-\x7e]{1,300}\}")


def _pick_flag_token(b):
    """从字节串里抠出完整 flag（含闭合花括号），没有返回 None"""
    if not b:
        return None
    m = _FLAG_TOKEN.search(b)
    return m.group(0) if m else None


def _text_like(b):
    """一段 bytes 看起来像不像人写的文本（中文题面的前缀也算）"""
    if not b or len(b) < 2 or len(b) > 8192:
        return False
    try:
        s = b.decode("utf-8")
    except UnicodeDecodeError:
        return _flag_like(b)
    return all(ch.isprintable() or ch in "\n\r\t" for ch in s)


def _stitch_segments(segs):
    """多段明文拼回完整明文。

    "多组模数共享素因子 / 分段加密" 的题会把一个明文切成几段分别加密，
    每段前面还套一句废话（"the front part is :xxx"）。先直接拼一次；不中，
    再按“统一分隔符”把每段的废话切掉后拼 —— 各段是同一种题面结构，
    必须用同一个切点，才拼得回原文。

    返回 (完整 flag 或 None, 拼接方式说明)
    """
    segs = [s for s in segs if s]
    if not segs:
        return None, ""
    if len(segs) == 1:
        return _pick_flag_token(segs[0]), "单段"
    # 每段各自都是一个完整 flag → 这是多组独立题，不是分段加密，不做拼接
    if sum(1 for s in segs if _pick_flag_token(s)) >= 2:
        return None, ""
    # 先试"统一分隔符切掉废话"：分段题的每段通常套着同一句格式
    # （"... the front part is :xxx"），必须先把废话切掉再拼，
    # 否则直接拼接会让 flag 正则把中间的废话整段吞进去。
    for sep in (b":", b"\xef\xbc\x9a", b"\n", b"\r\n", b"is :", b"part is", b"="):
        parts, ok = [], True
        for s in segs:
            i = s.rfind(sep)
            if i < 0:
                ok = False
                break
            parts.append(s[i + len(sep):].strip())
        if not ok:
            continue
        if len(b"".join(parts)) >= 0.75 * len(b"".join(segs)):
            continue            # 切了跟没切一样, 说明不是"废话+片段"结构
        hit = _pick_flag_token(b"".join(parts))
        if hit:
            _sep_txt = {"\xef\xbc\x9a": "全角冒号", "\n": "换行", "\r\n": "换行"}.get(
                sep.decode("latin-1"), sep.decode("latin-1"))
            return hit, "各段按%s切掉前缀后拼接" % _sep_txt
    # 兜底: 各段本身就是纯碎片, 直接拼
    hit = _pick_flag_token(b"".join(segs))
    if hit:
        return hit, "各段直接拼接"
    return None, ""


@attack("模不互素", "多组模数共享素因子，gcd 直接分解（含链式 n1=pq/n2=qr/n3=rs 全解 + 分段明文拼接）")
def a_shared_prime(ctx):
    ns = ctx.get("ns") or []
    cs = ctx.get("cs") or []
    es = ctx.get("es") or []
    c = ctx.get("c")
    e = ctx.get("e")
    if len(ns) < 2 or not (e or es):
        return None

    # ---------- 链式分解: 每个模数都靠共享素因子刨干净, 再各自解密 ----------
    seeds = {i: set() for i in range(len(ns))}
    for i in range(len(ns)):
        for j in range(i + 1, len(ns)):
            g = math.gcd(ns[i], ns[j])
            if 1 < g < ns[i] and 1 < g < ns[j]:
                seeds[i].add(g)
                seeds[j].add(g)

    def _full_factors(i):
        n = ns[i]
        fs, rem = [], n
        for s in sorted(seeds[i]):
            if 1 < s < rem and rem % s == 0:
                while rem % s == 0:
                    fs.append(s)
                    rem //= s
        if rem > 1:
            if is_prime(rem):
                fs.append(rem)
                rem = 1
            else:
                return None
        if rem != 1 or len(fs) < 2:
            return None
        return fs

    segs, chain_cands = [], []
    for i in range(len(ns)):
        fs = _full_factors(i)
        if not fs:
            continue
        ei = es[i] if i < len(es) else e
        ci = cs[i] if i < len(cs) else (c if i == 0 else None)
        if not ei or ci is None:
            continue
        try:
            d_i = modinv(ei, phi_from_factors(fs))
        except Exception:
            continue
        m_i = pow(ci, d_i, ns[i])
        chain_cands.append(m_i)
        b_i = int_to_bytes(m_i)
        if b_i and _text_like(b_i):
            segs.append(b_i)

    # 所有模数都解出来了 → 试分段拼接
    if len(segs) == len(ns) and len(ns) >= 2:
        stitched, how = _stitch_segments(segs)
        if stitched:
            return Result(
                True, bytes_to_int(stitched), "模不互素",
                "链式共享素因子: %d 组模数全部靠 gcd 分解（%d 段明文）; %s，拼回完整明文"
                % (len(ns), len(segs), how),
                extra={"segments": len(segs)},
                cands=[bytes_to_int(stitched)] + chain_cands)


    def _factors_of(n, g):
        """用公因子 g 分解 n, 失败返回 None"""
        if not (1 < g < n):
            return None
        p_, q_ = g, n // g
        if p_ * q_ != n:
            return None
        return [p_, q_]

    def _dec(n, x, fs):
        try:
            d_ = modinv(e, phi_from_factors(fs))
        except Exception:
            return None
        return pow(x, d_, n)

    cands, detail = [], None
    for i in range(len(ns)):
        for j in range(len(ns)):
            if i == j:
                continue
            n_out, n_in = ns[i], ns[j]
            g = math.gcd(n_out, n_in)
            fs_out = _factors_of(n_out, g)
            if not fs_out:
                continue
            x_in = cs[i] if i < len(cs) else c
            if x_in is None:
                continue
            mid = _dec(n_out, x_in, fs_out)
            if mid is None:
                continue
            cands.append(mid)                       # 单层
            fs_in = _factors_of(n_in, math.gcd(n_in, g))
            if fs_in:                               # 双层: 再解一层
                m2 = _dec(n_in, mid, fs_in)
                if m2 is not None:
                    cands.append(m2)
                    detail = ("双层 RSA：先解 %d bit 外层，中间值再解 %d bit 内层，"
                              "两模共享一个 %d bit 素因子" %
                              (n_out.bit_length(), n_in.bit_length(), g.bit_length()))
            if detail is None:
                detail = "gcd(n%d, n%d) = %d…（共享素因子）" % (i, j, g)

    if not cands:
        return None
    good = [x for x in cands if not _looks_garbage(x)]
    best, _score = pick_flag(good or cands)
    if best is None:
        return None
    return Result(True, best, "模不互素", detail or "共享素因子分解成功", cands=cands)


# ---------- D. 指数类 ----------

@attack("泄露 p²+q²", "z = p²+q² 时 (p+q)² = z+2n，解二次方程分解 n")
def a_p2q2(ctx):
    n, z = ctx.get("n"), ctx.get("z")
    if not (n and z):
        return None
    s2 = z + 2 * n
    s = math.isqrt(s2)
    if s * s != s2:
        return None
    disc = s * s - 4 * n
    t = math.isqrt(disc)
    if t * t != disc:
        return None
    p = (s + t) // 2
    q = (s - t) // 2
    if p * q != n or p <= 1 or q <= 1:
        return None
    e, c = ctx.get("e"), ctx.get("c")
    extra = {"p": p, "q": q}
    if e and c is not None:
        try:
            d = modinv(e, (p - 1) * (q - 1))
        except Exception:
            return None
        extra["d"] = d
        return Result(True, pow(c, d, n), "p²+q² 泄露",
                      "(p+q)² = z + 2n = %d²，二次方程解出 p、q" % s.bit_length(), extra)
    return Result(True, None, "p²+q² 泄露", "(p+q)² = z + 2n 分解成功", extra)


# ---------- v3.4: 整数等式泄露 (q·f(p) = 常数 型) ----------
#
# 题面长这样(没有 n, 只有 p、q 之间的整数关系式):
#     q + q*p^3  = 1285367317452089980789441829580397855321901891350...
#     qp + q*p^2 = 1109691832903289208389283296592510864729403914873...
#
# 做法: 每条式子写成 q 的多项式, 系数是 p 的多项式:
#     c1(p)·q + d1(p) = 0
#     c2(p)·q + d2(p) = 0
# 消去 q:  c2(p)·d1(p) - c1(p)·d2(p) = 0  -> 只含 p 的整系数多项式, 求整数根。

_EQ_PREFIX = ("('", '("', "(", "'", '"')
_EQ_SUFFIX = ("')", '")', ")", "'", '"', ",")


def _clean_eq_line(line):
    """把 ('q + q*p^3 =123') / #q + q*p^3 =123 / q + q*p^3 = 123 统一成 q + q*p^3 = 123"""
    s = line.strip()
    if not s:
        return None
    if s.startswith("#"):
        s = s.lstrip("#").strip()
    changed = True
    while changed:
        changed = False
        for pre in _EQ_PREFIX:
            if s.startswith(pre):
                s = s[len(pre):].strip()
                changed = True
                break
    changed = True
    while changed:
        changed = False
        for suf in _EQ_SUFFIX:
            if s.endswith(suf):
                s = s[:-len(suf)].strip()
                changed = True
                break
    return s


def _terms_of_pq(node, depth=0):
    """把 p、q 的表达式展开成 {(p 的次数, q 的次数): 系数}"""
    if depth > 16:
        raise ValueError("表达式嵌套太深")
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool) or not isinstance(v, int):
            raise ValueError("非常数")
        return {(0, 0): v}
    if isinstance(node, ast.Name):
        if node.id == "p":
            return {(1, 0): 1}
        if node.id == "q":
            return {(0, 1): 1}
        raise ValueError("未知变量 %s" % node.id)
    if isinstance(node, ast.UnaryOp):
        d = _terms_of_pq(node.operand, depth + 1)
        if isinstance(node.op, ast.USub):
            return {k: -v for k, v in d.items()}
        if isinstance(node.op, ast.UAdd):
            return d
        raise ValueError("不支持的一元运算")
    if isinstance(node, ast.BinOp):
        a = _terms_of_pq(node.left, depth + 1)
        if isinstance(node.op, ast.Pow):
            if not (isinstance(node.right, ast.Constant)
                    and isinstance(node.right.value, int)
                    and not isinstance(node.right.value, bool)):
                raise ValueError("指数不是整数")
            k = node.right.value
            if k < 0 or k > 8:
                raise ValueError("指数过大")
            out = {(0, 0): 1}
            for _ in range(k):
                out = _terms_mul(out, a)
            return out
        b = _terms_of_pq(node.right, depth + 1)
        if isinstance(node.op, ast.Add):
            out = dict(a)
            for k, v in b.items():
                out[k] = out.get(k, 0) + v
            return {k: v for k, v in out.items() if v}
        if isinstance(node.op, ast.Sub):
            out = dict(a)
            for k, v in b.items():
                out[k] = out.get(k, 0) - v
            return {k: v for k, v in out.items() if v}
        if isinstance(node.op, ast.Mult):
            return _terms_mul(a, b)
        raise ValueError("不支持的运算")
    raise ValueError("不支持的写法")


def _terms_mul(a, b):
    if len(a) * len(b) > 600:
        raise ValueError("展开项太多")
    out = {}
    for (i1, j1), c1 in a.items():
        for (i2, j2), c2 in b.items():
            k = (i1 + i2, j1 + j2)
            out[k] = out.get(k, 0) + c1 * c2
    return {k: v for k, v in out.items() if v}


def _pcoef_list(d):
    """{次数: 系数} -> 低次在前的系数列表"""
    if not d:
        return [0]
    out = [0] * (max(d) + 1)
    for k, v in d.items():
        out[k] = v
    return poly_trim(out)


def extract_poly_eqs(text):
    """从题面里抽 'q + q*p^3 = <大整数>' 这类整数等式

    也认「先写符号关系、再给数值」的写法：
        A = q + q*p^3
        # A = 1285367...
    """
    rows = []
    for line in text.splitlines():
        s = _clean_eq_line(line)
        if not s or "=" not in s:
            continue
        expr, _, rhs = s.partition("=")
        expr = expr.strip()
        rhs = rhs.strip().rstrip(",").strip().strip("'\"")
        if not expr or len(expr) > 160:
            continue
        rows.append((expr, rhs))

    # 符号别名: A = q*(1+p^3)
    alias = {}
    for expr, rhs in rows:
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]{0,15}", expr) and _to_int(rhs) is None:
            if re.search(r"[pq]", rhs) and re.search(r"[+\-*^]", rhs):
                alias[expr] = rhs

    out, seen = [], set()
    for expr, rhs in rows:
        if expr in alias:
            expr = alias[expr]
        if not re.search(r"[pq]", expr) or not re.search(r"[+\-*^]", expr):
            continue
        if re.search(r"[^pq0-9+\-*^(). ab]", expr):
            continue
        val = _to_int(rhs)
        if not val:
            continue
        if re.fullmatch(r"\(?[pq]\s*\*\s*[pq]\)?", expr.replace(" ", "")):
            continue  # n = p*q 这种定义, 不是泄露
        src = expr.replace("^", "**").replace(" ", "")
        # pq / qp 这种缩写 = p*q
        src = re.sub(r"(?<![A-Za-z_])(pq|qp)(?![A-Za-z0-9_])", "(p*q)", src)
        # 3p / 2(p+1) / (p+1)(q+2) 这类省略乘号
        src = re.sub(r"(?<=\d)(?=[pq(])", "*", src)
        src = re.sub(r"(?=\))(?=[pq\d(])", "*", src)
        src = re.sub(r"(?<=[pq])(?=\()", "*", src)
        try:
            node = ast.parse(src, mode="eval").body
            terms = _terms_of_pq(node)
        except Exception:
            continue
        if not terms:
            continue
        qpoly = {}
        for (i, j), v in terms.items():
            qpoly.setdefault(j, {})[i] = v
        qpoly.setdefault(0, {})
        qpoly[0][0] = qpoly[0].get(0, 0) - val
        key = (expr.replace(" ", ""), val)
        if key in seen:
            continue
        seen.add(key)
        out.append({"expr": expr, "val": val,
                    "qpoly": {d: _pcoef_list(c) for d, c in qpoly.items()}})
    return out


def _cauchy_bound(coeffs):
    """整系数多项式实根的上界"""
    c = [int(x) for x in coeffs]
    poly_trim(c)
    if len(c) < 2 or not c[-1]:
        return 1 << 16
    m = max(abs(x) for x in c[:-1])
    return 1 + m // abs(c[-1]) + 2


def _poly_int_roots_smart(coeffs):
    """整数根: 一/二次直接解, 高次走 Sturm 隔离"""
    c = [int(x) for x in coeffs]
    poly_trim(c)
    if len(c) < 2:
        return []
    if len(c) == 2:
        a, b = c[1], c[0]
        return [-b // a] if a and b % a == 0 else []
    if len(c) == 3:
        a, b, k = c[2], c[1], c[0]
        if not a:
            return []
        disc = b * b - 4 * a * k
        if disc < 0:
            return []
        r = math.isqrt(disc)
        if r * r != disc:
            return []
        out = []
        for sg in (1, -1):
            num, den = -b + sg * r, 2 * a
            if den and num % den == 0:
                x = num // den
                if x not in out:
                    out.append(x)
        return out
    try:
        return poly_int_roots(c, bound=_cauchy_bound(c), max_roots=8)
    except Exception:
        return []


def _eq_value(qpoly, p, q):
    """把 p、q 代回原式(已减去常数项), 应为 0"""
    s = 0
    for d, coeffs in qpoly.items():
        s += poly_eval(coeffs, p) * pow(q, d)
    return s


def _poly_sub(a, b):
    n = max(len(a), len(b))
    a = list(a) + [0] * (n - len(a))
    b = list(b) + [0] * (n - len(b))
    return poly_trim([x - y for x, y in zip(a, b)])


def _eq_pair_solve(e1, e2):
    """两条等式联立, 返回 [(p, q), ...]"""
    def split(eq):
        g = eq["qpoly"]
        if any(d >= 2 for d in g):
            return None
        return g.get(1), g.get(0) or [0]

    a, b = split(e1), split(e2)
    if a is None or b is None:
        return []
    c1, d1 = a
    c2, d2 = b

    if c1 is None and c2 is None:
        return []
    if c1 is None:
        out = []
        for p in _poly_int_roots_smart(d1):
            den = poly_eval(c2, p) if c2 else 0
            num = -poly_eval(d2, p) if c2 else 0
            if den and num % den == 0:
                out.append((p, num // den))
        return out
    if c2 is None:
        return _eq_pair_solve(e2, e1)

    # 消去 q 后的 p 的方程
    g = _poly_sub(poly_mul(c2, d1), poly_mul(c1, d2))
    out = []
    for p in _poly_int_roots_smart(g):
        if p <= 2:
            continue
        den = poly_eval(c1, p)
        if not den:
            continue
        num = -poly_eval(d1, p)
        if num % den:
            continue
        out.append((p, num // den))
    return out


@attack("整数等式泄露 (q·f(p) = 常数)",
        "题面没有 n，只给了几条 p、q 之间的整数等式（如 q+q*p^3=A、q*p+q*p^2=B）："
        "每条看成 q 的多项式（系数是 p 的多项式），两条联立消去 q 得到 p 的整系数多项式，"
        "求整数根还原 p、q、n，再正常解密")
def a_eq_leak(ctx):
    eqs = ctx.get("eqs") or []
    if not eqs:
        return None
    e, c = ctx.get("e"), ctx.get("c")
    pairs = []
    if len(eqs) == 1:
        pairs = [(eqs[0], eqs[0])]
    else:
        for i in range(len(eqs)):
            for j in range(i + 1, len(eqs)):
                pairs.append((eqs[i], eqs[j]))

    best = None
    best_score = -1
    extra_best = None
    cands_best = []
    for e1, e2 in pairs:
        for p, q in _eq_pair_solve(e1, e2):
            if not p or not q or p <= 2 or q <= 2:
                continue
            if _eq_value(e1["qpoly"], p, q) or _eq_value(e2["qpoly"], p, q):
                continue
            if not (is_prime(p) and is_prime(q)):
                continue
            n = p * q
            extra = {"p": p, "q": q, "n": n, "p 位数": p.bit_length(),
                     "q 位数": q.bit_length()}
            if not (e and c is not None):
                return Result(True, None, "整数等式泄露",
                              "%s 与 %s 联立解出 p、q" % (e1["expr"], e2["expr"]),
                              extra)
            got = decrypt_standard(n, e, c, [p, q])
            cands = []
            if got:
                cands = [got[0]]
                extra["d"] = got[1]["d"]
            if not cands:
                cands = [x for x in decrypt_general(n, e, c, [p, q]) if x]
            if not cands:
                continue
            m, sc = pick_flag(cands)
            if m is not None and sc > best_score:
                best_score, best, extra_best = sc, m, extra
                cands_best = cands
    if best is not None:
        return Result(True, best, "整数等式泄露",
                      "联立 %d 组整数等式消去 q，解出 p、q，n = p·q 后正常解密"
                      % len(pairs), extra_best, cands_best)
    return None


def _brute_e(m, n, c, hi=200000):
    """e 不大时线性爆破: 每步只做一次大数乘法, 比重复模幂快两个数量级"""
    cur = m % n
    for k in range(1, hi):
        if cur == c:
            return k
        cur = cur * m % n
    return None


def _brute_e_from_pow(base, n, target, hi=300000):
    """已知 base^e mod n 的值, 线性爬出 e"""
    cur = base % n
    for k in range(1, hi):
        if cur == target:
            return k
        cur = cur * base % n
    return None


def _plaintext_ratio(m):
    b = int_to_bytes(m)
    if not b:
        return 0.0
    return sum(1 for ch in b if ch in PRINTABLE) / float(len(b))


def _looks_garbage(m, bits=1024):
    """大模数解出来的东西超过一半不可打印 —— 这几乎一定是 e 用错了"""
    return _plaintext_ratio(m) < 0.6


def recover_unknown_e(ctx, hi=300000):
    """题面没写 e 时, 从线索里把 e 反推出来 (v2.7)

    线索优先级:
      1. print pow(294,e,n)   —— 底数、模数、结果三者都有, 直接爬
      2. bytes_to_long("BJD"*32) 之类已知明文 + 对应密文
    """
    if ctx.get("e") and not ctx.get("e_is_default"):
        return ctx.get("e")
    n = ctx.get("n")
    cand = None
    base, g = ctx.get("oracle_base"), ctx.get("oracle_val")
    if base and g and n:
        cand = _brute_e_from_pow(base, n, g, hi)
    if cand is None:
        known, c2, n2 = ctx.get("known_pt"), ctx.get("c2"), ctx.get("n2")
        if known is not None and c2 is not None and n2:
            cand = _brute_e(known, n2, c2, hi)
    if cand is None:
        known, c, nn = ctx.get("known_pt"), ctx.get("c"), ctx.get("n")
        if known is not None and c is not None and nn:
            cand = _brute_e(known, nn, c, hi)
    if cand is None:
        # v3.5: 题面根本没写 e，而密文本身就是某个小指数的完全幂（小明文攻击）。
        # 光靠"已知明文爬 e"发现不了这种题，这里直接试常见小指数。
        cc = ctx.get("c")
        if isinstance(cc, int) and cc > 1 and cc.bit_length() >= 64:
            for e_small in (3, 5, 7, 17, 257):
                r, exact = iroot(cc, e_small)
                if exact and r > 1 and _plaintext_ratio(r) > 0.9:
                    cand = e_small
                    break
    if cand:
        ctx["e"] = cand
        ctx["e_is_default"] = False
        ctx["e_recovered"] = cand
    return ctx.get("e")


@attack("e 未知 · 共享素因子", "e 未知，两组模数有公因子先分解，再用已知明文爆破 e")
def a_e_unknown(ctx):
    n1 = ctx.get("n")
    n2 = ctx.get("n2")
    if not (n1 and n2):
        ns = ctx.get("ns") or []
        if len(ns) >= 2:
            n1, n2 = ns[0], ns[1]
        else:
            return None
    g = math.gcd(n1, n2)
    if g in (1, n1, n2) or g <= 1:
        return None
    e = ctx.get("e")
    if ctx.get("e_is_default"):
        e = None  # 题面没写 e, 别拿默认的 65537 硬套
    known = ctx.get("known_pt")
    c2 = ctx.get("c2")
    if not e and known is not None and c2 is not None:
        e = _brute_e(known, n2, c2)
    if not e:
        return None
    if not (n1 % g == 0 and n2 % g == 0):
        return None
    p1, p2 = n1 // g, n2 // g
    c1 = ctx.get("c")
    if c1 is None:
        return Result(True, None, "e 未知 · 共享素因子", "e = %d，两模共享因子" % e,
                      {"e": e, "p": p1, "q": g})
    try:
        d = modinv(e, (p1 - 1) * (g - 1))
    except Exception:
        return None
    m1 = pow(c1, d, n1)
    if n1.bit_length() >= 1000 and _looks_garbage(m1):
        return None
    return Result(True, m1, "e 未知 · 共享素因子",
                  "e = %d（由已知明文爆破得到），gcd(n1,n2) = %d bit" % (e, g.bit_length()),
                  {"e": e, "d": d, "p": p1, "q": g})


@attack("e = 1", "指数为 1，明文就是密文")
def a_e1(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if e == 1 and c is not None:
        return Result(True, c, "e = 1", "c = m^1 mod n")
    return None


@attack("Wiener 攻击", "d 过小（d < n^0.25/3），连分数恢复 d")
def a_wiener(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    if not (n and e):
        return None
    if e > n:
        return None
    r = wiener_attack(n, e)
    if not r:
        r = boneh_durfee_lite(n, e)
        if not r:
            return None
        d, p, q = r
        m = pow(c, d, n) if c is not None else None
        return Result(True, m, "Wiener 攻击（扩展搜索）",
                      "d = %d（很小）" % d, {"d": d, "p": p, "q": q})
    d, p, q = r
    # 只给 n、e 的题（要求恢复 d）也要能走到这里
    m = pow(c, d, n) if c is not None else None
    return Result(True, m, "Wiener 攻击", "d = %d（很小），由连分数收敛子恢复" % d,
                  {"d": d, "p": p, "q": q})


@attack("Boneh-Durfee（d < n^0.292）", "小私钥指数格攻击，纯 Python 只做启发式尝试")
def a_boneh(ctx):
    return None  # 由 Wiener 扩展覆盖, 真正的 BD 需要格, 见报告提示



# ============================================================
# v3.2 新增：多组泄露 / nextprime 线性组合 / e 次根全组合枚举
# ============================================================

def _pq_from_n_phi(n, phi):
    """已知 n 和 φ(n) → 解 x² - (n-φ+1)x + n = 0"""
    if not n or not phi:
        return None
    s = n - phi + 1
    disc = s * s - 4 * n
    if disc < 0:
        return None
    t = math.isqrt(disc)
    if t * t != disc or (s + t) % 2:
        return None
    p, q = (s - t) // 2, (s + t) // 2      # 题面惯例 assert(p < q)
    if p * q != n or q <= 1:
        return None
    return p, q


def _pq_from_n_ed(n, ed):
    """已知 n 和 e·d → e·d-1 = k·φ, k 由 (e·d-1)//n 直接读出（φ 与 n 极接近）"""
    if not n or not ed or ed < 2:
        return None
    A = ed - 1
    k0 = A // n
    cand = [k for k in range(max(1, k0 - 6), k0 + 8)]
    cand += [k for k in range(1, 4096)]
    seen = set()
    for k in cand:
        if k in seen or k <= 0 or A % k:
            continue
        seen.add(k)
        r = _pq_from_n_phi(n, A // k)
        if r:
            return r
    return None


def _trim_flag(m, prefix=None):
    """已知前缀时把 flag 从尾部填充垃圾里截出来：截到第一个 } 为止"""
    if not prefix:
        return m
    b = int_to_bytes(m)
    if not b.startswith(prefix):
        return m
    end = b.find(b"}", len(prefix))
    if end < 0:
        return m
    return bytes_to_int(b[:end + 1])


def _flag_like(b):
    """一段 bytes 看起来像不像明文 flag"""
    if not b or len(b) < 3 or len(b) > 8192:
        return False
    printable = sum(1 for x in b if 32 <= x < 127)
    if printable < len(b) * 0.97:
        return False
    return True


def _big_root_search(s, g, moduli, per, prefix=None, budget=80000000):
    """e 次根有海量组合（如 e=4919 → 4919² ≈ 2400 万）时的暴力搜索。

    不再随机截断候选，而是逐组合 CRT + 明文特征过滤（低位可打印预筛 + flag 前缀）。
    """
    if len(moduli) != 2 or len(per) != 2:
        return []
    m1, m2 = moduli
    s1, s2 = per
    inv = modinv(m1 % m2, m2)
    u2 = [(x * inv) % m2 for x in s2]
    pres = int.from_bytes(prefix, "big") if prefix else None
    plen = len(prefix) if prefix else 0
    pr8 = m1 & 0xFF
    pset = set(PRINTABLE)
    hits = []
    tried = 0
    for a in s1:
        a8 = a & 0xFF
        v = (a * inv) % m2
        for u in u2:
            tried += 1
            if tried > budget:
                return hits
            t = u - v
            if t < 0:
                t += m2
            if ((a8 + pr8 * (t & 0xFF)) & 0xFF) not in pset:
                continue
            mv = a + m1 * t
            L = (mv.bit_length() + 7) >> 3
            if plen and L >= plen and (mv >> (8 * (L - plen))) != pres:
                continue
            b = int_to_bytes(mv)
            if _flag_like(b):
                hits.append(mv)
                if pres is not None:
                    return hits          # 前缀已对上，基本就是它
    return hits


@attack("多组泄露 + nextprime 线性组合",
        "题面分别打印了多组 (n, φ) / (n, e·d)，并用 nextprime(a·p±b·q) 重新造素数：先逐组反解 p,q，再按题面里的线性组合还原真正的模数")
def a_group_nextprime(ctx):
    got = ctx.get("group_pq")
    c = ctx.get("c")
    if not got or c is None:
        return None
    e = ctx.get("e") or 65537
    tf = ctx.get("transforms") or []
    if not tf:
        tf = [(1, 0, 1)]
    primes = []
    for _tag, p, q in got:
        for (A, B, sgn) in tf:
            v = A * p + sgn * B * q
            if v < 0:
                v = -v
            if v > 1:
                primes.append(next_prime(v))
    primes = list(dict.fromkeys(primes))
    if len(primes) < 2:
        return None
    cands = []
    detail = []
    for i, p1 in enumerate(primes):
        for j, q1 in enumerate(primes):
            if i == j:
                continue
            n_ = p1 * q1
            phi_ = (p1 - 1) * (q1 - 1)
            if math.gcd(e, phi_) != 1:
                continue
            try:
                m = pow(c, modinv(e, phi_), n_)
            except Exception:
                continue
            if pow(m, e, n_) != c:
                continue
            b = int_to_bytes(m)
            if _flag_like(b):
                cands.append(m)
                detail.append("%d 组泄露 → %d 个候选素数" % (len(got), len(primes)))
    if not cands:
        return None
    best, _sc = pick_flag(cands)
    if best is None:
        best = cands[0]
    return Result(True, best, "多组泄露 + nextprime 线性组合",
                  "%d 组 (n,φ/n,e·d) 各反解出 p,q，按题面 nextprime(a·p±b·q) 还原模数，"
                  "解出 %d 个可打印候选" % (len(got), len(cands)),
                  cands=cands)

@attack("e 与 φ(n) 不互素", "gcd(e, phi) > 1：先剥掉公因子降到 m^g，再分模开 g 次根 + CRT，按可打印性筛选")
def a_e_phi(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    fs = ctx.get("factors") or ([ctx["p"], ctx["q"]] if ctx.get("p") and ctx.get("q") else None)
    if not (n and e and c is not None and fs):
        return None
    phi = phi_from_factors(fs)
    g = math.gcd(e, phi)
    if g == 1:
        return None
    e2 = e // g
    if math.gcd(e2, phi) != 1:
        return None                     # 少见的病态情形, 交给通用模块
    s = pow(c, modinv(e2, phi), n)      # = m^g mod n

    cands = []
    # 1) m^g 恰好没超过 n 且是完全 g 次幂: 直接整数开根
    r, exact = iroot(s, g)
    if exact and pow(r, g, n) == s:
        cands.append(r)
    # 2) 分模开 g 次根, 再 CRT 拼回来
    fdict = _count(fs)
    per, moduli = [], []
    ok = True
    for pr, cnt in fdict.items():
        pk = pow(pr, cnt)
        sols = (nth_root_mod_prime_all(s % pk, g, pk) if cnt == 1
                else _roots_mod_prime_power(s, g, pr, cnt))
        if not sols:
            ok = False
            break
        per.append(sols)
        moduli.append(pk)
    if ok:
        total = 1
        for sols in per:
            total *= max(1, len(sols))
        if total <= 200000:
            comb = [0]
            cur = 1
            for mod, sols in zip(moduli, per):
                new_comb = []
                for base in comb:
                    for x in sols:
                        try:
                            iv = modinv(cur % mod, mod)
                        except ValueError:
                            continue
                        new_comb.append(base + cur * (((x - base) % mod) * iv % mod))
                comb = new_comb
                cur *= mod
            for m in comb:
                if pow(m, g, n) == s:
                    cands.append(m)
        else:
            # 组合数爆炸（e 大 → e² 量级）: 全组合搜，按明文特征筛
            cands.extend(_big_root_search(s, g, moduli, per, ctx.get("flag_prefix")))

    cands = list(dict.fromkeys(cands))
    if not cands:
        return None
    best, _sc = pick_flag(cands)
    if best is None:
        good = [x for x in cands if not _looks_garbage(x)]
        best = good[0] if good else None
    if best is None:
        return None
    best = _trim_flag(best, ctx.get("flag_prefix"))
    return Result(True, best, "e 与 φ(n) 不互素",
                  "gcd(e,φ)=%d → 先算 m^%d，再分模开 %d 次根（%d 个候选）, 按可打印性筛选"
                  % (g, g, g, len(cands)),
                  cands=cands)


@attack("Rabin (e = 2)", "e=2 时每个素因子两个平方根，4 个候选")
def a_rabin(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    fs = ctx.get("factors")
    if e != 2 or not fs or not c:
        return None
    if len(set(fs)) != 2:
        return None
    p, q = fs[0], fs[-1]
    if p == q:
        return None
    rp_ = tonelli_shanks(c % p, p)
    rq_ = tonelli_shanks(c % q, q)
    if rp_ is None or rq_ is None:
        return None
    cands = []
    for a in (rp_, p - rp_):
        for b in (rq_, q - rq_):
            m, mod = crt_pair(a, p, b, q)
            if m is not None:
                cands.append(m)
    best, _ = pick_flag(cands)
    return Result(True, best, "Rabin (e=2)", "4 个平方根候选，按可打印性筛选", cands=cands)


# ---------- E. 泄露类 ----------

@attack("已知 p 高位 (Coppersmith)", "已知 p 的高位比特，格攻击恢复低位")
def a_p_high(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    ph = ctx.get("ph")
    if not (n and e and c is not None and ph):
        return None
    ph = int(ph)
    if ph <= 1 or ph >= n:
        return None

    # 1) 直接是因子
    if n % ph == 0:
        m, info = decrypt_standard(n, e, c, [ph, n // ph])
        if m is not None:
            return Result(True, m, "已知素因子", "ph 本身就是 p", info)

    p_bits = n.bit_length() // 2
    tz = (ph & -ph).bit_length() - 1 if ph else 0
    if tz >= 4:
        unknown = tz          # p = ph + x, ph 低 tz 位全 0
    else:
        unknown = max(1, p_bits - ph.bit_length())
    limit = max(8, n.bit_length() // 4 - 2)   # n^0.25 附近是 beta=0.5 的理论上界
    if unknown > limit:
        unknown = limit
    X = 1 << unknown

    # 2) 未知位不多时直接暴力
    if unknown <= 22:
        base = ph & ~((1 << unknown) - 1) if (ph & ((1 << unknown) - 1)) else ph
        for d in range(1 << unknown):
            cand = base + d
            if cand > 1 and n % cand == 0:
                m, info = decrypt_standard(n, e, c, [cand, n // cand])
                if m is not None:
                    return Result(True, m, "已知 p 低位暴力",
                                  "未知 %d bit，枚举命中" % unknown, {"p": cand, "q": n // cand})

    # 3) Coppersmith
    roots = coppersmith_univariate([ph, 1], n, beta=0.5, X=X, max_dim=16, time_budget=30)
    if not roots and X < (1 << limit):
        roots = coppersmith_univariate([ph, 1], n, beta=0.5,
                                       X=min(1 << limit, X * 16), max_dim=18, time_budget=30)
    for r0 in roots:
        p = ph + r0
        if p > 1 and n % p == 0:
            q = n // p
            m, info = decrypt_standard(n, e, c, [p, q])
            if m is not None:
                return Result(True, m, "已知 p 高位 (Coppersmith)",
                              "p = p_high + x, x < 2^%d, 格攻击恢复" % unknown,
                              {"p": p, "q": q})
    return None


@attack("已知明文部分 (Coppersmith)", "已知 m 的部分比特或前缀，格攻击补全")
def a_known_plaintext(ctx):
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    mh = ctx.get("mh")
    if not (n and e and c is not None and mh):
        return None
    mh = int(mh)
    if mh <= 0:
        return None
    # f(x) = (mh + x)^e - c
    base = [mh % n, 1]
    poly = [1]
    for _ in range(e):
        poly = poly_mul(poly, base)
    f = [x % n for x in poly]
    f[0] = (f[0] - c) % n

    hard_limit = max(8, n.bit_length() // max(e, 1) - 8)
    xbits = ctx.get("xbits") or ctx.get("unknown_bits")
    if xbits:
        ks = [int(xbits)]
    else:
        ks = [k for k in (24, 32, 48, 56, 64, 80, 96, 112, 128, 160, 192,
                          224, 256, 288, 320) if k <= hard_limit]
        if not ks:
            ks = [hard_limit]
    t_start = time.time()
    for k in ks:
        if time.time() - t_start > 30:
            break
        X = 1 << k
        roots = coppersmith_univariate(f, n, beta=1.0, X=X, max_dim=14, time_budget=12)
        for r0 in roots:
            m0 = mh + r0
            if pow(m0, e, n) == c % n:
                return Result(True, m0, "已知明文部分 (Coppersmith)",
                              "m = m_high + x, x < 2^%d, 格攻击恢复" % k)
    return None


@attack("Franklin-Reiter 相关消息", "两组密文对应线性相关的明文，多项式 GCD 恢复")
def a_franklin(ctx):
    n, e = ctx.get("n"), ctx.get("e")
    c1, c2 = ctx.get("c1"), ctx.get("c2")
    if not (n and e and c1 is not None and c2 is not None):
        return None
    a, b = ctx.get("a", 1), ctx.get("b", 0)
    if a == 1 and b == 0:
        return None
    # g1 = x^e - c1, g2 = (a x + b)^e - c2
    g1 = [(-c1) % n] + [0] * (e - 1) + [1]
    lin = [b % n, a % n]
    g2 = [1]
    for _ in range(e):
        g2 = poly_mul(g2, lin)
    g2[0] = (g2[0] - c2) % n
    g = poly_gcd_mod(g1, g2, n)
    if g is None or len(g) < 2:
        return None
    # 线性因子 a*x + b -> m = -b/a
    if len(g) == 2:
        try:
            m = (-g[0]) * modinv(g[1], n) % n
        except ValueError:
            return None
        if pow(m, e, n) == c1 % n:
            return Result(True, m, "Franklin-Reiter 相关消息", "gcd(x^e-c1, (ax+b)^e-c2) 得线性因子")
    return None


def poly_mod(a, b, n):
    a = [x % n for x in a]
    b = [x % n for x in b]
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    if len(b) == 1 and b[0] == 0:
        return None
    while len(a) >= len(b) and any(a):
        try:
            inv = modinv(b[-1], n)
        except ValueError:
            return None
        coef = a[-1] * inv % n
        shift = len(a) - len(b)
        for i in range(len(b)):
            a[i + shift] = (a[i + shift] - coef * b[i]) % n
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return a


def poly_gcd_mod(a, b, n):
    a = [x % n for x in a]
    b = [x % n for x in b]
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    it = 0
    while not (len(b) == 1 and b[0] == 0) and it < 200:
        it += 1
        r = poly_mod(a, b, n)
        if r is None:
            return None
        a, b = b, r
        while len(b) > 1 and b[-1] == 0:
            b.pop()
    return a

# ============================================================
# 10. 题目解析
# ============================================================

ALIASES = {
    "n": ["n", "N", "modulus", "mod", "nn", "pubkey_n"],
    "e": ["e", "E", "exp", "exponent", "ee", "pubkey_e", "public_exponent"],
    "c": ["c", "C", "ct", "ciphertext", "enc", "encrypted", "cipher", "cc",
          "enc_flag", "flag_enc", "flagcipher", "encrypted_flag", "c_flag",
          "cipher_text", "ciphertxt"],
    "p": ["p", "P", "prime1", "p1", "factor1"],
    "q": ["q", "Q", "prime2", "q1", "factor2"],
    "r": ["r", "R"],
    "d": ["d", "D", "private_exponent", "priv", "privkey"],
    "dp": ["dp", "d_p", "dP", "DP"],
    "dq": ["dq", "d_q", "dQ", "DQ"],
    "phi": ["phi", "phin", "phi_n", "PHI", "fn", "euler", "phiN"],
    "ns": ["ns", "Ns", "n_list", "modulus_list", "pubkeys"],
    "cs": ["cs", "Cs", "c_list", "ciphertexts", "ct_list"],
    "es": ["es", "Es", "e_list", "exponents"],
    "m1": ["m1", "M1", "msg1", "m_1"],
    "m2": ["m2", "M2", "msg2", "m_2"],
    "c1": ["c1", "C1", "ct1", "flag1", "enc1"],
    "c2": ["c2", "C2", "ct2", "flag2", "enc2"],
    "ph": ["ph", "p_high", "phigh", "pbar", "p_hi", "phint", "hint_p"],
    "mh": ["mh", "m_high", "mhigh", "mbar", "m_hi"],
    "z": ["z", "Z", "p2q2", "ppqq", "sq_sum"],
    "e_product": ["e_product", "e1e2", "e1_e2", "e1e2_product", "e_prod",
                  "e1_times_e2", "e1_x_e2", "eprod", "e1e2_value"],
    "known_pt": ["known_pt", "known_m", "m_known"],
    "a": ["a", "aa"],
    "b": ["b", "bb"],
}

_ALIAS_MAP = {}
for _k, _v in ALIASES.items():
    for _a in _v:
        _ALIAS_MAP[_a] = _k
    _ALIAS_MAP[_k.lower()] = _k


def detect_number_base(s):
    """判断一个数字字面量到底是几进制。

    CTF 里常见「五进制伪装」: 一长串只由 0-4 组成的数字, 实际是 base-5 编码的 n/c。
    规则: 长度 >= 25 且字符集 ⊆ {0,1,2,3,4} -> 判为 5 进制。
    """
    s = s.strip().replace("_", "").rstrip("Ll").rstrip(",")
    if s.lower().startswith("0x"):
        return 16
    if s.lower().startswith("0b"):
        return 2
    if len(s) >= 25 and set(s) <= set("01234"):
        return 5
    return 10


def int_any(s):
    """按自动识别出的进制把字符串转成 int"""
    if s is None:
        return None
    s = s.strip().replace("_", "").rstrip("Ll").rstrip(",")
    if not s:
        return None
    b = detect_number_base(s)
    try:
        return int(s, b)
    except ValueError:
        try:
            return int(s, 10)
        except ValueError:
            return None


def _to_int(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return v
    if isinstance(v, bytes):
        return int.from_bytes(v, "big")
    if isinstance(v, str):
        return int_any(v)
    return None


def _to_list(v):
    if isinstance(v, (list, tuple)):
        out = []
        for x in v:
            t = _to_int(x)
            if t is not None:
                out.append(t)
        return out
    return None


_SAFE_CALLS = {"int", "len", "abs", "pow", "bytes", "hex", "str", "ord", "sum", "max", "min", "range"}

# 素因子偏移泄露: (p-2)*(q-2) = ... / (p+1)*(q+1) = ...
_SHIFT_PAT = re.compile(
    r"\(\s*p\s*([+-])\s*(\d+)\s*\)\s*[\*·×]?\s*\(\s*q\s*([+-])\s*(\d+)\s*\)\s*[=:：]\s*"
    r"(0[xX][0-9a-fA-F]+|\d+)")

# p+q 泄露: "p+q : 0x..." / "p + q = 123..."
_SUM_PAT = re.compile(
    r"(?<![A-Za-z0-9_])p\s*\+\s*q(?![A-Za-z0-9_])[\s\w]{0,4}?[=:：]\s*"
    r"(0[xX][0-9a-fA-F]+|\d+)")

# p−q 泄露: "p-q = ..." / "p - q : ..." / "q-p = ..."
_DIFF_PAT = re.compile(
    r"(?<![A-Za-z0-9_])(?:p\s*[-−–]\s*q|q\s*[-−–]\s*p)(?![A-Za-z0-9_])[\s\w]{0,6}?[=:：]\s*"
    r"(0[xX][0-9a-fA-F]+|\d+)")

_SUP2 = r"(?:\*\*\s*2|\^\s*2|²)"

# p²−q² 泄露: "p**2 - q**2 = ..." / "p^2-q^2 : ..."
_SQDIFF_PAT = re.compile(
    r"(?<![A-Za-z0-9_])p\s*" + _SUP2 + r"\s*[-−–]\s*q\s*" + _SUP2 +
    r"[\s\w]{0,6}?[=:：]\s*(0[xX][0-9a-fA-F]+|\d+)")

# 做内联扫描前先把这几种"式子型"字段抹掉, 否则 p+q 里的 q 会被当成独立的 q
_LEAK_MASK = re.compile(
    r"(?<![A-Za-z0-9_])p\s*\+\s*q(?![A-Za-z0-9_])[\s\w]{0,4}?[=:：]\s*(?:0[xX][0-9a-fA-F]+|\d+)"
    r"|(?<![A-Za-z0-9_])(?:p\s*[-−–]\s*q|q\s*[-−–]\s*p)(?![A-Za-z0-9_])[\s\w]{0,6}?[=:：]\s*"
    r"(?:0[xX][0-9a-fA-F]+|\d+)"
    r"|(?<![A-Za-z0-9_])p\s*" + _SUP2 + r"\s*[-−–]\s*q\s*" + _SUP2 +
    r"[\s\w]{0,6}?[=:：]\s*(?:0[xX][0-9a-fA-F]+|\d+)"
    r"|\(\s*p\s*[+-]\s*\d+\s*\)\s*[\*·×]?\s*\(\s*q\s*[+-]\s*\d+\s*\)\s*[=:：]\s*"
    r"(?:0[xX][0-9a-fA-F]+|\d+)")

# 题面把关系写成 "hint = p + q" / "s = p - q" 这种先赋给变量再 print 的形式:
# 记下变量名, 等 env 建好后回头取值
_EXPR_SUM_PAT = re.compile(r"(?m)^\s*([A-Za-z_]\w*)\s*=\s*p\s*\+\s*q\s*$")
_EXPR_DIFF_PAT = re.compile(r"(?m)^\s*([A-Za-z_]\w*)\s*=\s*(?:p\s*[-−–]\s*q|q\s*[-−–]\s*p)\s*$")
_EXPR_SQDIFF_PAT = re.compile(
    r"(?m)^\s*([A-Za-z_]\w*)\s*=\s*p\s*" + _SUP2 + r"\s*[-−–]\s*q\s*" + _SUP2 + r"\s*$")

# 常见 hint 变量名(题目里不写 p+q 而是直接给个 s / pq_sum)
_SUM_NAMES = ("p_q_sum", "pq_sum", "sum_pq", "p_add_q", "paddq", "p_plus_q", "pplusq",
              "s_pq", "spq", "sum_pq_val", "hint_sum", "pq_sum_hint", "s")
_DIFF_NAMES = ("p_q_diff", "pq_diff", "diff_pq", "p_sub_q", "psubq", "p_minus_q",
               "pminusq", "p_q_sub", "diff_pq_val", "hint_diff", "delta", "diff", "d_pq", "dpq")
_SQDIFF_NAMES = ("p2_minus_q2", "p2q2_diff", "p_sq_minus_q_sq", "p_2_minus_q_2", "sqdiff")


def _safe_eval(node, env, depth=0):
    """受限表达式求值 (只支持常量/变量/算术/白名单调用)"""
    if depth > 30:
        return None
    try:
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            return env.get(node.id)
        if isinstance(node, ast.UnaryOp):
            v = _safe_eval(node.operand, env, depth + 1)
            if v is None:
                return None
            if isinstance(node.op, ast.USub):
                return -v
            if isinstance(node.op, ast.UAdd):
                return +v
            if isinstance(node.op, ast.Invert):
                return ~v
            if isinstance(node.op, ast.Not):
                return not v
            return None
        if isinstance(node, ast.BinOp):
            l = _safe_eval(node.left, env, depth + 1)
            r = _safe_eval(node.right, env, depth + 1)
            if l is None or r is None:
                return None
            op = node.op
            if isinstance(op, ast.Add):
                return l + r
            if isinstance(op, ast.Sub):
                return l - r
            if isinstance(op, ast.Mult):
                return l * r
            if isinstance(op, ast.FloorDiv):
                return l // r
            if isinstance(op, ast.Div):
                return l / r
            if isinstance(op, ast.Mod):
                return l % r
            if isinstance(op, ast.Pow):
                if isinstance(r, int) and 0 <= r < 100000:
                    return pow(l, r)
                return None
            if isinstance(op, ast.LShift):
                return l << r
            if isinstance(op, ast.RShift):
                return l >> r
            if isinstance(op, ast.BitAnd):
                return l & r
            if isinstance(op, ast.BitOr):
                return l | r
            if isinstance(op, ast.BitXor):
                return l ^ r
            return None
        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            vals = []
            for x in node.elts:
                v = _safe_eval(x, env, depth + 1)
                if v is None:
                    return None
                vals.append(v)
            return vals
        if isinstance(node, ast.Call):
            fn = node.func
            name = None
            if isinstance(fn, ast.Name):
                name = fn.id
            elif isinstance(fn, ast.Attribute):
                # bytes.fromhex / binascii.unhexlify
                if isinstance(fn.value, ast.Name) and fn.value.id == "bytes" and fn.attr == "fromhex":
                    name = "fromhex"
                else:
                    return None
            args = [_safe_eval(a, env, depth + 1) for a in node.args]
            if any(a is None for a in args):
                return None
            if name == "fromhex" and len(args) == 1:
                return bytes.fromhex(args[0])
            if name == "int" and args:
                if isinstance(args[0], str):
                    base = args[1] if len(args) > 1 else 10
                    try:
                        return int(args[0], base)
                    except Exception:
                        return None
                return int(args[0])
            if name == "len" and args:
                return len(args[0])
            if name == "abs" and args:
                return abs(args[0])
            if name == "pow" and len(args) >= 2:
                return pow(args[0], args[1], args[2]) if len(args) == 3 else pow(args[0], args[1])
            if name == "bytes" and args:
                if isinstance(args[0], str):
                    return args[0].encode()
                return bytes(args[0])
            if name == "max" and args:
                return max(args[0]) if isinstance(args[0], (list, tuple)) else max(args)
            if name == "min" and args:
                return min(args[0]) if isinstance(args[0], (list, tuple)) else min(args)
            if name == "sum" and args:
                return sum(args[0])
            if name == "str" and args:
                return str(args[0])
            if name == "hex" and args:
                return hex(args[0])
            if name == "ord" and args:
                return ord(args[0])
            return None
        return None
    except Exception:
        return None


def parse_py_file(path):
    """用 ast 只读解析 .py 题目文件里的模块级赋值 (不执行文件)"""
    with open(path, "rb") as f:
        src = f.read()
    text = src.decode("utf-8", "replace")
    # v3.3: 长数字被聊天框/OCR 折断成两行时, ast 会把前半截当成变量值(位数少一半),
    # 后面那半截当成一个表达式语句。先把折行接回去再交给 ast。
    text_joined = _join_wrapped_numbers(text)
    try:
        tree = ast.parse(text_joined)
    except SyntaxError:
        return {}, text
    env = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            val = _safe_eval(node.value, env)
            if val is None:
                continue
            for t in node.targets:
                if isinstance(t, ast.Name):
                    env[t.id] = val
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            val = _safe_eval(node.value, env)
            if val is not None:
                env[node.target.id] = val
        elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
            # v3.2: 题面里 print(c) 之后那行裸数字(输出), ast 里是表达式语句
            v = node.value.value
            if isinstance(v, int) and not isinstance(v, bool) and v > 1 << 32:
                env.setdefault("__py_out_%d" % len(
                    [k for k in env if k.startswith("__py_out_")]), v)
    outs = [env[k] for k in sorted(env) if k.startswith("__py_out_")]
    if len(outs) == 1 and not any(
            k.lower() in ("c", "ct", "ciphertext", "enc", "cipher", "flag1", "flag2")
            for k in env):
        env["c"] = outs[0]
    for k in [k for k in env if k.startswith("__py_out_")]:
        del env[k]
    return env, text


_FW_TRANS = str.maketrans({
    "，": ",", "；": ";", "：": ":", "＝": "=", "、": ",",
    "（": "(", "）": ")", "【": "[", "】": "]", "　": " ",
    "－": "-", "＋": "+", "＊": "*", "／": "/", "。": ".",
})


def _normalize_punct(text):
    """全角标点 -> 半角 (中文题干里 , : = 常是全角)"""
    return text.translate(_FW_TRANS)


# 内联宽松扫描: 不管在不在行首、前后有没有中文, 抓所有 key=数字
# 例: "假设p=473398607161，q=4511491，e=17" -> p/q/e 全抓出来
_INLINE_KV = re.compile(
    r"(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)\s*[:=]\s*(0[xX][0-9a-fA-F]+|\d+)")

_CORE_KEYS = ("p", "q", "n", "e", "c", "d", "phi", "dp", "dq", "ph",
              "n1", "n2", "e1", "e2", "c1", "c2", "flag1", "flag2")

# 题目里直接粘 print 输出: ('n=', '0x86f4...L')  /  ("c=", "12345")
_TUPLE_KV = re.compile(
    r"\(\s*['\"]\s*([A-Za-z_][A-Za-z0-9_]*)\s*=?\s*['\"]\s*,\s*['\"]?\s*"
    r"(0[xX][0-9a-fA-F]+|\d+)\s*[lL]?\s*['\"]?\s*\)")

# python2 长整型后缀 12345L / 0xffL
_LONG_SUF = re.compile(r"(?<![0-9A-Za-z_])(0[xX][0-9a-fA-F]+|\d+)[lL](?![0-9A-Za-z_])")


# 赋值行以数字结尾: "n2 = 11538319..." / "c = 6040616..."
_ASSIGN_TAIL_DIGITS = re.compile(r"^[ \t#]*[A-Za-z_][A-Za-z0-9_]*\s*[:=].*\d[ \t]*$")
# 纯数字行(折行后的下半截)
_PURE_DIGIT_LINE = re.compile(r"^[ \t]*(0[xX][0-9a-fA-F]+|\d{6,})[ \t]*$")
# 裸数字行(可能不长, 用于密文折行; 要求更长, 避免把两段独立输出拼一起)
_BARE_DIGIT_LINE = re.compile(r"^[ \t]*(0[xX][0-9a-fA-F]+|\d{16,})[ \t]*$")


def _has_multi_print(text):
    """题目里有 print(c,z,n) / print c,n 这种多变量输出

    这类题目的三行裸数字是 c、z、n, 绝不能当成"数字被折断"拼起来。
    """
    return bool(re.search(r"^[ \t]*print\s*\(?\s*[A-Za-z_][A-Za-z0-9_]*\s*,", text, re.M))


def _join_wrapped_numbers(text):
    """修复"长数字被聊天框/截图 OCR 折断成两行"

    很多人是把题目从微信/TG/PDF 里复制出来粘进工具的, 1024 bit 的 n 会被
    客户端在 60~100 个字符处硬插一个换行, 变成:

        n2 = 11538319858467714748755601433644831072185384116875801244563418281
        4180314480501828927160071015197089456042472185850893847370481817325868824076245290735749717384769661698895000176441497242371873981353689607711146852891551491168528799814311992471449640014501858763495472267168224015665906627382490565507927272073

    于是解析器把前半截当成 n2(位数少一半), 后面半截被当成一个垃圾数字,
    gcd(n1, n2) 自然白算 —— 全部模块 0.00s 未命中, 一个 flag 都不出。

    这里在预处理阶段把断开的数字接回去: 上一行是 "变量 = ...数字结尾",
    下一行是纯数字就粘成一行。裸数字行(没有变量名前缀)只在题目里没有
    多变量 print 时才拼接, 免得把 print(c,z,n) 的三行输出粘成一个数。
    """
    allow_bare = not _has_multi_print(text)
    lines = text.splitlines()
    out = []
    i = 0
    n = len(lines)
    while i < n:
        cur = lines[i]
        while i + 1 < n:
            nxt = lines[i + 1]
            if not _PURE_DIGIT_LINE.match(nxt):
                break
            if _ASSIGN_TAIL_DIGITS.match(cur):
                cur = cur.rstrip() + nxt.strip()
                i += 1
                continue
            if allow_bare and _BARE_DIGIT_LINE.match(cur):
                cur = cur.rstrip() + nxt.strip()
                i += 1
                continue
            break
        out.append(cur)
        i += 1
    return "\n".join(out)


def _pre_clean(text):
    """把 print 元组输出 / py2 长整型后缀 还原成标准 key=value"""
    text = _join_wrapped_numbers(text)
    text = _TUPLE_KV.sub(lambda m: "%s = %s" % (m.group(1), m.group(2)), text)
    text = _LONG_SUF.sub(lambda m: m.group(1), text)
    return text


_PRINT_VAR = re.compile(r"^\s*print\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)?\s*$")
# print pow(294,e,n) —— 已知底数, 拿来反推 e
_ORACLE_POW = re.compile(r"^pow\s*\(\s*(\d+)\s*,\s*e\s*,\s*[A-Za-z_][A-Za-z0-9_]*\s*\)$")
_BARE_NUM_LINE = re.compile(r"^\s*#*\s*(0[xX][0-9a-fA-F]+|\d+)[lL]?\s*$")


def _split_top_commas(s):
    """按顶层逗号切分, 括号内的逗号不切 (pow(294,e,n) 算一个整体)"""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out]


def _print_var_sequence(text):
    """收集所有 print 语句的变量顺序

    print(c,z,n)      -> ['c', 'z', 'n']
    print pow(294,e,n) -> [None]        (表达式, 只占输出位置)
    print c,n          -> ['c', 'n']
    """
    seq = []
    for ln in text.splitlines():
        s = ln.strip()
        if not s.startswith("print"):
            continue
        if s != "print" and s[5] not in " \t(":
            continue
        body = s[5:].strip()
        if body.startswith("(") and body.endswith(")"):
            body = body[1:-1]
        if not body:
            continue
        for part in _split_top_commas(body):
            part = part.strip().strip("'\"")
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", part):
                seq.append(part)
                continue
            # print pow(294,e,n) —— 底数已知的模幂, 输出值可以直接反推 e
            mo = _ORACLE_POW.match(part)
            if mo:
                seq.append(("__oracle__", int(mo.group(1))))
                continue
            seq.append(None)
    return seq


def _bare_number_lines(text):
    """只由数字/注释组成的行, 按出现顺序取出所有数字"""
    nums = []
    for ln in text.splitlines():
        s = ln.strip()
        if not re.fullmatch(r"[#\s]*(?:(?:0[xX][0-9a-fA-F]+|\d+)[\s,]*)+", s):
            continue
        if not re.search(r"\d{4,}|0[xX]", s):
            continue
        nums.extend(re.findall(r"0[xX][0-9a-fA-F]+|\d+", s))
    return nums


def _recover_print_output(text):
    """题目里直接粘 print 输出:

        c = pow(int(b2a_hex(flag),16),e,n)
        print c
        #27565231154623519221597938803435789010285480123476977081867877272451638645710

    print 后面那一行(常常被 # 注释掉)就是它的值。旧版解析不出来, 只能拿 p、q
    算出 d 就停, 密文一个都没认到 —— 这里把值补给对应字段。

    另外处理 print(a,b,c) 这种一次输出多个变量的写法: 按变量顺序对齐后面的
    裸数字行; 同名变量第二次出现时加后缀 (c -> c2, n -> n2)。
    """
    lines = text.splitlines()
    rec = {}
    # ---- 先做多变量 print 顺序对齐 (v3.3.1) ----
    # 连续两行 print(n) / print(c), 后面再跟两行注释数字时, 若先跑"print 下一行"
    # 的启发式, print(c) 会抢到紧跟其后的那个 n 值 —— n 和 c 变成同一个数,
    # 结果 pow(c,d,n)=0, 明文输出 0。所以顺序对齐必须优先, 且直接覆盖。
    seq = _print_var_sequence(text)
    aligned = False
    if seq and any(v for v in seq):
        nums = _bare_number_lines(text)
        if len(nums) >= len(seq):
            aligned = True
            seen = {}
            idx = 0
            for var in seq:
                if idx >= len(nums):
                    break
                if var is None:
                    idx += 1
                    continue
                if isinstance(var, tuple):
                    # pow(底数,e,n) 的输出: 记下底数和值, 用来反推 e
                    rec["__oracle_base"] = str(var[1])
                    rec["__oracle_val"] = nums[idx]
                    idx += 1
                    continue
                seen[var] = seen.get(var, 0) + 1
                key = var if seen[var] == 1 else "%s%d" % (var, seen[var])
                rec[key] = nums[idx]
                idx += 1

    if aligned:
        return rec

    # ---- 单变量 print: 紧跟其后的那一行(常被 # 注释掉)就是它的值 ----
    for i, ln in enumerate(lines):
        m = _PRINT_VAR.match(ln)
        if not m:
            continue
        var = m.group(1)
        for j in range(i + 1, min(i + 4, len(lines))):
            mm = _BARE_NUM_LINE.match(lines[j])
            if mm:
                rec.setdefault(var, mm.group(1))
                break
            nxt = lines[j].strip()
            if nxt and not nxt.startswith("#"):
                break
    return rec


def parse_text(text):
    """从纯文本里提取 key = value / key: value / 裸大整数"""
    text = _normalize_punct(_pre_clean(text))
    rec = _recover_print_output(text)
    env = {}
    pat = re.compile(r"^[ \t#]*([A-Za-z_][A-Za-z0-9_]*)\s*[:=]\s*(.+?)\s*$", re.M)
    for m in pat.finditer(text):
        k, v = m.group(1), m.group(2)
        v = v.rstrip(",").strip()
        if v.startswith("[") and v.endswith("]"):
            items = [x.strip() for x in v[1:-1].split(",") if x.strip()]
            nums = [_to_int(x) for x in items]
            if all(x is not None for x in nums):
                env[k] = nums
                continue
        num = _to_int(v)
        if num is not None:
            # 同一份题面里既写了真值、又写了 n = 1 / n = 0 这种循环初始化时，
            # 别让后面的占位值把前面的真值盖掉
            if (k in ("n", "N", "modulus", "c", "C") and num <= 1
                    and isinstance(env.get(k), int) and env[k] > 1):
                continue
            env[k] = num
            continue
        if v.startswith("'") or v.startswith('"'):
            env[k] = v.strip("'\"")

    # ---- 式子型泄露字段: p+q / (p±a)(q±a) ----
    # 先单独认出来, 再把这些片段从文本里抹掉; 否则 "p+q : 0x..." 里的 q
    # 会被内联扫描当成一个独立的 q 字段, 直接把 q 设成 p+q 的值
    for ms_ in _SUM_PAT.finditer(text):
        v = int_any(ms_.group(1))
        if v:
            env["__sum__"] = v
            break
    # p−q / p²−q² 同样先单独认, 再统一抹掉
    md_ = _DIFF_PAT.search(text)
    if md_:
        v = int_any(md_.group(1))
        if v:
            env["__diff__"] = v
    mq_ = _SQDIFF_PAT.search(text)
    if mq_:
        v = int_any(mq_.group(1))
        if v:
            env["__sqdiff__"] = v
    # "hint = p + q" 这种先赋中间变量再打印的写法, 记下变量名待回查
    for _pat, _tag in ((_EXPR_SUM_PAT, "__sum_var__"),
                      (_EXPR_DIFF_PAT, "__diff_var__"),
                      (_EXPR_SQDIFF_PAT, "__sqdiff_var__")):
        _m = _pat.search(text)
        if _m:
            env[_tag] = _m.group(1)
    masked = _LEAK_MASK.sub(" ", text)

    # ---- 内联宽松扫描 (v2.1) ----
    # 题干写成一整句 / 一行里塞多个 key=value 时, 上面按行首的规则会全部漏掉
    inline = {}
    for m in _INLINE_KV.finditer(masked):
        k, raw_v = m.group(1), m.group(2)
        if k in inline:
            continue
        num = _to_int(raw_v)
        if num is not None:
            inline[k] = num
    if sum(1 for k in inline if k.lower() in _CORE_KEYS) >= 2:
        for k, v in inline.items():
            env.setdefault(k, v)
        for k in [k for k in env if re.fullmatch(r"num\d+", k)]:
            del env[k]

    if not env:
        # 纯大整数: 按出现顺序编号
        nums = re.findall(r"\b\d{10,}\b|\b0x[0-9a-fA-F]{8,}\b", text)
        for i, x in enumerate(nums):
            n = _to_int(x)
            if n:
                env["num%d" % i] = n
    for k, v in rec.items():
        if k not in env:
            num = _to_int(v)
            if num is not None:
                env[k] = num
    ms = _SHIFT_PAT.search(text)
    if ms:
        s1, d1, s2, d2, val = ms.groups()
        if s1 == s2 and d1 == d2:
            # (p-2)(q-2) -> a = +2 ; (p+2)(q+2) -> a = -2
            a = int(d1) * (1 if s1 == "-" else -1)
            v = int_any(val)
            if v:
                env["__shift__"] = (a, v)
    # bytes_to_long("BJD"*32) 这类已知明文: e 未知时靠它爆破
    mk = re.search(r"bytes_to_long\(\s*['\"]([^'\"]{1,200})['\"]\s*(?:\*\s*(\d+))?\s*\)", text)
    if mk:
        try:
            data = mk.group(1).encode("utf-8")
            if mk.group(2):
                data = data * int(mk.group(2))
            if 0 < len(data) <= 4096:
                env["known_pt"] = int.from_bytes(data, "big")
        except Exception:
            pass

    # ---- 密文完全没标名字(常见: 题面写着 c = pow(flag,e,p*q), 下一行 # 一个长数字)----
    if not any(k.lower() in ("c", "ct", "ciphertext", "c1", "c2", "cs", "flag1", "flag2")
               for k in env):
        bare = [_to_int(x) for x in _bare_number_lines(text)]
        bare = [x for x in bare if x and x > 1000]
        if len(bare) == 1:
            env["c"] = bare[0]

    # ---- v3.5: print('flag= '+str(flag1)) 这种，flag 这个变量名装的是密文 ----
    if "c" not in env and not any(k.lower() in ("c1", "c2", "cs") for k in env):
        fv = env.get("flag")
        if isinstance(fv, int) and fv > (1 << 64):
            env["c"] = fv

    # ---- v3.2: flag 前缀 + 题面里的 nextprime(a·p ± b·q) 构造 ----
    mp = re.search(r"startswith\(\s*['\"]([^'\"]{1,60})['\"]\s*\)", text)
    if not mp:
        mp = re.search(r"(?m)^\s*flag\s*=\s*b?['\"]([^'\"]{1,80})['\"]", text)
    if mp:
        pf = mp.group(1).split("{")[0].encode()
        if 0 < len(pf) <= 32:
            env["__flag_prefix"] = pf
    tf = []
    for mtf in re.finditer(r"(\d+)\s*\*\s*p\s*([+-])\s*(\d+)\s*\*\s*q", text):
        item = (int(mtf.group(1)), int(mtf.group(3)), 1 if mtf.group(2) == "+" else -1)
        if item not in tf:
            tf.append(item)
    if tf:
        env["__transforms"] = tf

    # ---- v3.7: assert e1 * e2 == 3087 这类"只给指数乘积"的约束 ----
    mep = (re.search(r"\b[eE]1\s*\*\s*[eE]2\s*=+\s*(\d{1,12})\b", text)
           or re.search(r"\b[eE]2\s*\*\s*[eE]1\s*=+\s*(\d{1,12})\b", text))
    if mep:
        try:
            env["__e_product__"] = int(mep.group(1))
        except ValueError:
            pass

    # ---- v4.0: hint 变量名 / 中间变量 -> p±q 关系值 ----
    def _resolve_leak(tag, names, var_tag):
        if tag in env:
            return
        v = None
        vn = env.get(var_tag)
        if vn:
            v = _to_int(env.get(vn))
        if not isinstance(v, int) or v <= 0:
            for nm in names:
                t = _to_int(env.get(nm))
                if isinstance(t, int) and t > 0:
                    v = t
                    break
        if isinstance(v, int) and v > 0:
            env[tag] = v
        env.pop(var_tag, None)

    _resolve_leak("__sum__", _SUM_NAMES, "__sum_var__")
    _resolve_leak("__diff__", _DIFF_NAMES, "__diff_var__")
    _resolve_leak("__sqdiff__", _SQDIFF_NAMES, "__sqdiff_var__")

    # ---- v3.4: 整数等式泄露 (q + q*p^3 = A 这种) ----
    # 这类题根本不给 n, 只给几条 p、q 之间的整数关系式;
    # 先原样抽出来, 交给 normalize 放进 ctx["eqs"]
    eqs = extract_poly_eqs(text)
    if eqs:
        env["__eqs__"] = eqs
    return env


def normalize(env):
    """把解析出的变量映射成标准字段 + 启发式兜底"""
    ctx = {}
    used = set()
    if env.get("__eqs__"):
        ctx["eqs"] = env["__eqs__"]
    if env.get("__shift__"):
        ctx["phishift"] = env["__shift__"]
    if env.get("__sum__"):
        ctx["sum_pq"] = env["__sum__"]
    if env.get("__diff__"):
        ctx["diff_pq"] = env["__diff__"]
    if env.get("__sqdiff__"):
        ctx["sqdiff"] = env["__sqdiff__"]
    # p+q / p−q 这类"关系值"变量不能被当成 n（否则 n 会被设成 p+q 直接算错）
    for _nm in list(env):
        if _nm in _SUM_NAMES or _nm in _DIFF_NAMES or _nm in _SQDIFF_NAMES:
            used.add(_nm)
    _leak_vals = {v for v in (env.get("__sum__"), env.get("__diff__"),
                              env.get("__sqdiff__")) if isinstance(v, int)}
    if _leak_vals:
        for _nm, _vv in env.items():
            if not str(_nm).startswith("__") and _to_int(_vv) in _leak_vals:
                used.add(_nm)
    # print pow(294,e,n) 的输出: 底数 + 值, 用来反推未知的 e
    if env.get("__oracle_base") and env.get("__oracle_val"):
        ctx["oracle_base"] = _to_int(env["__oracle_base"])
        ctx["oracle_val"] = _to_int(env["__oracle_val"])
    # 同时给了 p+q 和 (p±a)(q±a): 先反解出 n, 免得后面的"按数值猜字段"拿 p+q 当 n
    if env.get("__shift__") and env.get("__sum__"):
        a, T = env["__shift__"]
        x = -a
        S_ = env["__sum__"]
        cand = T - x * S_ - x * x
        if cand > 0:
            ctx["n"] = cand
    for name, val in env.items():
        key = _ALIAS_MAP.get(name) or _ALIAS_MAP.get(name.lower())
        if key is None:
            continue
        if key in ("ns", "cs", "es"):
            lst = _to_list(val)
            if lst:
                ctx[key] = lst
                used.add(name)
            continue
        iv = _to_int(val)
        if iv is not None:
            ctx[key] = iv
            used.add(name)

    # 编号变量: e1/e2、c1/c2、n1/n2、p1/p2 -> 列表/字段
    groups = {}
    pat_num = re.compile(r"^([A-Za-z_]+?)(\d+)$")
    for name, val in env.items():
        mm_ = pat_num.match(name)
        if not mm_:
            continue
        stem = mm_.group(1).lower()
        idx = int(mm_.group(2))
        iv = _to_int(val)
        if iv is None:
            continue
        groups.setdefault(stem, []).append((idx, iv))
    for stem, items in groups.items():
        items.sort()
        vals = [v for _i, v in items]
        if stem in ("n", "modulus", "mod") and len(vals) >= 2 and "ns" not in ctx:
            ctx["ns"] = vals
            used.update("%s%d" % (stem, i) for i, _ in items)
        elif stem in ("c", "ct", "ciphertext", "flag", "enc") and len(vals) >= 2:
            if "cs" not in ctx:
                ctx["cs"] = vals
            ctx.setdefault("c1", vals[0])
            ctx.setdefault("c2", vals[1])
            used.update("%s%d" % (stem, i) for i, _ in items)
        elif stem in ("e", "exp") and len(vals) >= 2 and "es" not in ctx:
            ctx["es"] = vals
            used.update("%s%d" % (stem, i) for i, _ in items)
        elif stem in ("p", "prime") and len(vals) == 2 and "p" not in ctx and "q" not in ctx:
            ctx["p"], ctx["q"] = vals[0], vals[1]
            used.update("%s%d" % (stem, i) for i, _ in items)
        elif len(vals) == 1 and items[0][0] >= 2:
            # 只有 n2 / m2 这种单个带编号的字段: 原样保留, 别丢
            _k = "%s%d" % (stem, items[0][0])
            ctx[_k] = vals[0]
            used.add(_k)

    # 启发式: 名字对不上时按数值特征猜
    ints = []
    for name, val in env.items():
        if name in used or name.startswith("__"):
            continue
        iv = _to_int(val)
        if iv is not None and iv > 1000:
            ints.append((name, iv))
    ints.sort(key=lambda x: -x[1])

    _has_rel = bool(ctx.get("sum_pq") or ctx.get("diff_pq")
                    or ctx.get("sqdiff") or ctx.get("z"))
    if "n" not in ctx and ints and not _has_rel:
        ctx["n"] = ints[0][1]
    if ctx.get("cs") and "c" not in ctx:
        ctx["c"] = ctx["cs"][0]
    if "c" not in ctx and "n" in ctx and not ctx.get("cs"):
        nn = ctx["n"]
        # ints 里已经剔掉了被识别成字段的变量(含 n 自己)，所以从头上找，
        # 不能取 ints[1:] —— 那样当题面只有 "flag=密文 / n=模数" 两行时会全丢
        for name, v in ints:
            if v != nn and v < nn:
                ctx["c"] = v
                break
    if "e" not in ctx:
        common = (65537, 257, 17, 3, 5, 7, 11, 13)
        for cv in common:
            for name, val in env.items():
                if _to_int(val) == cv:
                    ctx["e"] = cv
                    break
            if "e" in ctx:
                break
    if "e" not in ctx and "n" in ctx:
        ctx["e"] = 65537
        ctx["e_is_default"] = True
    # 列表型 (ns/cs)
    if "ns" not in ctx:
        lists = []
        for name, val in env.items():
            lst = _to_list(val)
            if lst and len(lst) >= 2 and max(lst) > 1000:
                lists.append((name, lst))
        lists.sort(key=lambda x: -max(x[1]))
        if len(lists) >= 2:
            ctx.setdefault("ns", lists[0][1])
            ctx.setdefault("cs", lists[1][1])

    # ---- v3.2: 多组模数泄露 (P_n / P_F_n / Q_n / Q_E_D 这类命名) ----
    grp = {}
    for name, val in env.items():
        if name.startswith("__"):
            continue
        m2 = re.match(r"^([A-Za-z]{1,6})_(.+)$", name)
        if not m2:
            continue
        tag = m2.group(1).upper()
        tail = m2.group(2).lower().replace("_", "")
        iv = _to_int(val)
        if iv is None:
            continue
        if tail == "n":
            grp.setdefault(tag, {})["n"] = iv
        elif tail in ("fn", "phin", "phi", "phe", "euler"):
            grp.setdefault(tag, {})["phi"] = iv
        elif tail in ("ed", "de", "eed"):
            grp.setdefault(tag, {})["ed"] = iv
    grp = {k: v for k, v in grp.items() if v.get("n")}
    if grp:
        ctx["groups"] = grp
    # v3.5: 题面里任何"看起来是某种运算结果"的大整数都留一份，供泄露型攻击试 gcd
    if ctx.get("n"):
        nn = ctx["n"]
        leaks = []
        for k2, v2 in env.items():
            if k2.startswith("__"):
                continue
            iv2 = _to_int(v2)
            if iv2 and 1 < iv2 < nn and iv2.bit_length() >= 64:
                leaks.append(iv2)
        if leaks:
            ctx["leak_vals"] = leaks
    if env.get("__flag_prefix"):
        ctx["flag_prefix"] = env["__flag_prefix"]
    if env.get("__e_product__"):
        try:
            ctx["e_product"] = int(env["__e_product__"])
        except (TypeError, ValueError):
            pass
    if env.get("__transforms"):
        ctx["transforms"] = env["__transforms"]

    _core_vals = set()
    for _k in ("n", "c", "e", "d", "phi", "p", "q", "dp", "dq", "m1", "m2", "ph", "mh"):
        _vv = ctx.get(_k)
        if isinstance(_vv, int):
            _core_vals.add(_vv)
    _c_now, _n_now = ctx.get("c"), ctx.get("n")
    spares = []
    for _nm, _vv in env.items():
        if str(_nm).startswith("__"):
            continue
        _iv = _to_int(_vv)
        if not isinstance(_iv, int) or _iv <= (1 << 63):
            continue
        if _iv in _core_vals:
            continue
        if _iv not in spares:
            spares.append(_iv)
    if spares:
        ctx["spare_ints"] = spares[:8]
    return ctx


# ============================================================
# 10.5 多实例(批量题库)模式  —— v2 新增
# ============================================================

SMALL_E_CANDIDATES = (3, 5, 7, 11, 13, 17)

_KV_LINE = re.compile(
    r"(?m)^\s*([A-Za-z_][A-Za-z0-9_]*)\s*[:=]\s*(0[xX][0-9a-fA-F]+|\d+)\s*,?\s*$")


def split_instances(text):
    """把一段文字里 N 组 n/c 拆成独立实例 [{n,c,e}, ...]"""
    text = _normalize_punct(text)
    insts, cur = [], {}
    for m in _KV_LINE.finditer(text):
        k = m.group(1).lower()
        if k in ("n", "modulus", "mod", "nn"):
            k = "n"
        elif k in ("c", "ct", "ciphertext", "cipher", "enc"):
            k = "c"
        elif k in ("e", "exp", "exponent"):
            k = "e"
        else:
            continue
        v = int_any(m.group(2))
        if v is None:
            continue
        if k == "n" and "n" in cur:
            if "c" in cur:
                insts.append(cur)
            cur = {}
        cur[k] = v
    if cur.get("n") and "c" in cur:
        insts.append(cur)
    return insts


def _inst_result(inst, base_e, effort, idx):
    env = {"n": inst["n"], "c": inst["c"]}
    if inst.get("e"):
        env["e"] = inst["e"]
    elif base_e:
        env["e"] = base_e
    ctx = normalize(env)
    ctx = fill_derived(ctx)
    att, res, trace = solve(ctx, effort=effort)
    return {"idx": idx, "n": inst["n"], "c": inst["c"], "e": env.get("e"),
            "ctx": ctx, "att": att, "res": res, "trace": trace}


def cross_attacks(inst_results, insts, base_e):
    """跨实例关系: 共享素因子 / 共模 / 同指数广播"""
    hits = {}

    def put(k, why, m, extra=None):
        if k not in hits:
            hits[k] = {"why": why, "m": m, "extra": extra or {}}

    # 1) 任意两组共享素因子
    N = min(len(insts), len(inst_results))
    for a in range(N):
        for b in range(a + 1, N):
            na, nb = insts[a].get("n"), insts[b].get("n")
            if not na or not nb or na == nb:
                continue
            g = math.gcd(na, nb)
            if not (1 < g < min(na, nb)):
                continue
            for k, other in ((a, b + 1), (b, a + 1)):
                nk, ck = insts[k].get("n"), insts[k].get("c")
                p, q = g, nk // g
                if p * q != nk:
                    continue
                e = insts[k].get("e") or base_e
                m, info = decrypt_standard(nk, e, ck, [p, q])
                if m is not None:
                    put(k, "与第 %d 组共享 %d 位素因子" % (other, g.bit_length()), m,
                        {"p": p, "q": q, "d": info.get("d")})

    # 2) 同一个 n 用不同 e 加密 (跨实例共模)
    byn = {}
    for i, inst in enumerate(insts):
        if inst.get("n") and inst.get("c") is not None:
            byn.setdefault(inst["n"], []).append(i)
    for n, idxs in byn.items():
        if len(idxs) < 2:
            continue
        for x in range(len(idxs)):
            for y in range(x + 1, len(idxs)):
                i, j = idxs[x], idxs[y]
                e1 = insts[i].get("e") or base_e
                e2 = insts[j].get("e") or base_e
                if e1 == e2:
                    continue
                g, s1, s2 = egcd(e1, e2)
                if g != 1:
                    continue
                c1, c2 = insts[i]["c"], insts[j]["c"]
                try:
                    if s1 < 0:
                        c1 = modinv(c1, n); s1 = -s1
                    if s2 < 0:
                        c2 = modinv(c2, n); s2 = -s2
                    m = pow(c1, s1, n) * pow(c2, s2, n) % n
                except Exception:
                    continue
                if pow(m, e1, n) == insts[i]["c"] % n:
                    put(i, "与第 %d 组共模 (e1=%d, e2=%d)" % (j + 1, e1, e2), m)

    # 3) 同一个小 e 的多组广播
    groups = {}
    for i, inst in enumerate(insts):
        e = inst.get("e") or base_e
        if not (inst.get("n") and inst.get("c") is not None):
            continue
        if e is None:
            cand = SMALL_E_CANDIDATES          # 题目没写指数 -> 自动试小指数
        elif 2 <= e <= 64:
            cand = [e]
        else:
            cand = []
        for ke in cand:
            groups.setdefault(ke, []).append(i)
    for e, idxs in groups.items():
        if len(idxs) < 2:
            continue
        x, mod = 0, 1
        ok = True
        for i in idxs:
            ni = insts[i]["n"]
            if math.gcd(mod, ni) != 1:
                ok = False
                break
            x, mod = crt_pair(x, mod, insts[i]["c"] % ni, ni)
        if not ok:
            continue
        r, exact = iroot(x, e)
        if exact:
            for i in idxs:
                put(i, "与其他 %d 组同指数 e=%d 广播" % (len(idxs) - 1, e), r)

    return hits


def render_brief(m):
    info = render_m(m)
    if "text" in info:
        t = info["text"]
        t = "".join(ch if 32 <= ord(ch) < 127 or ch in "\r\n\t" else "." for ch in t)
        return t.strip()
    if "unpadded" in info:
        return info["unpadded"].decode("utf-8", "replace")
    if "ascii_run" in info:
        return info["ascii_run"].decode("ascii", "replace")
    return repr(info["bytes"][:60])


def run_multi(insts, base_e, args):
    t0 = time.time()
    if not args.json and not args.quiet:
        print("═" * 60)
        print("  " + BANNER + "   多组模式")
        print("═" * 60)
        print_announce()
        print()
        print("  识别到 %d 组独立题目 (n/c 成对)" % len(insts))
        bits = sorted({i["n"].bit_length() for i in insts})
        print("  模数位数 : %s" % bits)
        if any(i.get("e") for i in insts):
            eshow = "各组自带"
        elif base_e:
            eshow = str(base_e)
        else:
            eshow = "题目未给 -> 自动探测 " + "/".join(str(x) for x in SMALL_E_CANDIDATES)
        print("  指数     : %s" % eshow)

    if not args.json and not args.quiet:
        print("  【正在逐组求解】...")
    results = []
    for k, inst in enumerate(insts, 1):
        results.append(_inst_result(inst, base_e, args.effort, k))

    hits = cross_attacks(results, insts, base_e)

    solved = []
    for r in results:
        k = r["idx"] - 1
        if r["res"]:
            solved.append((r["idx"], r["att"]["name"], r["res"].m, "单独解出"))
        elif k in hits:
            h = hits[k]
            solved.append((r["idx"], "跨组关系", h["m"], h["why"]))
    elapsed = time.time() - t0

    if args.json:
        out = {
            "ok": bool(solved),
            "instances": len(insts),
            "elapsed": round(elapsed, 3),
            "solved": [{"index": i, "type": t, "m": m, "m_hex": hex(m),
                        "text": render_brief(m), "why": w} for i, t, m, w in solved],
            "unsolved": [r["idx"] for r in results
                         if not r["res"] and (r["idx"] - 1) not in hits],
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return 0 if solved else 1

    print("\n[结果]")
    print("  %-4s %-10s %-26s %s" % ("组号", "状态", "命中方式", "明文 / flag"))
    print("  " + "-" * 56)
    for r in results:
        k = r["idx"] - 1
        if r["res"]:
            print("  #%-3d %-10s %-26s %s" % (r["idx"], "✅ 解出", r["att"]["name"], render_brief(r["res"].m)))
        elif k in hits:
            print("  #%-3d %-10s %-26s %s" % (r["idx"], "✅ 解出", "跨组关系", render_brief(hits[k]["m"])))
        else:
            att = r["att"]
            print("  #%-3d %-10s %-26s %s" % (r["idx"], "× 未解出", "-", "n=%d bit 无泄露" % r["n"].bit_length()))

    if hits and not args.quiet:
        print("\n[跨组关系]")
        for k, h in sorted(hits.items()):
            print("  · 第 %d 组: %s" % (k + 1, h["why"]))

    flags = []
    for i, t, m, w in solved:
        txt = render_brief(m)
        if txt not in flags:
            flags.append(txt)
    if flags:
        print("\n[flag 汇总]")
        for f in flags:
            print("  %s" % f)

    n_ok = len(solved)
    print("\n完成: %d/%d 组解出, 用时 %.2fs" % (n_ok, len(insts), elapsed))
    if n_ok < len(insts):
        print("  没解出的组是「n 位数够大 + 题目没给任何泄露」的,这种本来就需要额外 hint 或外部算力")
    return 0 if solved else 1


def detect_base5_in_text(text):
    cnt = 0
    for m in re.finditer(r"\b[0-4]{25,}\b", text):
        if detect_number_base(m.group(0)) == 5:
            cnt += 1
    return cnt


def _safe_isfile(target):
    """多行题面文本传给 os.path.isfile 会抛 OSError, 这里兜住"""
    try:
        return os.path.isfile(target)
    except (OSError, ValueError):
        return False


def _is_junk_value(key, val):
    """ast 解析拿到的“初始化占位值”。

    典型写法:
        n = 1
        for i in range(15):
            n *= getPrime(32)          # AugAssign, ast 求不出值
    结果 env["n"] 永远停在第 1 行的 1，真正的 n 只出现在题面注释/输出里。
    这类占位值必须让位给文本里抓到的真值，否则整个求解过程拿 n=1 在算。
    """
    iv = _to_int(val)
    if iv is None:
        return False
    kl = str(key).lower()
    if kl in ("n", "modulus", "mod", "nn", "pubkey_n"):
        return iv <= 1
    if kl in ("e", "exp", "exponent", "ee", "pubkey_e"):
        return iv <= 1
    if kl in ("c", "ct", "ciphertext", "enc", "cipher", "cc"):
        return iv <= 0
    return iv < 0


def load_challenge(target):
    """target: 文件路径 / '-' stdin / 直接文本"""
    raw_text = ""
    env = {}
    if target == "-":
        raw_text = sys.stdin.read()
        env = parse_text(raw_text)
    elif _safe_isfile(target):
        if target.lower().endswith(".py"):
            env, raw_text = parse_py_file(target)
            # .py 里不一定都是 Python 赋值: 很多人直接把题目原文存成 .py,
            # 或者脚本是 py2 语法(ast 解析失败). 这时回退到文本解析, 否则整个文件白读
            # v3.3: ast 只看得到赋值, 注释里的值一律看不见 —— 而 CTF 题面的密文、
            # 私钥 d 常常就是 `# c = ...` / `#c = ...` 注释掉的。所以不设门槛,
            # 文本解析的结果一律作为兜底补进来(ast 认到的优先, setdefault 不覆盖)。
            for k, v in parse_text(raw_text).items():
                if k in env and _is_junk_value(k, env[k]) and not _is_junk_value(k, v):
                    env[k] = v      # ast 只拿到 n = 1 这种占位值, 用文本里的真值顶上
                else:
                    env.setdefault(k, v)
        elif target.lower().endswith(".json"):
            with open(target) as f:
                data = json.load(f)
            env = {k: v for k, v in data.items()}
            raw_text = json.dumps(data)[:2000]
            if sum(1 for k in env if k.lower() in _CORE_KEYS) < 2:
                for k, v in parse_text(json.dumps(data, ensure_ascii=False)).items():
                    env.setdefault(k, v)
        else:
            with open(target, "rb") as f:
                raw_text = f.read().decode("utf-8", "replace")
            env = parse_text(raw_text)
    else:
        raw_text = target
        env = parse_text(target)
    # 兜底: 任何后缀如果还没认够字段, 再按文本宽松扫一遍
    if sum(1 for k in env if k.lower() in _CORE_KEYS) < 2 and raw_text:
        for k, v in parse_text(raw_text).items():
            env.setdefault(k, v)
    # v3.2: flag 前缀 / nextprime 线性组合这类附加信息, 不管什么后缀都从原文再捞一遍
    if raw_text:
        for k, v in parse_text(raw_text).items():
            if k.startswith("__") and k not in env:
                env[k] = v
    return normalize(env), env, raw_text


# ============================================================
# 11. 题型判定
# ============================================================

def diagnose(ctx):
    """根据字段组合 + 数值特征给出题型判断 (列表 of (类型, 依据))"""
    out = []
    n, e, c = ctx.get("n"), ctx.get("e"), ctx.get("c")
    ns, cs, es = ctx.get("ns") or [], ctx.get("cs") or [], ctx.get("es") or []

    if ctx.get("d"):
        out.append(("已知私钥 d", "题目给出了 d"))
    if ctx.get("sum_pq") and ctx.get("phishift"):
        out.append(("p+q 与 (p±a)(q±a) 泄露",
                    "两个式子联立还原 n 和 p、q（(p+x)(q+x) = n + x(p+q) + x²）"))
    elif ctx.get("sum_pq"):
        out.append(("p+q 泄露", "题目给出了 p+q，配 n 可解二次方程拿 p、q"))
    if ctx.get("phi"):
        out.append(("已知 φ(n)", "题目给出了 phi"))
    if ctx.get("p") and ctx.get("q"):
        out.append(("已知素因子", "题目给出了 p、q"))
    if ctx.get("dp") or ctx.get("dq"):
        out.append(("CRT 参数泄露", "题目给出了 dp/dq"))
    if ctx.get("ph") or ctx.get("p_high"):
        out.append(("p 高位泄露", "题目给出了 p 的部分比特"))
    if ctx.get("m_high") or ctx.get("mh"):
        out.append(("明文部分已知", "题目给出了 m 的部分比特"))
    if e == 1:
        out.append(("e = 1", "指数为 1"))
    if e == 2:
        out.append(("Rabin 体制", "e = 2，平方加密"))
    if e and n and e > n:
        out.append(("e 过大（等价小 d）", "e > n，试 Wiener"))
    if len(ns) >= 2 and es and len(set(es)) >= 2:
        out.append(("共模攻击", "同一 n、多个 e 加密同一明文"))
    if len(ns) >= 2 and len(set(es or [e])) == 1:
        out.append(("多组同 e（广播/共享素因子）", "%d 组 (n,c) 且 e 相同" % len(ns)))
    if len(cs) >= 2 and ctx.get("c1") and ctx.get("c2"):
        out.append(("相关消息攻击", "两组密文"))
    if n and e and e <= 7:
        out.append(("低加密指数小明文", "e 很小（%d），密文可能没绕模" % e))
    if n:
        if n.bit_length() <= 256:
            out.append(("n 可分解", "n 只有 %d bit" % n.bit_length()))
        if is_perfect_square(n):
            out.append(("n 是平方数", "p = q"))
    return out


# ============================================================
# 12. 求解主流程
# ============================================================

def _set_pq(ctx, p, q, kind):
    """校验后写入 p、q（p·q 必须等于题面 n）"""
    if p <= 1 or q <= 1 or p == q:
        return False
    n = ctx.get("n")
    if n and p * q != n:
        # 题面里的 n 可能只是把 p+q / p−q 误当成了模数: 这种就按关系式算出的乘积为准
        if n in (ctx.get("sum_pq"), ctx.get("diff_pq"), ctx.get("z"), ctx.get("sqdiff")):
            ctx["n"] = p * q
        else:
            return False
    if not ctx.get("n"):
        ctx["n"] = p * q
    ctx["p"], ctx["q"] = p, q
    ctx["factors"] = [p, q]
    ctx["leak_pq_kind"] = kind
    return True


def _solve_pq_relation(ctx):
    """p±q 关系型泄露统一处理:

    · 给了 p+q 和 p−q        → 直接联立（n 都能省）
    · 只给 p−q 和 n          → (p+q)² = (p−q)² + 4n
    · 只给 p−q 和 phi        → phi = n − (p+q) + 1 → 和，再联立
    · 给 p²−q² 和 n          → S² = 2n + √(4n² + K²)
    · 给 p²+q² 和 n          → (p+q)² = p²+q² + 2n
    · 给 p²+q² 和 p−q        → 同上反推
    · 给 p+q 和 n            → 解 x² − (p+q)x + n = 0
    """
    if ctx.get("factors"):
        return
    n = ctx.get("n")
    S, T = ctx.get("sum_pq"), ctx.get("diff_pq")
    Z, K = ctx.get("z"), ctx.get("sqdiff")
    phi = ctx.get("phi")

    # phi + (p−q) → 先换出 p+q
    if phi and n and T and not S:
        S_ = n - phi + 1
        if S_ > 0:
            S = S_

    # phi + (p−q)，连 n 都没给: (p+q−2)² = (p−q)² + 4φ
    if phi and T and not n:
        s2 = T * T + 4 * phi
        r = math.isqrt(s2)
        if r * r == s2:
            Sx = r + 2
            if (Sx + T) % 2 == 0:
                if _set_pq(ctx, (Sx + T) // 2, (Sx - T) // 2,
                           "给了 φ 和 p−q，(p+q−2)² = (p−q)² + 4φ → 反解 p+q 再劈开"):
                    return

    # phi + (p+q)，连 n 都没给: (p−q)² = (p+q−2)² − 4φ
    if phi and S and not n:
        t2 = (S - 2) * (S - 2) - 4 * phi
        r = math.isqrt(t2) if t2 >= 0 else -1
        if r >= 0 and r * r == t2 and (S + r) % 2 == 0:
            if _set_pq(ctx, (S + r) // 2, (S - r) // 2,
                       "给了 φ 和 p+q，(p−q)² = (p+q−2)² − 4φ → 反解 p−q 再劈开"):
                return

    # 1) 和 + 差
    if S and T and (S + T) % 2 == 0 and (S - T) % 2 == 0:
        if _set_pq(ctx, (S + T) // 2, (S - T) // 2,
                   "给了 p+q 和 p−q → 直接联立 p=(S+T)/2、q=(S−T)/2"):
            return

    # 2) 差 + n
    if T and n and not S:
        disc = T * T + 4 * n
        r = math.isqrt(disc)
        if r * r == disc and (r + T) % 2 == 0:
            if _set_pq(ctx, (r + T) // 2, (r - T) // 2,
                       "给了 p−q，用 (p+q)² = (p−q)² + 4n 反解 p+q 再劈开"):
                return

    # 3) p²−q² 平方差 + n
    if K and n:
        d = math.isqrt(4 * n * n + K * K)
        if d * d == 4 * n * n + K * K:
            s2 = 2 * n + d
            Sx = math.isqrt(s2)
            if Sx * Sx == s2 and Sx:
                Tx = K // Sx
                if Tx * Sx == K and Sx * Sx - Tx * Tx == 4 * n:
                    if _set_pq(ctx, (Sx + Tx) // 2, (Sx - Tx) // 2,
                               "给了 p²−q² = (p+q)(p−q)，联立 4n 反解"):
                        return

    # 4) p²+q² + n
    if Z and n:
        s2 = Z + 2 * n
        Sx = math.isqrt(s2)
        if Sx * Sx == s2:
            disc = s2 - 4 * n
            r = math.isqrt(disc) if disc >= 0 else -1
            if r >= 0 and r * r == disc and (Sx + r) % 2 == 0:
                if _set_pq(ctx, (Sx + r) // 2, (Sx - r) // 2,
                           "给了 p²+q²，用 (p+q)² = p²+q² + 2n 反解"):
                    return

    # 5) p²+q² + 差（没给 n）
    if Z and T and not n:
        s2 = 2 * Z - T * T
        Sx = math.isqrt(s2) if s2 > 0 else 0
        if Sx * Sx == s2 and Sx:
            if _set_pq(ctx, (Sx + T) // 2, (Sx - T) // 2,
                       "给了 p−q 和 p²+q²，联立解出 p、q"):
                return

    # 6) 和 + n
    if S and n:
        disc = S * S - 4 * n
        if disc >= 0:
            r = math.isqrt(disc)
            if r * r == disc and (S + r) % 2 == 0:
                if _set_pq(ctx, (S + r) // 2, (S - r) // 2,
                           "给了 p+q，解 x² − (p+q)·x + n = 0"):
                    return


def fill_derived(ctx):
    """补齐派生字段"""
    n, e = ctx.get("n"), ctx.get("e")

    # 式子型泄露: 题里给了 p+q 和 (p±a)(q±a), 就能反解出 n
    #   (p+x)(q+x) = pq + x(p+q) + x² = n + x·S + x²
    leak, S = ctx.get("phishift"), ctx.get("sum_pq")
    if leak and S and not n:
        a, T = leak
        x = -a                      # 与 parse_text 里的记号对齐: (p-a) -> a>0
        cand = T - x * S - x * x
        if cand > 0:
            ctx["n"] = n = cand
            
    # ---- v4.0: p±q 关系型泄露（和 / 差 / 平方差 / 平方和）----
    if not ctx.get("factors"):
        _solve_pq_relation(ctx)

    # p、q -> n
    if ctx.get("p") and ctx.get("q") and not n:
        ctx["n"] = ctx["p"] * ctx["q"]
        n = ctx["n"]
    if ctx.get("p") and ctx.get("q") and ctx.get("n"):
        if ctx["p"] * ctx["q"] == ctx["n"]:
            ctx["factors"] = [ctx["p"], ctx["q"]]
    # d -> p,q
    if ctx.get("d") and n and e and not ctx.get("factors"):
        pq = factor_with_d(n, e, ctx["d"])
        if pq:
            ctx["p"], ctx["q"] = pq
            ctx["factors"] = [pq[0], pq[1]]
    # phi -> p,q
    if ctx.get("phi") and n and not ctx.get("factors"):
        s = n - ctx["phi"] + 1
        disc = s * s - 4 * n
        if disc >= 0:
            t = math.isqrt(disc)
            if t * t == disc and (s + t) % 2 == 0:
                p = (s + t) // 2
                q = (s - t) // 2
                if p * q == n:
                    ctx["p"], ctx["q"] = p, q
                    ctx["factors"] = [p, q]
    # ns -> n
    if not ctx.get("n") and ctx.get("cs") and n is None:
        pass
    if ctx.get("ns") and not ctx.get("n"):
        ctx["n"] = ctx["ns"][0]
    if ctx.get("cs") and ctx.get("c") is None:
        ctx["c"] = ctx["cs"][0]
    if ctx.get("es") and not ctx.get("e"):
        ctx["e"] = ctx["es"][0]
    # ---- v3.2: 每组模数各自的泄露 (n+φ / n+e·d) 反解 p,q ----
    if ctx.get("groups"):
        got = []
        for tag, gd in ctx["groups"].items():
            n_ = gd.get("n")
            pq = None
            if gd.get("phi"):
                pq = _pq_from_n_phi(n_, gd["phi"])
            if pq is None and gd.get("ed"):
                pq = _pq_from_n_ed(n_, gd["ed"])
            if pq:
                got.append((tag, pq[0], pq[1]))
        if got:
            ctx["group_pq"] = got
            if len(got) == 1 and not ctx.get("factors"):
                ctx["p"], ctx["q"] = got[0][1], got[0][2]
                ctx["n"] = ctx["p"] * ctx["q"]
                ctx["factors"] = [ctx["p"], ctx["q"]]
    return ctx


def solve(ctx, verbose=True, effort=2):
    """按优先级跑所有攻击, 返回 (hit_attack, Result, trace)"""
    trace = []
    # v2.7: e 未知时先把 e 反推出来, 否则后面每个模块都拿错的 e 一路跑到底
    if not ctx.get("e") or ctx.get("e_is_default"):
        got = recover_unknown_e(ctx)
        if got:
            trace.append(("反推加密指数 e", "命中 e = %d" % got, 0))
    ordered = sorted(ATTACKS, key=lambda a: ATTACK_ORDER.index(a["name"])
                     if a["name"] in ATTACK_ORDER else 99)
    for att in ordered:
        t0 = time.time()
        try:
            res = att["fn"](ctx)
        except Exception as ex:
            trace.append((att["name"], "异常: %s" % ex, 0))
            continue
        dt = time.time() - t0
        if res and res.ok:
            trace.append((att["name"], "命中", dt))
            return att, res, trace
        trace.append((att["name"], "未命中", dt))
    return None, None, trace


ATTACK_ORDER = [
    "e = 1",
    "整数等式泄露 (q·f(p) = 常数)",
    "只给 d、没给 n（p、q 挨着 / nextPrime 型）",
    "已知私钥 d",
    "已知 p±q 关系（和 / 差 / 平方差 / 平方和）",
    "p±q 两个未命名大数（无 n）",
    "已知 p、q",
    "已知 phi",
    "泄露 φ/λ 的倍数（lcm 型）",
    "素因子偏移泄露 (p±a)(q±a)",
    "已知 dp、dq / CRT 参数",
    "n 为素数",
    "n 为素数 · e 与 n−1 不互素",
    "n 为素数幂",
    "模不互素",
    "e 未知 · 共享素因子",
    "模下幂泄露 (P≡p^k mod n)",
    "共模攻击",
    "共模 · e1·e2 = 常数",
    "低加密指数 · 多组广播 (Håstad)",
    "n 可分解",
    "泄露 p²+q²",
    "两段明文 (和 / 立方和)",
    "多素数 RSA",
    "低加密指数 · 小明文",
    "已知明文部分 (Coppersmith)",
    "Rabin (e = 2)",
    "已知 p 高位 (Coppersmith)",
    "Franklin-Reiter 相关消息",
    "Wiener 攻击",
    "多组泄露 + nextprime 线性组合",
    "e 与 φ(n) 不互素",
]

# ============================================================
# 13. 输出
# ============================================================

BANNER = "RSA 自动解题器 v" + __version__

# ============================================================
# 启动公告（换公告只改 ANNOUNCE 这三行，别处不用动）
# ============================================================
ANNOUNCE = {
    "title": "终于可以耍起了耶",
    "sub": "耍起耍起耍起 ~",
    "by": "——by 我脑子有问题",
}


def announce_text(indent="  "):
    """公告文本（多行字符串）。indent 配合各处已有的缩进。"""
    return "\n".join([
        indent + "【公告】" + ANNOUNCE["title"],
        indent + "        " + ANNOUNCE["sub"],
        indent + "        " + ANNOUNCE["by"],
    ])


def print_announce(indent="  "):
    """打印公告。只在给人看的启动界面/帮助里调，别放进 --json / --quiet 的输出里。"""
    print(announce_text(indent))



def _setup_stdout():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass


def hx(x, maxlen=64):
    if x is None:
        return "None"
    s = hex(x)
    if len(s) > maxlen:
        return s[:maxlen] + "…(%d bit)" % x.bit_length()
    return s


def show_int(label, v, indent="  "):
    if v is None:
        return
    print("%s%-10s %d bit   %s" % (indent, label, v.bit_length(), hx(v, 48)))


def render_m(m):
    """把 m 渲染成多种形式"""
    b = int_to_bytes(m)
    out = {"int": m, "hex": hex(m), "bytes": b, "len": len(b)}
    try:
        txt = b.decode("utf-8")
        if all(0x09 <= ord(ch) or ch in "\r\n" for ch in txt):
            out["text"] = txt
    except Exception:
        pass
    # PKCS#1 v1.5 去填充
    if b[:2] == b"\x00\x02":
        i = b.find(b"\x00", 2)
        if i > 0:
            out["unpadded"] = b[i + 1:]
    # 找里面的 flag 形态
    if "text" not in out:
        m2 = re.search(rb"[ -~]{4,}", b)
        if m2:
            out["ascii_run"] = m2.group()
    return out


def print_result(att, res, trace, ctx, quiet=False):
    m = res.m
    info = render_m(m) if m is not None else {}
    print("")
    print("━" * 52)
    print("  命中题型: %s" % att["name"])
    print("  判定依据: %s" % res.detail)
    print("━" * 52)
    if m is not None:
        print("  明文 int : %d" % m)
        print("  明文 hex : %s" % hex(m))
    if "text" in info:
        print("  明文文本 : %s" % info["text"])
    elif "unpadded" in info:
        try:
            print("  明文文本 : %s" % info["unpadded"].decode("utf-8"))
        except Exception:
            print("  解密后(去填充): %r" % info["unpadded"])
    elif "ascii_run" in info:
        print("  可打印片段: %s" % info["ascii_run"].decode("ascii", "replace"))
    elif m is not None:
        print("  明文字节 : %r" % info["bytes"][:80])
    if res.extra:
        for k, v in res.extra.items():
            if isinstance(v, int) and v.bit_length() > 128:
                print("  %-6s : %s" % (k, hx(v)))
            else:
                print("  %-6s : %s" % (k, v))
    if res.cands and len(res.cands) > 1 and not quiet:
        print("  其他候选 (%d 个):" % (len(res.cands) - 1))
        cnt = 0
        for cand in res.cands:
            if cand == m:
                continue
            try:
                t = int_to_bytes(cand).decode("utf-8")
                print("      %s" % t[:120])
            except Exception:
                print("      %s" % hex(cand)[:80])
            cnt += 1
            if cnt >= 5:
                break
    # 很多题最终要的是 md5(hex(d))，解出 d 就顺手算一份
    _dv = None
    if isinstance(res.extra, dict) and isinstance(res.extra.get("d"), int):
        _dv = res.extra["d"]
    if _dv is None and isinstance(ctx, dict) and isinstance(ctx.get("d"), int):
        _dv = ctx["d"]
    if _dv:
        # v2.7: 自校验, 让使用者能自己确认 d 是不是真的对 (而不是只看到一个哈希)
        _ex = res.extra if isinstance(res.extra, dict) else {}
        _n2 = ctx.get("n") if isinstance(ctx, dict) else None
        _p2 = _ex.get("p") if isinstance(_ex.get("p"), int) else None
        _q2 = _ex.get("q") if isinstance(_ex.get("q"), int) else None
        _e2 = _ex.get("e") if isinstance(_ex.get("e"), int) else (ctx.get("e") if isinstance(ctx, dict) and isinstance(ctx.get("e"), int) else None)
        if _p2 and _q2 and _n2:
            print("  自校验     : p * q == n            %s" % ("通过" if _p2 * _q2 == _n2 else "不通过"))
        if _e2 and _p2 and _q2:
            _phi2 = (_p2 - 1) * (_q2 - 1)
            print("  自校验     : e*d ≡ 1 (mod φ(n))   %s" % ("通过" if (_e2 * _dv - 1) % _phi2 == 0 else "不通过"))
        _md5_tags = _print_d_md5(_dv, has_plain_flag=bool(_find_flag_text(info)))
    else:
        _md5_tags = []
    print("━" * 52)
    _print_flag_box(info, _md5_tags)


_FLAG_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]{1,20}\{[ -~]{3,}\}")


def _py2_sanitize(text):
    """v3.7: 把题面里挡路的 py2 语法就地降级，让 ast 能读（只做文本级改写，不执行）

    要处理的就三种，全是 CTF 题面高频：
      1. 长整型后缀   n = 123456789L  /  0xdeadbeefL
      2. print 语句   print c,n       -> print(c, n)
      3. except 子句  except X, e:    -> except X as e:
    """
    if not text:
        return text
    out = []
    for line in text.split("\n"):
        # print x, y  ->  print(x, y)
        m = re.match(r"^(\s*)print\s+(?!\s*[\(])(.+?)\s*$", line)
        if m and not line.lstrip().startswith("#"):
            line = "%sprint(%s)" % (m.group(1), m.group(2))
        m = re.match(r"^(\s*)except\s+([\w\.\(\)]+)\s*,\s*(\w+)\s*:\s*$", line)
        if m:
            line = "%sexcept %s as %s:" % (m.group(1), m.group(2), m.group(3))
        out.append(line)
    s = "\n".join(out)
    # 数字/十六进制后面的 L 后缀
    s = re.sub(r"\b(0[xX][0-9a-fA-F]+|\d+)L\b", r"\1", s)
    return s


def _py2_likely(raw):
    """题面是不是 Python 2 写的。返回 True / False / None(看不出来)

    为什么要判: 很多题最后一行是 hashlib.md5(hex(d)).hexdigest(),
    而 Python 2 里 d 是 long 型, hex(d) 会带一个 'L' 后缀 -> '0x...L',
    Python 3 没有。同一个 d, 两种 hex 写法, md5 出来是两个完全不同的值。
    """
    if not raw:
        return None
    score = 0
    if re.search(r"(?m)^\s*print\s+(?!\()[^=\s]", raw):
        score += 2                      # print x   而不是 print(x)
    if re.search(r"\b(xrange|raw_input|iteritems|itervalues|has_key|basestring)\b", raw):
        score += 2
    if re.search(r"(?m)^\s*except\s+\w+\s*,\s*\w+\s*:", raw):
        score += 2                      # except X, e:
    if re.search(r"(?m)^\s*print\(", raw) or re.search(r"(?m)^\s*print\(.*\)\s*$", raw):
        score -= 1
    if re.search(r"""\bf["']""", raw):
        score -= 2                      # f-string 只有 py3
    if score >= 2:
        return True
    if score <= -1:
        return False
    return None


def _md5_of_hex(d_):
    return {
        "py3": hashlib.md5(hex(d_).encode()).hexdigest(),
        "py2": hashlib.md5((hex(d_) + "L").encode()).hexdigest(),
    }


def _print_d_md5(d_, has_plain_flag=False):
    """算出 md5(hex(d)) 的两种写法。返回 [(flag 形式, 标签)] 供 FLAG 框使用"""
    v = _md5_of_hex(d_)
    py2 = _py2_likely(_RAW_SRC.get("text", ""))
    if has_plain_flag:
        print("  md5(hex(d)) : py3 → %s" % v["py3"])
        print("                py2 → %s   (明文本身就是 flag, 这两行只在题面要 md5 时用)" % v["py2"])
        return []
    order = ["py2", "py3"] if py2 else ["py3", "py2"]
    print("  md5(hex(d)) :  (Python2 的 hex(long) 带 L 后缀, 两种写法结果不同)")
    for tag in order:
        note = "py2 / hex(d)='0x…L'" if tag == "py2" else "py3 / hex(d)='0x…'"
        print("      %-22s %s" % (note, v[tag]))
    if py2:
        print("      ↑ 题面有 Python 2 特征, 优先带 L 的那条")
    elif py2 is False:
        print("      ↑ 题面是 Python 3, 优先不带 L 的那条; 对不上答案再试带 L 的")
    else:
        print("      ↑ 题面看不出哪个版本, 两条都拿去对答案")
    return [("flag{%s}" % v[t], t) for t in order]


def _find_flag_text(info):
    """从渲染结果里找 flag 形态的字符串, 找不到返回 None"""
    for key in ("text", "unpadded"):
        if key not in info:
            continue
        try:
            if isinstance(info[key], bytes):
                s = info[key].decode("utf-8", "replace")
            else:
                s = info[key]
        except Exception:
            continue
        hit = _FLAG_RE.search(s)
        if hit:
            return hit.group()
    if "ascii_run" in info:
        try:
            s = info["ascii_run"].decode("utf-8", "replace")
        except Exception:
            s = ""
        hit = _FLAG_RE.search(s)
        if hit:
            return hit.group()
    return None


def _print_flag_box(info, extras=None):
    """把 flag 单独拎出来放大显示, 免得淹没在一堆 hex 里"""
    cand = _find_flag_text(info)
    lines = []
    if cand:
        lines.append((cand, ""))
    for s, tag in (extras or []):
        if s and s not in [x[0] for x in lines]:
            lines.append((s, tag))
    if not lines:
        return
    print("")
    print("╔" + "═" * 60 + "╗")
    print("║  FLAG")
    print("╠" + "═" * 60 + "╣")
    for s, tag in lines:
        print("║  " + s + (("   (" + tag + ")") if tag else ""))
    print("╚" + "═" * 60 + "╝")


def print_trace(trace):
    print("\n[攻击模块执行记录]")
    for name, status, dt in trace:
        mark = "✅" if status == "命中" else "·"
        print("  %s %-28s %-6s %5.2fs" % (mark, name, status, dt))


def print_analysis(ctx, diag, trace):
    print("\n[题目解析]")
    n = ctx.get("n")
    if n:
        print("  n         : %d bit" % n.bit_length())
        print("  n(hex)    : %s" % hx(n, 80))
        if n.bit_length() <= 300:
            print("  n(dec)    : %d" % n)
    show_int("e", ctx.get("e"))
    show_int("c", ctx.get("c"))
    for k in ("p", "q", "d", "phi", "dp", "dq", "ph", "mh"):
        if ctx.get(k):
            show_int(k, ctx[k])
    if ctx.get("ns"):
        print("  ns        : %d 个模数, 位数 %s" % (len(ctx["ns"]), [x.bit_length() for x in ctx["ns"]]))
    if ctx.get("cs"):
        print("  cs        : %d 个密文" % len(ctx["cs"]))

    if diag:
        print("\n[题型判定]")
        for name, why in diag:
            print("  · %-24s %s" % (name, why))
    else:
        print("\n[题型判定]")
        print("  · 常规 RSA —— 没发现特殊泄露，按通用路径处理")

    print("\n[攻击模块执行记录]")
    for name, status, dt in trace:
        mark = "✅" if status == "命中" else "·"
        print("  %s %-30s %-6s %5.2fs" % (mark, name, status, dt))


def parse_health(ctx, raw):
    """解析体检: 认出来的东西哪里不像样, 直接说人话

    最常见的翻车点: 从聊天框/PDF 复制的长数字被折成两行, 于是 n2 只认到
    前半截, 位数少了、gcd 白算, 最后全部模块 0.00s 未命中 —— 用户完全看不出
    是哪里出了问题, 只能觉得"工具坏了"。
    """
    warn = []
    text = raw or ""
    ns = ctx.get("ns") or []
    n = ctx.get("n")
    c = ctx.get("c")
    cs = ctx.get("cs") or []

    if not n and not ns and not ctx.get("p"):
        warn.append("一个模数都没认出来 —— 确认题目里的 n / p / q 完整粘进来了")

    if ns and len(ns) >= 2:
        bl = [x.bit_length() for x in ns]
        if min(bl) > 0 and max(bl) > 2 * min(bl):
            warn.append("两个模数位数差很多 %s —— 其中一段数字很可能被换行折断了" % bl)

    used = set(re.findall(r"\b(n\d{1,2})\b", text))
    if len(ns) == 1 and used:
        warn.append("题面里用到了 %s，但只认出 1 个模数 —— 另一个可能被折行拆断或漏粘"
                    % "/".join(sorted(used)))

    if (n or ns) and c is None and not cs and ctx.get("d") is None:
        warn.append("没认出密文 —— 检查 c 那一行(常常被 # 注释掉)是否完整粘进来了")

    return warn


def failure_hint(ctx):
    n = ctx.get("n")
    lines = ["\n[说明] 常规攻击都没打穿，可能的原因:"]
    if n:
        if n.bit_length() > 256:
            lines.append("  · n 有 %d bit，通用分解跑不动 —— 需要额外泄露（p 高位 / dp / phi 等）或用 yafu、msieve、Sage 做分解" % n.bit_length())
        else:
            lines.append("  · n 只有 %d bit 但没分解开，可以试更大 effort（--effort 3）" % n.bit_length())
    e = ctx.get("e")
    if e and e > (1 << 40):
        lines.append("  · e 很大 → 大概率是小 d 题，Wiener 已经试过；若是 d < n^0.292 需要用 Sage 跑 Boneh-Durfee")
    if e == 3:
        lines.append("  · e=3 没打穿 → 检查是不是 Håstad 广播（要 3 组 n,c）或明文不够小")
    lines.append("  · 如果题目有 hint（比如 p、q 的关系、m 的比特位），给我补上字段再来一次")
    return "\n".join(lines)


# ============================================================
# 14. CLI
# ============================================================

def net_state_text(on=None):
    """明确告诉用户当前会不会把 n 发出去（v3.9 起支持启动时自己选）"""
    if on is None:
        on = _ONLINE["on"]
    if on:
        return "[联网] 已允许查公开分解库：大 n 会发给 factordb.com"
    return "[纯本地] 不联网，题目数据不出本机"


def _net_state():
    return net_state_text()


# ---- v3.9: 联网偏好的记忆（exe 双击时问过一次，选大写 Y/N 就记下来）----

_CFG_FILE = "rsa_solver_config.json"


def _config_candidates():
    cands = []
    envp = os.environ.get("RSA_SOLVER_CFG")
    if envp:
        cands.append(os.path.abspath(envp))
    if getattr(sys, "frozen", False):
        cands.append(os.path.join(os.path.dirname(os.path.abspath(sys.executable)), _CFG_FILE))
    else:
        cands.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), _CFG_FILE))
    appdata = os.environ.get("APPDATA")
    if appdata:
        cands.append(os.path.join(appdata, "rsa_solver", _CFG_FILE))
    cands.append(os.path.join(os.path.expanduser("~"), ".config", "rsa_solver", _CFG_FILE))
    return cands


def config_path(for_write=False):
    """配置文件位置：程序/exe 同目录优先，不可写就落到用户目录。"""
    for p in _config_candidates():
        d = os.path.dirname(p) or "."
        if not for_write:
            if os.path.isfile(p):
                return p
            continue
        try:
            os.makedirs(d, exist_ok=True)
        except Exception:
            continue
        if os.access(d, os.W_OK):
            return p
    return None


def load_pref():
    """读记住的联网选择：True=允许 / False=纯本地 / None=没记住"""
    p = config_path(False)
    if not p:
        return None
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = json.load(f)
        v = data.get("online")
        return v if isinstance(v, bool) else None
    except Exception:
        return None


def save_pref(online):
    """记住联网选择，返回是否写成功"""
    p = config_path(True)
    if not p:
        return False
    try:
        with open(p, "w", encoding="utf-8") as f:
            json.dump({"online": bool(online), "note": "rsa_solver 联网设置；删掉本文件即恢复启动时询问"},
                      f, ensure_ascii=False, indent=2)
        return True
    except Exception:
        return False


def clear_pref():
    p = config_path(False)
    if not p:
        return False
    try:
        os.remove(p)
        return True
    except Exception:
        return False


def stdin_is_interactive():
    """判断 stdin 是不是真控制台。

    不能只信 sys.stdin.isatty()：Windows 上被重定向到文件/管道时，
    某些环境（含 wine）仍会答 True，询问就会吃掉题面的第一行。
    Windows 走 GetConsoleMode，只有真控制台才成功；其它平台用 isatty。
    """
    if os.name == "nt":
        try:
            import ctypes
            k = ctypes.windll.kernel32
            h = k.GetStdHandle(-10)          # STD_INPUT_HANDLE
            if not h or h == -1 or h == 0:
                return False
            mode = ctypes.c_uint(0)
            return bool(k.GetConsoleMode(h, ctypes.byref(mode)))
        except Exception:
            return False
    try:
        return sys.stdin is not None and sys.stdin.isatty()
    except Exception:
        return False


def ask_online(show_intro=True):
    """问一次「要不要联网查公开分解库」。

    返回 True=允许 / False=纯本地。非交互环境（管道、重定向、被脚本调用）
    一律返回 False 且不询问，绝不把批处理卡在等待输入上。
    """
    if not stdin_is_interactive():
        return False
    if show_intro:
        print("")
        print("=" * 58)
        print("  联网设置：允许查公开分解库（factordb.com）吗？")
        print("=" * 58)
        print("   y        允许：公开分解过的大 n 能秒解（题目里的 n 会发到网上）")
        print("   回车 / n 纯本地：数据不出本机（默认）")
        print("   大写 Y / N  记住这次选择，以后不再问（想改：输入 set 或删配置文件）")
        print("")
    for _ in range(5):
        try:
            s = input("你的选择 [回车=纯本地] > ").strip()
        except (EOFError, KeyboardInterrupt):
            print("")
            return False
        low = s.lower()
        if low in ("", "n", "0", "不", "否", "no"):
            remembered = save_pref(False) if s == "N" else False
            print("  → 纯本地，不联网。" + ("（已记住，下次不再问）" if remembered else ""))
            return False
        if low in ("y", "1", "是", "yes"):
            remembered = save_pref(True) if s == "Y" else False
            print("  → 允许联网查库。" + ("（已记住，下次不再问）" if remembered else ""))
            return True
        print("   只认 y / n（大写 = 记住这次选择），直接回车按纯本地处理。")
    print("  → 连续几次没看懂，按纯本地处理。")
    return False


def build_parser():
    import argparse
    p = argparse.ArgumentParser(
        prog="rsa_solver.py",
        description="CTF RSA 自动题型判定 + 自动解密 (纯标准库, 零依赖)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""示例:
  python3 rsa_solver.py chall.py              # 解析题目脚本里的 n/e/c
  python3 rsa_solver.py data.txt              # 从文本/粘贴内容解析
  cat data.txt | python3 rsa_solver.py -      # 从 stdin 读
  python3 rsa_solver.py --n 0x... --e 65537 --c 0x...
  python3 rsa_solver.py chall.py --json       # JSON 输出
  python3 rsa_solver.py --list-attacks        # 看支持哪些题型

公告:
""" + announce_text("  "))
    p.add_argument("target", nargs="?", help="题目文件 (.py/.txt/.json) 或 - 表示 stdin")
    for f in ("n", "e", "c", "p", "q", "d", "phi", "dp", "dq", "c1", "c2", "m1", "m2", "ph", "mh"):
        p.add_argument("--" + f, type=str, help="手动指定 %s（支持 0x 前缀）" % f)
    p.add_argument("--json", action="store_true", help="JSON 输出")
    p.add_argument("--quiet", "-q", action="store_true", help="精简输出")
    p.add_argument("--single", action="store_true", help="强制单组模式（文件里有多组时不要自动批量）")
    p.add_argument("--effort", type=int, default=2, choices=[1, 2, 3], help="分解强度 (默认 2)")
    p.add_argument("--offline", action="store_true",
                   help="强制纯本地算，不联网（也是默认；显式写上可跳过启动时的联网询问）")
    p.add_argument("--online", action="store_true",
                   help="允许联网查公开分解库 factordb（默认关闭，题目里的 n 不会离开本机）")
    p.add_argument("--ask-net", action="store_true",
                   help="启动时交互问一句要不要联网（exe 双击默认会问；非交互环境自动按纯本地）")
    p.add_argument("--forget-net", action="store_true",
                   help="清掉记住的联网设置，恢复成每次启动都询问")
    p.add_argument("--chain", action="store_true",
                   help="强制用链式求解（多段代码/断言驱动/跨段变量继承）")
    p.add_argument("--no-chain", action="store_true",
                   help="关闭链式求解兜底（默认普通攻击失败后自动试一次）")
    p.add_argument("--enum-max", type=int, default=MAX_ENUM,
                   help="链式求解里枚举未知小整数的上限 (默认 %d)" % MAX_ENUM)
    p.add_argument("--list-attacks", action="store_true", help="列出支持的所有攻击/题型")
    p.add_argument("--version", action="store_true", help="版本号")
    return p


def _phi_of_factors(factors):
    """由素因子列表(可重复)算 phi"""
    from collections import Counter
    ph = 1
    for p_, k in Counter(factors).items():
        ph *= (p_ - 1) * pow(p_, k - 1)
    return ph


def solve_d_only(ctx):
    """题目只要 d (压根没给密文) 时走这里"""
    e = ctx.get("e")
    if not e:
        return None
    if ctx.get("d"):
        return ctx["d"], "题目已直接给了 d"
    fs = ctx.get("factors")
    if fs and len(fs) >= 2:
        try:
            return modinv(e, _phi_of_factors(fs)), "φ(n) = ∏(p-1)·p^(k-1)，d = e⁻¹ mod φ(n)"
        except Exception:
            pass
    if ctx.get("phi"):
        try:
            return modinv(e, ctx["phi"]), "d = e⁻¹ mod φ(n)"
        except Exception:
            pass
    return None


_BLOCK_SPLIT_KEYS = ("n", "c")


def split_problem_blocks(text):
    """把"一次粘了好几道题"的文字切成独立题目。

    判据: 同一段里 n / c 再次出现, 说明换题了 (同一道题不会给两次 n、两次 c)。
    用户经常把几道题的脚本连着粘一起, 旧版会被后一道的 c/n 覆盖, 只解出最后一道。
    """
    blocks, cur, seen = [], [], set()
    for ln in text.splitlines():
        m = re.match(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*[:=]", ln)
        key = None
        if m:
            k = m.group(1)
            key = _ALIAS_MAP.get(k) or _ALIAS_MAP.get(k.lower())
        if key in _BLOCK_SPLIT_KEYS:
            if key in seen and any(x.strip() for x in cur):
                blocks.append("\n".join(cur))
                cur, seen = [], set()
            seen.add(key)
        cur.append(ln)
    if any(x.strip() for x in cur):
        blocks.append("\n".join(cur))
    return [b for b in blocks if re.search(r"\d", b)]


def _block_complete(text):
    """拆出来的块是不是一道完整题

    完整 = 能拿到模数（n，或 p、q 都有），并且有密文/私钥/因子之一。
    s05 那种第一问是「给 p、q 求 c」的，p、q 有值就算完整。
    """
    try:
        env = parse_text(text)
        ctx = normalize(env)
    except Exception:
        return False
    have_n = bool(ctx.get("n")) or (ctx.get("p") and ctx.get("q")) or ctx.get("ns")
    if not have_n:
        return False
    return (ctx.get("c") is not None or ctx.get("cs") or ctx.get("d")
            or ctx.get("p") or ctx.get("ns"))


def run_blocks(blocks, args):
    """逐题求解, 返回解出的题数"""
    hits = 0
    for i, blk in enumerate(blocks, 1):
        try:
            insts = split_instances(blk)
        except Exception:
            insts = []
        if len(insts) >= 2:
            base_e = next((x["e"] for x in insts if x.get("e")), None)
            print("\n" + "─" * 52)
            print("  第 %d/%d 题（内含 %d 组）" % (i, len(blocks), len(insts)))
            if run_multi(insts, base_e, args) == 0:
                hits += 1
            continue
        try:
            env = parse_text(blk)
            ctx = normalize(env)
        except Exception:
            continue
        if not (ctx.get("n") or ctx.get("p") or ctx.get("ns")):
            continue
        ctx = fill_derived(ctx)
        diag = diagnose(ctx)
        if ctx.get("c") is None and not ctx.get("cs"):
            got = solve_d_only(ctx)
            if not got:
                continue
            hits += 1
            print("\n" + "─" * 52)
            print("  第 %d/%d 题 —— 只有 d" % (i, len(blocks)))
            print("  d (十进制): %d" % got[0])
            continue
        att, res, trace = solve(ctx, effort=args.effort)
        if not res:
            continue
        hits += 1
        print("\n" + "─" * 52)
        print("  第 %d/%d 题" % (i, len(blocks)))
        print_result(att, res, trace, ctx, quiet=args.quiet)
    return hits



# ============================================================
# 20.6 链式求解对外入口
# ============================================================


def _chain_once(raw, args=None, verbose=True, budget_sec=180, inject=None, seed=None):
    prefix = None
    mp = re.search(r"startswith\(\s*['\"]([^'\"]{1,60})['\"]", raw)
    if mp:
        prefix = mp.group(1).split("{")[0].encode()
    effort = getattr(args, "effort", 2) if args else 2
    max_k = getattr(args, "enum_max", MAX_ENUM) if args else MAX_ENUM
    deadline = time.time() + budget_sec
    cache = {"sig": None}

    def rsa_pass(S):
        if time.time() > deadline:
            return None
        env = {}
        for k, v in S.items():
            if isinstance(v, bool):
                continue
            if isinstance(v, list):
                if (re.fullmatch(r"(n|c)(s?)", k)
                        and len(v) >= 2 and all(isinstance(x, int) for x in v)):
                    env[k] = v
                continue
            if not isinstance(v, int):
                continue
            if re.fullmatch(r"(n|c|e|p|q|d|phi|dp|dq)(\d*)", k):
                env[k] = v
        # 有编号的 nK 只带同号的 cK，别把别的段的密文塞进同一组广播
        num = {}
        for k in list(env):
            m2 = re.fullmatch(r"n(\d+)", k)
            if m2 and ("c" + m2.group(1)) in env:
                num["n" + m2.group(1)] = env[k]
                num["c" + m2.group(1)] = env["c" + m2.group(1)]
        if len(num) >= 4:
            # 只保留无编号的 e/p/q/d/phi（e1、e2 是本段解出来的中间量，混进去会被
            # normalize 当成"多组各自指数"，把广播攻击带偏）
            base = {k: v for k, v in env.items()
                    if k in ("e", "p", "q", "d", "phi", "dp", "dq")}
            base.update(num)
            env = base
        if len(env) < 2:
            return None
        sig = tuple(sorted(env.items()))
        if sig == cache["sig"]:
            return None
        cache["sig"] = sig
        try:
            ctx = normalize(dict(env))
            if not (ctx.get("n") or ctx.get("ns")):
                return None
            ctx = fill_derived(ctx)
            if ctx.get("c") is None and not ctx.get("cs"):
                return None
            n0 = ctx.get("n") or (ctx.get("ns") or [0])[0]
            leak = (ctx.get("factors") or ctx.get("p") or ctx.get("d")
                    or ctx.get("phi") or ctx.get("eqs") or ctx.get("dp"))
            if n0 and n0.bit_length() > 1500 and not leak and not ctx.get("ns"):
                return None
            att, res, trace = solve(ctx, effort=effort)
        except Exception:
            return None
        if res and isinstance(res.m, int) and res.m > 0:
            return res.m, att["name"]
        return None

    r = ChainRunner(raw, rsa_pass=rsa_pass, verbose=verbose, max_k=max_k,
                    flag_prefix=prefix, inject=inject, seed=seed,
                    deadline=min(deadline, time.time() + 120))
    try:
        r.run()
    except Exception:
        pass
    return r


def _chain_quality(r):
    """候选质量: (通过段数, 总段数)。全通过才算确定"""
    if r is None or not getattr(r, "flag_score", None):
        return (0, 0)
    ok, tot = r.flag_score[0][0], r.flag_score[0][1]
    return (ok, tot)


def _chain_perfect(r):
    ok, tot = _chain_quality(r)
    return bool(tot) and ok == tot


def chain_solve(raw, args=None, verbose=True, budget_sec=180):
    """跑链式求解。出了 flag 但没通过全部断言时，继续换"跨段继承"候选重跑，取最好的那个"""
    if not raw or not raw.strip():
        return None
    r = _chain_once(raw, args, verbose=verbose, budget_sec=budget_sec)
    if _chain_perfect(r):
        return r
    # 池子里有多个素数、不知道哪个该喂给后面的 p/q 时, 逐个试
    best = r
    tried = 0
    if r is not None:
        for name in sorted(r.wanted):
            for val, tag in r.pool:
                if tried >= 8:
                    return best
                tried += 1
                if verbose:
                    print("    · 换个继承候选重试: %s = %s（%s）" % (name, _ch_short(val), tag))
                r2 = _chain_once(raw, args, verbose=verbose, budget_sec=budget_sec,
                                 inject={name: val})
                if _chain_perfect(r2):
                    return r2
                if r2 is not None and _chain_quality(r2) > _chain_quality(best):
                    best = r2
    return best


def chain_report(r, quiet=False):
    """把链式求解结果打出来, 命中 flag 返回 True"""
    if r is None:
        return False
    if r.inherit and not quiet:
        print("\n[跨段继承]")
        for nm, (v, tag) in r.inherit.items():
            print("  · %s = %s    ← %s" % (nm, _ch_short(v), tag))
    if r.flags:
        print("\n[flag]")
        scored = getattr(r, "flag_score", []) or []
        if not scored:
            for f in r.flags:
                print("  %s" % f)
            return True
        ok, tot, _v, t = scored[0]
        if tot and ok == tot:
            print("  %s      ← 交叉验证 %d/%d 段断言全部通过" % (t, ok, tot))
        elif tot:
            print("  %s      ← 只通过 %d/%d 段断言" % (t, ok, tot))
            print("  [!] 不是所有段的断言都能验证通过，这个答案不保证正确，请人工核对")
        else:
            print("  %s      （题里没有可交叉验证的 pow 断言，单段解出）" % t)
        rest = [x for x in scored[1:] if x[3] != t]
        if rest:
            print("  其它候选（未全通过，仅供参考）:")
            for ok2, tot2, _v2, t2 in rest[:6]:
                print("    %-34s 通过 %d/%d 段" % (t2, ok2, tot2))
        return True
    return False


def main(argv=None):
    _setup_stdout()
    argv = list(sys.argv[1:] if argv is None else argv)
    ap = build_parser()
    args = ap.parse_args(argv)

    if args.version:
        print(BANNER)
        print()
        print_announce()
        return 0
    if getattr(args, "forget_net", False):
        had = clear_pref()
        print("[联网设置] " + ("已清除记住的选择，下次启动会重新问你。"
                              if had else "本来就没记住过，下次启动会问你。"))
        return 0
    if args.list_attacks:
        print("%s\n支持的攻击/题型:\n" % BANNER)
        for i, a in enumerate(sorted(ATTACKS, key=lambda x: ATTACK_ORDER.index(x["name"])
                                     if x["name"] in ATTACK_ORDER else 99), 1):
            print("  %2d. %-30s %s" % (i, a["name"], a["desc"]))
        print()
        print_announce()
        return 0

    # v3.9: 默认纯本地。--online / --offline 显式指定最优先；
    #       都没指定时，只有 --ask-net（exe 双击默认带）才交互问一句。
    on = bool(getattr(args, "online", False))
    if getattr(args, "offline", False) or os.environ.get("RSA_SOLVER_OFFLINE"):
        on = False
    elif getattr(args, "ask_net", False):
        on = ask_online()
    _ONLINE["on"] = on

    ctx = {}
    raw = ""
    if args.target:
        try:
            ctx, env, raw = load_challenge(args.target)
            _RAW_SRC["text"] = raw or ""
        except Exception as ex:
            print("[!] 解析失败: %s" % ex)
            return 2
        if not ctx:
            print("[!] 没能从输入里认出 n/e/c。用 --n/--e/--c 手动指定，或者检查文件内容。")
            print("    解析到的变量: %s" % (list(env.keys())[:20] if env else "无"))
            return 2
    else:
        ctx = {}

    # ---- 先看是不是"一次粘了好几道题" ----
    _blocks = []
    if args.target and args.n is None and not args.single and not args.json:
        try:
            _blocks = split_problem_blocks(raw)
        except Exception:
            _blocks = []
        if len(_blocks) >= 2:
            # 如果每一块都是纯 n/c(题库批量题), 保持旧的批量模式:
            # 那种题要靠跨组共模 / 共因子才能打穿, 拆开就没用了
            _simple = all(not re.search(
                r"(?mi)^\s*(p|q|d|phi|dp|dq|m1|m2|ph)\s*[:=]", b) for b in _blocks)
            if _simple:
                _blocks = []
            elif not all(_block_complete(b) for b in _blocks):
                # 拆开后缺 n 或缺 c: 本来就是一道题的几段代码, 不能拆
                _blocks = []

    # ---- 多组模式: 文件里有 >=2 组成对的 n/c 时自动进入 ----
    if args.target and args.n is None and not args.single and not _blocks:
        try:
            insts = split_instances(raw)
        except Exception:
            insts = []
        if len(insts) >= 2:
            base_e = None
            if any(i.get("e") for i in insts):
                base_e = next(i["e"] for i in insts if i.get("e"))
            elif re.search(r"(?mi)^\s*e\s*[:=]", raw):
                base_e = ctx.get("e")
            return run_multi(insts, base_e, args)

    # ---- 连贴多题模式: 一段文字里塞了好几道题时逐题解 ----
    if _blocks and len(_blocks) >= 2:
        if not args.quiet:
            print("═" * 52)
            print("  " + BANNER)
            print("═" * 52)
            print_announce()
            print()
            print("  " + _net_state())
            print("  [多题] 认出 %d 道题，逐题求解" % len(_blocks))
        hits = run_blocks(_blocks, args)
        if hits:
            print("\n" + "═" * 52)
            print("  共 %d 道题，解出 %d 道" % (len(_blocks), hits))
            return 0

    for f in ("n", "e", "c", "p", "q", "d", "phi", "dp", "dq", "c1", "c2", "m1", "m2", "ph", "mh"):
        v = getattr(args, f, None)
        if v is not None:
            iv = _to_int(v)
            if iv is not None:
                ctx[f] = iv

    # v2.9: 只给 d、连 n 都没打印的题（p、q 挨着 / nextPrime 型）也要放行
    if (not ctx.get("n") and not ctx.get("ns") and not ctx.get("p")
            and not ctx.get("d") and not ctx.get("eqs")
            and not any(ctx.get(k) for k in ("sum_pq", "diff_pq", "sqdiff", "z"))):
        ap.print_help()
        return 2

    ctx = fill_derived(ctx)
    diag = diagnose(ctx)

    if not args.json and not args.quiet:
        print("═" * 52)
        print("  " + BANNER)
        print("═" * 52)
        print_announce()
        print()
        print("  " + _net_state())
        nb = detect_base5_in_text(raw) if raw else 0
        if nb:
            print("  [进制识别] 发现 %d 个只由 0-4 组成的长整数，已按 base-5 解释" % nb)

    # ---- 没有密文、题目只要 d 的情况 ----
    if ctx.get("c") is None and not ctx.get("cs"):
        got = solve_d_only(ctx)
        if got:
            dval, why = got
            if args.json:
                print(json.dumps({"ok": True, "type": "求 d（无密文）", "d": dval,
                                  "d_hex": hex(dval), "why": why,
                                  "n": ctx.get("n"), "e": ctx.get("e")},
                                 ensure_ascii=False, indent=2))
                return 0
            print("\n[题目解析]")
            if ctx.get("p") and ctx.get("q"):
                print("  p        : %d" % ctx["p"])
                print("  q        : %d" % ctx["q"])
                print("  n = p·q  : %d" % (ctx["p"] * ctx["q"]))
            show_int("e", ctx.get("e"))
            print("\n[结果] 题目没给密文，只要求私钥 d")
            print("━" * 52)
            print("  判定依据: %s" % why)
            print("  d (十进制): %d" % dval)
            print("  d (十六进制): %s" % hex(dval))
            if ctx.get("p") and ctx.get("q"):
                print("  自校验     : p * q == n            %s" % ("通过" if ctx["p"] * ctx["q"] == ctx.get("n") else "不通过"))
            _tags = _print_d_md5(dval)
            print("━" * 52)
            _print_flag_box({}, _tags)
            return 0

    t0 = time.time()
    # v3.7: 一份文件里有多段（变量被反复覆盖）时先走链式 —— 否则普通攻击很容易
    # 命中前几段的中间量（比如 hint），把一个不是 flag 的东西当成答案交出去
    _nstage = len(split_stages(raw)) if raw else 0
    if raw and args.json and not getattr(args, "no_chain", False) and _nstage >= 2:
        # JSON 模式要干净输出, 多段题悄悄跑一遍链式, 成了就直接吐 JSON
        try:
            _rj = _chain_once(raw, args, verbose=False, budget_sec=120)
        except Exception:
            _rj = None
        if _rj is not None and _chain_perfect(_rj):
            _vj = _rj.flag_score[0][2]
            print(json.dumps({
                "ok": True, "type": "多段链式求解",
                "detail": "按段拆分 + 断言驱动 + 跨段继承, 交叉验证 %d/%d 段通过" % _chain_quality(_rj),
                "m": _vj, "m_hex": hex(_vj), "m_text": _rj.flags[0],
                "elapsed": round(time.time() - t0, 3), "diagnose": [d[0] for d in diag],
                "trace": [],
            }, ensure_ascii=False, indent=2))
            return 0
    if raw and not args.json and not getattr(args, "no_chain", False) and (
            getattr(args, "chain", False) or _nstage >= 2):
        if not args.quiet:
            if getattr(args, "chain", False):
                print("\n[链式求解] 强制模式：逐句读题 + 断言驱动 + 跨段继承")
            else:
                print("\n[链式求解] 这题有 %d 段（变量被反复赋值），先按段拆开逐段解" % _nstage)
        _r = chain_solve(raw, args, verbose=not args.quiet)
        if chain_report(_r, quiet=args.quiet):
            print("\n完成，用时 %.2fs" % (time.time() - t0))
            return 0
    att, res, trace = solve(ctx, effort=args.effort)
    total = time.time() - t0

    if args.json:
        out = {
            "ok": bool(res),
            "type": att["name"] if res else None,
            "detail": res.detail if res else None,
            "m": res.m if res else None,
            "m_hex": hex(res.m) if res else None,
            "m_text": None,
            "elapsed": round(total, 3),
            "diagnose": [d[0] for d in diag],
            "trace": [{"attack": t[0], "status": t[1], "time": round(t[2], 3)} for t in trace],
        }
        if res:
            info = render_m(res.m)
            if "text" in info:
                out["m_text"] = info["text"]
            elif "unpadded" in info:
                out["m_text"] = info["unpadded"].decode("utf-8", "replace")
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return 0 if res else 1

    if not args.quiet:
        print_analysis(ctx, diag, trace)
        _warn = parse_health(ctx, raw)
        if _warn:
            print("\n[解析体检] 这几处可能没认全:")
            for _w in _warn:
                print("  · " + _w)

    if res:
        print_result(att, res, trace, ctx, quiet=args.quiet)
        print("\n完成，用时 %.2fs" % total)
        return 0
    else:
        # v3.5: 普通攻击打不穿时，试一次链式求解（多段代码 / 断言驱动 / 跨段变量继承）
        if raw and not getattr(args, "no_chain", False):
            if not args.quiet:
                print("\n[链式求解] 换一种打法：逐句读题、按断言反解、跨段继承变量…")
            try:
                r = chain_solve(raw, args, verbose=not args.quiet)
            except Exception:
                r = None
            if chain_report(r, quiet=args.quiet):
                print("\n完成，用时 %.2fs" % (time.time() - t0))
                return 0
        print("\n[×] 没打穿。")
        print(failure_hint(ctx))
        return 1


# ============================================================
# 20. 链式求解引擎 (v3.5)
# ============================================================

MAX_ENUM = 400000
MAX_ROOTS = 20000


# ============================================================
# 20.1 表达式求值（纯 AST 解释, 绝不 exec/eval）
# ============================================================


class _ChUnk(Exception):
    """表达式里有未知量; names 是缺的名字集合"""

    def __init__(self, names=()):
        Exception.__init__(self, "unknown")
        self.names = set(names)


def _ch_merge(*excs):
    s = set()
    for e in excs:
        if isinstance(e, _ChUnk):
            s |= e.names
    return _ChUnk(s)


def _ch_ev(node, S):
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool):
            return int(v)
        if isinstance(v, (int, str, bytes)):
            return v
        if isinstance(v, (list, tuple)):
            return list(v)
        raise _ChUnk()
    if isinstance(node, ast.Name):
        if node.id in S:
            return S[node.id]
        raise _ChUnk([node.id])
    if isinstance(node, (ast.Tuple, ast.List)):
        return [_ch_ev(x, S) for x in node.elts]
    if isinstance(node, ast.UnaryOp):
        v = _ch_ev(node.operand, S)
        if not isinstance(v, int) or isinstance(v, bool):
            raise _ChUnk()
        if isinstance(node.op, ast.USub):
            return -v
        if isinstance(node.op, ast.UAdd):
            return v
        if isinstance(node.op, ast.Invert):
            return ~v
        raise _ChUnk()
    if isinstance(node, ast.BinOp):
        try:
            l = _ch_ev(node.left, S)
        except _ChUnk as e1:
            try:
                _ch_ev(node.right, S)
            except _ChUnk as e2:
                raise _ch_merge(e1, e2)
            raise e1
        try:
            r = _ch_ev(node.right, S)
        except _ChUnk as e2:
            raise e2
        return _ch_binop(node.op, l, r)
    if isinstance(node, ast.Call):
        return _ch_call(node, S)
    raise _ChUnk()


def _ch_binop(op, l, r):
    ii = lambda x: isinstance(x, int) and not isinstance(x, bool)
    if isinstance(op, ast.Add):
        if ii(l) and ii(r):
            return l + r
        if isinstance(l, (bytes, str)) and isinstance(r, type(l)):
            return l + r
        raise _ChUnk()
    if isinstance(op, ast.Sub):
        if ii(l) and ii(r):
            return l - r
        raise _ChUnk()
    if isinstance(op, ast.Mult):
        if ii(l) and ii(r):
            return l * r
        if isinstance(l, (bytes, str)) and ii(r):
            return l * r
        raise _ChUnk()
    if isinstance(op, (ast.Div, ast.FloorDiv)):
        if ii(l) and ii(r) and r:
            return l // r
        raise _ChUnk()
    if isinstance(op, ast.Mod):
        if ii(l) and ii(r) and r:
            return l % r
        raise _ChUnk()
    if isinstance(op, ast.Pow):
        if ii(l) and ii(r):
            if r < 0 or r > 200000 or (abs(l) > 2 and r > 8000):
                raise _ChUnk()
            return l ** r
        raise _ChUnk()
    if isinstance(op, ast.LShift):
        if ii(l) and ii(r) and 0 <= r < 64:
            return l << r
        raise _ChUnk()
    if isinstance(op, ast.RShift):
        if ii(l) and ii(r):
            return l >> r
        raise _ChUnk()
    raise _ChUnk()


def _ch_call(node, S):
    fn = node.func
    name = fn.id if isinstance(fn, ast.Name) else (
        fn.attr if isinstance(fn, ast.Attribute) else "")
    args, unk = [], None
    for a in node.args:
        try:
            args.append(_ch_ev(a, S))
        except _ChUnk as e:
            unk = e if unk is None else _ch_merge(unk, e)
    if unk is not None:
        raise unk
    ii = lambda x: isinstance(x, int) and not isinstance(x, bool)
    if name == "pow" and len(args) in (2, 3):
        a, b = args[0], args[1]
        if not (ii(a) and ii(b)):
            raise _ChUnk()
        if len(args) == 3:
            m = args[2]
            if not ii(m) or m <= 0:
                raise _ChUnk()
            if b > 200000 and m.bit_length() > 8192:
                raise _ChUnk()
            return pow(a, b, m)
        if b < 0 or b > 200000 or (abs(a) > 2 and b > 8000):
            raise _ChUnk()
        return a ** b
    if name in ("int", "long") and len(args) == 1:
        v = args[0]
        if ii(v):
            return v
        if isinstance(v, (str, bytes)):
            try:
                return int(v)
            except Exception:
                raise _ChUnk()
        raise _ChUnk()
    if name == "abs" and len(args) == 1 and ii(args[0]):
        return abs(args[0])
    if name == "len" and len(args) == 1:
        return len(args[0])
    if name in ("bytes_to_long", "s2n", "long_to_bytes_") and len(args) == 1:
        v = args[0]
        b = v if isinstance(v, bytes) else str(v).encode()
        return int.from_bytes(b, "big")
    if name == "ord" and len(args) == 1 and isinstance(args[0], str):
        return ord(args[0])
    if name == "chr" and len(args) == 1 and ii(args[0]):
        return chr(args[0])
    raise _ChUnk()


# ============================================================
# 20.2 可读性 / 渲染
# ============================================================

_CH_PRINT = set(range(32, 127)) | {9, 10, 13}


def _ch_printable(x):
    if not isinstance(x, int) or x <= 0:
        return 0.0
    b = x.to_bytes((x.bit_length() + 7) // 8, "big")
    if not b:
        return 0.0
    return sum(1 for c in b if c in _CH_PRINT) / float(len(b))


def _ch_pick(cands, want_prefix=None):
    """从候选明文里挑最像 flag 的一个"""
    best, sc = None, -1.0
    for m in cands:
        if not isinstance(m, int) or m <= 0:
            continue
        b = m.to_bytes((m.bit_length() + 7) // 8, "big")
        s = _ch_printable(m)
        if want_prefix and b.startswith(want_prefix):
            s += 2.0
        if b"{" in b and b"}" in b:
            s += 0.8
        if 3 <= len(b) <= 200:
            s += 0.3
        if s > sc:
            sc, best = s, m
    return best, sc


def _ch_render(m):
    if not isinstance(m, int) or m <= 0:
        return str(m)
    b = m.to_bytes((m.bit_length() + 7) // 8, "big")
    for w in (b, b.strip(b"\x00")):
        try:
            t = w.decode("utf-8")
            if t and sum(1 for c in t if c.isprintable()) >= len(t) * 0.95:
                return t
        except Exception:
            pass
    return "0x%x" % m


def _ch_short(v, n=44):
    if isinstance(v, int) and not isinstance(v, bool):
        if v.bit_length() > 200:
            return "%d bit 整数" % v.bit_length()
        return str(v)
    if isinstance(v, bytes):
        try:
            return repr(v.decode("utf-8")[:n])
        except Exception:
            return repr(v[:n])
    return repr(v)[:n]


# ============================================================
# 20.3 模开根（含模不互素 / 素数模 / 素幂模）
# ============================================================

def _ch_factor_by_known(n, S):
    """用符号表里已经解出来的素数去切 n (gcd 一击即中, 不需要分解)"""
    rest, parts = n, []
    vs = []
    for k, v in S.items():
        if isinstance(v, bool) or not isinstance(v, int):
            continue
        if v > 1 and v.bit_length() >= 32:
            vs.append(v)
    vs.sort(key=lambda x: -x.bit_length())
    for v in vs:
        if rest == 1:
            break
        g = math.gcd(rest, v)
        if 1 < g < rest:
            parts.append(g)
            rest //= g
    if rest > 1:
        parts.append(rest)
    return parts if len(parts) >= 2 else None


_CH_ROOT_CACHE = {}
_CH_ROOT_CACHE_MAX = 48


def _ch_rsa_roots(mod, e, c, max_cands=MAX_ROOTS, S=None):
    c %= mod
    if e <= 0 or mod <= 1:
        return []
    key = (mod, e, c)
    if key in _CH_ROOT_CACHE:
        return _CH_ROOT_CACHE[key]
    out = _ch_rsa_roots_uncached(mod, e, c, max_cands, S)
    if len(_CH_ROOT_CACHE) < _CH_ROOT_CACHE_MAX:
        _CH_ROOT_CACHE[key] = out
    return out


def _ch_rsa_roots_uncached(mod, e, c, max_cands=MAX_ROOTS, S=None):
    c %= mod
    if is_prime(mod):
        return nth_root_mod_prime_all(c, e, mod)[:max_cands]
    fs = _ch_factor_by_known(mod, S) if S else None
    if not fs:
        fs = factor_int(mod, effort=2)
    if not fs and mod.bit_length() > 320:
        r = fermat(mod, max_iter=200000)     # v3.7: nextprime 型两因子极近
        if r:
            fs = [r[0], r[1]]
    if not fs:
        return []
    pk = {}
    for p in fs:
        pk[p] = pk.get(p, 0) + 1
    per, mods = [], []
    for p in sorted(pk):
        k = pk[p]
        pkk = p ** k
        rs = nth_root_mod_prime_all(c % p, e, p) if k == 1 else _ch_roots_pk(c, e, p, k)
        if not rs:
            return []
        per.append(rs)
        mods.append(pkk)
    cands, cur = [0], 1
    for m, rs in zip(mods, per):
        nxt = []
        for base in cands:
            for s in rs:
                try:
                    inv = pow(cur % m, -1, m)
                except ValueError:
                    continue
                t = ((s - base) % m) * inv % m
                nxt.append(base + cur * t)
                if len(nxt) > max_cands:
                    break
            if len(nxt) > max_cands:
                break
        cands, cur = nxt, cur * m
        if not cands:
            return []
    out = []
    for x in cands:
        if pow(x, e, mod) == c and x not in out:
            out.append(x)
    return out


def _ch_roots_pk(c, e, p, k):
    sols = nth_root_mod_prime_all(c % p, e, p)
    if not sols:
        return []
    cur, pk = [s % p for s in sols], p
    for _ in range(k - 1):
        pk *= p
        nxt = []
        for x in cur:
            for t in range(min(p, 64)):
                xx = x + t * (pk // p)
                if (pow(xx, e, pk) - c) % pk == 0:
                    nxt.append(xx)
        cur = nxt
        if not cur:
            return []
    return cur


# ============================================================
# 20.4 等式反解
# ============================================================

def _ch_try(node, S):
    try:
        return True, _ch_ev(node, S)
    except _ChUnk:
        return False, None


def _ch_int_root_path(node, val, b, m, S, depth, max_cands, k_max=60000):
    """v3.7: pow(X, b, m) == val 但 X 很小时, X^b 根本没超过 m —— 直接整数开方

    覆盖 `pow(e1, 42, n) == ce1`（ce1 = e1^42 原值）和
    `pow(e2 + tmp, 3, n) == ce2`（ce2 = (e2+tmp)^3 mod n → 要试 val + k·m）
    """
    cands = []
    r, exact = iroot(val, b)
    if exact and r > 1:
        cands.append(r)
    if not cands:
        t0 = time.time()
        for k in range(1, k_max + 1):
            r, exact = iroot(val + k * m, b)
            if exact and r > 1:
                cands.append(r)
                break
            if (k & 1023) == 0 and time.time() - t0 > 4.0:
                break
    out = []
    for r in cands:
        out.extend(_ch_solve_expr(node.args[0], r, S, depth + 1, max_cands))
        if len(out) >= 8:
            break
    return out


def _ch_solve_expr(node, val, S, depth=0, max_cands=MAX_ROOTS):
    """让 node == val, 返回若干候选赋值 dict 列表"""
    if depth > 14 or not isinstance(val, int) or isinstance(val, bool) or val < 0:
        return []
    if isinstance(node, ast.Name):
        return [] if node.id in S else [{node.id: val}]

    if isinstance(node, ast.BinOp):
        op = node.op
        ok_l, vl = _ch_try(node.left, S)
        ok_r, vr = _ch_try(node.right, S)
        if isinstance(op, ast.Add):
            if ok_l and isinstance(vl, int):
                return _ch_solve_expr(node.right, val - vl, S, depth + 1, max_cands)
            if ok_r and isinstance(vr, int):
                return _ch_solve_expr(node.left, val - vr, S, depth + 1, max_cands)
            return []
        if isinstance(op, ast.Sub):
            if ok_l and isinstance(vl, int):
                return _ch_solve_expr(node.right, vl - val, S, depth + 1, max_cands)
            if ok_r and isinstance(vr, int):
                return _ch_solve_expr(node.left, val + vr, S, depth + 1, max_cands)
            return []
        if isinstance(op, ast.Mult):
            if ok_l and isinstance(vl, int) and vl:
                return (_ch_solve_expr(node.right, val // vl, S, depth + 1, max_cands)
                        if val % vl == 0 else [])
            if ok_r and isinstance(vr, int) and vr:
                return (_ch_solve_expr(node.left, val // vr, S, depth + 1, max_cands)
                        if val % vr == 0 else [])
            if isinstance(node.left, ast.Name) and isinstance(node.right, ast.Name):
                fs = _ch_factorize(val)          # v3.7: 大 n 先费马, 再交给 rho
                if fs and len(fs) == 2:
                    a, b = fs
                    if a == b:
                        return [{node.left.id: a, node.right.id: b}]
                    return [{node.left.id: a, node.right.id: b},
                            {node.left.id: b, node.right.id: a}]
            return []
        if isinstance(op, ast.Pow):
            if ok_r and isinstance(vr, int) and 2 <= vr <= 8192:
                r, exact = iroot(val, vr)
                if exact and r > 1:
                    return _ch_solve_expr(node.left, r, S, depth + 1, max_cands)
                return []
            if ok_l and isinstance(vl, int) and vl > 1:
                cur = 1
                for k in range(1, 129):
                    cur *= vl
                    if cur == val:
                        return _ch_solve_expr(node.right, k, S, depth + 1, max_cands)
                    if cur > val:
                        break
                return []
            return []
        return []

    if isinstance(node, ast.Call):
        fname = node.func.id if isinstance(node.func, ast.Name) else (
            node.func.attr if isinstance(node.func, ast.Attribute) else "")
        if fname != "pow" or len(node.args) not in (2, 3):
            return []
        info = [_ch_try(a, S) for a in node.args]
        if len(node.args) == 3:
            (ok_a, av), (ok_b, b), (ok_m, m) = info
            if ok_a and ok_b and ok_m:
                return []
            # 底数未知 -> 先看是不是"没取模的整数幂"(底数小、e 小, 没绕过模数),
            # 再退回模开根（模不互素也走这里）
            if (not ok_a) and ok_b and ok_m and isinstance(b, int) and isinstance(m, int) and m > 1:
                if 2 <= b <= 64:
                    got = _ch_int_root_path(node, val, b, m, S, depth, max_cands)
                    if got:
                        return got
                roots = _ch_rsa_roots(m, b, val % m, max_cands, S)
                if not roots:
                    return []
                roots.sort(key=lambda x: -_ch_printable(x))
                out = []
                for r in roots:
                    out.extend(_ch_solve_expr(node.args[0], r, S, depth + 1, max_cands))
                    if len(out) >= 12:
                        break
                return out
            # 指数未知 -> 爬 e
            if ok_a and (not ok_b) and ok_m and isinstance(av, int) and isinstance(m, int) and m > 1:
                e_found = _ch_crawl_e(av, m, val % m, MAX_ENUM)
                if e_found:
                    return _ch_solve_expr(node.args[1], e_found, S, depth + 1, max_cands)
                return []
            return []
        (ok_a, av), (ok_b, b) = info
        if ok_a and ok_b:
            return []
        if (not ok_a) and ok_b and isinstance(b, int) and 2 <= b <= 8192:
            r, exact = iroot(val, b)
            if exact and r > 1:
                return _ch_solve_expr(node.args[0], r, S, depth + 1, max_cands)
            return []
        if ok_a and (not ok_b) and isinstance(av, int) and av > 1:
            cur = 1
            for k in range(1, 129):
                cur *= av
                if cur == val:
                    return _ch_solve_expr(node.args[1], k, S, depth + 1, max_cands)
                if cur > val:
                    break
            return []
        return []
    return []


def _ch_crawl_e(base, mod, target, hi, budget=3.0):
    """小指数爬升。v3.6: 加时间预算，避免指数不明时在大模数上空转几十秒"""
    cur = base % mod
    t0 = time.time()
    for k in range(1, hi):
        if cur == target:
            return k
        cur = cur * base % mod
        if (k & 2047) == 0 and time.time() - t0 > budget:
            return None
    return None


class _ChSolver(object):
    """等式求解器: 一边已知 -> 反解另一边; 两边都未知 -> 枚举小未知"""

    def __init__(self, max_k=MAX_ENUM, verbose=False):
        self.max_k = max_k
        self.verbose = verbose

    def _names(self, node):
        return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}

    def _rank(self, names):
        def sc(nm):
            s = 0
            if nm in ("k", "i", "j", "tmp", "r", "x", "t", "k1", "k2", "cnt", "count"):
                s -= 100
            if len(nm) <= 2:
                s -= 10
            return (s, nm)
        return sorted(names, key=sc)

    def check(self, lhs, rhs, S):
        try:
            a, b = _ch_ev(lhs, S), _ch_ev(rhs, S)
        except _ChUnk:
            return False
        return a == b

    def step(self, lhs, rhs, S):
        for known, unk in ((rhs, lhs), (lhs, rhs)):
            ok, v = _ch_try(known, S)
            if ok and isinstance(v, int) and not isinstance(v, bool):
                for upd in _ch_solve_expr(unk, v, S):
                    if not upd:
                        continue
                    S2 = dict(S)
                    S2.update(upd)
                    if self.check(lhs, rhs, S2):
                        return upd, "等式反解"
        un = (self._names(lhs) | self._names(rhs)) - set(S)
        if 1 <= len(un) <= 2:
            for name in self._rank(un):
                limit = min(self.max_k, 400001)   # v3.6: 旧上限 50001 打不穿 k=5万+ 的题
                for i in range(2, limit):
                    S2 = dict(S)
                    S2[name] = i
                    for known, unk in ((rhs, lhs), (lhs, rhs)):
                        ok, v = _ch_try(known, S2)
                        if not ok or not isinstance(v, int):
                            continue
                        for upd in _ch_solve_expr(unk, v, S2):
                            if not upd:
                                continue
                            S3 = dict(S2)
                            S3.update(upd)
                            if self.check(lhs, rhs, S3):
                                out = {name: i}
                                out.update(upd)
                                return out, "枚举 %s=%d + 等式反解" % (name, i)
                if name in ("k", "i", "j", "tmp", "x", "r", "t"):
                    break
        return None, None


# ============================================================
# 20.5 链式执行器
# ============================================================

_CH_PRIME_ALIAS = ("p", "q", "p1", "q1", "prime", "primes", "pp", "qq", "p_", "q_")

# v3.7: 一份题面里"变量被反复赋值"就是换了一段。核心变量重新出现即切段。
_STAGE_CORE = ("n", "c", "e", "p", "q", "d", "phi", "dp", "dq")


def split_stages(raw):
    """按核心变量重新赋值的边界，把题面切成若干段（多段式 RSA 题的常见写法）

    例：n = [...] / c = [...] / assert(...)  ← 段1
        n = 1591…                            ← 段2 开始（n 又被赋值了）
    """
    if not raw:
        return []
    segs, cur, seen = [], [], set()
    for ln in raw.split("\n"):
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*=(?!=)", ln.strip())
        nm = m.group(1) if m else None
        if nm in _STAGE_CORE and nm in seen and any(x.strip() for x in cur):
            segs.append("\n".join(cur))
            cur, seen = [], set()
        if nm:
            seen.add(nm)
        cur.append(ln)
    if cur:
        segs.append("\n".join(cur))
    return [s for s in segs if s.strip()]


def _ch_factorize(val):
    """段内等式反解用的分解：小 n 走 rho，大 n 先费马（nextprime 型几乎立刻出）"""
    if not isinstance(val, int) or val < 4:
        return None
    if val.bit_length() <= 320:
        fs = factor_int(val, effort=2)
        if fs and len(fs) == 2:
            return fs
    r = fermat(val, max_iter=200000)
    if r:
        return [r[0], r[1]]
    fs = factor_int(val, effort=3)
    if fs and len(fs) == 2:
        return fs
    return None


def _ch_names_of(node):
    return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}


class ChainRunner(object):
    """逐语句解释题目源码, 断言驱动求值, 跨段结果回灌"""

    def __init__(self, text, rsa_pass=None, verbose=True, max_k=MAX_ENUM,
                 flag_prefix=None, use_pool=True, inject=None, deadline=None, seed=None):
        self.text = text
        self.S = {}
        self.seed = dict(seed or {})   # v3.7: 跨段题上一段的解直接当本段已知量
        self.pool = []            # [(value, tag)]
        self.inherit = {}         # name -> (value, tag) 跨段继承记录
        self.pending = []         # [(targets, node, lineno)]
        self.constraints = []     # [(lhs, rhs, lineno)]
        self.found = {}           # name -> value
        self.flags = []
        self.flag_cands = []      # [(int 候选, 来源行)] v3.6: 全部候选，不再只留第一个
        self.pow_eqs = []         # [(名字节点, e, mod, c, 行)] 形如 pow(X,e,mod)==c 的断言
        self.all_asserts = []     # 全部 assert 原样留存，最后统一解析
        self.flag_score = []      # [(通过段数, 总段数, int 候选, 文本)]
        self.verbose = verbose
        self.max_k = max_k
        self.flag_prefix = flag_prefix
        self.solver = _ChSolver(max_k=max_k, verbose=verbose)
        self.rsa_pass = rsa_pass   # fn(S) -> (m, how) 用主程序的攻击引擎
        self.use_pool = use_pool
        self.inject = dict(inject or {})   # 强制指定某个名字用哪个值
        self.deadline = deadline
        self.wanted = set()                # 想注入但没拿到的名字
        self.steps = []
        self.stage_snaps = []      # v3.7: [(该段结束时的符号表快照, 该段的断言区间)]
        self.t0 = time.time()
        self._rsa_sig = None

    # ---------- 输出 ----------
    def _note(self, ln, msg):
        self.steps.append((ln, msg))
        if self.verbose:
            print("    %s%s" % ("L%-4d " % ln if ln else "      ", msg))

    # ---------- 预置注释里的数值 ----------
    def preseed(self):
        pat = re.compile(r"(?m)^\s*#+\s*([A-Za-z_][A-Za-z0-9_]*)\s*[:=]\s*"
                         r"(0[xX][0-9a-fA-F]+|\d{5,})\s*$")
        for m in pat.finditer(self.text):
            k, v = m.group(1), m.group(2)
            if k in self.S or k in ("n", "e", "c"):
                continue
            try:
                self.S[k] = int(v, 16) if v.lower().startswith("0x") else int(v)
            except ValueError:
                pass

    # ---------- 主流程 ----------
    def run(self):
        self.preseed()
        if self.seed:
            for _k, _v in self.seed.items():
                self.S.setdefault(_k, _v)
        # v3.7: 一份文件里塞了好几段（变量被反复覆盖）时，按段拆开逐段求解，
        # 符号表跨段保留 —— 前一段解出的 p / q1p / e1 直接喂给后面
        segs = split_stages(self.text)
        if not segs:
            segs = [self.text]
        for idx, seg in enumerate(segs):
            tree = self._parse(seg)
            if tree is None:
                continue
            if len(segs) > 1:
                self._note(None, "——— 第 %d/%d 段 ———" % (idx + 1, len(segs)))
            _a0 = len(self.all_asserts)
            self._collect(tree.body)
            self._stage_hook(seg)      # 赋值先落进符号表, 段级特判才有东西可用
            self._solve_rounds()
            self.stage_snaps.append((dict(self.S), _a0, len(self.all_asserts)))
            if self.deadline and time.time() > self.deadline:
                if self.verbose:
                    print("    (到时间上限, 先收工)")
                break
        self._collect_pow_eqs()
        self._score_flags()
        return bool(self.flags) or bool(self.found)

    def _stage_hook(self, seg):
        """段级特判：`[p]*4, [4]*4` 这种「k 组模数广播同一明文 p 的 k 次方」"""
        m = re.search(r"\[p\]\s*\*\s*(\d+)\s*,\s*\[\s*(\d+)\s*\]\s*\*\s*(\d+)", seg)
        if not m:
            return
        k = int(m.group(1))
        ns, cs = self.S.get("n"), self.S.get("c")
        if not (isinstance(ns, list) and isinstance(cs, list)):
            return
        if not (len(ns) == len(cs) == k):
            return
        x, mod = 0, 1
        for ni, ci in zip(ns, cs):
            if math.gcd(mod, ni) != 1:
                return
            x, mod = crt_pair(x, mod, ci % ni, ni)
            if x is None:
                return
        r, exact = iroot(x, k)
        if exact and r > 1:
            self.S["p"] = r
            self.found["p"] = r
            self._harvest("p", r, tag="CRT %d 组广播开 %d 次方" % (k, k))
            self._note(None, "CRT 合 %d 组密文 → 开 %d 次方 → p = %s" % (k, k, _ch_short(r)))

    def _solve_rounds(self):
        rounds = 0
        while rounds < 80:
            rounds += 1
            if self.deadline and time.time() > self.deadline:
                break
            changed = False
            # a) 重试待定赋值（含跨段池注入）
            rest = []
            for targets, node, ln in self.pending:
                ok, v = self._eval_with_pool(node)
                if ok:
                    for t in targets:
                        self.S[t] = v
                    self._note(ln, "算出 %s = %s" % ("/".join(targets), _ch_short(v)))
                    changed = True
                else:
                    rest.append((targets, node, ln))
            self.pending = rest
            # b) 断言求解
            rest = []
            for lhs, rhs, ln in self.constraints:
                if self._known(lhs) and self._known(rhs):
                    continue
                upd, how = self.solver.step(lhs, rhs, self.S)
                if upd:
                    for k, v in upd.items():
                        self.S[k] = v
                        self.found[k] = v
                        self._harvest(k, v)
                    self._note(ln, "%s  [%s]" % (
                        ", ".join("%s = %s" % (k, _ch_short(v)) for k, v in upd.items()), how))
                    changed = True
                    continue
                rest.append((lhs, rhs, ln))
            self.constraints = rest
            # c) 拿当前符号表跑一遍标准 RSA 攻击
            if self.rsa_pass and self._rsa_changed():
                got = self._run_rsa_pass()
                if got:
                    changed = True
            if not changed:
                break
        self._collect_pow_eqs()
        self._score_flags()
        return bool(self.flags) or bool(self.found)

    def _score_flags(self):
        """拿题里每一条能算的断言给候选打分：全通过的才可信

        v3.7: 不再只认 `pow(X,e,mod)==c` 这一种写法，改成把 assert 两边都求值再比 ——
        `c1 == pow(flag, e1, p*q1)` 这种"密文在左边"的写法也能参加交叉验证。
        """
        if not self.flag_cands:
            self.flag_score = []
            return
        # 每条断言都按"它所在那一段结束时的符号表"求值 ——
        # 后面段把 n 覆盖掉也不会把前面段的断言算错
        checks, snaps = [], []
        if self.stage_snaps:
            for snap, a0, a1 in self.stage_snaps:
                for lhs, rhs, _ln in self.all_asserts[a0:a1]:
                    checks.append((lhs, rhs))
                    snaps.append(snap)
        if not checks:
            for lhs, rhs, _ln in self.all_asserts:
                checks.append((lhs, rhs))
                snaps.append(self.S)
        evaluable = []
        for (lhs, rhs), snap in zip(checks, snaps):
            try:
                _ch_ev(lhs, snap)
                _ch_ev(rhs, snap)
                evaluable.append((lhs, rhs, snap))
            except Exception:
                continue
        total = len(evaluable)
        out = []
        for v, t in self.flag_cands:
            ok = 0
            for lhs, rhs, snap in evaluable:
                S2 = dict(snap)
                S2["flag"] = v
                S2.setdefault("m", v)
                try:
                    if _ch_ev(lhs, S2) == _ch_ev(rhs, S2):
                        ok += 1
                except Exception:
                    pass
            out.append((ok, total, v, t))
        out.sort(key=lambda x: (-x[0], -_ch_printable(x[2])))
        self.flag_score = out

    def _known(self, node):
        try:
            _ch_ev(node, self.S)
            return True
        except _ChUnk:
            return False

    def _eval_with_pool(self, node):
        """求值; 缺 p/q 这类名字时从上一段的素数池里继承"""
        try:
            return True, _ch_ev(node, self.S)
        except _ChUnk as ex:
            for nm in ex.names:
                if nm in _CH_PRIME_ALIAS and nm in self.inject:
                    S2 = dict(self.S)
                    S2[nm] = self.inject[nm]
                    try:
                        v = _ch_ev(node, S2)
                    except _ChUnk:
                        continue
                    self.S[nm] = self.inject[nm]
                    self.inherit[nm] = (self.inject[nm], "指定注入")
                    self._note(None, "跨段继承 %s = %s（指定）" % (nm, _ch_short(self.inject[nm])))
                    return True, v
                if nm in _CH_PRIME_ALIAS:
                    self.wanted.add(nm)
            if not (self.use_pool and self.pool):
                return False, None
            pool_sorted = sorted(self.pool, key=lambda x: -x[0].bit_length())
            for nm in ex.names:
                if nm not in _CH_PRIME_ALIAS:
                    continue
                for pv, tag in pool_sorted:
                    S2 = dict(self.S)
                    S2[nm] = pv
                    try:
                        v = _ch_ev(node, S2)
                    except _ChUnk:
                        continue
                    self.S[nm] = pv
                    self.inherit[nm] = (pv, tag)
                    self._note(None, "跨段继承 %s = %s（来自%s）" % (nm, _ch_short(pv), tag))
                    return True, v
            return False, None

    def _rsa_changed(self):
        keys = tuple(sorted((k, id(v)) for k, v in self.S.items() if isinstance(v, int)))
        if keys == self._rsa_sig:
            return False
        self._rsa_sig = keys
        return True

    def _run_rsa_pass(self):
        try:
            got = self.rsa_pass(self.S)
        except Exception:
            return False
        if not got:
            return False
        m, how = got
        if not isinstance(m, int) or m <= 0:
            return False
        tag = "RSA 段解出"
        key = "m_stage%d" % (len(self.pool) + 1)
        self.S.setdefault(key, m)
        self.found[key] = m
        self._note(None, "%s -> %s（%s）" % (tag, _ch_short(m), how))
        self._harvest(key, m, tag=how)
        return True

    def _harvest(self, name, v, tag=None):
        if not isinstance(v, int) or isinstance(v, bool) or v <= 1:
            return
        if is_prime(v) and v.bit_length() >= 30:
            if all(pv != v for pv, _t in self.pool):
                self.pool.append((v, tag or ("%s 解出的素数" % name)))
        b = v.to_bytes((v.bit_length() + 7) // 8, "big") if v else b""
        if 3 <= len(b) <= 4096 and _ch_printable(v) > 0.95:
            looks = (b"{" in b and b"}" in b) or (
                self.flag_prefix and b.startswith(self.flag_prefix))
            if looks:
                t = _ch_render(v)
                if t not in self.flags:
                    self.flags.append(t)
                    self.flag_cands.append((v, t))
                    self._note(None, "★ 得到 flag: %s" % t)

    # ---------- AST 遍历 ----------
    def _parse(self, text=None):
        src = self.text if text is None else text
        # v3.7: py2 题面（1234L / print c,n）先降级再解析；另外长数字被折行时接回去
        cands = [src,
                 re.sub(r"(?<=\d)\s*\n\s*(?=\d{6,})", "", src)]
        fix = _py2_sanitize(src)
        if fix != src:
            cands.append(fix)
            cands.append(re.sub(r"(?<=\d)\s*\n\s*(?=\d{6,})", "", fix))
        for cand in cands:
            try:
                return ast.parse(cand)
            except SyntaxError:
                continue
        return None

    def _collect(self, body):
        for node in body:
            ln = getattr(node, "lineno", None)
            if isinstance(node, ast.Assign):
                targets = [t.id for t in node.targets if isinstance(t, ast.Name)]
                if not targets:
                    continue
                if any(t in _ch_names_of(node.value) for t in targets):
                    continue      # 自我引用 (flag = f(flag)) 跳过
                try:
                    v = _ch_ev(node.value, self.S)
                except _ChUnk:
                    self.pending.append((targets, node.value, ln))
                    continue
                for t in targets:
                    self.S[t] = v
            elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                try:
                    v = _ch_ev(node.value, self.S)
                    cur = self.S.get(node.target.id)
                    if cur is not None:
                        self.S[node.target.id] = _ch_aug(node.op, cur, v)
                except _ChUnk:
                    pass
            elif isinstance(node, ast.Assert):
                self._assert(node, ln)
            elif isinstance(node, (ast.If, ast.With, ast.Try)):
                self._collect(getattr(node, "body", []))
                for h in getattr(node, "handlers", []):
                    self._collect(getattr(h, "body", []))
                self._collect(getattr(node, "orelse", []))
                self._collect(getattr(node, "finalbody", []))

    def _assert(self, node, ln):
        t = node.test
        pairs, left = [], getattr(t, "left", None)
        if left is not None:
            for op, comp in zip(t.ops, t.comparators):
                if isinstance(op, ast.Eq):
                    pairs.append((left, comp))
                left = comp
        for lhs, rhs in pairs:
            if self._known(lhs) and self._known(rhs):
                if not self.solver.check(lhs, rhs, self.S):
                    self._note(ln, "[!] 断言与已知值冲突, 跳过该条")
                continue
            self.constraints.append((lhs, rhs, ln))
            self.all_asserts.append((lhs, rhs, ln))

    def _collect_pow_eqs(self):
        """用最终的符号表，把所有 assert 里能算出来的 pow(X,e,mod)==c 解析出来"""
        self.pow_eqs = []
        for lhs, rhs, ln in self.all_asserts:
            node = lhs
            if not isinstance(node, ast.Call):
                continue
            fname = node.func.id if isinstance(node.func, ast.Name) else ""
            if fname != "pow" or len(node.args) != 3:
                continue
            try:
                e = _ch_ev(node.args[1], self.S)
                m = _ch_ev(node.args[2], self.S)
                c = _ch_ev(rhs, self.S)
            except _ChUnk:
                continue
            if isinstance(e, int) and isinstance(m, int) and m > 1 and isinstance(c, int):
                self.pow_eqs.append((node.args[0], e, m, c, ln))

    def _record_pow_eq(self, lhs, rhs, ln):
        """记下 pow(X, e, mod) == c 形态的断言，供最后跨段交叉验证"""
        node = lhs
        if not isinstance(node, ast.Call):
            return
        fname = node.func.id if isinstance(node.func, ast.Name) else ""
        if fname != "pow" or len(node.args) != 3:
            return
        try:
            e = _ch_ev(node.args[1], self.S)
            m = _ch_ev(node.args[2], self.S)
            c = _ch_ev(rhs, self.S)
        except _ChUnk:
            return
        if isinstance(e, int) and isinstance(m, int) and m > 1 and isinstance(c, int):
            self.pow_eqs.append((node.args[0], e, m, c, ln))


def _ch_aug(op, a, b):
    if isinstance(op, ast.Add):
        return a + b
    if isinstance(op, ast.Sub):
        return a - b
    if isinstance(op, ast.Mult):
        return a * b
    if isinstance(op, (ast.Div, ast.FloorDiv)):
        return a // b
    if isinstance(op, ast.Mod):
        return a % b
    if isinstance(op, ast.Pow):
        return a ** b
    raise _ChUnk()


if __name__ == "__main__":
    sys.exit(main())
