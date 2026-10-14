"""check_paper.py -- recompute the numbers printed in preprint/main.tex.

  * Table 1 (the index I(n), 3 <= n <= 30), the footnote values I(3), I(4), I(5), and I(30) as
    printed in the introduction and in the caption of Figure 1, from Theorem C(i) evaluated by an
    independent implementation (exact integers) and from Theorem C(ii);
  * Table 2 (the largest number of distinct eigenvalues over all symmetric S) by exhaustive search;
  * Example 6.1 (two Cayley graphs on Z/24), Figure 3 (the decagonal prism) and Proposition 5.2 for
    k = 2, numerically with a clear gap between distinct and equal values.

Usage: python3 -I check_paper.py preprint/main.tex
"""
import cmath
import itertools
import math
import re
import sys

TEX = open(sys.argv[1]).read()
failures = 0


def report(ok, what):
    global failures
    print(("ok    " if ok else "FAIL  ") + what)
    failures += not ok


def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r


def eps(d):
    return 1 if d <= 2 else 2


def index_pairs(n):
    """Theorem C(i): product over d | d' | n with d'/d a prime power p^k, k >= 1."""
    divs = [d for d in range(1, n + 1) if n % d == 0]
    r = 1
    for d in divs:
        for e in divs:
            if e > d and e % d == 0:
                f = factor(e // d)
                if len(f) == 1:
                    (p,) = f
                    r *= p ** (2 * phi(d) // (eps(d) * eps(e)))
    return r


def index_valuations(n):
    """Theorem C(ii)."""
    r = 1
    for p, a in factor(n).items():
        m = n // p**a
        if p == 2:
            v = (n - m + 2 * a + 1)
            assert v % 2 == 0
            v //= 2
        else:
            v2 = (n - m) // (p - 1) + a * math.gcd(2, n)
            assert v2 % 2 == 0
            v = v2 // 2
        r *= p**v
    return r


def parse_power_product(s):
    """'2^{14}\\,3^5' -> 2^14 * 3^5."""
    r = 1
    for base, exp1, exp2 in re.findall(r"(\d+)(?:\^\{(\d+)\}|\^(\d))?", s.replace(r"\,", " ")):
        r *= int(base) ** int(exp1 or exp2 or 1)
    return r


# ---- Table 1
tab = re.search(r"n & I\(n\) & n & I\(n\) & n & I\(n\)\\\\\s*\\midrule(.*?)\\bottomrule", TEX, re.S).group(1)
printed = {}
for line in tab.strip().splitlines():
    cells = [c.strip() for c in line.strip().rstrip("\\").split("&")]
    for i in range(0, len(cells) - 1, 2):
        if cells[i]:
            printed[int(cells[i])] = parse_power_product(cells[i + 1])
report(sorted(printed) == list(range(3, 31)), "Table 1 lists n = 3, ..., 30")
bad = [n for n in printed if not (printed[n] == index_pairs(n) == index_valuations(n))]
report(not bad, f"Table 1 agrees with Theorem C(i) and C(ii) for all 28 entries {bad if bad else ''}")
report(all(index_pairs(n) == index_valuations(n) for n in range(3, 401)), "Theorem C(i) = C(ii) for 3 <= n <= 400")
report([index_pairs(n) for n in (3, 4, 5)] == [3, 16, 5] and "$I(n)=3,16,5$" in TEX, "footnote: I(3), I(4), I(5) = 3, 16, 5")
report(index_pairs(30) == 2**9 * 3**6 * 5**4 and TEX.count(r"2^9\cdot3^6\cdot5^4") == 2, "I(30) = 2^9 3^6 5^4 (introduction, Figure 1)")
report(all(index_pairs(p) == p for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)), "I(p) = p for primes p < 48 (Figure 2 caption)")


# ---- eigenvalue counts
def eigenvalues(ns, S):
    G = list(itertools.product(*[range(n) for n in ns]))
    return [sum(cmath.exp(2j * math.pi * sum(k * a / n for k, a, n in zip(kk, s, ns))) for s in S).real for kk in G]


def distinct(vals, tol=1e-9, gap=1e-5):
    vals = sorted(vals)
    cnt = 1
    for a, b in zip(vals, vals[1:]):
        if b - a > tol:
            assert b - a > gap, "eigenvalues too close to decide numerically"
            cnt += 1
    return cnt


def max_distinct(ns):
    G = list(itertools.product(*[range(n) for n in ns]))
    neg = lambda g: tuple((-a) % n for a, n in zip(g, ns))
    classes, seen = [], set()
    for g in G:
        if any(g) and g not in seen:
            c = sorted({g, neg(g)})
            seen |= set(c)
            classes.append(c)
    val = [[sum(math.cos(2 * math.pi * sum(k * a / n for k, a, n in zip(kk, g, ns))) for g in c) for c in classes] for kk in G]
    best = 0
    for mask in range(1, 1 << len(classes)):
        vals = [sum(row[j] for j in range(len(classes)) if mask >> j & 1) for row in val]
        best = max(best, distinct(vals))
    t = sum(1 for g in G if neg(g) == g)
    return len(G), best, (len(G) + t) // 2


GROUPS = {
    r"$(\Z/2)^2$": (2, 2), r"$\Z/2\times\Z/4$": (2, 4), r"$(\Z/2)^3$": (2, 2, 2), r"$(\Z/3)^2$": (3, 3),
    r"$\Z/2\times\Z/6$": (2, 6), r"$\Z/4\times\Z/4$": (4, 4), r"$(\Z/5)^2$": (5, 5),
    r"$\Z/2\times\Z/8$": (2, 8), r"$\Z/3\times\Z/6$": (3, 6), r"$\Z/2\times\Z/10$": (2, 10),
    r"$(\Z/2)^2\times\Z/4$": (2, 2, 4), r"$(\Z/2)^4$": (2, 2, 2, 2), r"$\Z/2\times\Z/12$": (2, 12),
    r"$\Z/3\times\Z/9$": (3, 9),
}
tab2 = re.search(r"\\label\{tab:maxdim\}", TEX)
body = re.findall(r"\\midrule(.*?)\\bottomrule", TEX[: tab2.start()], re.S)[-1]
rows = []
for line in body.strip().splitlines():
    cells = [c.strip() for c in line.strip().rstrip("\\").split("&")]
    rows += [cells[:4], cells[4:8]]
report(len(rows) == 14 and all(r[0] in GROUPS for r in rows), "Table 2 lists the fourteen groups")
for g, N, mx, bd in rows:
    got = max_distinct(GROUPS[g])
    report(got == (int(N), int(mx), int(bd)), f"Table 2 row {g}: N, max, bound = {got}")

# ---- Example 6.1
lam = eigenvalues((24,), [(1,), (23,), (5,), (19,)])
report(distinct(lam) == 7 and distinct(eigenvalues((24,), [(2,), (22,)])) == 7, "Example 6.1: both graphs have 7 distinct eigenvalues")
report(all(abs(lam[k] - v) < 1e-9 for k, v in zip((0, 2, 4, 8, 12), (4, 0, 2, -2, -4))), "Example 6.1: rational values 4, 0, 2, -2, -4 at k = 0, 2, 4, 8, 12")
report(abs(lam[1] - math.sqrt(6)) < 1e-9 and abs(lam[7] + math.sqrt(6)) < 1e-9, "Example 6.1: +-sqrt 6 at k = 1, 7")

# ---- Figure 3: the decagonal prism
pr = eigenvalues((10, 2), [(1, 0), (9, 0), (0, 1)])
g = (1 + math.sqrt(5)) / 2
claimed = [s * v for s in (1, -1) for v in (3, 1, g, g + 1, g - 1, g - 2)]
report(distinct(pr) == 12 == distinct(claimed) and all(min(abs(a - b) for b in pr) < 1e-9 for a in claimed), "Figure 3: the twelve eigenvalues of C_10 x K_2")

# ---- Proposition 5.2, k = 2 and 3
report(max_distinct((2, 2))[1] == 3 and max_distinct((3, 3))[1] == 3, "Proposition 5.2: bounds attained for k = 2")
report(max_distinct((2, 2, 2))[1] <= 5, "Proposition 5.2: (Z/2)^3 within 2^2 + 1")

print("check_paper:", "all checks passed" if not failures else f"{failures} failures")
sys.exit(1 if failures else 0)
