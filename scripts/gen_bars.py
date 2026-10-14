#!/usr/bin/env python3
"""gen_bars.py -- write preprint/figures/bars.tex, the 3D bar chart of log I(n)/n for 3 <= n <= 48.

I(n) is computed from Theorem C(ii) (the valuation formula), which verification/gp/thmC.gp checks
against discriminants for n <= 150.
"""
import math, os, sys

def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def log_index(n):
    tot = 0.0
    for p, a in factor(n).items():
        m = n // p**a
        if p == 2: v = (n - m + 2*a + 1) // 2
        else: v = ((n - m) // (p - 1) + a * math.gcd(2, n)) // 2
        tot += v * math.log(p)
    return tot

N0, N1 = 3, 48
W, H, DX, DY = 0.66, 7.0, 0.30, 0.12   # bar width (x units), height scale, depth offsets
out = [r"""\documentclass[tikz,border=6pt]{standalone}
\usepackage{amsmath}
\definecolor{cE}{RGB}{31,94,165}\definecolor{cO}{RGB}{214,96,33}\definecolor{cP}{RGB}{120,120,120}
\pgfdeclarelayer{bg}\pgfsetlayers{bg,main}
\begin{document}
\begin{tikzpicture}[x=0.36cm,y=1cm,line join=round]"""]
R = N1 - N0 + 1.2
for g in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7]:
    y = g * H
    out.append(r"\draw[black!15,line width=0.3pt] (-0.4,%.3f) -- (%.2f,%.3f);" % (y, R, y))
    out.append(r"\node[font=\small,anchor=east] at (-0.5,%.3f) {$%.1f$};" % (y, g))
out.append(r"\draw[black!60,line width=0.5pt] (-0.4,0) -- (%.2f,0);" % R)
isprime = lambda n: n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
for n in range(N0, N1 + 1):
    x, h = n - N0, H * log_index(n) / n
    col = 'cP' if isprime(n) else ('cE' if n % 2 == 0 else 'cO')
    out.append(r"\fill[%s!100!black!75] (%.3f,0) -- (%.3f,%.3f) -- (%.3f,%.3f) -- (%.3f,%.3f) -- cycle;"
               % (col, x + W, x + W + DX, DY, x + W + DX, h + DY, x + W, h))
    out.append(r"\fill[%s!45] (%.3f,%.3f) -- (%.3f,%.3f) -- (%.3f,%.3f) -- (%.3f,%.3f) -- cycle;"
               % (col, x, h, x + W, h, x + W + DX, h + DY, x + DX, h + DY))
    out.append(r"\fill[%s!85] (%.3f,0) rectangle (%.3f,%.3f);" % (col, x, x + W, h))
    out.append(r"\draw[black!45,line width=0.2pt] (%.3f,0) rectangle (%.3f,%.3f);" % (x, x + W, h))
    if n % 3 == 0:
        out.append(r"\node[font=\small,anchor=north] at (%.3f,-0.05) {$%d$};" % (x + W / 2, n))
out.append(r"\node at (%.2f,-0.75) {$n$};" % ((N1 - N0) / 2))
out.append(r"\node[rotate=90] at (-4.0,2.5) {$\log I(n)/n$};")
for i, (col, lab) in enumerate([('cE', 'even $n$'), ('cO', 'odd composite $n$'), ('cP', 'prime $n$')]):
    lx = 17 + 10 * i
    out.append(r"\fill[%s!85] (%.2f,5.55) rectangle +(0.9,0.22);" % (col, lx))
    out.append(r"\node[font=\small,anchor=west] at (%.2f,5.66) {%s};" % (lx + 1.0, lab))
out.append(r"""\begin{pgfonlayer}{bg}
\fill[black!3,rounded corners=8pt] ([shift={(-6pt,-6pt)}]current bounding box.south west) rectangle ([shift={(6pt,6pt)}]current bounding box.north east);
\end{pgfonlayer}
\end{tikzpicture}
\end{document}""")
dest = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), '..', 'preprint', 'figures', 'bars.tex')
open(dest, 'w').write("\n".join(out) + "\n")
