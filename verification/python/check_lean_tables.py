"""check_lean_tables.py -- the data written into the Lean files must be the data of the paper.

  * the table `psi` in lean/SpectralAlgebras/Cycles.lean lists the minimal polynomials Psi_d,
    d <= 30, exactly as PARI/GP computes them (verification/gp/psi.gp);
  * the list `table1` in lean/SpectralAlgebras/Index.lean is Table 1 of preprint/main.tex.

Usage: python3 -I check_lean_tables.py lean/SpectralAlgebras build/psi.txt preprint/main.tex
"""
import os
import re
import sys

leandir, psitxt, tex = sys.argv[1:4]
bad = 0

lean = dict((int(d), [int(c) for c in cs.split(",")])
            for d, cs in re.findall(r"^\s*\|\s*(\d+)\s*=>\s*\[([^\]]*)\]", open(os.path.join(leandir, "Cycles.lean")).read(), re.M))
gp = {}
for line in open(psitxt):
    d, cs = line.split(" ", 1)
    gp[int(d)] = [int(c) for c in cs.strip().strip("[]").split(",")]
diff = [d for d in range(1, 31) if lean.get(d) != gp.get(d)]
print(f"Lean table psi: {len(lean)} entries, {len(diff)} differ from PARI/GP {diff if diff else ''}")
bad += bool(diff) or len(lean) != 30

body = re.search(r"def table1 : List \(Nat × Nat\) :=\s*\[(.*?)\]\n", open(os.path.join(leandir, "Index.lean")).read(), re.S).group(1)
t1 = {int(a): int(b) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)}
T = open(tex).read()
tab = re.search(r"n & I\(n\) & n & I\(n\) & n & I\(n\)\\\\\s*\\midrule(.*?)\\bottomrule", T, re.S).group(1)
printed = {}
for line in tab.strip().splitlines():
    cells = [c.strip() for c in line.strip().rstrip("\\").split("&")]
    for i in range(0, len(cells) - 1, 2):
        if cells[i]:
            v = 1
            for base, e1, e2 in re.findall(r"(\d+)(?:\^\{(\d+)\}|\^(\d))?", cells[i + 1].replace(r"\,", " ")):
                v *= int(base) ** int(e1 or e2 or 1)
            printed[int(cells[i])] = v
same = t1 == printed and len(t1) == 28
print(f"Lean table1: {len(t1)} entries, {'equal to' if same else 'DIFFERENT FROM'} Table 1 of the paper")
bad += not same
sys.exit(1 if bad else 0)
