#!/usr/bin/env bash
# run_all.sh -- every check outside Lean; outputs go to build/.
#   PARI/GP: thmA.gp (Theorem A, 2412 cases), thmB.gp (Theorem B, p <= 7, n <= 80), thmC.gp (Theorem C
#            and Lemma 4.3 against discriminants, n <= 150; valuation formula, n <= 400), sym.gp
#            (Proposition 4.1, n <= 40), thmD.gp (Theorem D, exactly for m <= 60, numerically m <= 300)
#   Python:  semisimple.py (Theorem A without PARI), check_paper.py (every number printed in
#            preprint/main.tex: both tables, the footnotes, the examples, the prism)
#   Lean:    the tables psi and table1 in lean/ must match PARI/GP and Table 1 (check_lean_tables.py)
#   Figure:  gen_bars.py must reproduce preprint/figures/bars.tex exactly
# Needs PARI/GP and Python 3.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
B="$ROOT/build"
mkdir -p "$B"
cd "$ROOT/verification/gp"

expect_zero() {  # every line matching $2 in file $1 must end in ": 0"
  grep "$2" "$1" > /dev/null || { echo "run_all.sh: no '$2' line in $1" >&2; exit 1; }
  if grep "$2" "$1" | grep -v ': 0$'; then echo "run_all.sh: failures in $1" >&2; exit 1; fi
}

for t in thmA thmB thmC sym thmD; do
  echo "== PARI/GP: $t.gp"
  gp -q -s 400000000 "$t.gp" | tee "$B/$t.txt"
done
grep -q "Theorem A checks: 2412 cases, 0 failures" "$B/thmA.txt"
expect_zero "$B/thmB.txt" "mismatches up to"
expect_zero "$B/thmC.txt" "up to"
expect_zero "$B/sym.txt" "mismatches up to"
expect_zero "$B/thmD.txt" "failures"

cd "$ROOT"
echo "== Python: Theorem A without PARI"
python3 -I verification/python/semisimple.py | tee "$B/semisimple.txt"

echo "== Python: every number in the paper"
python3 -I verification/python/check_paper.py preprint/main.tex | tee "$B/check_paper.txt"

echo "== the Lean data tables are the paper's"
( cd verification/gp && gp -q psi.gp ) > "$B/psi.txt"
python3 -I verification/python/check_lean_tables.py lean/SpectralAlgebras "$B/psi.txt" preprint/main.tex

echo "== the bar chart is the generator's output"
python3 -I scripts/gen_bars.py "$B/bars.tex"
cmp "$B/bars.tex" preprint/figures/bars.tex
echo "all checks passed"
