import SpectralAlgebras.Cycles

/-!
# The index of `ℤ[A(C_n)]` in the maximal order

`ℤ[A(C_n)] ≅ ℤ[x]/(mC n)` embeds in `∏_{d ∣ n} ℤ[x]/(Ψ_d)`, which is the maximal order because
`ℤ[x]/(Ψ_d) ≅ ℤ[2 cos(2π/d)]` is the ring of integers of `ℚ(ζ_d)^+`. In the power bases the embedding
has the matrix `embedMatrix n`, so its determinant is `± I(n)`. We check the values of Table 1 for
`n ≤ 16`, the product formula of Theorem C(i) for `n ≤ 30`, and the valuation formula of Theorem C(ii)
for `n ≤ 60`.
-/

namespace Spectral

/-- Row `j`: the coordinates of `x^j` in `∏_{d ∣ n} ℤ[x]/(Ψ_d)`. -/
def embedMatrix (n : Nat) : List (List Int) :=
  (List.range (pdeg (mC n))).map fun j => ((divisors n).map fun d => xpowMod (psi d) j).flatten

def indexDet (n : Nat) : Nat := (det (embedMatrix n)).natAbs

def eps (d : Nat) : Nat := if d ≤ 2 then 1 else 2

/-- Theorem C(i): the product over `d ∣ d' ∣ n`, `d'/d = p^k`, of `p^(2φ(d)/(ε_d ε_d'))`. -/
def formulaIndex (n : Nat) : Nat :=
  ((divisors n).flatMap fun d => ((divisors n).filter fun e => d < e && e % d == 0).map fun e =>
    match primePowBase (e / d) with
    | some p => p ^ (2 * totient d / (eps d * eps e))
    | none => 1).foldl (· * ·) 1

/-- Theorem C(ii): the exponent of `p` in `I(n)`. -/
def vform (n p : Nat) : Nat :=
  let a := vpow p n
  let m := n / p ^ a
  if p == 2 then (n - m + 2 * a + 1) / 2 else ((n - m) / (p - 1) + a * Nat.gcd 2 n) / 2

def primesDividing (n : Nat) : List Nat := (divisors n).filter fun p => p ≥ 2 && minFac p == p

def valuationIndex (n : Nat) : Nat := ((primesDividing n).map fun p => p ^ vform n p).foldl (· * ·) 1

theorem index_3 : indexDet 3 = 3 := by decide +kernel
theorem index_4 : indexDet 4 = 16 := by decide +kernel
theorem index_5 : indexDet 5 = 5 := by decide +kernel
theorem index_6 : indexDet 6 = 72 := by decide +kernel
theorem index_7 : indexDet 7 = 7 := by decide +kernel
theorem index_8 : indexDet 8 = 128 := by decide +kernel
theorem index_9 : indexDet 9 = 27 := by decide +kernel
theorem index_10 : indexDet 10 = 400 := by decide +kernel
theorem index_11 : indexDet 11 = 11 := by decide +kernel
theorem index_12 : indexDet 12 = 3456 := by decide +kernel
theorem index_13 : indexDet 13 = 13 := by decide +kernel
theorem index_14 : indexDet 14 = 1568 := by decide +kernel
theorem index_15 : indexDet 15 = 675 := by decide +kernel
theorem index_16 : indexDet 16 = 4096 := by decide +kernel

theorem formula_3 : formulaIndex 3 = indexDet 3 := by decide +kernel
theorem formula_4 : formulaIndex 4 = indexDet 4 := by decide +kernel
theorem formula_5 : formulaIndex 5 = indexDet 5 := by decide +kernel
theorem formula_6 : formulaIndex 6 = indexDet 6 := by decide +kernel
theorem formula_7 : formulaIndex 7 = indexDet 7 := by decide +kernel
theorem formula_8 : formulaIndex 8 = indexDet 8 := by decide +kernel
theorem formula_9 : formulaIndex 9 = indexDet 9 := by decide +kernel
theorem formula_10 : formulaIndex 10 = indexDet 10 := by decide +kernel
theorem formula_11 : formulaIndex 11 = indexDet 11 := by decide +kernel
theorem formula_12 : formulaIndex 12 = indexDet 12 := by decide +kernel
theorem formula_13 : formulaIndex 13 = indexDet 13 := by decide +kernel
theorem formula_14 : formulaIndex 14 = indexDet 14 := by decide +kernel
theorem formula_15 : formulaIndex 15 = indexDet 15 := by decide +kernel
theorem formula_16 : formulaIndex 16 = indexDet 16 := by decide +kernel

/-- Table 1 (n ≤ 30) from the product formula. -/
def table1 : List (Nat × Nat) :=
  [(3, 3), (4, 16), (5, 5), (6, 72), (7, 7), (8, 128), (9, 27), (10, 400), (11, 11), (12, 3456), (13, 13), (14, 1568), (15, 675), (16, 4096), (17, 17), (18, 46656), (19, 19), (20, 128000), (21, 3969), (22, 15488), (23, 23), (24, 3981312), (25, 625), (26, 43264), (27, 6561), (28, 2809856), (29, 29), (30, 233280000)]

theorem table1_formula : table1.all (fun e => formulaIndex e.1 == e.2) = true := by decide +kernel

theorem valuation_formula : (List.range' 3 58).all (fun n => valuationIndex n == formulaIndex n) = true := by
  decide +kernel

end Spectral
