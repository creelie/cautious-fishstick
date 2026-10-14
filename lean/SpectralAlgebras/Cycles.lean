import SpectralAlgebras.Basic

/-!
# Cycles

`psi d` is the minimal polynomial `Ψ_d` of `2 cos(2π/d)` for `d ≤ 30` (constant term first), and
`mC n = ∏_{d ∣ n} Ψ_d`. For every `3 ≤ n ≤ 30`:

* over `ℤ`, `mC n` annihilates the adjacency matrix `A` of `C_n`, and `e_0, A e_0, …, A^⌊n/2⌋ e_0`
  are linearly independent (upper triangular in the coordinates `0, …, ⌊n/2⌋`). Hence `mC n`, of degree
  `⌊n/2⌋ + 1`, is the minimal polynomial of `A` over `ℚ`;
* for each prime `p ≤ 7` dividing `n`, the polynomial `muP n p` of Theorem B annihilates `A` modulo `p`
  and the Krylov vectors up to its degree are independent over `𝔽_p`, so `muP n p` is the minimal
  polynomial over `𝔽_p`, of degree `⌊n/2⌋ + 1` for odd `p` and `n/2` for `p = 2`.
-/

namespace Spectral

def psi : Nat → List Int
  | 1 => [-2, 1]
  | 2 => [2, 1]
  | 3 => [1, 1]
  | 4 => [0, 1]
  | 5 => [-1, 1, 1]
  | 6 => [-1, 1]
  | 7 => [-1, -2, 1, 1]
  | 8 => [-2, 0, 1]
  | 9 => [1, -3, 0, 1]
  | 10 => [-1, -1, 1]
  | 11 => [1, 3, -3, -4, 1, 1]
  | 12 => [-3, 0, 1]
  | 13 => [-1, 3, 6, -4, -5, 1, 1]
  | 14 => [1, -2, -1, 1]
  | 15 => [1, 4, -4, -1, 1]
  | 16 => [2, 0, -4, 0, 1]
  | 17 => [1, -4, -10, 10, 15, -6, -7, 1, 1]
  | 18 => [-1, -3, 0, 1]
  | 19 => [1, 5, -10, -20, 15, 21, -7, -8, 1, 1]
  | 20 => [5, 0, -5, 0, 1]
  | 21 => [1, -8, 8, 6, -6, -1, 1]
  | 22 => [-1, 3, 3, -4, -1, 1]
  | 23 => [-1, -6, 15, 35, -35, -56, 28, 36, -9, -10, 1, 1]
  | 24 => [1, 0, -4, 0, 1]
  | 25 => [-1, 5, 25, -5, -50, 1, 35, 0, -10, 0, 1]
  | 26 => [-1, -3, 6, 4, -5, -1, 1]
  | 27 => [1, 9, 0, -30, 0, 27, 0, -9, 0, 1]
  | 28 => [-7, 0, 14, 0, -7, 0, 1]
  | 29 => [-1, 7, 28, -56, -126, 126, 210, -120, -165, 55, 66, -12, -13, 1, 1]
  | 30 => [1, -4, -4, 1, 1]
  | _ => [1]

/-- `∏_{d ∣ n} Ψ_d`, the minimal polynomial of `A(C_n)` over `ℚ`. -/
def mC (n : Nat) : List Int := pprod 0 ((divisors n).map psi)

/-- Theorem B's polynomial `∏_{d ∣ m} Ψ_d^(e_d)` modulo `p`, where `n = p^a m`, `q = p^a`,
`e_d = q` for `d ≥ 3` and `e_d = ⌈q/2⌉` for `d ≤ 2`. -/
def muP (n p : Nat) : List Int :=
  let q := p ^ vpow p n
  pprod p ((divisors (n / q)).map fun d => ppow p (psi d) (if d ≤ 2 then (q + 1) / 2 else q))

def certZ (n : Nat) : Bool :=
  pdeg (mC n) == n / 2 + 1 &&
  annihilates 0 n adjCyc (mC n) &&
  upperTri 0 (n / 2 + 1) (krylov 0 n adjCyc (n / 2 + 1))

def certP (n p : Nat) : Bool :=
  let r := pdeg (muP n p)
  r == (if p == 2 then n / 2 else n / 2 + 1) &&
  annihilates p n adjCyc (muP n p) &&
  upperTri p r (krylov p n adjCyc r)

/-! ### Over `ℚ`: `mC n` is the minimal polynomial of `A(C_n)`, `3 ≤ n ≤ 30` -/

theorem minpoly_Q_3 : certZ 3 = true := by decide +kernel
theorem minpoly_Q_4 : certZ 4 = true := by decide +kernel
theorem minpoly_Q_5 : certZ 5 = true := by decide +kernel
theorem minpoly_Q_6 : certZ 6 = true := by decide +kernel
theorem minpoly_Q_7 : certZ 7 = true := by decide +kernel
theorem minpoly_Q_8 : certZ 8 = true := by decide +kernel
theorem minpoly_Q_9 : certZ 9 = true := by decide +kernel
theorem minpoly_Q_10 : certZ 10 = true := by decide +kernel
theorem minpoly_Q_11 : certZ 11 = true := by decide +kernel
theorem minpoly_Q_12 : certZ 12 = true := by decide +kernel
theorem minpoly_Q_13 : certZ 13 = true := by decide +kernel
theorem minpoly_Q_14 : certZ 14 = true := by decide +kernel
theorem minpoly_Q_15 : certZ 15 = true := by decide +kernel
theorem minpoly_Q_16 : certZ 16 = true := by decide +kernel
theorem minpoly_Q_17 : certZ 17 = true := by decide +kernel
theorem minpoly_Q_18 : certZ 18 = true := by decide +kernel
theorem minpoly_Q_19 : certZ 19 = true := by decide +kernel
theorem minpoly_Q_20 : certZ 20 = true := by decide +kernel
theorem minpoly_Q_21 : certZ 21 = true := by decide +kernel
theorem minpoly_Q_22 : certZ 22 = true := by decide +kernel
theorem minpoly_Q_23 : certZ 23 = true := by decide +kernel
theorem minpoly_Q_24 : certZ 24 = true := by decide +kernel
theorem minpoly_Q_25 : certZ 25 = true := by decide +kernel
theorem minpoly_Q_26 : certZ 26 = true := by decide +kernel
theorem minpoly_Q_27 : certZ 27 = true := by decide +kernel
theorem minpoly_Q_28 : certZ 28 = true := by decide +kernel
theorem minpoly_Q_29 : certZ 29 = true := by decide +kernel
theorem minpoly_Q_30 : certZ 30 = true := by decide +kernel

/-! ### Over `𝔽_p`, `p ≤ 7`, `p ∣ n ≤ 30`: `muP n p` is the minimal polynomial (Theorem B) -/

theorem minpoly_F3_3 : certP 3 3 = true := by decide +kernel
theorem minpoly_F2_4 : certP 4 2 = true := by decide +kernel
theorem minpoly_F5_5 : certP 5 5 = true := by decide +kernel
theorem minpoly_F2_6 : certP 6 2 = true := by decide +kernel
theorem minpoly_F3_6 : certP 6 3 = true := by decide +kernel
theorem minpoly_F7_7 : certP 7 7 = true := by decide +kernel
theorem minpoly_F2_8 : certP 8 2 = true := by decide +kernel
theorem minpoly_F3_9 : certP 9 3 = true := by decide +kernel
theorem minpoly_F2_10 : certP 10 2 = true := by decide +kernel
theorem minpoly_F5_10 : certP 10 5 = true := by decide +kernel
theorem minpoly_F2_12 : certP 12 2 = true := by decide +kernel
theorem minpoly_F3_12 : certP 12 3 = true := by decide +kernel
theorem minpoly_F2_14 : certP 14 2 = true := by decide +kernel
theorem minpoly_F7_14 : certP 14 7 = true := by decide +kernel
theorem minpoly_F3_15 : certP 15 3 = true := by decide +kernel
theorem minpoly_F5_15 : certP 15 5 = true := by decide +kernel
theorem minpoly_F2_16 : certP 16 2 = true := by decide +kernel
theorem minpoly_F2_18 : certP 18 2 = true := by decide +kernel
theorem minpoly_F3_18 : certP 18 3 = true := by decide +kernel
theorem minpoly_F2_20 : certP 20 2 = true := by decide +kernel
theorem minpoly_F5_20 : certP 20 5 = true := by decide +kernel
theorem minpoly_F3_21 : certP 21 3 = true := by decide +kernel
theorem minpoly_F7_21 : certP 21 7 = true := by decide +kernel
theorem minpoly_F2_22 : certP 22 2 = true := by decide +kernel
theorem minpoly_F2_24 : certP 24 2 = true := by decide +kernel
theorem minpoly_F3_24 : certP 24 3 = true := by decide +kernel
theorem minpoly_F5_25 : certP 25 5 = true := by decide +kernel
theorem minpoly_F2_26 : certP 26 2 = true := by decide +kernel
theorem minpoly_F3_27 : certP 27 3 = true := by decide +kernel
theorem minpoly_F2_28 : certP 28 2 = true := by decide +kernel
theorem minpoly_F7_28 : certP 28 7 = true := by decide +kernel
theorem minpoly_F2_30 : certP 30 2 = true := by decide +kernel
theorem minpoly_F3_30 : certP 30 3 = true := by decide +kernel
theorem minpoly_F5_30 : certP 30 5 = true := by decide +kernel

end Spectral
