import SpectralAlgebras.Index

/-!
# Prisms and the other examples

`prism m` is `C_m □ K_2 = Cay(ℤ/m × ℤ/2, {(±1, 0), (0, 1)})`, with `(x, y)` stored at index `2x + y`.
For `3 ≤ m ≤ 30` the polynomial `prismPoly m` annihilates its adjacency matrix and the Krylov vectors
`e_0, …, A^(r-1) e_0`, `r = deg prismPoly m`, have nonzero Gram determinant, so `r` is the number of
distinct eigenvalues. It equals the bound `(N + t)/2 = 2(⌊m/2⌋ + 1)` exactly when `4 ∤ m` and `6 ∤ m`
(Theorem D).
-/

namespace Spectral

def prism (m i : Nat) : List Nat :=
  let x := i / 2
  let y := i % 2
  [2 * ((x + 1) % m) + y, 2 * ((x + m - 1) % m) + y, 2 * x + (1 - y)]

/-- The same adjacency operator with the layers stored one after the other: `u = u₀ ++ u₁` with
`u_y` the values on `ℤ/m × {y}`. This is the fast form used below; `prism_layout` checks that the two
agree on every basis vector for `m ≤ 12`. -/
def prismOp (m : Nat) (u : List Int) : List Int :=
  let u0 := u.take m
  let u1 := u.drop m
  vadd (adjCyc u0) u1 ++ vadd (adjCyc u1) u0

/-- Reorder `(x, y) ↦ 2x + y` into `(x, y) ↦ x + m y`. -/
def relayout (m : Nat) (u : List Int) : List Int :=
  (List.range (2 * m)).map fun k => u.getD (2 * (k % m) + k / m) 0

/-- The minimal polynomial of `A(C_m □ K_2)`, constant term first. -/
def prismPoly : Nat → List Int
  | 3 => [0, 6, -5, -2, 1]
  | 4 => [9, 0, -10, 0, 1]
  | 5 => [-3, -8, 6, 14, -8, -2, 1]
  | 6 => [0, -36, 0, 49, 0, -14, 0, 1]
  | 7 => [-3, 16, -8, -38, 25, 20, -11, -2, 1]
  | 8 => [9, 0, -64, 0, 70, 0, -16, 0, 1]
  | 9 => [0, -18, 15, 78, -51, -88, 53, 26, -14, -2, 1]
  | 10 => [9, 0, -100, 0, 308, 0, -330, 0, 132, 0, -20, 0, 1]
  | 11 => [3, 20, -13, -148, 95, 258, -163, -156, 90, 32, -17, -2, 1]
  | 12 => [0, -144, 0, 484, 0, -484, 0, 165, 0, -22, 0, 1]
  | 13 => [3, -28, 15, 244, -163, -618, 395, 612, -371, -242, 136, 38, -20, -2, 1]
  | 14 => [9, 0, -208, 0, 1130, 0, -2418, 0, 2379, 0, -1118, 0, 251, 0, -26, 0, 1]
  | 15 => [0, 30, -25, -370, 245, 1304, -841, -1858, 1158, 1194, -702, -346, 191, 44, -23, -2, 1]
  | 16 => [9, 0, -244, 0, 1656, 0, -3700, 0, 3478, 0, -1468, 0, 296, 0, -28, 0, 1]
  | 17 => [-3, -32, 20, 546, -357, -2480, 1617, 4786, -3028, -4462, 2708, 2058, -1183, -468, 255, 50, -26, -2, 1]
  | 18 => [0, -324, 0, 3033, 0, -10782, 0, 18855, 0, -17698, 0, 9155, 0, -2614, 0, 406, 0, -32, 0, 1]
  | 19 => [-3, 40, -22, -762, 510, 4370, -2859, -10948, 7003, 13786, -8542, -9186, 5450, 3258, -1841, -608, 328, 56, -29, -2, 1]
  | 20 => [9, 0, -406, 0, 4167, 0, -16028, 0, 28469, 0, -25750, 0, 12341, 0, -3232, 0, 463, 0, -34, 0, 1]
  | 21 => [0, -42, 35, 1022, -679, -7280, 4774, 22828, -14724, -37116, 23325, 33398, -20281, -16948, 9870, 4848, -2703, -766, 410, 62, -32, -2, 1]
  | 22 => [9, 0, -478, 0, 6659, 0, -35672, 0, 96411, 0, -147432, 0, 134165, 0, -74036, 0, 24848, 0, -5034, 0, 597, 0, -38, 0, 1]
  | 23 => [3, 44, -27, -1352, 890, 11548, -7606, -44256, 28703, 89894, -57089, -104260, 64390, 71200, -42466, -28828, 16535, 6882, -3796, -942, 501, 68, -35, -2, 1]
  | 24 => [0, -576, 0, 8848, 0, -51088, 0, 143844, 0, -220600, 0, 194524, 0, -101304, 0, 31717, 0, -5992, 0, 666, 0, -40, 0, 1]
  | 25 => [3, -52, 29, 1736, -1162, -17596, 11606, 80896, -52691, -200078, 128077, 289300, -180938, -254232, 154454, 137740, -80884, -46068, 26093, 9414, -5147, -1136, 601, 74, -38, -2, 1]
  | 26 => [9, 0, -694, 0, 12911, 0, -96664, 0, 372049, 0, -833216, 0, 1157587, 0, -1030332, 0, 595783, 0, -224586, 0, 54966, 0, -8594, 0, 824, 0, -44, 0, 1]
  | 27 => [0, 54, -45, -2178, 1449, 25968, -17142, -140748, 92004, 415644, -267681, -730494, 461349, 799140, -492482, -555560, 332515, 247022, -143131, -70072, 39273, 12498, -6783, -1348, 710, 80, -41, -2, 1]
  | 28 => [9, 0, -766, 0, 16555, 0, -134004, 0, 542167, 0, -1242586, 0, 1720611, 0, -1490184, 0, 822776, 0, -293020, 0, 67546, 0, -9964, 0, 905, 0, -46, 0, 1]
  | 29 => [-3, -56, 34, 2710, -1790, -37238, 24637, 234884, -153943, -815218, 527534, 1707050, -1086382, -2266746, 1412693, 1958344, -1190203, -1113006, 657335, 416992, -238855, -102406, 56885, 16188, -8731, -1578, 828, 86, -44, -2, 1]
  | 30 => [0, -900, 0, 22825, 0, -227390, 0, 1178515, 0, -3616966, 0, 7059785, 0, -9126082, 0, 7988420, 0, -4786018, 0, 1969304, 0, -555334, 0, 106313, 0, -13510, 0, 1087, 0, -50, 0, 1]
  | _ => [1]

/-- The fast operator agrees with the neighbour lists. -/
def layoutOK (m : Nat) : Bool :=
  (List.range (2 * m)).all fun g =>
    relayout m (adj (2 * m) (prism m) (unit (2 * m) g)) == prismOp m (relayout m (unit (2 * m) g))

theorem prism_layout : (List.range' 3 10).all layoutOK = true := by decide +kernel

/-- `deg prismPoly m` is the number of distinct eigenvalues of the prism. -/
def prismCert (m : Nat) : Bool :=
  let r := pdeg (prismPoly m)
  annihilates 0 (2 * m) (prismOp m) (prismPoly m) &&
  rankMod bigP (krylov bigP (2 * m) (prismOp m) r) == r

/-- Theorem D for this `m`: the number of distinct eigenvalues reaches `2(⌊m/2⌋ + 1)` iff `4 ∤ m`
and `6 ∤ m`. -/
def prismD (m : Nat) : Bool :=
  prismCert m && ((pdeg (prismPoly m) == 2 * (m / 2 + 1)) == (m % 4 != 0 && m % 6 != 0))

theorem prism_3 : prismD 3 = true := by decide +kernel
theorem prism_4 : prismD 4 = true := by decide +kernel
theorem prism_5 : prismD 5 = true := by decide +kernel
theorem prism_6 : prismD 6 = true := by decide +kernel
theorem prism_7 : prismD 7 = true := by decide +kernel
theorem prism_8 : prismD 8 = true := by decide +kernel
theorem prism_9 : prismD 9 = true := by decide +kernel
theorem prism_10 : prismD 10 = true := by decide +kernel
theorem prism_11 : prismD 11 = true := by decide +kernel
theorem prism_12 : prismD 12 = true := by decide +kernel
theorem prism_13 : prismD 13 = true := by decide +kernel
theorem prism_14 : prismD 14 = true := by decide +kernel
theorem prism_15 : prismD 15 = true := by decide +kernel
theorem prism_16 : prismD 16 = true := by decide +kernel
theorem prism_17 : prismD 17 = true := by decide +kernel
theorem prism_18 : prismD 18 = true := by decide +kernel
theorem prism_19 : prismD 19 = true := by decide +kernel
theorem prism_20 : prismD 20 = true := by decide +kernel
theorem prism_21 : prismD 21 = true := by decide +kernel
theorem prism_22 : prismD 22 = true := by decide +kernel
theorem prism_23 : prismD 23 = true := by decide +kernel
theorem prism_24 : prismD 24 = true := by decide +kernel
theorem prism_25 : prismD 25 = true := by decide +kernel
theorem prism_26 : prismD 26 = true := by decide +kernel
theorem prism_27 : prismD 27 = true := by decide +kernel
theorem prism_28 : prismD 28 = true := by decide +kernel
theorem prism_29 : prismD 29 = true := by decide +kernel
theorem prism_30 : prismD 30 = true := by decide +kernel

/-- The decagonal prism has the twelve distinct eigenvalues `±3, ±1, ±φ, ±(φ+1), ±(φ-1), ±(φ-2)`:
its minimal polynomial is `(x²-9)(x²-1)(x²-x-1)(x²+x-1)(x²-3x+1)(x²+3x+1)`. -/
theorem decagonal_prism :
    prismPoly 10 = pprod 0 [[-9, 0, 1], [-1, 0, 1], [-1, -1, 1], [-1, 1, 1], [1, -3, 1], [1, 3, 1]] ∧
    pdeg (prismPoly 10) = 12 := by decide +kernel

/-! ## Example 3.2 (characteristic 3) -/

/-- `Cay(ℤ/6, {3})`, a perfect matching. -/
def matching6 (i : Nat) : List Nat := [(i + 3) % 6]

/-- `Cay(ℤ/6, {2, 4})`, two disjoint triangles. -/
def triangles6 (i : Nat) : List Nat := [(i + 2) % 6, (i + 4) % 6]

/-- Over `𝔽_3` the matching has minimal polynomial `x² - 1 = (x - 1)(x + 1)`, which is separable. -/
theorem matching_F3 :
    annihilates 3 6 (adj 6 matching6) [-1, 0, 1] = true ∧
    upperTriAt 3 [0, 3] (krylov 3 6 (adj 6 matching6) 2) = true := by decide +kernel

/-- Over `𝔽_3` the two triangles have minimal polynomial `(x + 1)²`, and `A³ = 2I`. -/
theorem triangles_F3 :
    annihilates 3 6 (adj 6 triangles6) [1, 2, 1] = true ∧
    upperTriAt 3 [0, 2] (krylov 3 6 (adj 6 triangles6) 2) = true ∧
    annihilates 3 6 (adj 6 triangles6) [-2, 0, 0, 1] = true := by decide +kernel

/-! ## Example 6.1 (two connection sets on `ℤ/24`) -/

def z24a (i : Nat) : List Nat := [(i + 2) % 24, (i + 22) % 24]

def z24b (i : Nat) : List Nat := [(i + 1) % 24, (i + 23) % 24, (i + 5) % 24, (i + 19) % 24]

/-- `S = {±2}` has minimal polynomial `mC 12 = ∏_{d ∣ 12} Ψ_d`, of degree `7`, whose only
irrational factor is `Ψ_12 = x² - 3`. -/
theorem z24_S :
    annihilates 0 24 (adj 24 z24a) (mC 12) = true ∧ pdeg (mC 12) = 7 ∧ psi 12 = [-3, 0, 1] ∧
    rankMod bigP (krylov bigP 24 (adj 24 z24a) 7) = 7 := by decide +kernel

/-- `S' = {±1, ±5}` has minimal polynomial `x(x - 4)(x + 4)(x - 2)(x + 2)(x² - 6)`, of degree `7`. -/
theorem z24_S' :
    annihilates 0 24 (adj 24 z24b) (pprod 0 [[0, 1], [-4, 1], [4, 1], [-2, 1], [2, 1], [-6, 0, 1]]) = true ∧
    rankMod bigP (krylov bigP 24 (adj 24 z24b) 7) = 7 := by decide +kernel

end Spectral
