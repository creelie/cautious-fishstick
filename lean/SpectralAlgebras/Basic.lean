/-!
# A computable model of adjacency operators

Vectors in `ℤ^N` are lists of integers. A graph on `{0, …, N-1}` is given by its neighbour lists
`nb`, and `adj N nb u` is `A u` for its adjacency matrix `A`. Polynomials are coefficient lists with
the constant term first. Everything reduces in the kernel, so the certificates in the other files are
proved by `decide +kernel`.

Reduction "modulo `0`" means no reduction, so `p = 0` gives statements over `ℤ` and a prime `p`
gives statements over `𝔽_p`.
-/

namespace Spectral

/-- The zero vector of length `N`. -/
def zeros (N : Nat) : List Int := List.replicate N 0

/-- The standard basis vector `e_k` of length `N`. -/
def unit (N k : Nat) : List Int := (List.range N).map fun i => if i = k then 1 else 0

def vadd (u v : List Int) : List Int := List.zipWith (· + ·) u v

def vsmul (c : Int) (u : List Int) : List Int := u.map (c * ·)

/-- Reduce every entry modulo `p` (no reduction when `p = 0`). -/
def vmod (p : Nat) (u : List Int) : List Int := if p = 0 then u else u.map (· % (p : Int))

/-- Is `x` zero modulo `p` (zero itself when `p = 0`)? -/
def isZeroMod (p : Nat) (x : Int) : Bool := if p = 0 then x == 0 else x % (p : Int) == 0

/-- `A u` for the graph with neighbour lists `nb` on `N` vertices. -/
def adj (N : Nat) (nb : Nat → List Nat) (u : List Int) : List Int :=
  (List.range N).map fun i => ((nb i).map fun j => u.getD j 0).foldl (· + ·) 0

/-- `A u` for the cycle: `(A u)_i = u_(i+1) + u_(i-1)`, indices mod the length of `u`. -/
def adjCyc (u : List Int) : List Int := vadd (u.rotateLeft 1) (u.rotateRight 1)

/-- `f(A) u` by Horner's rule, reduced modulo `p`; `op` is `u ↦ A u`. -/
def peval (p : Nat) (op : List Int → List Int) (f : List Int) (u : List Int) : List Int :=
  f.foldr (fun c acc => vmod p (vadd (op acc) (vsmul c u))) (u.map fun _ => 0)

/-- `f(A) e_0 = 0` modulo `p`. For a Cayley graph on an abelian group `f(A)` commutes with the
translations, which carry `e_0` to every basis vector, so this says `f(A) = 0`. -/
def annihilates (p N : Nat) (op : List Int → List Int) (f : List Int) : Bool :=
  (peval p op f (unit N 0)).all (isZeroMod p)

/-- The Krylov vectors `e_0, A e_0, …, A^(r-1) e_0`, reduced modulo `p`. -/
def krylov (p N : Nat) (op : List Int → List Int) (r : Nat) : List (List Int) :=
  (List.range r).foldl (fun acc _ => acc ++ [match acc.getLast? with
      | none => unit N 0
      | some v => vmod p (op v)]) []

/-- The first `r` coordinates of the vectors `vs[0], …, vs[r-1]` form an upper triangular matrix
with nonzero diagonal modulo `p`. Then the vectors are linearly independent over `ℚ` (if `p = 0`)
or over `𝔽_p`. -/
def upperTri (p r : Nat) (vs : List (List Int)) : Bool :=
  vs.length == r &&
  (List.range r).all fun j =>
    let v := vs.getD j []
    !(isZeroMod p (v.getD j 0)) && (List.range r).all fun i => i ≤ j || isZeroMod p (v.getD i 0)

/-- As `upperTri`, but reading the coordinates `cols` instead of the first `r`. -/
def upperTriAt (p : Nat) (cols : List Nat) (vs : List (List Int)) : Bool :=
  vs.length == cols.length &&
  (List.range cols.length).all fun j =>
    let v := vs.getD j []
    !(isZeroMod p (v.getD (cols.getD j 0) 0)) &&
      (List.range cols.length).all fun i => i ≤ j || isZeroMod p (v.getD (cols.getD i 0) 0)

/-! ## Polynomials -/

/-- Product of polynomials, reduced modulo `p`. -/
def pmul (p : Nat) (f g : List Int) : List Int :=
  vmod p <| (List.range (f.length + g.length - 1)).map fun k =>
    (List.range (k + 1)).foldl (fun s i => s + f.getD i 0 * g.getD (k - i) 0) 0

def ppow (p : Nat) (f : List Int) : Nat → List Int
  | 0 => [1]
  | k + 1 => pmul p (ppow p f k) f

def pprod (p : Nat) (fs : List (List Int)) : List Int := fs.foldl (pmul p) [1]

/-- Degree of a polynomial whose leading coefficient is nonzero. -/
def pdeg (f : List Int) : Nat := f.length - 1

/-- `x * r mod f` for monic `f`, with `r` of length `deg f`. -/
def mulXMod (f r : List Int) : List Int :=
  let s := 0 :: r
  let t := s.getLastD 0
  (List.zipWith (fun a b => a - t * b) s f).dropLast

/-- `x^j mod f` for monic `f` of positive degree, as a list of length `deg f`. -/
def xpowMod (f : List Int) : Nat → List Int
  | 0 => unit (f.length - 1) 0
  | j + 1 => mulXMod f (xpowMod f j)

/-! ## Determinants (fraction-free elimination) -/

/-- One Bareiss step with pivot row `r0` and previous pivot `prev`. -/
def bstep (prev : Int) (r0 : List Int) (rest : List (List Int)) : List (List Int) :=
  let p := r0.headD 0
  rest.map fun r => List.zipWith (fun x y => (p * x - r.headD 0 * y) / prev) r.tail r0.tail

/-- Move a row with nonzero first entry to the top; the flag records a swap. -/
def pivotRow : List (List Int) → Option (List Int × List (List Int) × Bool)
  | [] => none
  | r :: rest =>
    if r.headD 0 != 0 then some (r, rest, false)
    else match pivotRow rest with
      | none => none
      | some (q, rest', _) => some (q, r :: rest', true)

/-- Determinant of a square integer matrix (given as a list of rows) by Bareiss' algorithm. -/
def detAux : Nat → Int → Int → List (List Int) → Int
  | 0, _, _, _ => 0
  | _ + 1, prev, sgn, [] => sgn * prev
  | fuel + 1, prev, sgn, M =>
    match pivotRow M with
    | none => 0
    | some (r0, rest, swapped) =>
      detAux fuel (r0.headD 0) (if swapped then -sgn else sgn) (bstep prev r0 rest)

def det (M : List (List Int)) : Int := detAux (M.length + 1) 1 1 M

def dot (u v : List Int) : Int := (List.zipWith (· * ·) u v).foldl (· + ·) 0

/-- The Gram matrix of a list of vectors; its determinant is nonzero exactly when the vectors are
linearly independent over `ℚ`. -/
def gram (vs : List (List Int)) : List (List Int) := vs.map fun v => vs.map fun w => dot v w

/-! ## Arithmetic -/

def divisors (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d > 0 && n % d == 0

def totient (n : Nat) : Nat := ((List.range n).filter fun i => Nat.gcd i n == 1).length

def minFac (n : Nat) : Nat := ((List.range (n + 1)).filter fun d => d ≥ 2 && n % d == 0).headD n

/-- `some p` if `q = p^k` with `p` prime and `k ≥ 1`. -/
def primePowBase (q : Nat) : Option Nat :=
  if q < 2 then none
  else
    let p := minFac q
    if (List.range (q + 1)).any (fun k => k ≥ 1 && p ^ k == q) then some p else none

/-- The largest power of `p` dividing `n` (as an exponent), for `n ≥ 1` and `p ≥ 2`. -/
def vpow (p n : Nat) : Nat := ((List.range (n + 1)).filter fun k => n % (p ^ k) == 0).length - 1

/-! ## Rank modulo a prime -/

/-- `a^k mod P` by repeated squaring. -/
def powMod (P : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % P
  | fuel + 1, a, k =>
    if k == 0 then 1 % P
    else
      let h := powMod P fuel (a * a % P) (k / 2)
      if k % 2 == 1 then a * h % P else h

/-- Inverse modulo the prime `P` (Fermat). -/
def invMod (P a : Nat) : Nat := powMod P 64 (a % P) (P - 2)

def toNatMod (P : Nat) (x : Int) : Nat := (x % (P : Int)).toNat

/-- Rank over `𝔽_P` of a list of integer vectors, by Gaussian elimination. -/
def rankAux (P : Nat) : Nat → List (List Nat) → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, v :: vs =>
    match (v.zip (List.range v.length)).find? (fun e => e.1 != 0) with
    | none => rankAux P fuel vs
    | some (a, c) =>
      let ia := invMod P a
      let elim := fun (w : List Nat) =>
        let f := w.getD c 0 * ia % P
        List.zipWith (fun x y => (x + P * P - f * y) % P) w v
      1 + rankAux P fuel (vs.map elim)

def rankMod (P : Nat) (vs : List (List Int)) : Nat :=
  rankAux P (vs.length + 1) (vs.map fun v => v.map (toNatMod P))

/-- The prime `2^31 - 1`. A full rank modulo `P` implies full rank over `ℚ`. -/
def bigP : Nat := 2147483647

end Spectral
