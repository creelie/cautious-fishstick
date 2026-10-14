# Priority check: modular and integral spectral algebras of abelian Cayley graphs

Question: had anyone already published Theorems A–D of the paper, or answered the questions of
Bhattacharjee, Mandal and Bhattacharya, *Spectral algebras of abelian Cayley graphs*,
[arXiv:2609.09222](https://arxiv.org/abs/2609.09222) (v1, 7 September 2026, the only version), that
the paper settles?

- **Theorem A**: the Jacobson radical of the adjacency algebra of an abelian Cayley graph in
  characteristic p is (A − A^q), and the algebra is semisimple exactly when every element of S has
  order prime to p.
- **Theorem B**: the minimal polynomial of the cycle C_n over a field of characteristic p dividing n.
- **Theorem C**: the index I(n) of ℤ[A(C_n)] in the maximal order of ℚ[A(C_n)]; arXiv:2609.09222
  records the inclusion and leaves the index open.
- **Theorem D**: which prisms C_m □ K_2 attain the bound (N + t)/2 on the number of distinct
  eigenvalues; arXiv:2609.09222 (Remark 21.4) leaves open whether noncyclic groups attain it.

Checked 14 October 2026, 18:10–18:35 UTC.

| Source | Search | Result |
|---|---|---|
| arXiv API | `abs:"adjacency algebra" AND abs:Cayley`; `abs:"spectral algebra" AND abs:graph`; `abs:"Jacobson radical" AND abs:graph`; `abs:circulant AND abs:"minimal polynomial"`; `abs:"distinct eigenvalues" AND abs:Cayley`; `abs:"distinct eigenvalues" AND abs:circulant`; `abs:resultant AND abs:"real cyclotomic"`; newest first | arXiv:2609.09222 itself; arXiv:1707.02728 (the adjacency algebra of a unitary Cayley graph is a coherent algebra); arXiv:2310.06203 (graphs with three or four distinct eigenvalues from circulants); none treats characteristic p, the integral algebra, or the bound (N + t)/2 |
| arXiv:2609.09222 | version history | only v1; Theorem 6.1 covers characteristic not dividing N, Proposition 14.4 the semisimple quotient, Remarks 19.4 and 21.4 the dimension bound |
| OEIS | I(n) for n = 3, …, 12 (3, 16, 5, 72, 7, 128, 27, 400, 11, 3456); \|disc m_{C_n}\| for n = 3, …, 10 (9, 256, 125, 5184, 2401, 131072, 59049, 4000000) | no entries |
| Zenodo | `"adjacency algebra" Cayley`, `"spectral algebra" Cayley`, `circulant "minimal polynomial" characteristic`, `prism "distinct eigenvalues"` | nothing relevant |
| Web search | the radical of the adjacency algebra of a Cayley graph in characteristic p; the minimal polynomial of a cycle over a finite field; the index of ℤ[2cos(2π/n)]-type orders and of ℤ[C_n] in its maximal order; distinct eigenvalues of prisms and of abelian Cayley graphs; arXiv:2609.09222 | arXiv:2609.09222 and its summaries; arXiv:2512.06541 (Jacobson radicals of coherent configurations of partial geometries, a different family); de Smit on cyclic subgroup indices in group rings (a different index); nothing on Theorems A–D |
| Code and data repositories | web search for GitHub repositories on spectral or adjacency algebras of Cayley graphs, circulant minimal polynomials and indices of orders; arXiv:2609.09222 links no code or data repository | fostergreenwood/spectra (eigenvalues of Cayley graphs of complex reflection groups, GAP 3) and queue-miscreant/SymmetricGraph (a Haskell study toolkit); neither computes radicals, minimal polynomials in characteristic p, or indices |
| Semantic Scholar | papers citing arXiv:2609.09222 | the API refused the request (rate limit) |
| Classical literature | Lehmer (1933), Watkins–Zeitlin (1993): the minimal polynomial of 2cos(2π/n) over ℚ; Apostol (1970): resultants of cyclotomic polynomials; Loper–Werner (2016): resultants of the polynomials Ψ_d for d, d' ≥ 3; Mönius (2020, 2022): algebraic degree and splitting fields of circulant spectra; Babai (1979): spectra of Cayley graphs | the ingredients of the proofs, cited in the paper; none states Theorems A–D |

Conclusion: as of 14 October 2026 we found no earlier statement of Theorems A–D. The paper says
plainly which parts are standard: the quotient in Theorem A is Proposition 14.4 of arXiv:2609.09222,
the semisimplicity of group algebras of p′-groups is Maschke's theorem, Lemma 4.2 is the usual
index–resultant relation, and Lemma 4.3 rests on Apostol and, for d, d' ≥ 3, is Theorem 3.4 of
Loper and Werner. What is new is the explicit radical and the semisimplicity criterion (A), the
minimal polynomial of C_n in every characteristic (B), the index I(n) and its valuations (C), and the
prism criterion that answers Remark 21.4 and corrects Remark 19.4 of arXiv:2609.09222 (D).
