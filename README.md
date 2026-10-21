# CCDN Dimension Growth

A Lean 4 formalisation of Castryck–Cluckers–Dittmann–Nguyen's dimension-growth
paper, including coefficient-uniform point bounds.

The Lean namespace and module hierarchy are `CCDN`: use `import CCDN` for the
whole library, or a specific module such as `CCDN.AffineCurveBound`.

## Statement surface (Palomar)

[`Challenge.lean`](Challenge.lean) is the file to audit. It imports only Mathlib. It
defines the counting functions, zero sets and Hilbert-function notions of degree, then
states Theorems 1–4 and 6 and Proposition 5 in the `CCDN.Submission` namespace, with `sorry`.
[`Solution.lean`](Solution.lean) repeats those definitions verbatim and proves each
statement from the library. [`comparator.json`](comparator.json) lists the compared
theorems. [`formalization.yaml`](formalization.yaml) records sources, scope, known
divergences from the printed paper, and how the work was produced.

```text
bash scripts/check.sh             # source requirements, provenance, build, axiom audit
./scripts/verify-comparator.sh    # lake comparator, as Palomar runs it
```

`verify-comparator.sh` needs Linux, `bwrap`, and real directories under
`.lake/packages`, not symbolic links. The `Palomar preflight` workflow runs Palomar's
reusable verifier on a pushed commit. The repository is licensed under Apache-2.0; cited
papers and the vendored and adapted dependencies keep their own licences (see `NOTICE`).

**Status: Theorems 1–4 and 6, and Proposition 5, are proved in Lean.**
`CCDN.affineCurveBound` proves CCDN Theorem 3, and
`CCDN.projectiveCurveBound` proves Theorem 2. Both cover all
ambient dimensions `n ≥ 2` and all positive degrees, with no external
counting hypothesis. The proofs include the plane bounds, bounded projections
preserving degree, exceptional fibers and the uniform height/count assembly.
There are no counting axioms.

For every real `B ≥ 1`, the proved bounds are:

```text
N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d).
N_proj(X, B) ≤ C(n) d⁴ B^(2/d).
```

Degree is specified by the slope of the affine or homogeneous Hilbert function,
respectively. The projective count includes points at infinity, lines and
curves that split over an algebraic closure.

The full affine hypersurface bound (Theorem 4) and the projective hypersurface
case of Theorem 1 are also proved for every degree `d ≥ 5`, including degrees
5 through 15. In `n+3` affine variables, the improved bound is
`C(n) d^(18+3n) B^(n+1)`, using integer hyperplane normals bounded by `d³`.
The existing projective hypersurface endpoint in `n+3` homogeneous variables
retains `C(n) d^(18+9n) B^(n+1)`.

`projective_dimension_growth_cubic` proves Theorem 1 for general integral
projective varieties, including zero-dimensional and empty loci. In `P^n`,
one positive `C(n)` bounds `N(X,B)` by `C(n) d^(2n³) B^dim(X)` for every
`d ≥ 5` and `B ≥ 1`. Degree and dimension come from the actual homogeneous
coordinate ideal's Hilbert polynomial. All projections, fiber bounds and
height estimates are proved internally. The earlier exponent
`18 + 10(n+1) + 2(n+1)²` remains available through `projective_dimension_growth`.

`classGroup_two_torsion_bound` proves the full class-group Theorem 6. For
all fields of any fixed degree `n ≥ 3`, one positive `C(n)` gives
`h₂(K) ≤ C(n) |disc(K)|^(1/2−1/(2n)) (log|disc(K)|)^(1−n%2)`.
The short lattice basis, norm curves, exceptional subfields, quadratic
class-group descent and discriminant estimates are constructed and proved.
Strong induction on the field degree absorbs the prime-factor and logarithmic
losses in the quadratic case. Odd degrees retain the logarithm-free bound.

## Discrepancies with the paper

Formalising the whole paper, not only its main results, turned up the errors below,
measured against the published text and the authors' list of addenda dated 20 April 2026.
**None of them affects the six main results**, which are proved as printed, with explicit
exponents in place of `e(n)`. Each counterexample is stated and proved in Lean (named in
brackets) unless noted otherwise, and each intermediate result is also proved in a
corrected form, which the main results use.

### Not covered by the addenda

* **Lemma 2.2 is false for `n = 1`.** The hypothesis then reads `g(k) ≤ µ + cµ/k`.
  Take `c = 1`, `µ = K!`, `g(0) = 1` and `g(k) = µ + ⌊µ/k⌋`. Listing every weight up to `K`
  gives `s = 1 + µ(K + H_K)` terms with sum `µK(K+1)/2 + µK`, where `H_K = Σ_{k≤K} 1/k`.
  Then `s²/(2µ) − (n₁ + ⋯ + n_s) ≥ s (H_K − 3/2)/3`, which is not `O_c(s)`. In the proof,
  the replacement `g(k) = µ + cµ(k⁰ − (k−1)⁰) = µ` is not pointwise larger when `n = 1`.
  The hypersurface application is unaffected because there `g(k) ≤ µ`, and the lemma holds
  for `n ≥ 2` with an error independent of `µ`.
  [`no_uniform_dimension_one_profile_error`]
* **Corollary 2.5 needs the `Fⱼ` to have a common degree.** Take `n = 1`, the line
  `f = x₂` in `ℙ²` (so `µ = 1`), a prime `p > s`, the primitive points `ξᵢ = (i, p, 0)` for
  `1 ≤ i ≤ s`, which all reduce to `[1:0:0]`, and `Fⱼ = x₀^(j−1)`. Then `det(Fⱼ(ξᵢ))` is a Vandermonde
  determinant whose factors are all smaller than `p`, so `p ∤ det`, whereas the corollary
  asks for `e ≥ s²/2 − O(s)`. In the proof, `Fⱼ(ξᵢ)` differs from the value of the local
  function `Fⱼ/x₀^(deg Fⱼ)` by the factor `ξᵢ₀^(deg Fⱼ)`. That factor comes out of the
  determinant only when all the degrees are equal.
  [`no_uniform_mixed_degree_local_error`]
  The formalisation proves Proposition 2.6 and Corollary 2.9 only with a common degree.
  The paper deduces Proposition 3.2.6 from Corollary 2.9, so the next example indicates
  that they need it too.
* **Proposition 3.2.6 is false without a common degree in each matrix.** Take `n = d = L = 1`
  and `f = x₂`, so `b(f) = 1`. For `N ≥ 2` and `Q = N!`, take the `s = N²` primitive points
  `(iQ+1, j+1, 0)` with `0 ≤ i, j < N`, and the monomials `x₀^a x₁^b` with `0 ≤ a, b < N`.
  The evaluation matrix is a Kronecker product of two Vandermonde matrices, so
  `0 < log|Δ| ≤ (3/4) N⁴ log N`. The proposition would require
  `log|Δ| ≥ (s²/2)(log s − O(1)) = N⁴ log N − O(N⁴)`.
  [`no_uniform_global_mixed_degree_det_lower_bound`]
* **In the proof of Proposition 4.2.1, `b(F₁) = b(f)` fails.** Definition 3.2.1 does not
  count a prime at which the affine `f` drops degree. For `f = 439x₁² + x₂` (`d = 2`, and
  `27d⁴ = 432 < 439`), every reduction of `f` is absolutely irreducible because it is linear
  in `x₂`, so `b(f) = 1`. Its homogenization `F₁ = 439x₁² + x₂x₃` reduces to `x₂x₃` modulo
  439, so `b(F₁) = 439^(1/439) > 1`. Replacing 439 by a product of many primes above 432 makes
  `b(F₁)/b(f)` unbounded.
  The proposition, and Corollary 4.2.4, are nevertheless true as printed: the formalisation
  proves them by working directly in the affine chart
  (`literal_affine_hypersurface_auxiliary`, `literal_affine_plane_coefficient_count_uniform`).
  Defining `b(f)` through the homogenization would also repair the printed argument.
  (This example was checked by hand; it is not stated in Lean.)
* **In Lemma 5.2, the strict degree bound fails in dimension `m = 0`, and the printed
  argument does not give it when `m ≥ 1`.** For `m = 0`, geometric irreducibility forces
  `d = 1`, and the bound `< (m+1)²d² = 1` allows only constants. For `X = [1:0:0] ⊂ ℙ²`, the
  complement of `G_X` is a nonempty proper subset of `G(0, 2) = ℙ²`, which constant equations
  cannot cut out. Linear equations do, so the bound is `≤ 1` there.
  [`zero_dimensional_plucker_degree_bound_obstruction`]
  For `m ≥ 1`, the coefficients of `R_{X,Λ}` have Plücker degree `D = (m+1)d`, and the
  Noether forms of Theorem 3.2.2 have degree `D² − 1` in those coefficients. Composing them
  gives degree `D(D² − 1)`, not `< D²`. The lemma's bound is still true: the formalisation
  proves it with a derivative resultant along a generic line in one hyperplane block, which
  has degree `D(2d − 1) < D²` (`exists_dense_open_projective_center_plucker_equations`).
* **The constant in Lemma 5.4 is false.** For `s = 5`, `r = 6` and `B = 10`, the independent
  system with rows

  ```text
  ( 0,  0,   0,   0,  1, 0)
  (10, 10,  10,  10, -3, 0)
  (10, -9,   8,  -8, -6, 0)
  ( 9,  8, -10, -10, -5, 0)
  ( 9, -9,  -9,  10,  9, 0)
  ```

  forces `x₅ ∈ 120050ℤ` on every integer solution of the last four equations. So any
  solution violating the first has `|x₅| ≥ 120050`, whereas (5-6) promises
  `√(4!·6)·10⁴ = 120000`. Cofactors give the valid bound `(s−1)! B^(s−1)`
  (`exists_bounded_row_separator`). The projection estimate (5-5) keeps its exponent
  `2(n−m−1)²`. [`not_printed_row_separator_bound`]

### Already in the addenda

The formalisation follows the addenda's corrections. Proposition 2.6 is stated with
polynomials in `n + 2` variables. Proposition 4.3.3 assumes `h(f)` is absolutely
irreducible. Proposition 4.3.4 has `d¹⁸` in place of `d¹⁴`. Lemma 4.3.7 has degree
`(n+1)d(d² − 1)`. For Remark 4.3.8, the resulting exponents are `e = 3N + 9` in
Theorem 4 (in `N` variables) and `e = 2n³` in Theorem 1 (in `ℙⁿ`).

### Modelling choices

These are not errors in the paper. A variety is given by its ideal over `ℚ`, and
"integral" means that the ideal is prime, so varieties that split over `ℚ̄` are included.
Degree and dimension are read off the Hilbert function. Projective height is Mathlib's
multiplicative height, which equals `max |xᵢ|` on primitive integer coordinates.
Theorem 1 is proved for every `n`, including empty and zero-dimensional varieties. The
external inputs (Lang–Weil, Cafure–Matera, Salberger's Theorem 4.3.5, Heintz's bounds and
the class-group facts) are proved within the scope the paper needs, not assumed.
Proposition 5 uses Eisenstein equations in place of the paper's Newton-polytope
construction. The [full-paper ledger](docs/full-paper-plan.txt) and the
[completion audit](docs/completion-audit.json) map each of the 62 audited statements to its
Lean declaration.

## Build and audit

The toolchain is Lean `v4.35.0`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

With Elan, Python 3, and Git installed:

```sh
lake exe cache get
bash scripts/check.sh
```

The check enforces the module header and 10,000-line cap on every Lean source, verifies
vendored source hashes and import coverage, builds every module, and audits the transitive
axioms of every exported declaration in the library, the vendored dependency and
`Solution.lean`. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The audit is not an independent kernel implementation and does not replace mathematical
review of theorem statements; `verify-comparator.sh` additionally replays the compared
proofs through the toolchain's independent kernels.

## Reused proof

The exact Bombieri–Vaaler theorem cited in CCDN §3.3 is taken from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems/tree/09835cb23557ae5ae0cf55a9c4ab9055f5d60338).
Only its 25-module transitive dependency is vendored. Source attribution, original hashes,
local hashes, and the two compatibility changes are recorded under `vendor/bombieri-vaaler/`.
The code is rebuilt against this project's pinned Mathlib; upstream verification claims
are not a substitute for that build.

The first Mertens theorem is adapted from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean).
The extracted proof uses only Mathlib. Its source revision, hashes, adaptation notes, and
Apache license are recorded under `vendor/mertens/`.

## Documentation

- [`docs/development-notes.md`](docs/development-notes.md): proof routes, the module
  table and the Section 5 corrections in detail.
- [`docs/full-paper-plan.txt`](docs/full-paper-plan.txt): the full-paper ledger.
- [`docs/completion-audit.json`](docs/completion-audit.json): requirement-to-declaration
  audit with evidence hashes.
- [`docs/verification.txt`](docs/verification.txt): chronological verification log.
- [`docs/roadmap.txt`](docs/roadmap.txt) and the `docs/*-audit.txt` files: proof roadmap
  for Theorem 3 and individual statement audits.

## References

- W. Castryck, R. Cluckers, P. Dittmann, K. H. Nguyen,
  *The dimension growth conjecture, polynomial in the degree and without logarithmic factors*,
  Algebra & Number Theory 14 (2020), 2261–2294.
  [DOI](https://doi.org/10.2140/ant.2020.14.2261),
  [author PDF](https://rcluckers.perso.math.cnrs.fr/prints/Cast-Cl-Ditt-Nguy.pdf).
- The same counting input appears as Corollary 2.2 in
  [Cluckers–Dèbes–Hendel–Nguyen–Vermeulen (2025)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/improvements-on-dimension-growth-results-and-effective-hilberts-irreducibility-theorem/A7BCAEBF00B8B165D6DDB3FFB9B40B97).
