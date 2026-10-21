# Discrepancies with the paper

Formalising the whole paper, not only its main results, turned up the problems below. They are
measured against the published text and the authors' list of addenda dated 20 April 2026.
**None of them affects the six main results**, which are proved as printed, with explicit
exponents in place of `e(n)`. Each counterexample is stated and proved in Lean (named in
brackets), and each intermediate result is also proved in a corrected form, which the main
results use.

The status of each statement follows the rule in [audit-schema.md](audit-schema.md#statuses):
`refuted` when a Lean counterexample shows the printed statement false in some case,
`corrected` when the printed statement is amended and the amended form proved,
`proof_repaired` when the statement is true as printed but its printed proof is wrong.
[statements.md](statements.md) lists every audited statement with its status, and the README
has a summary table.

## Not covered by the addenda

* **Lemma 2.2 is false for `n = 1`** (`refuted`). The hypothesis then reads
  `g(k) ≤ µ + cµ/k`. Take `c = 1`, `µ = K!`, `g(0) = 1` and `g(k) = µ + ⌊µ/k⌋`. Listing every
  weight up to `K` gives `s = 1 + µ(K + H_K)` terms with sum `µK(K+1)/2 + µK`, where
  `H_K = Σ_{k≤K} 1/k`. Then `s²/(2µ) − (n₁ + ⋯ + n_s) ≥ s (H_K − 3/2)/3`, which is not
  `O_c(s)`. In the proof, the replacement `g(k) = µ + cµ(k⁰ − (k−1)⁰) = µ` is not pointwise
  larger when `n = 1`. The hypersurface application is unaffected because there `g(k) ≤ µ`, and
  the lemma holds for `n ≥ 2` with an error independent of `µ`.
  [[`no_uniform_dimension_one_profile_error`](../CCDNPaper/Counterexample/WeightedDimensionOne.lean)]
* **Corollary 2.5 needs the `Fⱼ` to have a common degree** (`refuted`). Take `n = 1`, the line
  `f = x₂` in `ℙ²` (so `µ = 1`), a prime `p > s`, the primitive points `ξᵢ = (i, p, 0)` for
  `1 ≤ i ≤ s`, which all reduce to `[1:0:0]`, and `Fⱼ = x₀^(j−1)`. Then `det(Fⱼ(ξᵢ))` is a
  Vandermonde determinant whose factors are all smaller than `p`, so `p ∤ det`, whereas the
  corollary asks for `e ≥ s²/2 − O(s)`. In the proof, `Fⱼ(ξᵢ)` differs from the value of the
  local function `Fⱼ/x₀^(deg Fⱼ)` by the factor `ξᵢ₀^(deg Fⱼ)`. That factor comes out of the
  determinant only when all the degrees are equal.
  [[`no_uniform_mixed_degree_local_error`](../CCDNPaper/Counterexample/MixedDegreeProjective.lean)]
  The formalisation proves Proposition 2.6 and Corollary 2.9 only with a common degree
  (`corrected`). The paper deduces Proposition 3.2.6 from Corollary 2.9, so the next example
  shows that they need it too.
* **Proposition 3.2.6 is false without a common degree in each matrix** (`refuted`). Take
  `n = d = L = 1` and `f = x₂`, so `b(f) = 1`. For `N ≥ 2` and `Q = N!`, take the `s = N²`
  primitive points `(iQ+1, j+1, 0)` with `0 ≤ i, j < N`, and the monomials `x₀^a x₁^b` with
  `0 ≤ a, b < N`. The evaluation matrix is a Kronecker product of two Vandermonde matrices, so
  `0 < log|Δ| ≤ (3/4) N⁴ log N`. The proposition would require
  `log|Δ| ≥ (s²/2)(log s − O(1)) = N⁴ log N − O(N⁴)`. The formalisation proves it when the
  columns of each matrix share a degree, which may differ between matrices.
  [[`no_uniform_global_mixed_degree_det_lower_bound`](../CCDNPaper/Counterexample/GlobalMixedDegreeDeterminant.lean)]
* **In the proof of Proposition 4.2.1, `b(F₁) = b(f)` fails** (`proof_repaired`). Definition
  3.2.1 does not count a prime at which the affine `f` drops degree. For `f = 439x₁² + x₂`
  (`d = 2`, and `27d⁴ = 432 < 439`), every reduction of `f` is absolutely irreducible because
  it is linear in `x₂`, so `b(f) = 1`. Its homogenisation `F₁ = 439x₁² + x₀x₂` reduces to
  `x₀x₂` modulo 439, so `b(F₁) = 439^(1/439) > 1`. Replacing 439 by a product of many primes
  above 432 makes `b(F₁)/b(f)` unbounded.
  [[`literalAffineBadPrimeFactor_homogenization_ne`](../CCDNPaper/Counterexample/HomogenizedBadPrimeFactor.lean),
  [`literalAffineBadPrimeFactor_homogenization_unbounded`](../CCDNPaper/Counterexample/HomogenizedBadPrimeFactor.lean)]
  The statements of Proposition 4.2.1 and Corollary 4.2.4, which depends on it, are true as
  printed: the formalisation proves them by working directly in the affine chart
  ([`literal_affine_hypersurface_auxiliary`](../CCDNPaper/AuxiliaryPolynomial/LiteralAffineAuxiliaryTheorem.lean),
  [`literal_affine_plane_coefficient_count_uniform`](../CCDNPaper/Statements/LiteralAffinePlaneCount.lean)).
  In Lean, "literal" names the paper's `b(f)` of the affine polynomial, as opposed to the
  factor of its homogenisation. Defining `b(f)` through the homogenisation would also repair
  the printed argument.
* **In Lemma 5.2, the strict degree bound fails in dimension `m = 0`, and the printed argument
  does not give it when `m ≥ 1`** (`refuted`). For `m = 0`, geometric irreducibility forces
  `d = 1`, and the bound `< (m+1)²d² = 1` allows only constants. For `X = [1:0:0] ⊂ ℙ²`, the
  complement of `G_X` is a nonempty proper subset of `G(0, 2) = ℙ²`, which constant equations
  cannot cut out. Linear equations do, so the bound is `≤ 1` there.
  [[`zero_dimensional_plucker_degree_bound_obstruction`](../CCDNPaper/Counterexample/ZeroDimensionalCenter.lean)]
  For `m ≥ 1`, the coefficients of `R_{X,Λ}` have Plücker degree `D = (m+1)d`, and the
  Noether forms of Theorem 3.2.2 have degree `D² − 1` in those coefficients. Composing them
  gives degree `D(D² − 1)`, not `< D²`. The lemma's bound is still true: the formalisation
  proves it with a derivative resultant along a generic line in one hyperplane block, which
  has degree `D(2d − 1) < D²`
  ([`exists_dense_open_projective_center_plucker_equations`](../CCDNPaper/Center/PluckerComplementEquations.lean)).
  In the formalisation, no main result depends on Section 5 (see [overview.md](overview.md)).
* **The constant in Lemma 5.4 is false** (`refuted`). For `s = 5`, `r = 6` and `B = 10`, the
  independent system with rows

  ```text
  ( 0,  0,   0,   0,  1, 0)
  (10, 10,  10,  10, -3, 0)
  (10, -9,   8,  -8, -6, 0)
  ( 9,  8, -10, -10, -5, 0)
  ( 9, -9,  -9,  10,  9, 0)
  ```

  forces `x₅ ∈ 120050ℤ` on every integer solution of the last four equations. So any solution
  violating the first has `|x₅| ≥ 120050`, whereas (5-6) promises `√(4!·6)·10⁴ = 120000`.
  Cofactors give the valid bound `(s−1)! B^(s−1)`
  ([`exists_bounded_row_separator`](../CCDN/Algebra/BoundedRowSeparation.lean)). The projection
  estimate (5-5) keeps its exponent `2(n−m−1)²`.
  [[`not_printed_row_separator_bound`](../CCDNPaper/Counterexample/RowSeparatorConstant.lean)]

## Covered by the addenda

The formalisation follows the addenda's corrections (all `corrected`). Proposition 2.6 is
stated with polynomials in `n + 2` variables. Proposition 4.3.3 assumes `h(f)` is absolutely
irreducible. Proposition 4.3.4 has `d¹⁸` in place of `d¹⁴`. Lemma 4.3.7 has degree
`(n+1)d(d² − 1)` in place of `(n+1)(d² − 1)`.

**Degree exponents (Remark 4.3.8).** As printed, Theorems 1 and 4 assert only that some
exponent `e(n)` exists. Remark 4.3.8 then estimates `e(n) ≤ 2n + 8` for Theorem 4 (where `n`
is the number of variables) and `e(n) ≤ 2n³` for Theorem 1 (where `X ⊆ ℙⁿ`). The addenda say
that the remark must be changed to follow their corrections of Proposition 4.3.4 and Lemma
4.3.7, but give no new values, so the estimate `2n + 8` is no longer supported. The
formalisation proves explicit exponents: `3N + 9` for Theorem 4 in `N ≥ 3` variables (`d¹⁸` for
`N = 3`, and a factor `d³` for each further variable, from hyperplane normals bounded by `d³`),
and `2n² + 5n − 5` for Theorem 1. Since `2n³ − (2n² + 5n − 5) = (n − 1)(2n² − 5)`, the
latter is at most `2n³` for every `n ≥ 1`, so the printed estimate for Theorem 1 holds.
In the Lean statement of Theorem 4, `N = n + 3`: the exponent appears as `18 + 3n` and the
power of `B` as `n + 1 = N − 2`.
