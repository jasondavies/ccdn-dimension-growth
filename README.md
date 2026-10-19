# Affine Curve Counting

A Lean 4 development of coefficient-uniform bounds for integral points on affine curves.

**Status: incomplete. The CCDN curve-counting theorem is not yet proved.**
The repository contains checked prerequisites and explicitly stated targets. There are no
counting axioms. A successful build certifies the implemented lemmas, not the unproved targets.

The intended theorem is Castryck–Cluckers–Dittmann–Nguyen (2020), Theorem 3:
for each ambient dimension `n ≥ 2`, there is a constant `C(n)` such that every integral
affine curve over `ℚ` of degree `d ≥ 1` satisfies, for every real `B ≥ 1`,

```text
N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d).
```

The constant is independent of the curve's coefficients. The project was started to supply
the external counting theorem needed by the proposed `13/44 + ε` Pierce-length bound.
It is not yet a usable dependency for that conclusion.

## Build and audit

The toolchain is Lean `v4.35.0`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`, matching `pierce-length-bound`.

With Elan, Python 3, and Git installed:

```sh
lake exe cache get
bash scripts/check.sh
```

The check verifies vendored source hashes and import coverage, builds every library module,
and audits the transitive axioms of exported declarations in both the new mathematics and
the vendored dependency. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The audit is not an independent kernel implementation and does not replace mathematical
review of theorem statements.

## Implemented mathematics

| Module | Checked content |
| --- | --- |
| `Box` | Exact integral-point counting at real radii; monotonicity, union bounds, injective transport. |
| `Plane` | Explicit plane-curve target; a coordinate-count bound for nonvertical affine lines. |
| `Curve` | Finite-dimensional filtered coordinate spaces, degree via eventual affine Hilbert growth, uniqueness of degree, full-dimensional target. |
| `Interpolation` | Evaluation matrices, nonzero coefficient vectors giving nonzero polynomials, degree and monomial-height bounds. |
| `RowSpan` | Vanishing transfers from selected evaluation rows to all rows in their rational span. |
| `AuxiliaryPolynomial` | Bombieri–Vaaler gives a nonzero vanishing polynomial with an explicit bound on every coefficient. |
| `Nondivisibility` | Leading coefficients obstruct divisibility; an explicit determinant threshold produces an auxiliary polynomial not divisible by the defining polynomial. |
| `Determinant` | Gram determinant upper bound; row-factor divisibility; determinant divisibility from congruent rows. |
| `LocalDeterminant` | Weighted factorizations over commutative rings, multiplicity exponents, quadratic determinant and maximal-minor-gcd divisibility for univariate polynomial evaluations in a residue class. |
| `PrimeProduct` | Combine divisibility at distinct primes into a product and a logarithmic lower bound. |
| `Analytic` | Elimination of coefficient height, absorption of additive errors, degree-2-through-24 square-root estimate, logarithm absorption. |

`PlaneCurveBound` and `AffineCurveBound` are definitions of propositions, not proved theorems.
The auxiliary-polynomial results state their rank, spanning, and numerical requirements
explicitly; they do not establish those requirements for the full point set of a curve.

## Reused proof

The exact Bombieri–Vaaler theorem cited in CCDN §3.3 is taken from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems/tree/09835cb23557ae5ae0cf55a9c4ab9055f5d60338).
Only its 25-module transitive dependency is vendored. Source attribution, original hashes,
local hashes, and the two compatibility changes are recorded under `vendor/bombieri-vaaler/`.
The code is rebuilt against this project's pinned Mathlib; upstream verification claims
are not a substitute for that build.

## Remaining work

The central unfinished input is the global determinant lower bound for curves, CCDN Proposition 3.2.6.
It requires local multiplicity estimates, point bounds over finite fields, control of bad
reduction, and prime sums. The resulting auxiliary-polynomial degree estimate must then be
combined with Bézout, affine specialization, and controlled projection. The relationship
between plane polynomial degree and the full target's Hilbert-function degree also remains
to be formalized. See [the proof roadmap](docs/roadmap.txt).

## References

- W. Castryck, R. Cluckers, P. Dittmann, K. H. Nguyen,
  *The dimension growth conjecture, polynomial in the degree and without logarithmic factors*,
  Algebra & Number Theory 14 (2020), 2261–2294.
  [DOI](https://doi.org/10.2140/ant.2020.14.2261),
  [author PDF](https://rcluckers.perso.math.cnrs.fr/prints/Cast-Cl-Ditt-Nguy.pdf).
- The same counting input appears as Corollary 2.2 in
  [Cluckers–Dèbes–Hendel–Nguyen–Vermeulen (2025)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/improvements-on-dimension-growth-results-and-effective-hilberts-irreducibility-theorem/A7BCAEBF00B8B165D6DDB3FFB9B40B97).

The new source and documentation were developed with AI assistance. This repository makes
no claim of independent human review or of a new mathematical counting theorem.
