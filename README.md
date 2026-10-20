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

## Source corrections

The six main results match the printed statements, with the explicit exponents and the
addenda's corrected Theorem 4 hypothesis described in `formalization.yaml`. Several
intermediate lemmas are false as printed; the library proves corrected versions and
formally refutes the literal claims. The [full-paper ledger](docs/full-paper-plan.txt)
records each correction, and the [completion audit](docs/completion-audit.json) maps all
62 audited requirements to their Lean declarations.

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
