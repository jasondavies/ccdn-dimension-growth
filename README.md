# CCDN Dimension Growth

A Lean 4 formalisation of Castryck–Cluckers–Dittmann–Nguyen's dimension-growth
paper, including coefficient-uniform point bounds.

**Where to start.**
- *Readers of the paper:* the statements are in [`Challenge.lean`](Challenge.lean), which uses
  only Mathlib. The [discrepancies](#discrepancies-with-the-paper) below summarise what is wrong
  in the printed text ([details](docs/discrepancies.md)), and
  [docs/statements.md](docs/statements.md) maps each of the paper's numbered statements to Lean.
- *Lean users:* see [Build and checks](#build-and-checks), then
  [docs/overview.md](docs/overview.md) for how each result is assembled and
  [docs/modules.md](docs/modules.md) for every module. Use `import CCDN` for the whole library,
  or a single module such as `CCDN.AffineCurveBound`; the namespace is `CCDN`.

## Results

**Theorems 1–4 and 6, and Proposition 5, are proved in Lean.** Every constant depends only on
the ambient dimension (or the field degree), and is chosen before the variety, its degree and
the radius `B ≥ 1`. Degree and dimension are read off Hilbert functions, and an integral variety
is a prime ideal over `ℚ`, so varieties that split over `ℚ̄` are included.

| Result | Bound | Lean |
| --- | --- | --- |
| Theorem 1 | `N(X, B) ≤ C(n) d^(2n²+5n−5) B^dim X` for integral `X ⊆ ℙⁿ`, `d ≥ 5` | `CCDN.projective_dimension_growth` |
| Theorem 2 | `N(X, B) ≤ C(n) d⁴ B^(2/d)` for integral curves `X ⊆ ℙⁿ`, `n ≥ 2` | `CCDN.projectiveCurveBound` |
| Theorem 3 | `N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d)` for integral curves `X ⊆ 𝔸ⁿ`, `n ≥ 2` | `CCDN.affineCurveBound` |
| Theorem 4 | `N_aff(f, B) ≤ C(N) d^(3N+9) B^(N−2)` in `N ≥ 3` variables, top form absolutely irreducible, `d ≥ 5` | `CCDN.affine_hypersurface_dimension_growth` (and `_rat`) |
| Proposition 5 | an integral plane curve of degree `d` with `N(X, B) ≥ d² B^(2/d) / 5` for some `B` | `CCDN.projective_integral_curve_lower_bound` |
| Theorem 6 | `h₂(K) ≤ C(n) \|disc K\|^(1/2−1/(2n)) (log \|disc K\|)^(1 − n mod 2)` for `[K : ℚ] = n ≥ 3` | `CCDN.classGroup_two_torsion_bound` |

**Degree exponents.** As printed, Theorems 1 and 4 assert only that some exponent `e(n)`
exists. Remark 4.3.8 then estimates `e(n) ≤ 2n + 8` for Theorem 4 (where `n` is the number of
variables) and `e(n) ≤ 2n³` for Theorem 1 (where `X ⊆ ℙⁿ`). The authors' addenda say that the
remark must be changed to follow their corrections of Proposition 4.3.4 and Lemma 4.3.7, but give
no new values, so the estimate `2n + 8` is no longer supported. The formalisation proves explicit
exponents: `3N + 9` for Theorem 4 in `N ≥ 3` variables (`d¹⁸` for `N = 3`, and a factor `d³`
for each further variable), and `2n² + 5n − 5` for Theorem 1, which is at most `2n³` for every
`n ≥ 1`, so the printed estimate for Theorem 1 holds. This README writes `N` for the number of
variables in Theorem 4, where the paper writes `n`; the Lean statement uses `N = n + 3`, so the
exponent appears there as `18 + 3n` and the power of `B` as `n + 1`.

The external results the paper cites (Lang–Weil, Cafure–Matera, Salberger's covering theorem,
Heintz's bounds, Bombieri–Vaaler, Mertens and others) are proved in the library, vendored, or
taken from Mathlib, not assumed; the second table of [docs/statements.md](docs/statements.md)
lists all 18 with their Lean declarations.

## Discrepancies with the paper

Formalising the whole paper, not only its main results, turned up the problems below, measured
against the published text and the authors' list of addenda dated 20 April 2026. **None of them
affects the six main results**, which are proved as printed, with explicit exponents in place of
`e(n)`. Each intermediate statement is also proved in a corrected form, which the main results
use. A status is `refuted` when a Lean counterexample shows the printed statement false in some
case, `corrected` when the printed statement is amended and the amended form is proved, and
`proof_repaired` when the statement is true as printed but its printed proof is wrong
([rule](docs/audit-schema.md#statuses)). [docs/discrepancies.md](docs/discrepancies.md) explains
each one, with the counterexamples.

| Statement | Issue | In addenda | Lean | Status |
| --- | --- | --- | --- | --- |
| Lemma 2.2 | false for `n = 1` | no | [`no_uniform_dimension_one_profile_error`](CCDN/Counterexample/WeightedDimensionOneExample.lean) | refuted |
| Corollary 2.5 | needs a common degree of the `Fⱼ` | no | [`no_uniform_mixed_degree_local_error`](CCDN/Counterexample/MixedDegreeProjectiveExample.lean) | refuted |
| Proposition 2.6 | `n + 2` variables; needs a common degree | yes (variables only) | [`projective_hypersurface_minorGcd_bound`](CCDN/Determinant/ProjectiveHypersurfaceResidueDeterminant.lean) | corrected |
| Corollary 2.9 | needs a common degree | no | [`projective_hypersurface_minorGcd_dvd`](CCDN/Determinant/HypersurfaceLocalDivisor.lean) | corrected |
| Proposition 3.2.6 | false without a common degree in each matrix | no | [`no_uniform_global_mixed_degree_det_lower_bound`](CCDN/Counterexample/GlobalMixedDegreeDeterminant.lean) | refuted |
| Proposition 4.2.1 | true, but the proof's `b(F₁) = b(f)` fails | no | [`literalAffineBadPrimeFactor_homogenization_ne`](CCDN/Counterexample/HomogenizedBadPrimeFactor.lean), [`literal_affine_hypersurface_auxiliary`](CCDN/Auxiliary/LiteralAffineAuxiliaryTheorem.lean) | proof_repaired |
| Corollary 4.2.4 | true, but proved through the faulty step of 4.2.1 | no | [`literal_affine_plane_coefficient_count_uniform`](CCDN/Paper/LiteralAffinePlaneCount.lean) | proof_repaired |
| Proposition 4.3.3 | the top form must be absolutely irreducible | yes | [`surface_line_contribution`](CCDN/Surface/SurfaceLineContribution.lean) | corrected |
| Proposition 4.3.4 | `d¹⁸` in place of `d¹⁴` | yes | [`affine_surface_dimension_growth`](CCDN/Surface/AffineSurfaceDimensionGrowth.lean) | corrected |
| Lemma 4.3.7 | degree `(n+1)d(d² − 1)` | yes | [`exists_integral_hyperplane_avoidance`](CCDN/Paper/IntegralHyperplaneAvoidance.lean) | corrected |
| Remark 4.3.8 | exponents must be recomputed (see above) | yes | [`affine_hypersurface_dimension_growth`](CCDN/AffineHypersurfaceDimensionGrowth.lean), [`projective_dimension_growth`](CCDN/ProjectiveDimensionGrowth.lean) | corrected |
| Lemma 5.2 | strict bound false for `m = 0`; printed argument insufficient for `m ≥ 1` | no | [`zero_dimensional_plucker_degree_bound_obstruction`](CCDN/Counterexample/ZeroDimensionalCenterObstruction.lean), [`exists_dense_open_projective_center_plucker_equations`](CCDN/Center/PluckerComplementEquations.lean) | refuted |
| Lemma 5.4 | the constant is false; `(s−1)! B^(s−1)` holds | no | [`not_printed_row_separator_bound`](CCDN/Counterexample/RowSeparatorCounterexample.lean), [`exists_bounded_row_separator`](CCDN/Algebra/BoundedRowSeparation.lean) | refuted |

`scripts/check-consistency.py` checks this table against `docs/completion-audit.json`.

**Modelling choices** (not errors in the paper). A variety is given by its ideal over `ℚ`, and
"integral" means that the ideal is prime. Degree and dimension are read off the Hilbert
function. Projective height is Mathlib's multiplicative height, which equals `max |xᵢ|` on
primitive integer coordinates. Theorem 1 is proved for every `n`, including empty and
zero-dimensional varieties. Proposition 5 uses Eisenstein equations in place of the paper's
Newton-polytope construction. [docs/statements.md](docs/statements.md) maps each of the 62
audited statements of the paper to its Lean declarations, and
[docs/completion-audit.json](docs/completion-audit.json) records the scope notes behind it
([schema](docs/audit-schema.md)).

## Statement surface and comparator

[`Challenge.lean`](Challenge.lean) is the file to audit. It imports only Mathlib, defines the
counting functions, zero sets and Hilbert-function notions of degree, and states the compared
theorems in the namespace `CCDN.Submission`, with `sorry`. [`Solution.lean`](Solution.lean)
repeats those definitions verbatim and proves each statement from the library.
[`comparator.json`](comparator.json) lists the nine compared theorems:

| Theorem | Content |
| --- | --- |
| `affineCount_set_finite`, `projectiveCount_set_finite` | the counted sets are finite, so the `Set.ncard` counts are true cardinalities |
| `projective_dimension_growth` | Theorem 1 |
| `projective_curve_bound` | Theorem 2 |
| `affine_curve_bound` | Theorem 3 |
| `affine_hypersurface_bound`, `affine_hypersurface_bound_rat` | Theorem 4, for integer and for rational equations |
| `projective_plane_curve_lower_bound` | Proposition 5 |
| `classGroup_two_torsion_bound` | Theorem 6 |

[`formalization.yaml`](formalization.yaml) records sources, scope, divergences from the printed
paper, and how the work was produced.

The comparator (`lake comparator`, shipped with the Lean toolchain) checks that `Solution.lean`
proves exactly the statements of `Challenge.lean`, using only the permitted axioms, and replays
the proofs through Lean's kernel and the toolchain's independent kernels (NanoDa and con-ron).
**CI does not run it.** There are two ways to run it:

- `./scripts/verify-comparator.sh` runs `lake comparator` locally, configured as Palomar runs
  it. It needs Linux, `bwrap`, and real directories (not symbolic links) under `.lake/packages`.
  It replays every declaration the compared proofs depend on, Mathlib's included, through three
  kernels, so it takes far longer than `lake build`. Its time and memory use have not been
  measured; the runs recorded in [docs/history/verification.txt](docs/history/verification.txt)
  used a 16-core workstation with 249 GiB of RAM. The last recorded run (20 October 2026)
  predates the change of the Theorem 1 exponent to `2n² + 5n − 5`, so it must be rerun before a
  submission.
- The `Palomar preflight` workflow (`.github/workflows/palomar-preflight.yml`) runs Palomar's
  reusable verifier, pinned to a fixed commit, on the pushed commit. It is advisory, not a
  submission, and runs only when started by hand (`workflow_dispatch`, from the Actions tab or
  with `gh workflow run palomar-preflight.yml`). Its `request_id` input (default
  `preflight001`) is a caller-chosen lowercase identifier that names the report artifact. The
  workflow uses Palomar's `palomar-standard-v1` profile: a GitHub-hosted `ubuntu-24.04` runner
  with at least 14 GiB of memory, a 350-minute job timeout and a 5.5-hour execution budget.
  Whether the whole verification of this library fits that budget has not been recorded;
  running the preflight is how to find out.

## Build and checks

The toolchain is Lean `v4.35.0`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. With Elan, Python 3.12 or later, and Git installed:

```sh
lake exe cache get
bash scripts/check.sh
```

`scripts/check.sh` runs the checks below in order, printing one line for each; CI
(`.github/workflows/ci.yml`) runs it on every push and pull request.

- `check-lean-sources.py`: every Lean source has the `module` header, is UTF-8 and has at most
  10,000 lines.
- `check-layers.py`: the foundation directories and `CCDN/Statements.lean` import no topic
  directory, no library module imports an endpoint, and the side results are imported only
  from their own directory ([layout](#documentation)).
- `check-provenance.py`: the vendored sources match their recorded hashes, reverse-applying
  `vendor/bombieri-vaaler/lean-4.35.patch` restores the upstream files, and every module is
  reachable from the root import.
- `audit-evidence.py`: `docs/completion-audit.json` follows its [schema](docs/audit-schema.md),
  and every evidence declaration is declared in the file it names.
- `check-docs.py`: links in README and `docs/` resolve, linked declarations exist, and every
  module and declaration cited in `docs/overview.md` lies in the import closure of its section's
  endpoint.
- `check-consistency.py`: the compared theorems agree across `comparator.json`,
  `formalization.yaml`, `Challenge.lean`, `Solution.lean` and `Axioms.lean`; the discrepancy
  table above and the statement counts agree with the audit; and the toolchain and Mathlib
  revision quoted here match `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
- `update-root.py --check` and `update-docs.py --check`: `CCDN.lean`, `docs/modules.md` and
  `docs/statements.md` are generated; run the scripts without `--check` after adding, moving or
  removing modules or editing the audit.
- `lake build`: builds the library, `Challenge`, `Solution` and `Axioms`. Building `Axioms`
  audits the transitive axioms of every declaration in the library, the vendored dependencies
  and `Solution.lean`, and prints the axioms of the compared theorems; only `propext`,
  `Classical.choice` and `Quot.sound` are allowed. Lake replays these messages when the build
  is cached.

The axiom audit is not an independent kernel and does not replace mathematical review of the
statements; the comparator additionally replays the compared proofs through independent kernels.

## Reused proofs

The exact Bombieri–Vaaler theorem cited in CCDN §3.3 is taken from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems/tree/09835cb23557ae5ae0cf55a9c4ab9055f5d60338).
Only its 25-module transitive dependency is vendored. Source attribution, original hashes,
local hashes, and the two compatibility changes are recorded under `vendor/bombieri-vaaler/`.
The code is rebuilt against this project's pinned Mathlib; upstream verification claims
are not a substitute for that build.

The first Mertens theorem is adapted from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean).
It is vendored as the separate library `Mertens` (`vendor/mertens/Mertens.lean`, namespace
`CCDN.Mertens`), which uses only Mathlib. Its source revision, hashes, adaptation notes and
Apache licence are recorded under `vendor/mertens/`.

The repository is licensed under Apache-2.0; cited papers and the vendored and adapted
dependencies keep their own licences (see [`NOTICE`](NOTICE)).

## Documentation

- [`docs/overview.md`](docs/overview.md): how each main result is assembled.
- [`docs/discrepancies.md`](docs/discrepancies.md): the discrepancies with the paper, in detail.
- [`docs/statements.md`](docs/statements.md): the paper's numbered statements and the external
  results it cites, with their Lean declarations (generated from `docs/completion-audit.json`;
  [schema](docs/audit-schema.md)).
- [`docs/modules.md`](docs/modules.md): every module, by directory (generated). The
  directories are layered, and `scripts/check-layers.py` enforces the layers:
  - [`CCDN/Statements.lean`](CCDN/Statements.lean) states Theorems 1–4, and each of the six
    main results has an endpoint module at the top of `CCDN/` (statement plus a short
    assembly), which no library module imports;
  - the foundation directories `ForMathlib/`, `Algebra/`, `Analysis/`, `Height/` and
    `Hilbert/` hold general results and import nothing else from the library
    (`CCDN/ForMathlib/` is written under Mathlib namespaces, for upstreaming);
  - the topic directories hold the proof routes, each in the directory of its topic;
  - `Counterexample/` and `Paper/` hold side results (refutations, and the paper's
    intermediate statements as stated there) that nothing else imports.
- [`docs/history/`](docs/history/): development notes, the verification log and the original
  statement audits, kept for the record and not maintained.

## References

- W. Castryck, R. Cluckers, P. Dittmann, K. H. Nguyen,
  *The dimension growth conjecture, polynomial in the degree and without logarithmic factors*,
  Algebra & Number Theory 14 (2020), 2261–2294.
  [DOI](https://doi.org/10.2140/ant.2020.14.2261),
  [author PDF](https://rcluckers.perso.math.cnrs.fr/prints/Cast-Cl-Ditt-Nguy.pdf).
- R. Cluckers, [list of addenda](https://rcluckers.perso.math.cnrs.fr/prints/list-of-addenda.pdf)
  to papers of R. Cluckers and coauthors, dated 20 April 2026.
- The same counting input appears as Corollary 2.2 in
  [Cluckers–Dèbes–Hendel–Nguyen–Vermeulen (2025)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/improvements-on-dimension-growth-results-and-effective-hilberts-irreducibility-theorem/A7BCAEBF00B8B165D6DDB3FFB9B40B97).
