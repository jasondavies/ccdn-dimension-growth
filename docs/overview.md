# Proof overview

How each main result is assembled, and where its ingredients live. Paths are relative to
`CCDN/`; [modules.md](modules.md) lists every module, and [statements.md](statements.md)
maps the paper's numbered statements to Lean declarations.

The directories are layered. `Statements.lean` states Theorems 1–4 as propositions, and each
main result has an endpoint module at the top of `CCDN/` that assembles its proof; no library
module imports an endpoint. The proofs live in topic directories (`Plane/`, `Curve/`,
`Surface/`, `Hypersurface/`, ...), which build on the foundation directories `ForMathlib/`,
`Algebra/`, `Analysis/`, `Height/` and `Hilbert/`; foundation modules import no topic module.
`CCDNPaper/Counterexample/` and `CCDNPaper/Statements/` hold side results that nothing else imports.
`scripts/check-layers.py` checks these rules.

## Theorem 3: affine curves (`AffineCurveBound.lean`)

`affineCurveBound` proves `AffineCurveBound` (in `Statements.lean`):
`N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d)` for every prime ideal of an affine curve of degree
`d` in `𝔸ⁿ`. The two steps below are combined in `Curve/AffineCurveCount.lean`.

1. **Plane curves** (`Plane/`, `Determinant/`, `AuxiliaryPolynomial/`). The determinant method gives the
   plane bound `PlaneCurveBound`. The local determinant estimates at smooth and singular
   residue classes are in `Determinant/`, the finite-field point count in
   `Plane/CurveCount.lean`, and the auxiliary polynomial of Theorem 3.1.1 with its
   bad-prime factor in `AuxiliaryPolynomial/`.
2. **Projection to the plane** (`Projection/`). A bounded integral linear projection preserves
   the degree of the curve (`Projection/BoundedDegreePreservingProjection.lean`). It costs a
   bounded enlargement of the box, which `Projection/ScaleAbsorption.lean` absorbs
   into the constant. Exceptional fibres contribute at most `d(d − 1)` points.

## Theorem 2: projective curves (`ProjectiveCurveBound.lean`)

`projectiveCurveBound` gives `N(X, B) ≤ C(n) d⁴ B^(2/d)` (`ProjectiveCurveBound`). A coordinate
permutation puts the curve in a chart where it is not contained in the hyperplane at infinity
(`Curve/ProjectiveCurveCount.lean`). The projective plane
count (`Plane/`) and a bounded projection from `ℙⁿ` to `ℙ²`
(`Projection/ProjectiveProjectionCount.lean`) then give the bound. Points at infinity are
included, and curves that are irreducible over `ℚ` but split over `ℚ̄` have at most `d² + d`
rational points (`Plane/ProjectivePlaneNonabsoluteCount.lean`).

## Theorem 4: affine hypersurfaces (`AffineHypersurfaceDimensionGrowth.lean`)

`affine_hypersurface_dimension_growth` gives `N_aff(f, B) ≤ C(N) d^(3N+9) B^(N−2)` in
`N ≥ 3` variables, for an equation of degree `d ≥ 5` whose top-degree form is absolutely
irreducible. The Lean statement writes `N = n + 3`, so the bound reads `C d^(18+3n) B^(n+1)`.
`Hypersurface/AffineHypersurfaceCount.lean` combines the two steps below.

1. **Surfaces** (`Surface/`). `Surface/AffineSurfaceDimensionGrowth.lean` proves the bound
   `C d¹⁸ B` in three variables. For `d ≥ 16` it combines an auxiliary polynomial, the line
   contribution of Proposition 4.3.3 and a cover of the remaining points by curves. For
   `5 ≤ d ≤ 15` it uses a Salberger-type cover by congruence classes (Theorem 4.3.5).
2. **Slicing** (`Hypersurface/`). `Hypersurface/HyperplaneSlicingInduction.lean` adds one
   variable at a time, counting points level by level along a linear form
   (`Hypersurface/IntegerHyperplaneSlices.lean`). The universal Noether forms give a nonzero
   detector of degree `d(d² − 1) + 1` for the bad hyperplanes (the corrected Lemma 4.3.7,
   `Hypersurface/EffectiveHyperplaneAvoidance.lean`), hence a good integer hyperplane with
   normal bounded by `d³` (`Hypersurface/GoodHyperplane.lean`). Its parallel slices keep an
   absolutely irreducible top form (`Hypersurface/IntegerGoodHyperplaneSlices.lean`), so each
   step costs a factor `d³ B`. (The audited statement of Lemma 4.3.7, which also covers
   degree one, is proved separately in `CCDNPaper/Statements/` and is not on this path.)

## Theorem 1: projective varieties (`ProjectiveDimensionGrowth.lean`)

`projective_dimension_growth` gives `N(X, B) ≤ C(n) d^(2n²+5n−5) B^dim X`, with degree and
dimension read off the Hilbert polynomial of the homogeneous prime ideal. `projectiveGrowth_of_le`
splits by codimension:
- **Points and curves:** zero-dimensional loci are counted directly, and curves use Theorem 2.
- **Hypersurfaces:** a homogeneous prime of codimension one is principal
  (`exists_prime_generator_of_hilbert_dimension`). Its count comes from Theorem 4 through the
  affine cone (`Hypersurface/ProjectiveHypersurfaceDimensionGrowth.lean`).
- **Codimension at least two:** a bounded integer linear projection maps the variety finitely
  and birationally onto a hypersurface of the same degree in `ℙ^(m+1)`
  (`Projection/BoundedBirationalHypersurfaceProjection.lean`). It is built from a bounded
  linear Noether normalisation (`Projection/BoundedIntegerNormalization.lean`) and a bounded
  primitive linear parameter, not from the Chow forms and good centres of Section 5. Its height
  and fibre losses are polynomial in `d` (`Projection/ProjectiveProjectionGrowth.lean`,
  `Hypersurface/ProjectiveVarietyDimensionGrowth.lean`). Section 5 itself (good centres,
  Chow forms, Plücker equations) is formalised in `CCDNPaper/Center/`, and Lemmas 5.1–5.4 are stated
  from it in `CCDNPaper/Statements/`, but no main result imports them.

## Proposition 5: lower bound (`ProjectiveCurveLowerBound.lean`)

`projective_integral_curve_lower_bound` constructs, for every `d ≥ 1`, an absolutely
irreducible plane curve through a full grid of rational points, using Eisenstein equations
(`LowerBound/`). The other Section 6 obstructions are stated in `CCDNPaper/Statements/`, from the
constructions in `LowerBound/`.

## Theorem 6: class groups (`ClassGroupBound.lean`)

`classGroup_two_torsion_bound` follows the reduction in Section 4.2 (`ClassGroup/`).
1. **Reduction to norm curves.** A two-torsion class has an integral representative whose
   square is principal, with a balanced generator. The generators are bounded integers of
   square norm, so they lie on signed norm curves, indexed by translation classes that a
   lattice packing bounds.
2. **Odd degree.** The norm curves are absolutely irreducible of the full degree, and the
   logarithm-free affine count (Corollary 4.2.4) bounds them.
3. **Even degree.** Without an index-two subfield, the same argument works with a logarithm.
   Otherwise, a descent through the quadratic subextension, by strong induction on the
   degree, absorbs the prime-factor and logarithmic losses.

## Counterexamples and the paper's intermediate statements

`CCDNPaper/Counterexample/` holds the formal refutations of printed intermediate statements described in
the README's "Discrepancies with the paper" section. `CCDNPaper/Statements/` states the paper's other
intermediate results as printed (or as corrected), where the main results use a different form
or do not need them; [statements.md](statements.md) links each to its paper label.
