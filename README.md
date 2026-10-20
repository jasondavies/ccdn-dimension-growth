# CCDN Dimension Growth

A Lean 4 formalisation of Castryck–Cluckers–Dittmann–Nguyen's dimension-growth
paper, including coefficient-uniform point bounds.

**Status: Theorems 1–4 and 6, and Proposition 5, are proved in Lean.**
`AffineCurveCounting.affineCurveBound` proves CCDN Theorem 3, and
`AffineCurveCounting.projectiveCurveBound` proves Theorem 2. Both cover all
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
5 through 15. In `n+3` affine or homogeneous variables, the bound is
`C(n) d^(18+9n) B^(n+1)`.

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

**The full paper is not yet formalised.** Several exact intermediate statements
remain open. The
[full-paper ledger](docs/full-paper-plan.txt) records the complete scope
and the external inputs that must be proved.

The general Noetherian-local determinant lemma (2.4) is proved in
`primeInteger_local_enumerated_weight_det`, with the actual target
`ℤ_(p)` and the exact sum of local-layer weights. The finite-profile version
constructs those weights, or proves the determinant zero when there are too few.
The local generators and residue-field identifications are proved internally.

`hypersurfacePointStalk_hilbert_eq` computes the exact Hilbert layers of the
actual localized coordinate ring at a rational hypersurface point.
`exists_hypersurfacePointStalk_hilbert_weights` constructs its multiplicity
and infinite weight sequence, proving the sharp Lemma 2.3 bound with error
`(m+1)s` in every positive hypersurface dimension `m`.
`exists_hypersurfacePointStalk_pointwise_remainder` also proves Lemma 2.1's
multiplicity-independent error `C(m) k^(m−2)`, with the constant chosen before
the field, equation and point. `no_uniform_dimension_one_profile_error`
formally refutes the arbitrary-profile dimension-one extension of Lemma 2.2;
the stronger actual hypersurface profile still gives the required bound.

`pure_ideal_grid_card_le` proves Lemma 4.1.1 in every finite ambient dimension
over characteristic-zero fields: a pure-dimensional ideal of dimension `m`
and Hilbert multiplicity `d` has at most `d*|S|^m` zeros in the grid `S`.
Its rational-box consequence is `d(2B+1)^m`. The proof constructs the
minimal-prime component degree budget and bounds actual integral fibers by
function-field rank. `exists_sharp_projective_projection` also gives the
exact factor `d` in the count comparison for a constructed finite birational
projective projection, with polynomial height cost.

The higher-dimensional bad-prime height estimate (CCDN Corollary 3.2.3) is
also proved. `hypersurface_bad_prime_factor_max` bounds the actual bad-prime
factor by a dimension-dependent constant times `max(log(H)/d², 1)`, where
`H >= 1` bounds the equation's coefficients. The proof constructs a bounded
integer plane specialization, a nonzero integer witness and its height bound.
It includes degree-dropping reductions.

`exists_explicit_noether_forms` proves the full universal Noether-form
Theorem 3.2.2. For `d ≥ 2`, it constructs one finite family of integer forms
for equations in `n+1` variables, homogeneous of degree `d²−1`, with coefficient
sums at most `d^(3d²−3) (choose(n+d,n) 3^d)^(d²−1)`. Every form vanishes on
equations that are not absolutely irreducible, in every characteristic; some
form is nonzero on every absolutely irreducible equation in characteristic
zero. The same family is chosen before the field and equation. The proof
uses universal plane Euler minors, including repeated and inseparable factors,
and proves the generic-plane nonvanishing and coefficient bounds internally.

The higher-dimensional simultaneous-prime determinant estimate is proved for
maximal minors of common-degree homogeneous evaluation matrices. It retains
the exact rank exponent and leading constant in Proposition 3.2.6, constructs
the bad-prime set, and discharges its coefficient-height bound. The resulting
Bombieri–Vaaler comparison and uniform auxiliary-degree selection in both
height ranges are also proved. For differing column degrees, the corrected
local theorem includes inverse-pivot normalization. A checked counterexample
rules out the unnormalized local statement. A separate global counterexample,
`no_uniform_global_mixed_degree_det_lower_bound`, now disproves the
unrestricted differing-degree formulation of Proposition 3.2.6 for every
proposed uniform error constant, using primitive points on one fixed line.
See the [determinant statement audit](docs/local-determinant-audit.txt).

The uniform Hilbert-rank estimates and normalized determinant comparison
are now proved. They retain the exact factorial leading coefficient, bound
the kernel-rank ratio error by `1/M`, and absorb the archimedean terms into
a dimension constant. A separate normalized comparison retains the exact
bad-prime factor needed for the coefficient-sensitive theorem.
`hypersurface_projective_auxiliary` proves the full CCDN auxiliary-polynomial
Theorem 3.1.1, for every positive degree and projective hypersurface dimension.
It constructs a nonzero homogeneous nonmultiple vanishing at every rational
zero of height at most B. The degree bound uses the original equation's maximum
absolute coefficient and the defined bad-prime factor, with a constant depending
only on dimension. Grid interpolation, a bounded integral shear, its height cost
and bad-prime invariance discharge coordinate positioning. The nonabsolute case
uses homogeneous coefficient descent to construct an auxiliary polynomial of
exactly degree d, vanishing at all rational zeros independently of height.
`projective_plane_coefficient_count_chain` proves both inequalities in
Corollary 3.1.2, including the uniform bound for the coefficient-sensitive
expression itself.

The height-transfer estimate in Lemma 4.2.3 and an all-case affine auxiliary
theorem are also proved. `affine_hypersurface_auxiliary` constructs a nonzero
nonmultiple vanishing on every integer zero in the box, with the affine
`B^(1/d^(1/r))` exponent, original leading coefficient height, and the minimum
of the logarithmic and bad-prime terms. Prime selection, the coefficient-height
dichotomy, polynomial box ranges and bounded translations are discharged.

**This affine theorem uses a bad-prime factor that includes degree loss.**
It differs from the literal affine wording of Definition 3.2.1. The factor
agrees with that definition for homogeneous equations, so the projective
results above do not have this issue. Exact literal Proposition 4.2.1 remains
open; the [statement audit](docs/affine-factor-audit.txt) gives a concrete
counterexample to the printed intermediate homogenization equality and records
the author's published corrections. Lemma 4.2.2 is proved with its printed
dimension-only multiplier: `projective_coefficient_height_dichotomy_uniform`
gives `H(f) ≤ C(n) B^(d*N)`, with `N = choose(n+1+d,d)` in `n+2` variables,
or a homogeneous degree-`d` nonmultiple vanishing on every bounded projective
zero. This proof does not use the disputed affine-factor equality.

`affine_plane_coefficient_count_uniform` proves the full coefficient-sensitive
minimum expression in Corollary 4.2.4 with the same degree-loss-inclusive
bad-prime factor. The generic coprime Newton-edge Corollary 4.2.5 is proved:
`coprime_newton_edge_log_free_bound` gives
`C d⁴ (log|c_d c_e|+1) B^(1/d)`. Irreducibility, the bad-prime bound and
primitive normalization are proved from the support and endpoint conditions.

The coefficient-uniform top-form auxiliary estimate (4-3-1) is now proved.
If the leading homogeneous part of an integer equation is absolutely
irreducible, `top_form_auxiliary_rational` constructs an integer auxiliary
that is a nonmultiple even over the rationals, vanishes on all bounded integer
zeros, and has degree at most
`C(r) d^(4−1/r) B^(1/d^(1/r))`, where `r` is the hypersurface dimension.
Integer content is removed inside the proof. For surfaces this is
`C d^(7/2) B^(1/√d)`. This consequence has no bad-prime-factor parameter.

For irreducible `f` and `f ∤ g` over the rationals, the common rational zeros
of `f` and `g` in affine three-space now have a constructed finite cover by
prime curves with positive Hilbert degrees whose sum is at most the product
of the equation degrees.
The proof obtains eventual linearity from standard monomials, constructs
minimal-prime components and separators, and proves the additive degree
budget. Applied to the surface auxiliary, this covers every original bounded
integer zero and gives total component degree at most
`C d^(9/2) B^(1/√d)`. Degree-one components containing a rational point are
proved to be exactly rational affine lines. For each line with at least two
bounded integer points, its primitive integer direction has height at most
`2B`, and the integer count is at most `1 + 2B/height(direction)`.

The corrected surface-line contribution is proved in
`surface_line_contribution`: for absolutely irreducible leading form and
`d ≥ 3`, any finite family of actual rational lines contributes at most
`C d^6 B + number_of_lines`. A constructed transverse plane bounds parallel
lines by `d(d−1)`, and the projective curve theorem bounds the sum of
reciprocal direction heights. Both geometric inputs are proved.

`top_form_surface_count` combines the line and nonlinear contributions into
the full corrected surface estimate `C d^18 B` for `d ≥ 16` and absolutely
irreducible leading form. Its constant is chosen before the equation and
real radius `B ≥ 1`. The absolute-irreducibility condition is the one printed
in Theorem 4 and Proposition 4.3.4; text extraction can lose the bar over Q.

`top_form_surface_dimension_growth` supplies the same `C d^18 B` estimate
for every `d ≥ 5`. The small degrees use a constructed smooth-congruence
cover, proper auxiliary crossings, retained low-degree curves and the proved
line contribution. The coefficient-height condition is discharged internally.

`top_form_hypersurface_dimension_growth` extends the bound to every ambient
dimension `n+3`, giving `C(n) d^(18+9n) B^(n+1)` for every `d ≥ 5`. It
constructs a good integer hyperplane with normal bounded by `750d^9`,
integer equations for all parallel slices, and the point maps used in the
induction. `exists_effective_hyperplane_avoidance` now also constructs a
nonzero homogeneous polynomial that vanishes on all bad hyperplane sections,
in explicit graph coordinates for `d ≥ 2`. Its degree `d(d²−1)+1` is below
the corrected bound in Lemma 4.3.7; the omitted coordinate chart is covered
by a coordinate factor. `rational_top_form_hypersurface_dimension_growth`
also covers rational equations. `projective_hypersurface_dimension_growth` proves the
corresponding projective hypersurface bound, including rationally irreducible
equations that split over an algebraic closure. These endpoints have no
external counting, slicing, height or covering premise. The general
projective-variety reduction is also completed by ProjectiveDimensionGrowth.

`non_rational_prime_count_le_box` and `nonabsolute_variety_count_le_box`
prove the general affine statements of 4.1.3 and 4.1.4: the rational integer
points on a geometric prime variety not defined over the rationals, or a
rational prime variety that becomes nonprime over an algebraic closure,
number at most `d²(2B+1)^m` in dimension `m+1`. Their zero-dimensional
rational loci are empty. Projective versions give `d²(2B+1)^m` in projective
dimension `m`. Galois descent constructs the moving automorphism and geometric
component; its degree and inclusion of all rational points are proved
internally. The hypersurface bound over arbitrary field extensions remains
available as `nonabsolute_hypersurface_count_le_sharp`.
The corresponding projective curves satisfy the stronger, height-independent
bound `projectiveCount ≤ d²`, proved in `NonRationalProjectiveCurve` from their
actual homogeneous ideals. This supplies the curve case of Remark 4.1.5.

`principal_section_count_le_box` bounds a proper degree-`e` section of a
degree-`d`, dimension-`m+1` prime variety by `de(2B+1)^m`; section purity and
its degree budget are proved.

The exact complex interpolation estimates of Lemmas 3.4.1 and 3.4.2 are now
proved. Integer-grid values bound every coefficient by `3^d` in one variable
and `3^(nd)` in `n` variables. One grid point controls all coefficients, and
a bounded integer shear puts that value in the leading coefficient of a
homogeneous form.

The lower-bound constructions in Lemma 6.1 and Proposition 5 are proved.
`exists_absolutely_irreducible_integer_grid` constructs a prescribed-degree
equation through the entire stated integer grid. `projective_integral_curve_lower_bound`
constructs an actual integral projective plane curve and an integer radius
with at least `(d²/5) B^(2/d)` rational points, for every positive degree.
Its prime defining ideal and projective Hilbert degree are also certified.
The proof uses explicit Eisenstein equations instead of the paper's
Newton-polytope construction.
The Section 6 degree-dependence obstructions are also proved for actual
families: the projective curve factor cannot be `o(d²)`; the affine envelope
`g(d) B^(1/d) log B` cannot have `g(d)=o(d²/log d)`; and dimension-growth degree
exponents must be at least one projectively and two affinely. The affine
examples have absolutely irreducible leading forms, meeting Theorem 4's
actual hypothesis.

For the small-degree surface cases, the smooth-congruence
determinant divisors, their simultaneous global logarithmic estimate and
the combined bad-prime charge are proved. The standard-monomial weight is
bounded by `(2/3)s sqrt(2s/d)+(2d+2)s`, and the determinant upper bound retains
the sum of column degrees. `exists_surface_congruence_auxiliary` now constructs
an actual proper integer auxiliary on every bounded smooth congruence class,
with degree at most `C(d,K)(B^(1/√d)/exp Q + 1)(1 + log B + Q)` when
`log H ≤ K(log B + 1)` and `Q` is the sum of the selected prime logarithms.
The constant is independent of the coefficients, radius and chosen congruences.
A common prime window, its smooth residue classes and the boundary of its
subsets are constructed. Every nonsingular point on a sufficiently large-degree
initial curve lies on a proper auxiliary crossing. The product-of-degrees
crossing bound, subpower subset count and logarithmic-degree curve contribution
are proved. Summing the actual crossings gives a linear residual count.
Combining this with retained curves and lines proves a coefficient-uniform
`C(d) B` bound for every fixed `d ≥ 5`; the finitely many degrees 5 through 15
then join the large-degree estimate above.

The bounded linear algebra for general projective projections is proved:
actual integer projection matrices, their kernels and ranks, height bounds,
and bounded specialization of polynomials in maximal minors. Bounded linear
elimination makes a chosen nonzero ideal equation monic and constructs an
integral coordinate map. The general filtered Hilbert polynomial is
constructed for every ideal, with positive integral multiplicity for proper
ideals. Its dimension yields independent original coordinates, and its
multiplicity bounds the degree of an actual nonzero ideal equation and the
finite parameter-field extension. Each elimination step preserves Hilbert
dimension, bounds the new multiplicity by the original one, and uses integer
linear forms with bounded coefficients. Iteration constructs an injective,
integral normalization map whose integer coefficients are at most
`n! (d+1)^n`. A bounded primitive coordinate now augments this to a finite
birational projection. The actual homogeneous irreducible image equation has
exactly degree `d`: a nonzero conductor compares the two Hilbert filtrations
in both directions. The projection height is polynomial in `d`, with constants
depending only on ambient dimension. Minimal polynomials bound actual affine
fibers by `d^n`. Projective count transfer, the hypersurface theorem and a
finite maximum over dimensions give the full uniform general-variety bound.
The zero-dimensional and empty-locus cases are proved separately.

The class-group application now starts with the actual ideal class group:
two-torsion classes have integral representatives with principal squares,
chosen square generators are injective, and rescaling inside the inverse ideal
preserves the class and exact generator. Signed norms are handled explicitly.
Balanced generators are now constructed: each infinite-place absolute value
is less than `9 |disc(K)|^(1/[K:Q])`. This gives an injection into a finite set
of bounded integers with square absolute norm. Actual signed norm-polynomial
curves are constructed and, in odd field degree, proved absolutely irreducible
of the full field degree over every field. In odd degree, they have no bad
reduction primes and satisfy a uniform logarithm-free `C d⁴ B^(1/d)` count.
The actual two-torsion count is reduced to a finite sum of these signed norm
curves indexed by integer translation classes. An injective packing argument
bounds those classes by an ordinary lattice-box count. Its uniform estimate
is now proved: a prescribed greedy lattice basis, the multiplication pairing
and covolume packing give basis lengths at most `n³ |disc(K)|^(1/n)`.
`odd_degree_classGroup_two_torsion_bound` completes Theorem 6 in odd degree.
`no_index_two_classGroup_two_torsion_bound` proves the logarithmic bound when
there is no index-two intermediate field. The norm polynomial factors through
the generated subfield; odd index gives absolute irreducibility. The remaining
integers lie in subfields of degree at most `n/4`. An actual intermediate-field
count and lattice packing bound this exceptional set uniformly.

The quadratic branch is proved by descent on field degree. The relative norm,
Hilbert 90 correction and unit obstruction reduce fixed two-torsion to invariant
ideal classes. Actual invariant ideals factor into an extended base ideal and
distinct ramified primes. Those primes lie above rational primes dividing the
absolute discriminant. For a quadratic extension `K/F`, the resulting estimate is
`h₂(K) ≤ (h₂(F) 2^([K:Q] ω(D_K)+[F:Q]))²`.
The exact discriminant inequality `D_F² ≤ D_K` leaves an exponent saving;
a proved subpower estimate absorbs both the prime-factor loss and logarithms.
The degree-one and degree-two base cases are proved. Strong induction completes
Theorem 6 with constants chosen before the number field, without a supplied
genus-theory or counting hypothesis.

## Build and audit

The toolchain is Lean `v4.35.0`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

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
| `HypersurfaceTangentEquality`, `HypersurfacePointStalk`, `ActualLocalHilbertWeights` | Exact local Hilbert layers and constructed weight sequences with the sharp multiplicity bound. |
| `InfiniteWeightEnumeration`, `WeightedDimensionOneExample` | Actual infinite profile enumerations and a counterexample to the arbitrary-profile dimension-one claim. |
| `PrincipalSectionPurity`, `PrincipalSectionGridBound`, `SharpPrincipalSectionCount` | Pure proper sections, exact grid counts and the sharp nonabsolute hypersurface bound. |
| `HilbertScalarExtension`, `IdealScalarDescent`, `GeometricPrimeIntersectionGrid` | Scalar-extension Hilbert invariance, descended separators and sharp geometric intersection counts. |
| `GaloisPolynomialPrimes`, `AlgebraicHilbertDimension`, `FiniteGaloisIdealDefinition` | Actual component conjugacy, dimension preservation and constructed finite Galois fields of definition. |
| `EulerProductVanishing`, `EulerSparseMatrix`, `IntegerPolynomialL1`, `EulerUniversalHeight` | All-characteristic product vanishing and the exact plane coefficient-sum bound. |
| `CoprimeNewtonEdge`, `CoprimeNewtonEdgeReduction`, `CoprimeNewtonEdgeCount`, `AffinePlaneCoefficientCount` | Generic logarithm-free Newton-edge count and the coefficient-sensitive plane minimum expression with the defined bad-prime factor. |
| `HilbertLowDegreeEquation`, `HilbertFunctionFieldRank`, `HilbertCoordinateParameterField`, `BoundedIntegerNormalization` | Construct a low-degree ideal equation and finite parameter field; iterate bounded integral elimination to obtain actual integer normalization. |
| `LatticeSuccessiveMinima`, `LatticeMinimaProduct`, `LatticePrescribedProduct`, `NumberFieldShortBasis` | Construct greedy lattice bases, prove their product bound, and obtain a uniform discriminant-root bound for integral basis vectors. |
| `UniformNumberFieldLatticeCount`, `OddDegreeClassGroupCounting`, `OddDegreeClassGroupBound` | Actual lattice and translation-class counts and the unconditional odd-degree branch of Theorem 6. |
| `ClassGroupRelativeNorm`, `ClassGroupQuadraticInvolution` | Construct the class-group norm and involution action; prove norm after extension and the fixed-subgroup cardinality bound. |
| `FiniteBirationalConductor`, `HomogeneousBirationalDegree`, `BoundedBirationalHypersurfaceProjection` | Construct bounded finite birational projections and prove exact equality of source and image degree. |
| `LinearNormalizationFiberCount`, `ProjectiveVarietyUniformGrowth`, `ZeroDimensionalProjectiveCount`, `ProjectiveDimensionGrowth` | Full Theorem 1 with constants depending only on ambient dimension, including zero-dimensional and empty loci. |
| `IntegralAlgebraPointCount`, `IntegralProjectionFiberCount`, `ProjectiveLinearCountTransfer`, `ProjectiveProjectionGrowth` | Count actual integral-coordinate fibers, transfer projective counts and absorb the projection's polynomial height loss. |
| `IntermediateFieldCount`, `SmallSubfieldIntegerCount`, `NoIndexTwoClassGroupBound` | Count intermediate fields and exceptional integers; prove the logarithmic class-group bound for fields without an index-two subfield. |
| `DiscriminantPrimeIdealCover`, `StronglyAmbiguousClassCount`, `QuadraticClassGroupDescent` | Construct the ramification cover and prove quadratic class-group descent and the small-degree base cases. |
| `PrimeFactorSubpower`, `QuadraticClassGroupNumerics`, `ClassGroupUniformBound`, `ClassGroupBound` | Absorb prime-factor and logarithmic losses, perform degree induction, and prove full Theorem 6 with its exact parity-dependent logarithm. |
| `ProperHilbertDimension`, `ProjectiveHilbertCurveGrowth`, `ProjectiveCubicExponent` | Exclude full ambient dimension when degree exceeds one and sharpen Theorem 1 to exponent `2*n^3`. |
| `SmallOutsidePoint`, `CurveGridDegreeBound` | Construct integer points of height at most the degree outside proper prime varieties and prove sharp grid counts for prime curves in every ambient dimension. |
| `WeightedSequenceEstimate`, `MixedDegreeProjectiveLocal`, `MixedDegreeProjectiveExample` | Prove the weighted-profile estimate in dimensions at least two, normalize arbitrary-degree local determinants, and check the unnormalized counterexample. |
| `AmbientProjectiveDeterminant`, `ProjectiveCoefficientNumerics`, `ProjectiveCoefficientHeightUniform` | Absorb interpolation costs with an actual minor-gcd divisor and prove Lemma 4.2.2 with a dimension-only multiplier. |
| `QuadraticHilbert90`, `QuadraticInvariantIdeal`, `QuadraticUnitNormQuotient`, `QuadraticInvariantIdeals`, `FiniteGroupPowerTorsion` | Explicit norm-one correction, invariant representatives, unit quotient and torsion bounds, and quadratic prime extension identities. |
| `SurfaceResidueEdgeCount`, `SurfaceResidueCover`, `SurfaceCoefficientReduction`, `SurfaceResidueLinearCount`, `SurfaceSmallCurveCover`, `SurfaceRetainedCurveCount`, `PrimitiveSurfaceFixedDegree`, `TopFormSurfaceFixedDegree` | Construct and count the smooth-congruence cover; discharge coefficient height and prove the full fixed-degree surface bound for every d ≥ 5. |
| `BoundedHyperplaneDimensionGrowth`, `TopFormDimensionGrowthAllDegrees`, `HypersurfaceDimensionGrowth` | Theorem 4 in all degrees d ≥ 5 and all ambient dimensions; rational equations and the full projective hypersurface case of Theorem 1. |
| `MonomialOrthants`, `OrthantHilbertPolynomial`, `OrthantMultiplicity`, `FilteredHilbertPolynomial` | Construct the eventual filtered Hilbert polynomial and its positive integral multiplicity for every proper ideal. |
| `ClassGroupTranslateFibers`, `ClassGroupNormCurveReduction`, `IntegerTranslationClassPacking` | Reduce actual two-torsion to signed norm curves and inject integer translates into a bounded archimedean lattice box. |
| `OddDegreeNormCurveBaseChange`, `AffinePlaneBadPrimeCount`, `OddDegreeNormCurveCount` | Prove odd-degree norm curves have full degree and irreducibility in every characteristic, bad-prime factor one, and a logarithm-free count. |
| `SurfaceLineDirections`, `BinaryHomogeneousIrreducibility`, `SurfaceDirectionalDerivative`, `SurfaceTransversePlane`, `SurfaceParallelLines` | Construct actual projective directions, nonzero directional derivatives and transverse irreducible plane sections; bound distinct parallel surface lines by d(d−1). |
| `SurfaceDirectionSum`, `SurfaceLineContribution`, `DegreeOneComponentLines`, `SurfaceDegreeOneCount`, `TopFormSurfaceCount` | Uniform reciprocal direction-height sum, corrected line contribution and full corrected surface bound C d^18 B for absolutely irreducible top form and d ≥ 16. |
| `CurveBoxDegreeBound`, `NonabsoluteSurfaceCount` | Elementary d(2B+1) prime-curve box bound and exact d²(2B+1) nonabsolute full-surface bound via constructed descent and components. |
| `ComplexGridInterpolation`, `ComplexMultivariateGrid` | Exact complex coefficient bounds 3^d and 3^(nd), a simultaneous bounded integer-grid witness and the corresponding leading-coefficient shear. |
| `TopFormIrreducibility`, `TopFormBadPrimes`, `TopFormAuxiliaryEstimate`, `TopFormAuxiliary` | Absolute irreducibility of the leading form controls the original equation and its bad primes; the resulting coefficient-uniform auxiliary has degree `C(r)d^(4−1/r)B^(1/d^(1/r))` and is a rational nonmultiple. |
| `StandardMonomials`, `MonomialRays`, `FilteredHilbertLinearity`, `FilteredLinearGrowth` | Exact standard-monomial model of filtered dimensions, eventual linearity under an actual linear growth bound, and the proper-intersection specialization with arbitrary initial cutoff. |
| `FilteredPrimeDecomposition`, `FilteredComponentRank`, `FilteredComponentDegreeBudget`, `CompleteIntersectionHeight`, `PrimeComponentTranscendence`, `CompleteIntersectionDegreeBudget`, `TopFormSurfaceComponents` | Actual minimal-prime decomposition, separators and additive Hilbert degree budget. The surface auxiliary covers all original bounded integer zeros by positive-degree rational prime curves of total degree at most `C d^(9/2) B^(1/√d)`. |
| `IntegralAffineLine`, `CriticalFilteredGrowth`, `DegreeOneAffineLine` | Degree-one prime curves with a rational point equal actual rational lines; primitive integer parametrization proves the box count `1+2B/height(direction)` and identifies the projective direction height. |
| `ClosedFormReducibilityCharZero`, `UniversalPlaneGoodSpecializationCharZero` | Characteristic-zero rank-drop criterion and an actual integer plane specialization that is geometrically irreducible of full degree while avoiding a prescribed nonzero parameter polynomial. |
| `SurfaceAuxiliaryExponent`, `SurfaceNonlinearCount`, `TopFormSurfaceNonlinear` | Both nonlinear curve-degree ranges are summed using the total-degree budget. Constructed components give the actual surface count outside their degree-one union at most `A d^18 B` for `d ≥ 16`, with a constant independent of the equation and radius. |
| `Box` | Exact integral-point counting at real radii; monotonicity, union bounds, injective transport. |
| `ProjectiveBox`, `ProjectivePrimitive` | Finite sets of actual rational projective points of bounded height; primitive integer representatives, exact maximum-coordinate height, and injective transport to integer boxes. |
| `ProjectiveZeroLocus`, `ProjectivePointSeparation` | Representative-independent homogeneous zero loci, reduction to integer families, and homogeneous interpolation at distinct projective points. |
| `ProjectiveSection`, `ProjectivePlaneBezout` | Projective Hilbert degree and sharp bounds for proper homogeneous sections over arbitrary fields; projective plane Bézout including points at infinity. |
| `ProjectiveLocalDeterminant`, `ProjectiveReduction`, `ProjectiveResidueDeterminant` | Unit normalization modulo prime powers, actual projective residue classes and multiplicities, and single-prime divisibility of all homogeneous evaluation minors. |
| `ProjectiveAffineChart`, `ProjectiveResidueCardinality` | Injective affine coordinates and a finite-field projective count bounded by its affine chart count plus the degree. |
| `HomogeneousChartIrreducible`, `ProjectiveFiniteFieldCount` | Degree and irreducibility under dehomogenization; actual projective plane residue count at most `p + 162 d² sqrt(p)` for irreducible homogeneous reduction of degree `d ≥ 2` and `p > 27 d⁴`. |
| `ProjectiveMultiplicity`, `ProjectivePrimeDeterminant`, `ProjectiveHeightDeterminant` | Singular multiplicity correction, sharp global prime-sum determinant bound, and coefficient-controlled bad-prime charge. |
| `ProjectiveHeightComparison`, `ProjectiveAuxiliary`, `ProjectiveAuxiliaryCount` | Exact-rank determinant comparison, bounded-degree homogeneous auxiliary polynomials, and projective point counts via Bézout. |
| `ProjectiveTranslation`, `ProjectivePlanePositionedCount`, `ProjectivePlaneAbsoluteCount` | Bounded coordinate positioning and coefficient-uniform `d⁴ B^(2/d)` counts for rational absolutely irreducible plane equations. |
| `ProjectivePlaneNonabsoluteCount`, `ProjectivePlaneLinearCount` | Nonabsolute and linear cases; the uniform plane-equation theorem in every positive degree. |
| `ProjectiveChartDegree`, `ProjectiveChartIdeal` | Exact equality of projective and affine-chart Hilbert functions, actual prime chart ideals, and transport of projective points. |
| `ProjectiveIntegerHeight`, `ProjectivePlaneProjection`, `ProjectiveProjectionCount` | Bounded projective projection preserving degree, with total exceptional loss at most `d²`. |
| `ProjectivePermutation`, `ProjectiveCurveBound` | Height-preserving coordinate changes and the full ambient-dimensional projective curve bound, CCDN Theorem 2. |
| `Plane` | Explicit plane-curve target; a coordinate-count bound for nonvertical affine lines. |
| `Curve` | Finite-dimensional filtered coordinate spaces, degree via eventual affine Hilbert growth, uniqueness of degree, full-dimensional target. |
| `Interpolation` | Evaluation matrices, nonzero coefficient vectors giving nonzero polynomials, degree and monomial-height bounds. |
| `RowSpan` | Vanishing transfers from selected evaluation rows to all rows in their rational span. |
| `AuxiliaryPolynomial` | Bombieri–Vaaler gives a nonzero vanishing polynomial with an explicit bound on every coefficient. |
| `Nondivisibility` | Leading coefficients obstruct divisibility; an explicit determinant threshold produces an auxiliary polynomial not divisible by the defining polynomial. |
| `Determinant` | Gram determinant upper bound; row-factor divisibility; determinant divisibility from congruent rows. |
| `LocalDeterminant` | Weighted factorizations over commutative rings, multiplicity exponents, quadratic determinant and maximal-minor-gcd divisibility for univariate polynomial evaluations in a residue class. |
| `BlockDeterminant` | Integer column-lattice factorization; residue-block maximal-minor divisors multiply and their prime exponents add, including deficient and empty blocks. |
| `SmoothLocalDeterminant`, `SmoothPlaneChart` | Finite polynomial Newton approximation proves the triangular local determinant exponent for actual smooth plane-curve residue classes, in either coordinate direction. |
| `SingularTangent`, `OriginLayerGenerators`, `OriginTruncationGenerators` | Actual origin-adic layers have dimension at most the plane-curve multiplicity; homogeneous generators span every finite truncation. |
| `ModularPolynomialLift`, `ModularOriginGenerators`, `SingularApproximation` | Lift the local generators to integer polynomials and prove uniform approximation modulo every prime power at actual integral zeros. |
| `FilteredDeterminant`, `HypersurfaceHilbert` | Actual local generators and determinant factorization in arbitrary dimension, with cumulative layer dimension bounded by `μ binomial(n+k,n)`. |
| `HypersurfaceLocalDeterminant`, `HypersurfaceMultiplicityEstimate`, `HypersurfaceResidue` | Every actual hypersurface residue point supplies determinant exponent at least `(n!/μ)^(1/n) n/(n+1) s^(1+1/n) − (n+1)s`, including singular points and zeros modulo the needed prime power. |
| `ProjectiveHypersurfaceLocal`, `ProjectiveHypersurfaceReduction` | Projective unit normalization in every dimension and chart, using actual reductions of primitive integer vectors. |
| `HypersurfaceAggregation`, `ProjectiveHypersurfaceResidueDeterminant` | Construct the actual projective residue partition and prove the sharp maximal-minor divisor in terms of total multiplicity, for homogeneous columns of a common degree. |
| `HypersurfaceCountNormalization` | Normalize a displayed finite-field count bound without changing the leading constant; the higher-dimensional finite-field count itself remains open. |
| `BinomialSectionBound`, `FiniteFieldInterpolation`, `FiniteFieldSectionCount` | Explicit polynomial separators and filtered Koszul dimensions bound actual common zeros by a dimension-only constant times the product of the degrees and `q^(ambient dimension−2)`, below the stated field-size degree threshold. |
| `HypersurfaceSingularities`, `ProjectiveHypersurfaceMultiplicity` | Count actual affine and projective singular points and prove the multiplicity correction `O_m(d² p^(m−1/2))` for projective hypersurface dimension `m ≥ 1` and `p > d²`. The sharp unweighted hypersurface count is still open. |
| `FiniteFieldProjectiveCone` | Exact cone identity `#affine zeros = (q−1) #projective zeros + 1` in positive homogeneous degree, and transfer of an explicit affine-cone estimate preserving leading coefficient one. |
| `SingularLocalDeterminant`, `SingularPlaneChart` | Actual singular residue classes contribute exponent `sum(i < s, floor(i / multiplicity))` to evaluation determinants and maximal-minor gcds; translation and residue-block assembly are proved. |
| `PlaneMultiplicity`, `SingularReduction` | Actual reduced points determine positive multiplicities bounded by the equation degree, the complete residue partition, and the quadratic exponent bound using their total multiplicity; no smoothness or supplied partition is required. |
| `PlaneMultiplicitySmooth` | Actual multiplicity greater than one forces singularity; total multiplicity is at most the point count plus `d²(d−1)` for an irreducible reduction below the characteristic. |
| `SmoothReduction`, `SmoothDeterminant` | Construct the actual smooth residue partition and prove the global logarithmic maximal-minor-gcd bound; finite-field point bounds and excluded primes remain explicit inputs. |
| `SingularDeterminant` | Global logarithmic maximal-minor-gcd bounds for arbitrary reduced points, including singular points, using actual point counts and the proved multiplicity correction; the prime-sum form retains explicit sharp point-count and good-prime hypotheses. |
| `PrimeCutoff`, `SingularDeterminantCutoff` | A prime-weighted tail bound of order `1/sqrt(L)` gives the `27d⁴` cutoff and a global rank-level determinant bound with `4 log(d)` loss and degree-independent error; sharp point counts and good reductions remain explicit inputs. |
| `HypersurfaceRankProfile`, `HypersurfaceRankRoots`, `HypersurfaceKernelRatio` | Exact binomial-layer rank formula, sharp power/root bounds, and kernel-rank ratio within `1/M` of `1/(d(r+1))`. |
| `WeightedHeightRatio`, `HypersurfaceHeightTransfer`, `ScaledHypersurfaceModel`, `ScaledHypersurfaceHeight`, `PrimeScaledAffineAuxiliary`, `AffineScalingExponent`, `PrimeScaledAffineHeight` | Lemma 4.2.3, prime-scaled model irreducibility, exact leading-height gain, and actual affine auxiliary polynomials with the affine exponent saving; the scaling prime is constructed for the small nonzero constant-coefficient branch. |
| `HomogeneousLinearDescent`, `HypersurfaceNonabsoluteAuxiliary`, `IntegerRationalIrreducibility`, `HypersurfaceBadPrimeFactor`, `HypersurfaceAuxiliaryTheorem`, `PaperLogarithmEstimate`, `ProjectivePlaneCoefficientCount` | Full auxiliary Theorem 3.1.1, exact degree-d nonabsolute auxiliary equation, the defined bad-prime factor and its height bound, Lemma 3.3.5, and coefficient-sensitive plane count. |
| `MultivariateGridHeight`, `HypersurfaceLeadingCoefficient`, `HypersurfacePositionHeight`, `HypersurfaceShearInvariance`, `IntegerCoefficientHeight`, `HypersurfaceAuxiliaryScaling`, `HypersurfaceAbsoluteAuxiliary`, `HypersurfaceProjectiveAuxiliary` | Arbitrary-dimensional bounded coordinate positioning, exact bad-prime invariance, and the coefficient-sensitive auxiliary theorem for all bounded rational projective zeros of absolutely irreducible homogeneous equations. |
| `HypersurfaceSmallHeightDegree`, `HypersurfaceSmallHeightAuxiliary`, `HypersurfaceLargeHeightDegree`, `HypersurfaceLargeHeightAuxiliary`, `HypersurfacePositionedAuxiliary` | Both numerical height regimes, integer degree selection, and actual auxiliary polynomials under explicit leading-coefficient positioning, retaining the exact bad-prime factor. |
| `HypersurfaceRankArchimedean`, `HypersurfaceRankLogarithm`, `HypersurfaceNormalizedComparison`, `HypersurfaceBadPrimeComparison` | Explicit logarithmic rank and archimedean errors, followed by the actual normalized no-auxiliary comparison with both leading coefficients retained exactly. |
| `GenericPlaneEulerMinorCharZero`, `UniversalPlaneEulerMinorCharZero`, `CoefficientwiseHomogeneous`, `UniversalHomogeneousForm`, `AmbientNoetherForms`, `AmbientNoetherVanishing`, `AmbientNoetherNonvanishing`, `NestedPolynomialL1`, `UniversalPlaneL1`, `AmbientNoetherHeight`, `UniversalNoetherForms`, `ExplicitNoetherTheorem`, `CoefficientwiseSubstitution` | Full Theorem 3.2.2: a finite universal family, exact degree and coefficient bound, all-characteristic vanishing, and characteristic-zero detection; homogeneous coefficient substitution. |
| `PolynomialUniformDifference`, `HypersurfacePointwiseRemainder` | Lemma 2.1's pointwise Hilbert remainder, uniform in multiplicity and coefficients, for actual hypersurface stalks. |
| `GaloisStableIdealDescent`, `GaloisComponentDegree`, `GaloisComponentPoints`, `NonRationalVarietyCount`, `ZeroDimensionalPrimeDescent`, `NonRationalProjectiveCount` | General affine and projective 4.1.3/4.1.4 counts, with Galois descent, component degree control and empty zero-dimensional rational loci. |
| `UniversalHyperplaneRestriction`, `GoodHyperplaneReindex`, `EffectiveHyperplaneAvoidance` | A constructed homogeneous bad-hyperplane detector of degree `d(d²−1)+1` for `d≥2`, with the omitted chart covered. |
| `GridVandermondeCounterexample`, `GlobalMixedDegreeDeterminant` | A primitive factorial grid on a fixed line refutes the differing-degree global determinant bound for every uniform error constant; common-degree bounds remain valid. |
| `HomogeneousFilteredRank`, `HomogeneousCurveHilbert`, `ProjectiveCoefficientExtension`, `HomogeneousPrimeComponents`, `NonRationalProjectiveCurve` | Graded/filtered Hilbert comparison, homogeneous geometric components, and the height-independent projective count `≤d²` for the nonrational and nonabsolute curve cases of 4.1.5. |
| `RowSeparatorCounterexample` | Formal counterexample to Lemma 5.4's printed constant; the existing factorial cofactor replacement remains valid. |
| `PaperPrimeEstimates` | CCDN 3.2.4 with its explicit constant 2, and 3.2.5 including convergence and an explicit infinite-tail bound for every positive cutoff. |
| `HigherDimensionalPrimeSum`, `HypersurfacePrimeDeterminant`, `HypersurfaceDeterminantRank` | Combine actual prime-power divisors, retain the fourth-power cutoff cost, and choose the dimension root of the rank as prime endpoint, giving the exact leading constant and rank power. |
| `HypersurfaceBadPrimeCoordinates`, `HypersurfaceHeightDeterminant`, `HypersurfaceHeightComparison` | Construct the exact geometric bad-prime set, discharge its height bound, and combine the global determinant estimate with exact Hilbert rank and Bombieri–Vaaler in the absence of an auxiliary polynomial. |
| `IntegerPolynomialAvoidance`, `PolynomialBoxHeight`, `IntegerPlaneWitness` | A nonzero evaluation on the grid `[0,2d³]`, coefficient-uniform box estimates, and a nonzero integer divisible by every actual bad prime above the degree. |
| `IntegerPlaneHeight`, `IntegerPlaneWitnessHeight`, `IntegerPlaneLogHeight`, `HypersurfaceBadPrimeHeight` | Bound the section coefficients and evaluated determinant witness, then prove the higher-dimensional bad-prime factor bound `O_m(max(log(H)/d²,1))` without an assumed witness or external Noether-form theorem. |
| `BadPrimeCharge` | A nonzero integer witness bounds the sum of log(p)/p over its prime divisors; splitting at the logarithmic height gives the exponential bad-prime factor linear in scaled logarithmic height. The geometric input is supplied for plane equations by `GeneralBadReduction` and `PlaneBadPrimes`. |
| `AlgebraicDifferentialConstants`, `RationalDifferential` | Formal differentiation on F(t), its characteristic-zero constant field, and descent of constants through algebraic differential extensions over an algebraically closed constant base. |
| `BoundedDifferentialConstants` | In positive characteristic, zero derivative implies constancy for rational functions with reduced numerator and denominator degrees below the characteristic; algebraic constant descent follows from the corresponding explicit minimal-polynomial coefficient bounds. |
| `DifferentialConstantRelation`, `PolynomialResultantDegree`, `ResidueEliminant`, `ResidueEliminantEvaluation`, `PositiveCharacteristicResidue` | Construct the nonzero resultant of `f` and `u f′−g`, prove its parameter-degree bound and its vanishing at `u=g(β)/f′(β)`, then prove the bounded-residue constant lemma in large characteristic directly from this relation. |
| `SeparableRootDifferential`, `PositiveCharacteristicClosedForms`, `PositiveCharacteristicRank` | Construct the separable differential root extension in positive characteristic and prove the monic irreducible closed-form classification. Over an algebraically closed field of characteristic `>2d²`, a monic irreducible equation of total and outer degree `d` gives coefficient-matrix rank at least `2d²−1`. Generic-plane irreducibility and hypersurface positioning are proved below; the effective bad-section estimate remains open. |
| `PowerSeriesBaseChange`, `FormalBranchBaseChange`, `PlaneSmoothGeometricIrreducibility` | Finite coefficient minors preserve power-series linear independence under arbitrary field extension. A faithful formal branch embeds the extended coordinate algebra into power series. Consequently, an irreducible plane curve with a smooth rational point remains irreducible over every extension field, in any characteristic and without a monicity assumption. |
| `HypersurfaceSmoothPoint`, `HypersurfaceGoodDirection` | Construct a smooth point on an irreducible hypersurface of degree below the characteristic over an algebraically closed field, and choose a direction avoiding the top homogeneous form, the tangent hyperplane and a selected coordinate hyperplane. |
| `AffinePlaneRestriction`, `SmoothPlaneMinor` | Actual affine-plane substitutions, their derivative and degree formulas, and a nonzero closed-form minor over the original field for a monic irreducible plane equation with a smooth rational point in characteristic `>2d²`. The positioned generic-plane argument is proved below; the effective bad-section estimate remains open. |
| `PolynomialPrimeLocalization`, `GenericPlaneStretch`, `GenericPlaneIrreducibility` | Nonconstant prime polynomials survive coefficient localization, and irreducibility survives purely transcendental extension. The actual equation `f(x,y*z)` is irreducible over the rational function field in the slopes when `f` is irreducible and monic in `x`. |
| `GenericPlaneSmoothness`, `GenericPlaneMinor` | A smooth origin in the distinguished direction makes the positioned generic plane geometrically irreducible. In characteristic `>2d²`, a monic equation of full outer degree `d` and total degree at most `d` supplies a nonzero determinant polynomial in its slopes. Hypersurface positioning is proved below; bounding the parameter degree and counting bad sections remain open. |
| `AffineLineLeading`, `HypersurfaceAffineCoordinates`, `HypersurfaceFullOuterDegree` | The top affine-line coefficient is the leading homogeneous form evaluated on its direction. An explicit invertible affine coordinate map preserves the degree bound, realizes the directional derivative at the origin, and gives full outer degree when that top value is nonzero. |
| `HypersurfacePositioning` | Construct the smooth base point, transverse full-degree direction and nonzero scalar normalization for every irreducible positive-degree hypersurface over an algebraically closed field with degree below the characteristic. In characteristic `>2d²`, this discharges the generic-plane construction's positioning assumptions and produces a nonzero slope minor. The universal affine-plane parameter bound and bad-section counts remain open. |
| `DifferentialResidue`, `RationalClosedForms`, `BivariateClosedForms` | A simple-root residue of a closed form is constant; for monic irreducible bivariate equations over an algebraically closed characteristic-zero field, every form within the strict outer-degree bounds is a constant multiple of the gradient. |
| `BivariateFactorForms` | Explicit closed forms from factors and repeated factors, with polynomial divisibility obstructions to their being scalar multiples of the whole gradient under stated coprimality hypotheses. |
| `BivariateCoefficientMatrix`, `ClosedFormBaseChange` | Actual integer coefficient matrix on 2d² unknowns, exact kernel encoding, and compatibility with arbitrary coefficient ring maps. |
| `ClosedFormRank`, `FiniteRowMinor`, `ClosedFormIntegerMinor` | Monic absolute irreducibility in characteristic zero forces rank at least 2d²−1, yielding a nonzero integer minor; rank drop in characteristic p forces p to divide it. |
| `ClosedFormHeight`, `ClosedFormMinorCharge` | Each entry is bounded by 2dH and each r-minor by r!(2dH)^r. The logarithmic bound fits the 27d⁴ cutoff and bounds the charge of primes with rank drop by log(1+log(H)/d²)+O(1). |
| `ClosedFormKernelWitness` | Every polynomial pair supported on the grid reconstructs as a coefficient vector; two independent closed forms force rank drop by two. |
| `BivariateTotalDegree` | Total degree transported from the multivariate ring, exact product degrees, derivative bounds, and actual grid support for factor forms of every multiplicity. |
| `ClosedFormFactorRank`, `ClosedFormReducibility` | Below the characteristic, every reducible monic equation of full outer degree forces rank drop by two; monic primary-factor extraction and all multiplicities are proved. |
| `MonicBadReduction` | For monic absolutely irreducible integer equations of full outer degree, constructs a positive height-controlled integer divisible by every geometric bad prime above the degree, and proves the geometric prime-charge bound. |
| `ClosedFormScaling`, `ConstantLeadingBadReduction` | Nonzero constant scaling preserves matrix rank. For integer equations of full outer degree, leading coefficient times minor detects geometric reducibility and degree drops, with the required scaled-height charge; integer monicity is unnecessary. |
| `PlaneShear`, `LeadingDirection`, `ShearNormalization` | Integral shears preserve irreducibility and total degree and commute with coefficient maps. A parameter in 0,...,d gives full outer degree, and the actual bad-prime set is preserved. |
| `ShearHeight` | A bounded integral shear increases coefficient height by at most (d+1)^(d+2). |
| `GeneralBadReduction`, `PlaneBadPrimes` | For every absolutely irreducible integer plane equation, construct a positive integer witness and the actual finite set of geometric bad primes above 27d⁴. Its charge is at most log(1+log(H)/d²)+O(1), including degree drops. |
| `HeightDeterminant`, `PlaneChartHeight` | Discharge the bad-prime assumptions in the determinant lower bound and actual affine-chart comparison using the equation's coefficient height. The sharp finite-field point count remains an explicit hypothesis. |
| `ResidueAggregation` | Cauchy–Schwarz aggregation of local multiplicity exponents with the leading constant preserved; global logarithmic lower bound from explicit local divisibilities. |
| `PrimeProduct` | Combine divisibility at distinct primes into a product and a logarithmic lower bound. |
| `MertensFirst` | First Mertens theorem: a uniform bounded error for the prime sum of log(p)/p, with convergent prime-power error. |
| `PrimeSums` | Weighted good-prime sums, charges for excluded primes, and analytic determinant lower bound from explicit local divisibility and finite-field point estimates. |
| `FilteredIntersection`, `MonomialDimension` | Filtered multiples, kernel dimension bounds, and exact monomial-space dimensions. |
| `PlaneHilbert` | Exact principal-plane Hilbert function; polynomial total degree equals the degree used by the counting target. |
| `PointSeparation`, `PolynomialSection`, `Bezout` | A proper degree-`m` section of an actual degree-`d` prime curve has at most `dm` distinct points; sharp plane intersection and integer-box counting forms. |
| `FormalImplicitRoot`, `FormalPlaneBranch` | Construct the unique formal power-series branch at a point with a nonzero partial derivative, in arbitrary characteristic. |
| `SectionImageRank`, `FormalBranchFaithful`, `FormalBranchOrder` | A proper section bounds independent polynomial images; the actual formal branch is faithful, and a degree-m section has local order at most dm. |
| `PowerSeriesOrderIndependence`, `PowerSeriesFrobenius` | Distinct orders and injective finite jets prevent Frobenius cancellation; the plane-curve condition is dD<p. |
| `FormalBranchMultiplicity`, `FormalPlaneDifferentiation`, `PlaneTangentMultiplicity` | Prove N times the number of distinct selected points is at most dm when a proper section's first N tangent derivatives vanish, with N at most the characteristic. All formal branches are constructed. |
| `PlaneFrobeniusAuxiliary`, `PlaneFrobeniusSystem`, `PlaneStepanovBound` | Construct nontrivial auxiliary coefficients from a strict finite-dimensional inequality and prove the resulting prime-field point count, including the d(d-1) critical-point correction. The numerical choice and sharp estimate are supplied by the next row. |
| `StepanovParameters`, `PlaneStepanovDimension`, `StepanovRealBound`, `SharpPlaneCount` | Choose integer degrees above 27d⁴, verify the exact dimension inequality, prove the prime-field bound p+161d² sqrt(p), and discharge the full coefficient-uniform rational-plane integral-point theorem. |
| `FunctionFieldRank`, `CurveFunctionField` | Hilbert growth bounds independent polynomial classes over a transcendental parameter field; common denominators prove the actual function-field extension is finite of degree at most d. |
| `CurveParameter`, `CurveRationalParameter` | Positive affine Hilbert degree supplies a transcendental original coordinate and a constructed embedding K(t) into the fraction field. |
| `BoundedLinearSeparation`, `BoundedPrimitiveElement`, `CurvePrimitivePair` | Construct an integer linear form with moment-curve coefficients (1,k,...) and k<=n*d² which, together with an original coordinate, generates the function field. |
| `BoundedProjectionCoordinates` | The pair maps integer points to integer points with box factor 1+n*(n*d²+1)^n. Preservation of curve degree and exceptional-fiber control are not asserted. |
| `PlaneSingularities` | Nonzero partial derivative below the characteristic and the `d(d-1)` bound for distinct singular points of an irreducible plane equation. |
| `RowSelection` | Independent spanning rows selected from a finite matrix, with strict rank deficiency from a nonzero annihilator. |
| `HomogeneousMonomials`, `HomogeneousHilbert` | Complete homogeneous monomial indexing, binomial dimensions, homogeneous-factor extraction, and the exact principal homogeneous Hilbert function. |
| `HomogeneousEvaluation`, `HomogeneousRank`, `HomogeneousAuxiliary` | An actual homogeneous equation supplies independent spanning evaluation rows with the full binomial rank deficit; Bombieri–Vaaler then produces a small homogeneous polynomial vanishing on the entire supplied point set. |
| `HomogeneousRankDichotomy` | Clearing denominators transfers absence of integer auxiliary polynomials to rational relations; exact evaluation rank and the plane identity 2s+d²=d(2M+3). |
| `HomogeneousDeterminantComparison`, `PlaneChartDeterminant` | Exact-rank Bombieri–Vaaler and coefficient obstruction give the logarithmic Gram/gcd upper bound; actual affine-chart rows combine it with the singular determinant lower bound. |
| `PlaneAuxiliaryDegree`, `PlaneAuxiliaryLargeHeight`, `PlaneAuxiliarySelection` | Derive explicit integer auxiliary degrees from the determinant comparison in both height ranges. The small-height bound retains B^(2/d) and the leading-coefficient saving L^(-1/d²); the large-height bound is O(d³). Sharp finite-field counts and coefficient positioning remain hypotheses. |
| `PrimitiveIntegerPolynomial`, `PrimitiveNormalization` | Extract primitive integer models of rational equations, preserving degree and homogeneous grading. Removing integer content does not increase coefficient height. Rational divisibility reflects to integer divisibility for every primitive equation. |
| `HomogeneousChart` | Restriction to x₀=1 is injective on each homogeneous degree. Explicit bounded homogenization inverts it; full chart degree transfers affine divisibility back to homogeneous divisibility. |
| `PlaneAuxiliaryCount` | The actual primitive auxiliary nonmultiples give proper rational affine sections. Bézout yields distinct-point bounds and bounds in the integer-box counting interface in both height ranges, still conditional on sharp finite-field counting and the stated coefficient-position hypotheses. |
| `IntegerGridInterpolation`, `PlaneGridHeight` | Integer-grid values control every coefficient, with factor (d+1)^(d+1) in one variable and (d+1)^(2(d+1)) in two. A bounded plane grid point supplies a nonzero height witness. |
| `HomogeneousTranslation`, `AffineTranslation` | Integral chart translations lift to homogeneous automorphisms. They preserve primitive equations, homogeneity, chart degree and irreducibility under coefficient maps; the point box grows by at most d+1. |
| `HomogeneousLeadingCoefficient`, `HomogeneousEvaluationHeight`, `LeadingPositionHeight` | A translation with parameters in 0,...,d gives a lexicographic leading coefficient L and an actual transformed-chart coefficient bound H with 1≤H and log L≤log H≤log L+14d². |
| `Analytic` | Elimination of coefficient height, absorption of additive errors, degree-2-through-24 square-root estimate, logarithm absorption. |

`PlaneCurveBound`, `AffineCurveBound` and `ProjectiveCurveBound` name
propositions proved by `planeCurveBound`, `affineCurveBound` and
`projectiveCurveBound`, respectively. The required finite-field estimates,
coefficient positioning, auxiliary polynomials and projection steps are proved.

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

## Remaining work

The six main results are proved. Remaining intermediate obligations include
exact projection geometry and height estimates, the Salberger covering
statement, the degree-one geometric boundary of hyperplane avoidance, and
the literal affine-factor versions of 4.2.1 and 4.2.4. The ledger distinguishes proved replacements
from the exact statements they do not yet imply.

`not_printed_row_separator_bound` formally disproves Lemma 5.4's printed
numerical constant. A five-equation system requires a coordinate of at least
120,050, while the stated bound is 120,000. The valid factorial cofactor bound
used by the existing proofs is unaffected; see the
[row-separator audit](docs/row-separator-audit.txt).

CCDN Lemmas 2.7--2.8 and Corollary 2.9 are now proved for the actual projective
hypersurface residue count and common-degree homogeneous evaluation matrices.
For a geometrically irreducible degree-`d` affine hypersurface in `n+3`
coordinates and `p > 27*d^4`, the point count is at most
`p^(n+2) + 164*d^2*p^(n+1)*sqrt(p)`. The projective count has constant 330;
including singular multiplicities gives the dimension-only constant
`330 + (n+3)*(n+4)^n`. The normalized root and sharp single-prime determinant
bound use this proved count, with no external finite-field hypothesis.

The proof constructs a cubic-degree bad-plane witness, separately bounds zero
sections by their three defining points, and uses an exact incidence bijection.
The characteristic-zero universal witness now supplies an actual nonzero
integer divisible by every bad prime above the degree. The exact bad-prime
set is proved finite, including degree-dropping reductions. Its quantitative
coefficient-height bound, the projective auxiliary theorem, and the surface and
slicing arguments are proved. The universal Noether-form theorem is now
proved separately with its exact coefficient bound and specialization properties.
See [the full-paper ledger](docs/full-paper-plan.txt) for precise coverage,
including the abstract statements not implied by the concrete local theorem.

## Curve proof route

The global determinant lower bound for curves is proved.
The local plane estimate now includes singular residue classes: the multiplicity
is the order of the actual translated reduction, and the local exponent is
`sum(i < s, floor(i / multiplicity))`, at least `s²/(2*multiplicity) - s`.
The full reduced-point partition and its positive total multiplicity are now
constructed from the actual equation. Residue-block aggregation and prime sums
are also proved. The sharp finite-field point bound is proved in `SharpPlaneCount`. The coefficient-controlled
bad-prime estimate for plane equations is now proved. The multiplicity correction is proved: it adds at most
`d²(d−1)` to the point count for irreducible reductions below the characteristic.
`SingularDeterminant` now combines this correction with the actual local
divisibilities into a global logarithmic gcd bound. Its exact-denominator form
needs no point-count estimate; its prime-sum form assumes the sharp point-count
bound and an explicit set of good primes. The cutoff refinement in `SingularDeterminantCutoff` removes the polynomial
degree error: primes above `27d⁴` yield a `4 log(d)` loss and an error independent
of `d`. The required sharp point-count bound is now proved in `SharpPlaneCount`. `HeightDeterminant`
discharges the bad-prime charge using the actual coefficient height.
`PlaneChartDeterminant` combines the singular lower bound with the actual
exact-rank homogeneous upper bound on the chart x₀=1.
The bad-prime witness construction now has a proved differential core: formal
rational differentiation, algebraic constant descent, simple-root residue
constancy, and the characteristic-zero monic bivariate closed-form
classification. Factor forms and their divisibility obstructions are also
proved. The actual integer matrix, characteristic-zero rank bound, nonzero
integer minor, coefficient-height bound and prime charge are now checked.
The full reducibility-to-rank-drop implication is proved for monic equations
of full outer degree below the characteristic, including repeated factors.
In this monic case the minor now detects every geometric bad prime above the
degree, with the required height and charge. The extension to non-monic equations of full outer degree is now proved,
including reductions whose degree drops. Bounded integral shears now supply
full outer degree and preserve the actual bad-prime set. The coefficient-height
cost is now bounded by (d+1)^(d+2). This completes the required uniform
bad-prime charge for plane equations in arbitrary coordinates. `PlaneBadPrimes`
constructs the finite excluded set, and `PlaneChartHeight` incorporates its
charge into the actual affine-chart determinant comparison.
`PlaneAuxiliarySelection` now chooses an integer degree and constructs a nonmultiple
in both height ranges. Writing L for the leading coefficient's absolute value and
K for the determinant error, the small-height degree is at most
`d + log(B) + 2 exp(K+23) d³ (1+log(H)/d²) B^(2/d) / L^(1/d²) + 2`.
When `log(H) ≥ 4d log(B)` and `log(H) ≤ log(L)+Td²`, the degree is at most
`(34+8 exp(K+6+T))d³`. The finite-field estimate is explicit in both theorems.
Primitive normalization and rational nondivisibility are now proved.
`HomogeneousChart` supplies the chart transfer, and `PlaneAuxiliaryCount`
applies Bézout to the actual integer points and to the real-radius counting
interface. In the small-height range its bound is d times the displayed
auxiliary-degree bound; in the large-height range it is
`(34+8 exp(K+6+T))d⁴`. These are conditional bounds preceding the affine scaling
step: this earlier chart bound has exponent 2/d. The scaled-model result below
obtains exponent 1/d under an explicit scaling-prime hypothesis.
Coefficient positioning is now proved: a translation with parameters in 0,...,d
preserves the primitive equation, homogeneous degree, chart degree and
irreducibility, and increases the point-box radius by at most d+1. For the
actual transformed equation it supplies H with `log(L)≤log(H)≤log(L)+14d²`.
The scaled-model translation and height elimination are now assembled.
`PolynomialMapAuxiliary` applies the determinant argument to polynomial
coordinates of the original curve. `ScaledHomogenization` constructs the
integral model with points `(p,x,y)` and a coefficient of size at least `p^d`.
It is primitive when the prime p does not divide the original constant term.
`HomogeneousSlice` and `ScaledAuxiliaryCount` transfer nonmultiples to proper
sections on x₀=p. The actual bounded translation has point radius `(d+1)B`,
and `ScaledModelPosition` supplies H≥p^d with the position loss 14d².
`ScaledPlaneCount` combines both auxiliary-degree branches with Bézout;
`scaled_plane_finite_count_one_over_degree` in `ScaledBoxExponent` gives
`K(C,A) d³ B^(1/d) (log B+d)` for actual distinct integer points when
`B/A≤p≤B`, p does not divide the constant term, and the stated sharp
finite-field estimate holds with constant C. The constant is explicit and
independent of the equation's coefficients. `ScalingPrime` constructs a suitable
prime with the absolute ratio `A=exp(2*mertensError+2)` when `B≥A` and the
nonzero constant term has `log|f(0)|<B/A`. `ScaledPlaneSmallCoefficient`
therefore removes the prime hypothesis in that branch. The complementary height and box cases are now covered by `UnscaledModelCount`,
`AffineBoxRanges` and `AffineNonzeroConstant`: large coefficients give O(d⁴),
and small boxes use the coefficient-uniform 2/d fallback. `AffineTranslationCount`
removes a zero constant term by a bounded integer translation, preserving
primitivity, degree, irreducibility and the actual residue count.
`AffinePlaneAssembly` therefore proves the target 1/d count for primitive
absolutely irreducible integer plane equations at every B≥1, conditional only
on the stated sharp finite-field estimate. `RationalPlaneAssembly` extends it
to rational absolutely irreducible equations with one coefficient-independent
constant. `SharpPlaneResidueBound` names the remaining finite-field obligation;
it is discharged with constant 161 by `SharpPlaneCount.sharpPlaneResidueBound`.
`PolynomialLinearDescent` and `NonabsolutePlaneCount` now handle rational
irreducible equations that split over an extension: each factor's base-field
zeros lie on a nonzero base-field polynomial of no larger degree, and Bézout
gives at most d² points in total. `PlaneCurveAssembly` therefore proves
`SharpPlaneResidueBound C → PlaneCurveBound` for C≥0. The finite-field
nongeometric case also costs at most d²; `GeometricResidueReduction` reduces
the missing point estimate to geometrically irreducible equations alone.
The local Stepanov machinery is now proved: formal branches, local and summed
multiplicity bounds, tangent differentiation, and Frobenius noncancellation.
`PlaneFrobeniusSystem` constructs actual auxiliary coefficients from a strict
dimension inequality. `PlaneStepanovBound` proves
`#S * N <= d*(D+p*A) + d*(d-1)*N` provided `d*D<p`, `N<=p`, and
`sum(r<N, H(D+A+r*d)) < H(D)*H(A)`, where H is the actual filtered
coordinate-ring dimension. It constructs polynomial bases, the nontrivial
auxiliary and every formal branch. `StepanovParameters` now chooses
`A=floor(sqrt(p)/d)`, `D=floor((p-1)/d)` and `N=d*A-4*d²`.
`PlaneStepanovDimension` proves the dimension inequality above `27d⁴`;
`StepanovRealBound` handles all rounding and proves the explicit error constant
161. Thus `SharpPlaneCount` proves `p+161d² sqrt(p)` for every irreducible
prime-field equation above the cutoff, discharges `SharpPlaneResidueBound 161`,
and proves `PlaneCurveBound` unconditionally. The next projection steps now
construct a transcendental original coordinate, prove its function-field
extension has degree at most d, and produce a primitive linear form with
integer moment-curve coefficients and k<=n*d². This actual pair has integral
coordinates and box factor `1+n*(n*d²+1)^n`. It generates the function field;
`PlaneProjectionDegree` now constructs its irreducible image equation and proves
that its degree is at most d. `PlaneIdealCount` proves the complete prime-ideal
counting interface in dimension two. `ProjectionFieldDegree` proves degree
preservation when the parameter extension has degree d.
`BoundedBirationalProjection` constructs polynomial reconstruction identities
with a proper common denominator Q. `ProjectionExceptionalCount` proves that
a finite source set loses at most d*deg(Q) points under projection.
`CurveProjectionDeformation` now constructs a polynomial family of plane
relations. Differentiating it in `CurveDerivativeReconstruction` reconstructs
every linear source coordinate using the same partial-derivative denominator,
provided the projection preserves degree. Its degree is at most d-1, so
`DegreePreservingProjectionCount` proves an actual point-count error of
at most d(d-1). This includes geometrically reducible prime curves and uses no
normalization or exceptional-fiber assumption.
`BoundedDegreePreservingProjection` now constructs such a pair unconditionally.
The first moment parameter satisfies `k₀<=n²*d`, and the second `k₁<=n*d²`.
The proof bounds geometric infinity points using the actual infinity Hilbert
pieces, chooses a bounded form avoiding them, and uses the Nullstellensatz to
generate the eventual coordinate filtration. This forces the parameter-field
extension to have degree exactly d. No geometric-integrality or supplied
parameter-field hypothesis remains. The two moment forms have integral
coefficients, preserve degree, and incur at most d(d-1) exceptional points.
`DegreePreservingProjectionBox` now bounds the actual integral projection in
a box enlarged by `(n+1)*((n+1)*(d+1))^(2*n)`. `ProjectionScaleAbsorption`
proves its logarithm is at most `(2*n²+3*n)*d`, retaining the exact exponent
1/d and the d³ factor after rescaling. `AffineProjectionCount` transports
actual integral points to the plane image. `AffineCurveBound.affineCurveBound`
assembles these proved inputs and the d(d-1) error into the full theorem.
The constant depends only on n; the ideal, degree, coefficients and real radius
are universally quantified afterward.
See [the proof roadmap](docs/roadmap.txt).

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
