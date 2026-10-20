# CCDN Dimension Growth

A Lean 4 formalisation of Castryck–Cluckers–Dittmann–Nguyen's dimension-growth
paper, including coefficient-uniform point bounds.

**Status: the full affine and projective curve bounds are proved in Lean.**
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

**The full paper is not yet formalised.** Higher-dimensional dimension growth,
lower-bound constructions and the class-group application remain open. The
[full-paper ledger](docs/full-paper-plan.txt) records the complete scope
and the external inputs that must be proved.

The higher-dimensional bad-prime height estimate (CCDN Corollary 3.2.3) is
also proved. `hypersurface_bad_prime_factor_max` bounds the actual bad-prime
factor by a dimension-dependent constant times `max(log(H)/d², 1)`, where
`H >= 1` bounds the equation's coefficients. The proof constructs a bounded
integer plane specialization, a nonzero integer witness and its height bound.
It includes degree-dropping reductions. The exact universal Noether-form
statement in Theorem 3.2.2 remains open.

The higher-dimensional simultaneous-prime determinant estimate is proved for
maximal minors of common-degree homogeneous evaluation matrices. It retains
the exact rank exponent and leading constant in Proposition 3.2.6, constructs
the bad-prime set, and discharges its coefficient-height bound. The resulting
Bombieri–Vaaler comparison and uniform auxiliary-degree selection in both
height ranges are also proved. The arbitrary-family formulation with differing column degrees
is not yet claimed.

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
the author's published corrections. The proved coefficient-height dichotomy
has an explicit degree-dependent multiplier, sufficient for the auxiliary
argument; Lemma 4.2.2's printed dimension-only multiplier is also still open.

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
The generic commutative algebra adapted from the Pierce development retains
its Apache-2.0 headers; [the provenance manifest](docs/pierce-generic-provenance.json)
records the exact source and destination hashes and the scope of each port.

Characteristic-zero plane specialization also constructs an integer plane
whose section is geometrically irreducible of full degree while avoiding any
additional nonzero polynomial condition on its parameters. The parallel-line
multiplicity bound and the sum over directions are still needed for corrected
Proposition 4.3.3. For surface degree `d ≥ 16`, the nonlinear components'
contribution is bounded by `C d^18 B`, using the proved total-degree budget
and the unconditional affine curve theorem. The combined theorem
`top_form_surface_nonlinear_count` constructs the components and bounds the
original surface's bounded integer points outside their degree-one union by
`A d^18 B`, with `A` chosen independently of the equation and radius.
The complete surface count still needs the line contribution. Degrees 5
through 15 and higher-dimensional dimension growth remain open.

The constant is independent of the curve's coefficients. The project supplies the external
counting input for the Pierce-length refinements.
The Pierce joint-lift development proves `128/435 + ε`, then the optimization
`(1310 − √655)/4365 + ε`. It needs ambient dimension seven: unpowered graph degrees
17 through 5928, and degrees bounded in terms of the fixed powers for the optimized
version. Exceptional curves still use dimension three in degrees 2 through 24.
The new route uses ordinary pattern counting. The external counting theorem
and its integration into the Pierce application are proved. The Pierce
repository retains a source-hashed snapshot of the affine-curve library
while this standalone repository develops the rest of the CCDN paper.

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
| `FilteredIntersection`, `MonomialDimension` | Filtered multiples, kernel dimension bounds, and exact monomial-space dimensions, adapted from the Pierce development. |
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

Theorems 1 and 4 (higher-dimensional dimension growth), Proposition 5 and
Section 6 (lower bounds), and Theorem 6 (class-group application) remain open.
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
coefficient-height bound remains open, as do the global auxiliary polynomials
and the surface, slicing and projection arguments.
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
