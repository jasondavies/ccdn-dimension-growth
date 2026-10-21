/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.AffineNormalizationRank
public import CCDNPaper.Center.AffinePointZariski
public import CCDNPaper.Center.BalancedParameterFiniteness
public import CCDNPaper.Center.BirationalCenterExtensionWitness
public import CCDNPaper.Center.BirationalCenterLocus
public import CCDNPaper.Center.BirationalCenterSubspace
public import CCDNPaper.Center.BirationalComplementProjection
public import CCDNPaper.Center.BoundedCenterProjection
public import CCDNPaper.Center.BoundedCenterProjectionAllRows
public import CCDNPaper.Center.BoundedGoodCenter
public import CCDNPaper.Center.ChowAxisEvaluation
public import CCDNPaper.Center.ChowDistinguishedVariable
public import CCDNPaper.Center.ChowExactDegree
public import CCDNPaper.Center.ChowIncidenceBaseChange
public import CCDNPaper.Center.ChowIncidenceIdeal
public import CCDNPaper.Center.ChowIncidenceMinimalPolynomial
public import CCDNPaper.Center.ChowLastRowSplit
public import CCDNPaper.Center.ChowLinearSpecialization
public import CCDNPaper.Center.ChowNestedIncidence
public import CCDNPaper.Center.ChowNormalizationDegreeComparison
public import CCDNPaper.Center.ChowPivotParametrization
public import CCDNPaper.Center.ChowPolynomialPower
public import CCDNPaper.Center.ChowProjectionCriterion
public import CCDNPaper.Center.ChowProjectionPower
public import CCDNPaper.Center.ChowRestrictionBirational
public import CCDNPaper.Center.ChowRowSymmetry
public import CCDNPaper.Center.ClosedFieldChowBirationalCriterion
public import CCDNPaper.Center.ClosureNormalizationInfinite
public import CCDNPaper.Center.ClosurePolynomialFractionField
public import CCDNPaper.Center.ClosurePolynomialMap
public import CCDNPaper.Center.DetectorBounds
public import CCDNPaper.Center.DetectorExtension
public import CCDNPaper.Center.FixedCoordinateCenterRows
public import CCDNPaper.Center.FixedCoordinateEliminationInfinite
public import CCDNPaper.Center.FixedCoordinateGenericNormalization
public import CCDNPaper.Center.GenericBlockLine
public import CCDNPaper.Center.GenericBlockLineHomogeneity
public import CCDNPaper.Center.GenericBlockLineIrreducible
public import CCDNPaper.Center.GenericHomogeneousGeneration
public import CCDNPaper.Center.GenericLinearIndependence
public import CCDNPaper.Center.GenericLinearNormalizationOpenness
public import CCDNPaper.Center.GenericLinearParameterField
public import CCDNPaper.Center.GenericLinearPowerBasis
public import CCDNPaper.Center.GenericPolynomialIndependence
public import CCDNPaper.Center.GeometricCenterRows
public import CCDNPaper.Center.GeometricIdealPrimality
public import CCDNPaper.Center.GeometricProjectionCenter
public import CCDNPaper.Center.GeometricProjectionHilbert
public import CCDNPaper.Center.GeometricProjectiveChow
public import CCDNPaper.Center.GeometricProjectiveCurveProjection
public import CCDNPaper.Center.GoodCenterWitness
public import CCDNPaper.Center.HomogeneousCurveHilbert
public import CCDNPaper.Center.HomogeneousIntegralRelation
public import CCDNPaper.Center.HomogeneousNormalizationRank
public import CCDNPaper.Center.HomogeneousParameterCertificates
public import CCDNPaper.Center.HomogeneousParameterPowers
public import CCDNPaper.Center.HomogeneousProjectionBirational
public import CCDNPaper.Center.HomogeneousProjectionNoBasePoint
public import CCDNPaper.Center.HomogeneousProjectionRankBound
public import CCDNPaper.Center.IncidenceDeterminantCertificate
public import CCDNPaper.Center.IndependentBirationalProjection
public import CCDNPaper.Center.IndependentPrimitiveExtension
public import CCDNPaper.Center.IndependentProjectionRows
public import CCDNPaper.Center.IntegerMinorProjectiveHeight
public import CCDNPaper.Center.IntermediateFieldParameterTower
public import CCDNPaper.Center.MatrixProjectionFields
public import CCDNPaper.Center.MinorMatrix
public import CCDNPaper.Center.MinorProjection
public import CCDNPaper.Center.MultivariateDeformation
public import CCDNPaper.Center.PluckerComplementEquations
public import CCDNPaper.Center.PluckerCoordinates
public import CCDNPaper.Center.PluckerZariski
public import CCDNPaper.Center.PolynomialCoefficientBasis
public import CCDNPaper.Center.PolynomialCoefficientDescent
public import CCDNPaper.Center.PolynomialCoefficientNormalizationRank
public import CCDNPaper.Center.PolynomialCoordinateEmbeddings
public import CCDNPaper.Center.PolynomialLinearSpecialization
public import CCDNPaper.Center.PrincipalWeightedHomogeneous
public import CCDNPaper.Center.ProjectionHeight
public import CCDNPaper.Center.ProjectiveChowChartReduction
public import CCDNPaper.Center.ProjectiveChowEquation
public import CCDNPaper.Center.ProjectiveChowExactDegree
public import CCDNPaper.Center.ProjectiveChowIncidence
public import CCDNPaper.Center.ProjectiveChowWithoutChart
public import CCDNPaper.Center.ProjectiveClosureRecovery
public import CCDNPaper.Center.ProjectiveIncidenceClosed
public import CCDNPaper.Center.ProjectiveIncidencePermutation
public import CCDNPaper.Center.RadialParameterFieldRank
public import CCDNPaper.Center.ResultantCoefficientFamily
public import CCDNPaper.Center.ResultantDetector
public import CCDNPaper.Center.ResultantForms
public import CCDNPaper.Center.ScalarQuotientFractionField
public import CCDNPaper.Center.ScalarQuotientPolynomialLocalization
public import CCDNPaper.Center.SubspaceQuotient
public import CCDNPaper.Center.UniversalCenterChowRestriction
public import CCDNPaper.Center.ZeroColumnCenterDensity
public import CCDNPaper.Center.ZeroColumnCenterSubspace
public import CCDNPaper.Center.ZeroColumnMinorSpecialization
public import CCDNPaper.Counterexample.DegreeFactorSharpness
public import CCDNPaper.Counterexample.GlobalMixedDegreeDeterminant
public import CCDNPaper.Counterexample.GridVandermonde
public import CCDNPaper.Counterexample.HomogenizedBadPrimeFactor
public import CCDNPaper.Counterexample.MixedDegreeProjective
public import CCDNPaper.Counterexample.OriginProjectivePoint
public import CCDNPaper.Counterexample.RowSeparatorConstant
public import CCDNPaper.Counterexample.WeightedDimensionOne
public import CCDNPaper.Counterexample.ZeroDimensionalCenter
public import CCDNPaper.Statements.AffineCurveDegreeSharpness
public import CCDNPaper.Statements.AffineVarietyProjection
public import CCDNPaper.Statements.AmbientCenterProjection
public import CCDNPaper.Statements.BirationalCenterPluckerHeight
public import CCDNPaper.Statements.CenterProjectionFormula
public import CCDNPaper.Statements.ComplexMultivariateGrid
public import CCDNPaper.Statements.CoprimeNewtonEdgeCount
public import CCDNPaper.Statements.ExplicitNoetherTheorem
public import CCDNPaper.Statements.FixedPluckerComplementEquations
public import CCDNPaper.Statements.GeometricProjectiveProjection
public import CCDNPaper.Statements.HypersurfaceDeterminantFamily
public import CCDNPaper.Statements.HypersurfaceLowerBoundAllDegrees
public import CCDNPaper.Statements.HypersurfacePointwiseRemainder
public import CCDNPaper.Statements.HypersurfaceSourcePositionedAuxiliary
public import CCDNPaper.Statements.IntegralHyperplaneAvoidance
public import CCDNPaper.Statements.LiteralAffineBadPrimeHeight
public import CCDNPaper.Statements.LiteralAffinePlaneCount
public import CCDNPaper.Statements.LogarithmEstimate
public import CCDNPaper.Statements.MixedDegreeProjectiveLocal
public import CCDNPaper.Statements.NonRationalProjectiveCurve
public import CCDNPaper.Statements.PrimeEstimates
public import CCDNPaper.Statements.PrimeIntegerLocalDeterminant
public import CCDNPaper.Statements.ProjectiveCoefficientHeightUniform
public import CCDNPaper.Statements.ProjectiveCurveDegreeSharpness
public import CCDNPaper.Statements.ProjectivePlaneUniformExpression
public import CCDNPaper.Statements.SalbergerSurfaceTheorem

/-!
# CCDNPaper

Root module of the paper library of the CCDN formalisation. It imports every module of the
library; `scripts/update-root.py` generates it. The library builds on the main library `CCDN`
and holds the parts of the paper that the main results do not use:
* `CCDNPaper/Center/`: Section 5 (Chow forms, good centres and Plücker equations);
* `CCDNPaper/Statements/`: the paper's intermediate statements and side results as printed
  (or as corrected), linked to their labels in `docs/statements.md`;
* `CCDNPaper/Counterexample/`: the formal refutations of printed intermediate statements.

Its declarations live in the namespace `CCDN`, like those of the main library.
-/
