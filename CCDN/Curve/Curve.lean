/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.FilteredIntersection
public import CCDN.Plane.Plane
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Affine curves and the full counting target

An affine algebraic set is represented by an ideal in `ℚ[x₁,…,xₙ]`. For an integral curve,
its degree is the slope of the eventually linear affine Hilbert function: the dimension
of polynomials of total degree at most `M` in its coordinate ring is `d*M + c` for large `M`.

`AffineCurveBound` records the full target, with constants depending only on the ambient
dimension. It is proved by `affineCurveBound` in the `AffineCurveBound` module.
`PlaneHilbert` proves the passage from a plane defining
polynomial to this Hilbert-function degree. `exists_plane_count_reduction` (in
`AffineProjectionCount`) reduces a prime ideal of any ambient dimension, including two, to an
irreducible plane equation of the same degree. `BoundedDegreePreservingProjection`
constructs bounded integral projections preserving degree in every dimension.
The general integer-height and counting assembly is completed in
`AffineProjectionCount`, `ProjectionScaleAbsorption` and `AffineCurveBound`.
-/

@[expose] public section

namespace CCDN

abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- The affine Hilbert function: the dimension of the polynomials of total degree at
most `M` in the coordinate ring. -/
noncomputable def affineHilbertFunction {n : ℕ} (I : Ideal (CoordinatePolynomial n))
    (M : ℕ) : ℕ := Module.finrank ℚ (filteredCoordinateSpace I M)

/-- Degree via the eventual affine Hilbert polynomial. This condition is mathematical
data about the coordinate ring, and contains no point-counting estimate. -/
def HasAffineCurveDegree {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (affineHilbertFunction I M : ℤ) = (d : ℤ) * M + c

theorem affineCurveDegree_unique {n : ℕ} {I : Ideal (CoordinatePolynomial n)} {d e : ℕ}
    (hd : HasAffineCurveDegree I d) (he : HasAffineCurveDegree I e) : d = e := by
  obtain ⟨N, c, hN⟩ := hd
  obtain ⟨P, k, hP⟩ := he
  have hN0 := hN (max N P) (le_max_left _ _)
  have hP0 := hP (max N P) (le_max_right _ _)
  have hN1 := hN (max N P + 1) (by omega)
  have hP1 := hP (max N P + 1) (by omega)
  push_cast at hN0 hP0 hN1 hP1
  have hde : (d : ℤ) = e := by nlinarith
  exact_mod_cast hde

/-- CCDN (2020), Theorem 3, using the affine Hilbert function to specify degree.
The constant is chosen before the ideal, degree, and real box radius. -/
def AffineCurveBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (CoordinatePolynomial n), I.IsPrime →
      ∀ d : ℕ, 0 < d → HasAffineCurveDegree I d →
        ∀ B : ℝ, 1 ≤ B → (count (idealZeroLocus I) B : ℝ) ≤ C * curveBound d B

end CCDN
