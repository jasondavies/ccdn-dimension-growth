/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import CCDN.Noether.RationalDifferential
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! Coefficientwise and outer derivatives of bivariate polynomials, and their
compatibility with rational differentiation, for the closed-form criterion. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Polynomial.Bivariate
attribute [local instance] rationalDifferential

/-- Differentiate the inner variable of a bivariate polynomial. -/
def bivariateCoefficientDerivative (F : Type*) [CommRing F] :
    Derivation F F[X][X] F[X][X] :=
  PolynomialModule.equivPolynomialSelf.compDer Polynomial.derivative'.mapCoeffs

@[simp]
lemma coeff_bivariateCoefficientDerivative {F : Type*} [CommRing F] (p : F[X][X]) (n : ℕ) :
    ((bivariateCoefficientDerivative F) p).coeff n = (p.coeff n).derivative := rfl

lemma bivariateCoefficientDerivative_monomial {R : Type*} [CommRing R] (m n : ℕ) (a : R) :
    (bivariateCoefficientDerivative R) (monomial m (monomial n a)) =
      monomial m (monomial (n - 1) (a * n)) := by
  ext i
  simp only [coeff_bivariateCoefficientDerivative, coeff_monomial]
  split_ifs <;> simp [derivative_monomial]

/-- Differentiate a bivariate monomial in the outer variable. -/
lemma bivariate_derivative_monomial {R : Type*} [CommRing R] (m n : ℕ) (a : R) :
    (monomial m (monomial n a)).derivative = monomial (m - 1) (monomial n (a * m)) := by
  rw [derivative_monomial, ← map_natCast (C : R →+* R[X]) m, monomial_mul_C]

lemma bivariateCoefficientDerivative_map {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).map (algebraMap F[X] (RatFunc F)) =
      Differential.mapCoeffs (p.map (algebraMap F[X] (RatFunc F))) := by
  ext n
  simp only [coeff_map, coeff_bivariateCoefficientDerivative, Differential.coeff_mapCoeffs]
  exact (rationalDerivative_polynomial (p.coeff n)).symm

end
end CCDN
