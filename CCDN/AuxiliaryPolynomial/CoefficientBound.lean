/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix

/-!
# Coefficient bounds for interpolation polynomials

A polynomial assembled by `polynomialOfCoefficients` from an integer coefficient vector
bounded by `R` has every coefficient bounded by `R`. The Bombieri–Vaaler auxiliary
constructions of the determinant method use this to bound the coefficients of the auxiliary
polynomial. Nondivisibility by the defining polynomial is a separate step, proved from the
global determinant lower bound in Section 3.3.
-/

@[expose] public section

namespace CCDN

open Matrix

theorem abs_coefficient_polynomialOfCoefficients_le {n N : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (v : Fin N → ℤ) {R : ℝ} (hR : 0 ≤ R) (hv : InBox v R)
    (e : Fin n →₀ ℕ) :
    |((polynomialOfCoefficients mon v).coeff e : ℝ)| ≤ R := by
  classical
  by_cases he : ∃ j, mon j = e
  · obtain ⟨j, rfl⟩ := he
    rw [coefficient_polynomialOfCoefficients mon hmon]
    exact hv j
  · have hz : (polynomialOfCoefficients mon v).coeff e = 0 := by
      simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial, not_exists.mp he]
    simpa [hz] using hR

end CCDN
