/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.Interpolation
public import ArithmeticHeights.BombieriVaaler

/-!
# Bombieri–Vaaler applied to polynomial interpolation

This is the small-coefficient auxiliary-polynomial step of the determinant method.
It does not yet ensure nondivisibility by a defining polynomial. Establishing that property
requires the global determinant lower bound and the Hilbert-function argument in CCDN §3.3.
-/

@[expose] public section

namespace CCDN

open Matrix

theorem abs_coefficient_polynomialOfCoefficients_le {n N : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (v : Fin N → ℤ) {R : ℝ} (hR : 0 ≤ R) (hv : ∀ j, |(v j : ℝ)| ≤ R)
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
