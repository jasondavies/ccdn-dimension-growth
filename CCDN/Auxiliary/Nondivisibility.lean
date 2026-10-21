/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Small coefficients exclude polynomial multiples

The arithmetic point is that a nonzero integer multiplier has a leading coefficient of
absolute value at least one. This is the coefficient obstruction used in CCDN §3.3.
The determinant bound needed to make the auxiliary polynomial small enough remains separate.
-/

@[expose] public section

namespace CCDN

theorem abs_leadingCoeff_le_of_dvd {n : ℕ} (order : MonomialOrder (Fin n))
    {f g : MvPolynomial (Fin n) ℤ} (hg : g ≠ 0) (hfg : f ∣ g) :
    |order.leadingCoeff f| ≤ |order.leadingCoeff g| := by
  obtain ⟨q, rfl⟩ := hfg
  have hq : q ≠ 0 := by intro h; simp [h] at hg
  have hq1 := Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hq)
  rw [MonomialOrder.leadingCoeff_mul, abs_mul]
  nlinarith [abs_nonneg (order.leadingCoeff f)]

end CCDN
