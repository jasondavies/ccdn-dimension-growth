/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Algebra.CharZeroOrGT
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Height.FiniteFieldSectionCount
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.SimpleRing.Principal
/-! The singular points of an irreducible hypersurface satisfy a
coefficient-uniform codimension-two finite-field bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero partial derivative cuts the irreducible hypersurface
properly. Fixed-degree finite-field interpolation bounds all its singular points. -/
theorem hypersurface_singular_points_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 2)) (ZMod p))
    (hf : Irreducible f) (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin (n + 2) → ZMod p) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ (n + 4) ^ n * f.totalDegree * (f.totalDegree - 1) * p ^ n := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  have hdeg := pderiv_totalDegree_le f j
  have hnd := not_dvd_pderiv_of_pderiv_ne_zero hf.ne_zero hj
  have hdegrees : f.totalDegree + (pderiv j f).totalDegree ≤
      2 * (Fintype.card (ZMod p) - 1) := by
    rw [ZMod.card]
    omega
  have h := finite_field_common_zeros_card_le f (pderiv j f) hf.prime hnd hdegrees
    z hz hzf (fun i => hzsing i j)
  rw [ZMod.card] at h
  exact h.trans (Nat.mul_le_mul_right (p ^ n)
    (Nat.mul_le_mul_left ((n + 4) ^ n * f.totalDegree) hdeg))

end
end CCDN
