/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The plane-curve target

`PlaneCurveBound` records the statement proved by `planeCurveBound` in `SharpPlaneCount`.
Irreducibility is over `ℚ`, not absolute irreducibility. The one constant is uniform in the
polynomial, its degree, its coefficients, and the real radius.
-/

@[expose] public section

namespace CCDN

def zeroLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}

noncomputable def curveBound (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d)

/-- The `n = 2` case of CCDN (2020), Theorem 3, expressed using rational defining
polynomials. The proof in `SharpPlaneCount` includes denominator clearing and content removal. -/
def PlaneCurveBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 2) ℚ, Irreducible f →
    0 < f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤ C * curveBound f.totalDegree B

end CCDN
