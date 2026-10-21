/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Curve.CurvePrimitivePair
/-! Evaluation of the moment coordinates used by the bounded primitive pair. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma momentCoordinate_eval {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (z : Fin n → K) :
    eval z (momentCoordinate K n k) = ∑ j : Fin n, (k : K) ^ j.val * z j := by
  simp only [momentCoordinate, map_sum, map_mul, eval_C, eval_X]

end
end CCDN
