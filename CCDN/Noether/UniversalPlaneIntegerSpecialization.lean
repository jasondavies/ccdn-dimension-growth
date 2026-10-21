/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.FiniteFieldBadPlanes
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.IntegerPolynomialAvoidance
/-! A nonzero universal witness certifies a geometrically irreducible
plane section in characteristic zero. Integer specialization can simultaneously
avoid any additional nonzero polynomial condition on the plane parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Construct an integer plane specialization which is geometrically
 irreducible of full degree and avoids an additional algebraic condition.
 The parameter bound is independent of the equation's coefficient height. -/
theorem exists_integer_geometrically_good_plane_avoiding {σ : Type*} [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (P : MvPolynomial (PlaneParameters (Option σ)) ℤ) (hP : P ≠ 0) :
    ∃ v : PlaneParameters (Option σ) → ℤ,
      (∀ i, 0 ≤ v i ∧ v i ≤ 2 * f.totalDegree ^ 3 + P.totalDegree) ∧
      eval v P ≠ 0 ∧
      (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)).natDegree =
        f.totalDegree ∧
      bivariateTotalDegree
          (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)) =
        f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  obtain ⟨rows, cols, hW, hdegree⟩ := exists_integer_universalPlane_badWitness f hir hd
  let W := universalPlaneBadWitness f rows cols
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero (W * P) (mul_ne_zero hW hP)
    (2 * f.totalDegree ^ 3 + P.totalDegree)
    ((totalDegree_mul W P).trans (Nat.add_le_add_right hdegree _))
  rw [eval_mul] at hvalue
  obtain ⟨hvW, hvP⟩ := mul_ne_zero_iff.mp hvalue
  let φ := (Int.castRingHom (AlgebraicClosure ℚ)).comp (eval v)
  have hwφ : φ W ≠ 0 := by
    simpa only [φ, RingHom.comp_apply, Int.coe_castRingHom, ne_eq, Int.cast_eq_zero] using hvW
  have hgood := universalPlaneBadWitness_good_specialization f hd (.of_charZero _) rows cols φ hwφ
  refine ⟨v, hv, hvP, ?_⟩
  simpa only [φ, bivariateMap_comp_apply, universalPlaneSection] using hgood

end
end CCDN
