/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.BoundedPrimitiveElement
/-! Bounded linear coordinates generating an affine curve's function
field. Degree preservation and control of exceptional fibers are separate
projection obligations; this module proves the quantified birational input. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The bounded integer moment-curve linear form. -/
def momentCoordinate (K : Type*) [CommRing K] (n k : ℕ) : MvPolynomial (Fin n) K :=
  ∑ j : Fin n, C ((k : K) ^ j.val) * X j

lemma momentCoordinate_degree (K : Type*) [CommRing K] [Nontrivial K] (n k : ℕ) :
    (momentCoordinate K n k).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

lemma momentCoordinate_fraction {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F] (k : ℕ) :
    algebraMap (MvPolynomial (Fin n) K ⧸ I) F
      ((Ideal.Quotient.mk I) (momentCoordinate K n k)) =
      ∑ j : Fin n, algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (X j)) * (k : F) ^ j.val := by
  simp only [momentCoordinate, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end
end CCDN
