module

public import CCDN.BoundedMinorSpecialization
public import CCDN.CoordinateGridAvoidance

/-! Each entry of a matrix occurs to degree at most one in every maximal
minor. Substituting maximal minors therefore preserves a polynomial's degree
bound in every individual matrix coordinate, independently of the row count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem aeval_degreeOf_le
    {K σ τ : Type*} [Field K] [Fintype σ]
    (a : σ → MvPolynomial τ K) (i : τ) (D : ℕ)
    (ha : ∀ j, (a j).degreeOf i ≤ D) (f : MvPolynomial σ K) :
    (aeval a f).degreeOf i ≤ D * f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro e he
  rw [aeval_monomial]
  change (C (f.coeff e) * e.prod (fun j k => a j ^ k)).degreeOf i ≤ _
  apply (degreeOf_C_mul_le _ _ _).trans
  rw [Finsupp.prod_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ j, (a j ^ e j).degreeOf i := degreeOf_prod_le _ _ _
    _ ≤ ∑ j, e j * D := Finset.sum_le_sum (fun j _ =>
      (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (ha j)))
    _ = D * e.sum (fun _ k => k) := by
      rw [← Finset.sum_mul, Finsupp.sum_fintype _ _ (by simp), Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left D (le_totalDegree he)

end
end CCDN
