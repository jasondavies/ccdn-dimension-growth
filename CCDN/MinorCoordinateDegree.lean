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

theorem universalMaximalMinor_degreeOf {r n : ℕ}
    (c : Fin r ↪ Fin n) (p : Fin r × Fin n) :
    (universalMaximalMinor c).degreeOf p ≤ 1 := by
  classical
  rw [universalMaximalMinor, Matrix.det_apply']
  apply (degreeOf_sum_le p _ _).trans
  apply Finset.sup_le
  intro σ _
  have hcast : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin r × Fin n) ℚ)) =
      C ((Equiv.Perm.sign σ : ℤ) : ℚ) := by simp
  rw [hcast]
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le p _ _).trans
  calc
    _ ≤ ∑ j : Fin r, if σ j = p.1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hrow : σ j = p.1
      · simp only [hrow, ite_true, Matrix.of_apply]
        simp only [degreeOf_X]
        split_ifs <;> omega
      · have hp : p ≠ (σ j, c j) := by
          intro he
          exact hrow (congrArg Prod.fst he).symm
        simp only [hrow, ite_false, Matrix.of_apply, degreeOf_X_of_ne hp]
        exact le_rfl
    _ = 1 := by simp only [← σ.eq_symm_apply]; simp

theorem minor_substitution_degreeOf_le {r n : ℕ}
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ) (p : Fin r × Fin n) :
    (aeval universalMaximalMinor F).degreeOf p ≤ F.totalDegree := by
  simpa only [one_mul] using aeval_degreeOf_le universalMaximalMinor p 1
    (fun c => universalMaximalMinor_degreeOf c p) F

end
end CCDN
