module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! The degree and leading coefficient of a finite difference, used for
proper sections of filtered coordinate rings. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

theorem polynomial_finite_difference_degree_leadingCoeff
    (P : Polynomial ℚ) (m : ℕ) (hm : P.natDegree = m + 1)
    (s : ℚ) (hs : s ≠ 0) :
    (P.comp (X + C s) - P).natDegree = m ∧
      (P.comp (X + C s) - P).leadingCoeff =
        P.leadingCoeff * (m + 1) * s := by
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hm
  have hhasse : (hasseDeriv m P).natDegree ≤ 1 := by
    have h := natDegree_hasseDeriv_le P m
    omega
  have hform := eq_X_add_C_of_natDegree_le_one hhasse
  have hcoeff : (P.comp (X + C s) - P).coeff m =
      P.leadingCoeff * (m + 1) * s := by
    rw [coeff_sub, ← taylor_apply, taylor_coeff, hform]
    simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
      zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show 1 + m = m + 1 by omega, Nat.choose_succ_self_right, ← hm,
      coeff_natDegree]
    rw [hm, Nat.cast_add, Nat.cast_one]
    ring
  have hcoeff0 : (P.comp (X + C s) - P).coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP) (by positivity)) hs
  have hdiff0 : P.comp (X + C s) - P ≠ 0 := by
    intro h
    simp [h] at hcoeff0
  have hdeg : (P.comp (X + C s) - P).natDegree = m := by
    apply le_antisymm
    · have hlt := degree_sub_lt_right (degree_taylor P s) hP (leadingCoeff_taylor s P)
      change (P.comp (X + C s) - P).degree < P.degree at hlt
      rw [degree_eq_natDegree hdiff0, degree_eq_natDegree hP, Nat.cast_lt] at hlt
      omega
    · exact le_natDegree_of_ne_zero hcoeff0
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

end
end CCDN
