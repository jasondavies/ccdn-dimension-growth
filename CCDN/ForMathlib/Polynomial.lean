/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Finite differences and derivatives of univariate polynomials

## Main results

* `Polynomial.natDegree_comp_X_add_C_sub_self` and
  `Polynomial.leadingCoeff_comp_X_add_C_sub_self`: in characteristic zero, the finite difference
  `P(X + s) - P(X)` of a polynomial of degree `m + 1` with step `s ≠ 0` has degree `m` and
  leading coefficient `P.leadingCoeff * (m + 1) * s`.
* `Polynomial.derivative_ne_zero_of_natCast_natDegree_ne_zero`: a polynomial whose degree is
  nonzero in the coefficient ring has nonzero derivative.
-/

@[expose] public section

namespace Polynomial

section FiniteDifference

variable {K : Type*} [Field K] [CharZero K]

private theorem natDegree_and_leadingCoeff_comp_X_add_C_sub_self
    (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1) (s : K) (hs : s ≠ 0) :
    (P.comp (X + C s) - P).natDegree = m ∧
      (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s := by
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
    exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
      (Nat.cast_add_one_ne_zero m)) hs
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

/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` lowers
the degree by exactly one. -/
theorem natDegree_comp_X_add_C_sub_self (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1)
    (s : K) (hs : s ≠ 0) : (P.comp (X + C s) - P).natDegree = m :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).1

/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` of a
polynomial of degree `m + 1` has leading coefficient `P.leadingCoeff * (m + 1) * s`. -/
theorem leadingCoeff_comp_X_add_C_sub_self (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1)
    (s : K) (hs : s ≠ 0) :
    (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).2

end FiniteDifference

/-- A polynomial whose degree `n` satisfies `(n : R) ≠ 0` has nonzero derivative. -/
theorem derivative_ne_zero_of_natCast_natDegree_ne_zero {R : Type*} [Semiring R]
    [NoZeroDivisors R] {f : R[X]} (hn : (f.natDegree : R) ≠ 0) : derivative f ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    rintro h
    simp [h] at hn
  have hf : f ≠ 0 := by intro h; simp [h] at hpos
  intro hz
  have hc := congrArg (fun g : R[X] => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  have he : ((f.natDegree - 1 : ℕ) : R) + 1 = (f.natDegree : R) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  rw [he] at hc
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hn) hc

end Polynomial
