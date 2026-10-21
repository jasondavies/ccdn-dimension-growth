/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Echelon.Zsqrtd

/-! Uniform first-order bounds for differences of monic polynomials with
nonnegative coefficients. The error constant does not depend on the step. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Finset

lemma nat_power_gap_le (n x y μ : ℕ) (hxy : x = y + μ) :
    x ^ (n + 1) ≤ y ^ (n + 1) + (n + 1) * μ * x ^ n := by
  induction n with
  | zero => simpa using hxy.le
  | succ n ih =>
    have hy : y ≤ x := by omega
    have h₁ := Nat.mul_le_mul_left y ih
    have h₂ := Nat.mul_le_mul_left ((n + 1) * μ * x ^ n) hy
    have h₃ := congrArg (fun z => z * x ^ (n + 1)) hxy
    simp only [pow_succ] at *
    nlinarith

lemma nat_augmented_power_gap_le (n x y μ a : ℕ) (hxy : x = y + μ)
    (ha : a ≤ μ) :
    x ^ (n + 2) + a * x ^ (n + 1) ≤
      y ^ (n + 2) + a * y ^ (n + 1) + (n + 2) * μ * x ^ (n + 1) := by
  have h₁ := Nat.mul_le_mul_left (y + a) (nat_power_gap_le n x y μ hxy)
  have hya : y + a ≤ x := by omega
  have h₂ := Nat.mul_le_mul_left ((n + 1) * μ * x ^ n) hya
  have h₃ := congrArg (fun z => z * x ^ (n + 1)) hxy
  simp only [pow_succ] at *
  nlinarith

lemma nat_augmented_power_gap_uniform (n x y μ a : ℕ) (hxy : x = y + μ) :
    x ^ (n + 2) + a * x ^ (n + 1) ≤
      y ^ (n + 2) + a * y ^ (n + 1) + (n + 2) * μ * x ^ (n + 1) +
        a ^ 2 * (n + 1) * x ^ n := by
  by_cases ha : a ≤ μ
  · exact (nat_augmented_power_gap_le n x y μ a hxy ha).trans (Nat.le_add_right _ _)
  · have hμ : μ ≤ a := by omega
    have h₁ := nat_power_gap_le (n + 1) x y μ hxy
    have h₂ := Nat.mul_le_mul_left a (nat_power_gap_le n x y μ hxy)
    have h₃ := Nat.mul_le_mul_left (a * (n + 1) * x ^ n) hμ
    nlinarith

lemma nat_polynomial_eval_top_two (p : ℕ[X]) (n : ℕ)
    (hdegree : p.natDegree = n + 2) (hmonic : p.Monic) (x : ℕ) :
    p.eval x = x ^ (n + 2) + p.coeff (n + 1) * x ^ (n + 1) +
      ∑ i ∈ range (n + 1), p.coeff i * x ^ i := by
  rw [p.eval_eq_sum_range, hdegree, sum_range_succ, sum_range_succ]
  have hc : p.coeff (n + 2) = 1 := hdegree ▸ hmonic.coeff_natDegree
  rw [hc]
  ring

lemma nat_polynomial_lower_terms_le (p : ℕ[X]) (n x : ℕ) (hx : 0 < x) :
    (∑ i ∈ range (n + 1), p.coeff i * x ^ i) ≤
      (∑ i ∈ range (n + 1), p.coeff i) * x ^ n := by
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by simpa using mem_range.mp hi))

/-- This constant depends only on the polynomial, never on the evaluation
point or on the difference step. -/
def polynomialDifferenceConstant (p : ℕ[X]) (n : ℕ) : ℕ :=
  (∑ i ∈ range (n + 1), p.coeff i) + p.coeff (n + 1) ^ 2 * (n + 3)

lemma nat_polynomial_difference_uniform (p : ℕ[X]) (n : ℕ)
    (hdegree : p.natDegree = n + 2) (hmonic : p.Monic)
    (k μ : ℕ) (hk : 0 < k) (hμ : μ ≤ k) :
    p.eval k ≤ p.eval (k - μ) + (n + 2) * μ * k ^ (n + 1) +
      polynomialDifferenceConstant p n * k ^ n := by
  have hgap := nat_augmented_power_gap_uniform n k (k - μ) μ (p.coeff (n + 1))
    (by omega)
  have hrem := nat_polynomial_lower_terms_le p n k hk
  rw [nat_polynomial_eval_top_two p n hdegree hmonic k,
    nat_polynomial_eval_top_two p n hdegree hmonic (k - μ)]
  unfold polynomialDifferenceConstant
  have hz := Nat.zero_le (∑ i ∈ range (n + 1), p.coeff i * (k - μ) ^ i)
  have he := Nat.zero_le (p.coeff (n + 1) ^ 2 * k ^ n)
  nlinarith only [hgap, hrem, hz, he]

lemma nat_polynomial_before_step_uniform (p : ℕ[X]) (n : ℕ)
    (hdegree : p.natDegree = n + 2) (hmonic : p.Monic)
    (k μ : ℕ) (hk : 0 < k) (hμ : k < μ) :
    p.eval k ≤ (n + 2) * μ * k ^ (n + 1) +
      polynomialDifferenceConstant p n * k ^ n := by
  have hrem := nat_polynomial_lower_terms_le p n k hk
  rw [nat_polynomial_eval_top_two p n hdegree hmonic k]
  unfold polynomialDifferenceConstant
  by_cases ha : p.coeff (n + 1) ≤ k
  · have hbase : k + p.coeff (n + 1) ≤ (n + 2) * μ := by nlinarith
    have h₁ := Nat.mul_le_mul_right (k ^ (n + 1)) hbase
    have he := Nat.zero_le (p.coeff (n + 1) ^ 2 * (n + 3) * k ^ n)
    simp only [pow_succ, pow_zero] at h₁ he ⊢
    nlinarith only [h₁, hrem, he]
  · have hka : k ≤ p.coeff (n + 1) := by omega
    have h₁ : k ^ 2 ≤ p.coeff (n + 1) ^ 2 := Nat.pow_le_pow_left hka 2
    have h₂ := Nat.mul_le_mul_left (p.coeff (n + 1)) hka
    have h₃ := Nat.mul_le_mul_right (k ^ n) h₁
    have h₄ := Nat.mul_le_mul_right (k ^ n) h₂
    have he := Nat.zero_le (p.coeff (n + 1) ^ 2 * (n + 1) * k ^ n)
    have hz := Nat.zero_le ((n + 2) * μ * k ^ (n + 1))
    simp only [pow_succ, pow_zero] at h₃ h₄ he hz ⊢
    nlinarith only [h₃, h₄, hrem, he, hz]

end
end CCDN
