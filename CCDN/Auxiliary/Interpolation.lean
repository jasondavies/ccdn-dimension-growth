/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Evaluation matrices and auxiliary polynomials

A coefficient vector in the kernel of the monomial evaluation matrix produces a polynomial
vanishing at every specified point. Injectivity of the list of monomials ensures that a
nonzero vector produces a nonzero polynomial.
-/

@[expose] public section

namespace CCDN

open Matrix

noncomputable def polynomialOfCoefficients {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (v : Fin N → ℤ) : MvPolynomial (Fin n) ℤ :=
  ∑ j, MvPolynomial.monomial (mon j) (v j)

theorem coefficient_polynomialOfCoefficients {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (hmon : Function.Injective mon) (v : Fin N → ℤ) (j : Fin N) :
    (polynomialOfCoefficients mon v).coeff (mon j) = v j := by
  classical
  simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial,
    hmon.eq_iff]

theorem polynomialOfCoefficients_ne_zero {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (hmon : Function.Injective mon) {v : Fin N → ℤ} (hv : v ≠ 0) :
    polynomialOfCoefficients mon v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hc := coefficient_polynomialOfCoefficients mon hmon v j
  rw [h] at hc
  simpa using hc.symm

theorem totalDegree_polynomialOfCoefficients_le {n N M : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (v : Fin N → ℤ)
    (hdeg : ∀ j, (mon j).degree ≤ M) :
    (polynomialOfCoefficients mon v).totalDegree ≤ M := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (hdeg j)

noncomputable def evaluationMatrix {n N s : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (points : Fin s → (Fin n → ℤ)) : Matrix (Fin s) (Fin N) ℤ :=
  fun i j => (mon j).prod fun k e => points i k ^ e

theorem eval_polynomialOfCoefficients {n N s : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (points : Fin s → (Fin n → ℤ)) (v : Fin N → ℤ) (i : Fin s) :
    MvPolynomial.eval (points i) (polynomialOfCoefficients mon v) =
      (evaluationMatrix mon points *ᵥ v) i := by
  simp [polynomialOfCoefficients, evaluationMatrix, Matrix.mulVec, dotProduct,
    MvPolynomial.eval_monomial, mul_comm]

/-- Monomial evaluation has the expected height bound, uniformly in the exponents and point. -/
theorem abs_monomial_value_le {n M : ℕ} (e : Fin n →₀ ℕ) (x : Fin n → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hx : ∀ i, |(x i : ℝ)| ≤ B)
    (he : e.degree ≤ M) :
    |((e.prod (fun i k => x i ^ k) : ℤ) : ℝ)| ≤ B ^ M := by
  have hsum : ∑ i, e i ≤ M := by rwa [Finsupp.degree_eq_sum] at he
  rw [Finsupp.prod_fintype e (fun i k => x i ^ k) (fun _ => pow_zero _)]
  push_cast
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin n, B ^ e i := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
    _ = B ^ (∑ i, e i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ M := pow_le_pow_right₀ hB hsum

end CCDN
