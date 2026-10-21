/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Vanishing partial derivatives

If `∂f/∂xᵢ = 0`, then each exponent of `xᵢ` occurring in `f` is zero in the coefficient ring.
Below the characteristic this means that `xᵢ` does not occur in `f`.

## Main results

* `MvPolynomial.coeff_mul_natCast_eq_zero_of_pderiv_eq_zero`: the coefficient of `m` is
  annihilated by the exponent `m i`.
* `MvPolynomial.notMem_vars_of_pderiv_eq_zero`: a variable with vanishing partial derivative does
  not occur, when its exponents are nonzero in the coefficient ring.
* `MvPolynomial.exists_pderiv_ne_zero`: a nonconstant polynomial of total degree below the
  characteristic has a nonzero partial derivative.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*}

/-- If `∂f/∂xᵢ = 0`, then the coefficient of `f` at `m` is annihilated by the exponent `m i`. -/
theorem coeff_mul_natCast_eq_zero_of_pderiv_eq_zero [CommSemiring R] {f : MvPolynomial σ R}
    {i : σ} (h : pderiv i f = 0) (m : σ →₀ ℕ) : f.coeff m * (m i : R) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (m i) with hmi | hmi
  · simp [hmi]
  have hu : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    refine tsub_add_cancel_of_le fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hji
    · simpa using Nat.one_le_iff_ne_zero.mpr hmi.ne'
    · simp [Finsupp.single_eq_of_ne hji]
  have hc : (pderiv i f).coeff (m - Finsupp.single i 1) = 0 := by simp [h]
  rw [coeff_pderiv, hu, Finsupp.tsub_apply, Finsupp.single_eq_same,
    ← Nat.cast_add_one, Nat.sub_add_cancel hmi] at hc
  exact hc

/-- A variable with vanishing partial derivative does not occur in `f`, provided the positive
natural numbers up to its degree are nonzero in `R`. -/
theorem notMem_vars_of_pderiv_eq_zero [CommSemiring R] [NoZeroDivisors R]
    {f : MvPolynomial σ R} {i : σ} (h : pderiv i f = 0)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.degreeOf i → (n : R) ≠ 0) : i ∉ f.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  exact mul_ne_zero (mem_support_iff.mp hm)
    (hchar _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi)) (monomial_le_degreeOf i hm))
    (coeff_mul_natCast_eq_zero_of_pderiv_eq_zero h m)

/-- A polynomial of positive total degree has a nonzero partial derivative, provided the
positive natural numbers up to its total degree are nonzero in `R`. -/
theorem exists_pderiv_ne_zero [CommSemiring R] [NoZeroDivisors R] {f : MvPolynomial σ R}
    (hpos : 0 < f.totalDegree)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.totalDegree → (n : R) ≠ 0) :
    ∃ i, pderiv i f ≠ 0 := by
  classical
  obtain ⟨m, hm, i, hi⟩ : ∃ m ∈ f.support, ∃ i, m i ≠ 0 := by
    by_contra! h
    exact hpos.ne' ((totalDegree_eq_zero_iff (p := f)).mpr h)
  refine ⟨i, fun hz ↦ notMem_vars_of_pderiv_eq_zero hz
    (fun n hn hle ↦ hchar n hn (hle.trans (degreeOf_le_totalDegree f i))) ?_⟩
  exact (mem_vars_iff_mem_support i).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hi⟩

end MvPolynomial
