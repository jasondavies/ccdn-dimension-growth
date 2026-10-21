/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
public import CCDN.Hypersurface.NonabsolutePlaneCount
/-! The geometric bad-prime factor used by the determinant method.
It is zero for nonabsolute equations and an exact finite exponential product
otherwise. For nonzero homogeneous equations it agrees with CCDN Definition
3.2.1. For affine equations its bad-prime predicate also includes degree loss;
this stronger convention is not identical to the literal printed definition. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma absolute_integer_polynomial_totalDegree_pos {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    0 < f.totalDegree := by
  have hh := totalDegree_pos_of_nonzero_nonunit _ hf.ne_zero hf.not_isUnit
  unfold totalDegree at hh ⊢
  rwa [support_map_of_injective _ Int.cast_injective] at hh

def hypersurfaceBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ := by
  classical
  exact if h : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f) then
    Real.exp (∑ p ∈ (finite_fin_hypersurface_bad_primes f h
      (absolute_integer_polynomial_totalDegree_pos f h)).toFinset, Real.log p / p)
  else 0

lemma hypersurfaceBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ hypersurfaceBadPrimeFactor f := by
  unfold hypersurfaceBadPrimeFactor
  split <;> positivity

lemma hypersurfaceBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    hypersurfaceBadPrimeFactor f = 0 := by
  simp only [hypersurfaceBadPrimeFactor, dite_eq_right hf]

lemma hypersurfaceBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ 27 * d ^ 4 < p ∧ HypersurfaceBadReduction f p) :
    hypersurfaceBadPrimeFactor f = primeSetFactor bad := by
  classical
  unfold hypersurfaceBadPrimeFactor
  rw [dite_eq_left hf]
  congr 1
  have he : (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset = bad := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdegree, hbad]
  rw [he]

/-- The bad-prime factor satisfies the coefficient-height bound also
for nonabsolute equations, where the factor is zero by definition. -/
theorem hypersurfaceBadPrimeFactor_le_height {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H) :
    hypersurfaceBadPrimeFactor f ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  have hc : 0 < hypersurfaceHeightConstant (n + 1) :=
    lt_of_lt_of_le zero_lt_one (hypersurfaceHeightConstant_one_le _)
  by_cases hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)
  · obtain ⟨bad, hbad, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge f hf
      (absolute_integer_polynomial_totalDegree_pos f hf) H hH hcoeff
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    calc
      _ ≤ Real.exp (Real.log (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1) :=
        Real.exp_le_exp.mpr hcharge
      _ = _ := by
        rw [show Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 =
          Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + (2 * mertensError + 1) by ring,
          Real.exp_add, Real.exp_log (by positivity)]
        ring
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    positivity

/-- The max-form of CCDN Corollary 3.2.3 for the defined factor itself. -/
theorem hypersurfaceBadPrimeFactor_le_max {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H) :
    hypersurfaceBadPrimeFactor f ≤
      (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
  have hh := hypersurfaceBadPrimeFactor_le_height f H hH hcoeff
  have h1 := le_max_left (Real.log H / (f.totalDegree : ℝ) ^ 2) (1 : ℝ)
  have h2 := le_max_right (Real.log H / (f.totalDegree : ℝ) ^ 2) (1 : ℝ)
  have hc : 0 ≤ Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1) :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2 h1) hc]

end
end CCDN
