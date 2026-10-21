/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.IntegerPlaneLogHeight
public import CCDN.Analysis.PrimeSums
public import CCDN.Auxiliary.AuxiliaryDegreeBound
public import CCDN.Auxiliary.HypersurfaceBadPrimes
import CCDN.Auxiliary.BadPrimeCharge
import CCDN.Plane.IntegerPlaneWitness
import CCDN.Plane.IntegerPlaneWitnessHeight
/-! The geometric bad-prime charge in arbitrary dimension is controlled by
coefficient height, via an explicit integer witness with bounded height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  obtain ⟨rows, cols, v, hv, hw, hdiv⟩ := exists_bounded_integer_plane_witness f hf hpos
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H (2 * (f.totalDegree : ℝ) ^ 3)
  have hd : 1 ≤ f.totalDegree := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by nlinarith [one_le_pow₀ hdR (n := 3)]
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [abs_of_nonneg (by exact_mod_cast (hv i).1)]
    exact_mod_cast (hv i).2
  have hS : 1 ≤ S := integerPlaneHeight_one_le _ _ hd H hH
  have hcoeffS : BivariateCoefficientBound (universalPlaneSection f v) S :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_, ?_⟩
  · rw [Int.cast_abs]
    exact (universalPlaneBadWitness_eval_log_bound f hd rows cols v S hS hcoeffS hw).trans
      (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · intro p hp hbad
    exact (dvd_abs _ _).mpr (hdiv p hp hbad)

/-- The logarithmic charge bound for any finite family of bad primes.
This includes degree-dropping primes as well as geometric reducibility. -/
theorem hypersurface_bad_prime_charge
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, 27 * f.totalDegree ^ 4 < p) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hpos
  apply bad_prime_charge_of_height P hD (fun p hp => (hP p hp).choose) _ _ _ _ hheight
  · intro p hp
    apply hdiv p _ (hP p hp)
    have h1 := Nat.le_mul_self f.totalDegree
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    nlinarith [hcut p hp]
  · nlinarith [one_le_pow₀ hd1 (n := 4)]
  · exact one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _)))
  · intro p hp
    exact_mod_cast hcut p hp

/-- The exponential bad-prime factor has the coefficient-height dependence
required in CCDN Corollary 3.2.3. -/
theorem hypersurface_bad_prime_factor
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, 27 * f.totalDegree ^ 4 < p) :
    primeSetFactor P ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (Fintype.card (Option σ))) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have h := Real.exp_le_exp.mpr (hypersurface_bad_prime_charge f hf hpos H hH hcoeff P hP hcut)
  have hc : 0 < hypersurfaceHeightConstant (Fintype.card (Option σ)) :=
    lt_of_lt_of_le zero_lt_one (hypersurfaceHeightConstant_one_le _)
  have hh : 0 < 1 + Real.log H / (f.totalDegree : ℝ) ^ 2 := by
    have := div_nonneg (Real.log_nonneg hH) (sq_nonneg (f.totalDegree : ℝ))
    linarith
  calc
    _ ≤ Real.exp (Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1) := h
    _ = _ := by
      rw [add_assoc, Real.exp_add, Real.exp_log (mul_pos hc hh)]
      ring

/-- The maximum formulation of CCDN Corollary 3.2.3, with an explicit
constant depending only on the number of variables. -/
theorem hypersurface_bad_prime_factor_max
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, 27 * f.totalDegree ^ 4 < p) :
    primeSetFactor P ≤
      (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (Fintype.card (Option σ))) *
        max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
  have h := hypersurface_bad_prime_factor f hf hpos H hH hcoeff P hP hcut
  have hc : 0 ≤ Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (Fintype.card (Option σ)) :=
    mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one (hypersurfaceHeightConstant_one_le _))
  have hm : 1 + Real.log H / (f.totalDegree : ℝ) ^ 2 ≤
      2 * max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
    have h1 := le_max_left (Real.log H / (f.totalDegree : ℝ) ^ 2) 1
    have h2 := le_max_right (Real.log H / (f.totalDegree : ℝ) ^ 2) 1
    linarith
  apply h.trans
  convert mul_le_mul_of_nonneg_left hm hc using 1
  ring

end
end CCDN
