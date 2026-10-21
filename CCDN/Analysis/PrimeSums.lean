/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mertens
public import CCDN.Determinant.ResidueAggregation
/-! The Mertens lower bound for the prime sum after excluding a finite
bad-prime set. -/

@[expose] public section
namespace CCDN
open Finset Real

noncomputable def mertensError : ℝ := Real.log 4 + 6 + Mertens.E₁

lemma mertensError_pos : 0 < mertensError := by
  have hE : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertensError
  linarith

/-- The first Mertens estimate retains an explicit charge for excluded primes. -/
theorem prime_sum_lower_sdiff {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) :
    Real.log x - mertensError - (∑ p ∈ B, Real.log p / p) ≤
      ∑ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, Real.log p / p := by
  let S := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hm := (abs_le.mp (Mertens.prime_sum_bounded_error hx)).1
  have he := sum_inter_add_sum_sdiff S B (fun p : ℕ => Real.log p / p)
  have hB : (∑ p ∈ S ∩ B, Real.log p / p) ≤ ∑ p ∈ B, Real.log p / p := by
    apply sum_le_sum_of_subset_of_nonneg inter_subset_right
    intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  change Real.log x - mertensError - _ ≤ ∑ p ∈ S \ B, Real.log p / p
  change -mertensError ≤ (∑ p ∈ S, Real.log p / p) - Real.log x at hm
  linarith

end CCDN
