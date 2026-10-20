module

public import CCDN.PrimeCutoff

/-! CCDN Lemmas 3.2.4 and 3.2.5: the stated Chebyshev constant and the
convergent infinite prime tail, for every positive real cutoff. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

/-- CCDN Lemma 3.2.4, including its explicit constant 2. -/
theorem prime_log_sum_le_two_mul {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p) ≤ 2 * x := by
  have h := Chebyshev.theta_le_log4_mul_x hx
  have hl : Real.log 4 ≤ 2 := by
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hl hx)

/-- The finite-subset prime tail bound holds for every positive cutoff. -/
theorem prime_sqrt_tail_le_positive {L : ℝ} (hL : 0 < L) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ)) :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
  by_cases hL1 : 1 ≤ L
  · exact prime_sqrt_tail_le hL1 S hprime hlo
  have h := prime_sqrt_tail_le (L := 1) le_rfl S hprime
    (fun p hp => by exact_mod_cast (hprime p hp).one_lt)
  have hs : Real.sqrt L ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (le_of_not_ge hL1)
  apply h.trans
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) primeBlockMass_pos.le)
    (Real.sqrt_pos.mpr hL) hs

/-- The unrestricted infinite-series version of CCDN Lemma 3.2.5, with
an explicit bound 2*primeBlockMass/sqrt(L). -/
theorem prime_sqrt_tail_summable_and_bound {L : ℝ} (hL : 0 < L) :
    Summable (fun p : ℕ => if p.Prime ∧ L < (p : ℝ) then Real.log p / p / Real.sqrt p else 0) ∧
    (∑' p : ℕ, if p.Prime ∧ L < (p : ℝ) then Real.log p / p / Real.sqrt p else 0) ≤
      2 * primeBlockMass / Real.sqrt L := by
  classical
  have hnonneg : 0 ≤ (fun p : ℕ => if p.Prime ∧ L < (p : ℝ) then Real.log p / p / Real.sqrt p else 0) := by
    intro p
    change 0 ≤ if p.Prime ∧ L < (p : ℝ) then Real.log p / p / Real.sqrt p else 0
    split_ifs <;> positivity
  have hsum (S : Finset ℕ) :
      (∑ p ∈ S, if p.Prime ∧ L < (p : ℝ) then Real.log p / p / Real.sqrt p else 0) ≤
        2 * primeBlockMass / Real.sqrt L := by
    rw [← sum_filter]
    exact prime_sqrt_tail_le_positive hL _ (fun p hp => (mem_filter.mp hp).2.1)
      (fun p hp => (mem_filter.mp hp).2.2)
  exact ⟨summable_of_sum_le hnonneg hsum, Real.tsum_le_of_sum_le hnonneg hsum⟩

end
end CCDN
