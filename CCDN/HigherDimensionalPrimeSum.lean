module

public import CCDN.PrimeCutoff

/-! Simultaneous prime divisibility with arbitrary main and error coefficients.
This retains the higher-dimensional local exponent, including its exact rank power. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

lemma log_lower_of_general_local_exponents (P : Finset ℕ) (e : ℕ → ℕ)
    (mass : ℕ → ℝ) (A E : ℝ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime)
    (he : ∀ p ∈ P, A / mass p - E ≤ e p)
    (hdiv : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D) :
    A * (∑ p ∈ P, Real.log p / mass p) - E * (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (A / mass p - E) * Real.log p ≤ (e p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_right (he p hp) (Real.log_natCast_nonneg p)
  have hsum := sum_le_sum hpoint
  have hlog := sum_log_prime_powers_le_log P e hD hP hdiv
  have hidentity : (∑ p ∈ P, (A / mass p - E) * Real.log p) =
      A * (∑ p ∈ P, Real.log p / mass p) - E * (∑ p ∈ P, Real.log p) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [hidentity] at hsum
  exact hsum.trans hlog

/-- A lower cutoff costs log(L); perturbing p by C sqrt(p) costs O(C/sqrt(L)).
All selected prime-power divisors are multiplied into the actual integer D. -/
theorem general_determinant_log_lower_cutoff {x L C A E : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (B : Finset ℕ) (mass : ℕ → ℝ) (e : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      mass p ≤ p + C * Real.sqrt p)
    (he : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      A / mass p - E ≤ e p)
    (hdiv : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      (p : ℤ) ^ e p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) - C * (2 * primeBlockMass / Real.sqrt L)) -
      E * ((Real.log 4 + 4) * x) ≤ Real.log D := by
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B).filter (fun p : ℕ => L < (p : ℝ))
  have hp (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have hbase := log_lower_of_general_local_exponents S e mass A E hD hp
    (fun p hp => he p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
    (fun p hp => hdiv p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
  have hm := weighted_prime_sum_lower_cutoff hx hL hC B mass hmass hupper
  have htheta : (∑ p ∈ S, Real.log p) ≤ (Real.log 4 + 4) * x := by
    calc
      _ ≤ Chebyshev.theta x := by
        apply sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans sdiff_subset)
        intro p _ _
        exact Real.log_natCast_nonneg p
      _ ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm hA
  have ht' := mul_le_mul_of_nonneg_left htheta hE
  linarith

end
end CCDN
