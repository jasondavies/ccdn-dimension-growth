module

public import CCDN.HigherDimensionalPrimeSum

/-! Adding prescribed congruence primes to the global determinant estimate.
The two disjoint collections of actual prime-power divisors are multiplied
before taking logarithms. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

lemma sum_log_disjoint_prime_powers_le_log (P Q : Finset ℕ)
    (hPQ : Disjoint P Q) (e v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hdivP : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D)
    (hdivQ : ∀ p ∈ Q, (p : ℤ) ^ v p ∣ D) :
    (∑ p ∈ P, (e p : ℝ) * Real.log p) +
      (∑ p ∈ Q, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  let w : ℕ → ℕ := fun p => if p ∈ P then e p else v p
  have hw (p : ℕ) (hp : p ∈ P ∪ Q) : (p : ℤ) ^ w p ∣ D := by
    by_cases h : p ∈ P
    · simpa only [w, ite_eq_left h] using hdivP p h
    · simpa only [w, ite_eq_right h] using hdivQ p ((mem_union.mp hp).resolve_left h)
  have hh := sum_log_prime_powers_le_log (P ∪ Q) w hD
    (fun p hp => (mem_union.mp hp).elim (hP p) (hQ p)) hw
  rw [sum_union hPQ] at hh
  have h₁ : (∑ p ∈ P, (w p : ℝ) * Real.log p) =
      ∑ p ∈ P, (e p : ℝ) * Real.log p := by
    apply sum_congr rfl
    intro p hp
    simp only [w, ite_eq_left hp]
  have h₂ : (∑ p ∈ Q, (w p : ℝ) * Real.log p) =
      ∑ p ∈ Q, (v p : ℝ) * Real.log p := by
    apply sum_congr rfl
    intro p hp
    have hn : p ∉ P := fun h => (disjoint_left.mp hPQ) h hp
    simp only [w, ite_eq_right hn]
  rwa [h₁, h₂] at hh

/-- Prescribed primes excluded from the global sum contribute their entire
local valuation, in addition to the global lower bound. -/
theorem general_determinant_log_lower_cutoff_congruence {x L C A E : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (mass : ℕ → ℝ) (e v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      mass p ≤ p + C * Real.sqrt p)
    (he : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      A / mass p - E ≤ e p)
    (hdiv : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      (p : ℤ) ^ e p ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ bad, Real.log p / p) - C * (2 * primeBlockMass / Real.sqrt L)) -
      E * ((Real.log 4 + 4) * x) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad).filter (fun p : ℕ => L < (p : ℝ))
  have hp (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have hSP : Disjoint S P := by
    apply disjoint_left.mpr
    intro p hpS hpP
    exact (mem_sdiff.mp (mem_filter.mp hpS).1).2 (hPbad hpP)
  have hsum := sum_log_disjoint_prime_powers_le_log S P hSP e v hD hp hP
    (fun p hp => hdiv p (mem_filter.mp hp).1 (mem_filter.mp hp).2) hcong
  have hlocal : A * (∑ p ∈ S, Real.log p / mass p) - E * (∑ p ∈ S, Real.log p) ≤
      ∑ p ∈ S, (e p : ℝ) * Real.log p := by
    calc
      _ = ∑ p ∈ S, (A / mass p - E) * Real.log p := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro p _
        ring
      _ ≤ _ := sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
        (he p (mem_filter.mp hp).1 (mem_filter.mp hp).2) (Real.log_natCast_nonneg p)
  have hm := weighted_prime_sum_lower_cutoff hx hL hC bad mass hmass hupper
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
