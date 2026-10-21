/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Finiteness.Ideal

/-! A polynomial ideal whose only possible geometric zero is the origin
contains a positive power of the irrelevant ideal. This is the concrete
Nullstellensatz certificate for an empty projective fiber. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_positive_irrelevant_power_le_of_zero_locus_subset_origin
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (J : Ideal (MvPolynomial σ K))
    (hzero : ∀ x ∈ MvPolynomial.zeroLocus K J, x = 0) :
    ∃ M : ℕ, 0 < M ∧ (idealOfVars σ K) ^ M ≤ J := by
  have hrad : idealOfVars σ K ≤ J.radical := by
    rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    rw [hzero x hx, aeval_X]
    rfl
  obtain ⟨M, hM⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ K)
  exact ⟨M + 1, Nat.succ_pos M, (Ideal.pow_le_pow_right (Nat.le_succ M)).trans hM⟩

end
end CCDN
