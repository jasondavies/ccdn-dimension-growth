/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.FiltrationWeights
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat

/-! Infinite monotone enumerations of positive integer profiles.
These supplement the finite initial-segment construction and identify the
exact length and weight sum of every complete block. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- Every profile `g` of positive integers has an infinite monotone enumeration: a monotone sequence
`a` taking each value `k` exactly `g k` times, with `a i ≤ k` exactly for the first
`weightProfileCumulative g k` indices `i`. -/
theorem exists_positive_profile_enumeration (g : ℕ → ℕ) (hg : ∀ k, 0 < g k) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ k, {i | a i = k}.Finite) ∧
      (∀ k, {i | a i = k}.ncard = g k) ∧
      (∀ i k, a i ≤ k ↔ i < weightProfileCumulative g k) := by
  classical
  have hcap (i : ℕ) : i < weightProfileCumulative g i := by
    have h := sum_le_sum (s := range (i + 1)) (f := fun _ => 1)
      (g := g) (fun k _ => hg k)
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at h
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
  have hex (i : ℕ) : ∃ k, i < weightProfileCumulative g k := ⟨i, hcap i⟩
  let a (i : ℕ) := Nat.find (hex i)
  have ha (i k : ℕ) : a i ≤ k ↔ i < weightProfileCumulative g k := by
    constructor
    · intro h
      exact (Nat.find_spec (hex i)).trans_le (weightProfileCumulative_mono g h)
    · exact fun h => Nat.find_le h
  have hfiber (k : ℕ) :
      {i | a i = k} = Set.Ico (∑ j ∈ range k, g j) (weightProfileCumulative g k) := by
    ext i
    cases k with
    | zero =>
      simp only [range_zero, sum_empty, Set.mem_ofPred_eq, Set.mem_Ico,
        Nat.zero_le, true_and, ← Nat.le_zero]
      exact ha i 0
    | succ k =>
      change a i = k + 1 ↔ weightProfileCumulative g k ≤ i ∧
        i < weightProfileCumulative g (k + 1)
      have h0 := ha i k
      have h1 := ha i (k + 1)
      omega
  refine ⟨a, ?_, ?_, ?_, ha⟩
  · intro i j hij
    apply (ha i (a j)).mpr
    exact hij.trans_lt (Nat.find_spec (hex j))
  · intro k
    rw [hfiber]
    exact Set.finite_Ico _ _
  · intro k
    rw [hfiber, Set.ncard_Ico_nat]
    simp only [weightProfileCumulative, sum_range_succ, Nat.add_sub_cancel_left]

/-- Ending at a complete layer gives the exact sum of its multiplicities
times their weights, for the infinite enumeration. -/
theorem enumeration_full_block_sum (g a : ℕ → ℕ)
    (hfinite : ∀ k, {i | a i = k}.Finite)
    (hcount : ∀ k, {i | a i = k}.ncard = g k)
    (ha : ∀ i k, a i ≤ k ↔ i < weightProfileCumulative g k) (K : ℕ) :
    (∑ i ∈ range (weightProfileCumulative g K), a i) =
      ∑ k ∈ range (K + 1), k * g k := by
  classical
  have hmaps (i : ℕ) (hi : i ∈ range (weightProfileCumulative g K)) :
      a i ∈ range (K + 1) := by
    simpa only [mem_range, Nat.lt_succ_iff] using (ha i K).mpr (mem_range.mp hi)
  rw [← sum_fiberwise_of_maps_to' hmaps (fun k : ℕ => k)]
  apply sum_congr rfl
  intro k hk
  have he : (range (weightProfileCumulative g K)).filter (fun i => a i = k) =
      (hfinite k).toFinset := by
    ext i
    simp only [mem_filter, mem_range, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(ha i K).mp (by rw [h]; exact Nat.le_of_lt_succ (mem_range.mp hk)), h⟩
  rw [sum_const, he, ← Set.ncard_eq_toFinset_card _ (hfinite k), hcount]
  exact Nat.mul_comm _ _

end
end CCDN
