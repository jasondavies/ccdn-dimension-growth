/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Grid avoidance using the degree in each coordinate separately. Unlike
the total-degree version, its side length does not grow with the number of
blocks or variables. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem coordinate_grid_vanishing_eq_zero_fin
    {K : Type*} [CommRing K] [IsDomain K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (S : Finset K)
    (hdeg : ∀ i, f.degreeOf i < S.card)
    (hzero : ∀ x : Fin n → K, (∀ i, x i ∈ S) → eval x f = 0) : f = 0 := by
  classical
  induction n with
  | zero =>
      have h := hzero (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      rw [eq_C_of_isEmpty f] at h ⊢
      simpa using h
  | succ n ih =>
      apply (finSuccEquiv K n).injective
      rw [map_zero]
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_zero]
      apply ih _
      · intro i
        exact (degreeOf_coeff_finSuccEquiv f i k).trans_lt (hdeg i.succ)
      · intro x hx
        let p := (finSuccEquiv K n f).map (eval x)
        have hp : p = 0 :=
          Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S
            (fun t ht => by
              rw [← eval_eq_eval_mv_eval']
              exact hzero (Fin.cons t x) (fun i => Fin.cases ht hx i))
            (Polynomial.natDegree_map_le.trans_lt
              (by simpa only [natDegree_finSuccEquiv] using hdeg 0))
        have hh := congrArg (fun q : Polynomial K => q.coeff k) hp
        simpa only [p, Polynomial.coeff_map, Polynomial.coeff_zero] using hh

theorem coordinate_grid_vanishing_eq_zero
    {K σ : Type*} [CommRing K] [IsDomain K] [Fintype σ]
    (f : MvPolynomial σ K) (S : Finset K)
    (hdeg : ∀ i, f.degreeOf i < S.card)
    (hzero : ∀ x : σ → K, (∀ i, x i ∈ S) → eval x f = 0) : f = 0 := by
  let e := Fintype.equivFin σ
  apply (rename_injective e e.injective)
  rw [map_zero]
  apply coordinate_grid_vanishing_eq_zero_fin (rename e f) S
  · intro i
    have hh := degreeOf_rename_of_injective (p := f) e.injective (e.symm i)
    have he : (rename e f).degreeOf i = f.degreeOf (e.symm i) := by
      simpa only [e.apply_symm_apply] using hh
    rw [he]
    exact hdeg _
  · intro x hx
    rw [eval_rename]
    exact hzero (x ∘ e) (fun i => hx (e i))

/-- A rational polynomial with coordinate degrees at most D has a nonzero
value on the integer grid {0,...,D}, in any finite number of variables. -/
theorem exists_integer_grid_eval_ne_zero_of_degreeOf
    {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℚ) (hf : f ≠ 0)
    (D : ℕ) (hdeg : ∀ i, f.degreeOf i ≤ D) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ D) ∧
      eval (fun i => (v i : ℚ)) f ≠ 0 := by
  classical
  by_contra! hn
  let S : Finset ℚ := (Finset.range (D + 1)).image Nat.cast
  have hS : S.card = D + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  apply hf
  apply coordinate_grid_vanishing_eq_zero f S (fun i => by
    rw [hS]
    exact Nat.lt_succ_of_le (hdeg i))
  intro x hx
  have hpre (i : σ) : ∃ a : ℕ, a ≤ D ∧ (a : ℚ) = x i := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hx i)
    exact ⟨a, by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha, he⟩
  choose a ha he using hpre
  have hh := hn (fun i => (a i : ℤ)) (fun i =>
    ⟨Int.natCast_nonneg _, by exact_mod_cast ha i⟩)
  simpa only [Int.cast_natCast, he] using hh

end
end CCDN
