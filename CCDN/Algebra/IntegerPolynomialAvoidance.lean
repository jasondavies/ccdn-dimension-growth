/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.ENatToNat
import Mathlib.NumberTheory.Chebyshev
import ArithmeticHeights.Absolute
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Ring.Star
/-! A nonzero integer polynomial of total degree at most A has a nonzero
value at an integer point with every coordinate between 0 and A. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_integer_grid_eval_ne_zero_fin {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : Fin n → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧ eval v f ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  let S := Finset.Icc (0 : ℤ) (A : ℤ)
  have hS : S.card = A + 1 := by simp [S, Int.card_Icc]
  have he : (Fintype.piFinset fun _ : Fin n => S).filter (fun v => eval v f = 0) =
      Fintype.piFinset (fun _ : Fin n => S) := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    apply hn v
    intro i
    exact Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hv) i)
  have h := schwartz_zippel_totalDegree hf S
  rw [he] at h
  have hR : (1 : ℚ) ≤ (f.totalDegree : ℚ) / (A + 1) := by
    simpa [hS] using (NNRat.cast_le (K := ℚ)).mpr h
  have ha : (0 : ℚ) < A + 1 := by positivity
  have hh := (le_div_iff₀ ha).mp hR
  have hdR : (f.totalDegree : ℚ) ≤ A := by exact_mod_cast hd
  linarith

/-- The bound is independent of the number and names of the coordinates. -/
theorem exists_integer_grid_eval_ne_zero {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧ eval v f ≠ 0 := by
  let e := Fintype.equivFin σ
  let g := rename e f
  have hg : g ≠ 0 := (map_ne_zero_iff _ (rename_injective e e.injective)).mpr hf
  obtain ⟨v, hv, he⟩ := exists_integer_grid_eval_ne_zero_fin g hg A
    ((totalDegree_rename_le e f).trans hd)
  refine ⟨v ∘ e, fun i => hv (e i), ?_⟩
  simpa only [g, eval_rename] using he

end
end CCDN
