/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Basic.Real.Basic
/-! The maximum absolute coefficient height of an integer polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def integerCoefficientHeight {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natAbs)

lemma coefficient_abs_le_integerCoefficientHeight {σ : Type*}
    (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ (integerCoefficientHeight f : ℝ) := by
  have hh : (f.coeff m).natAbs ≤ integerCoefficientHeight f := by
    by_cases hm : m ∈ f.support
    · exact Finset.le_sup (f := fun m => (f.coeff m).natAbs) hm
    · simp [notMem_support_iff.mp hm]
  simpa only [Nat.cast_natAbs, Int.cast_abs] using (show ((f.coeff m).natAbs : ℝ) ≤ integerCoefficientHeight f by exact_mod_cast hh)

lemma integerCoefficientHeight_le {σ : Type*} (f : MvPolynomial σ ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hc : ∀ m, |(f.coeff m : ℝ)| ≤ H) :
    (integerCoefficientHeight f : ℝ) ≤ H := by
  classical
  by_cases hf : f.support.Nonempty
  · obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup f.support hf (fun m => (f.coeff m).natAbs)
    unfold integerCoefficientHeight
    rw [hm]
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc m
  · have he : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    simpa [integerCoefficientHeight, he] using hH

lemma integerCoefficientHeight_pos {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) :
    0 < integerCoefficientHeight f := by
  obtain ⟨m, hne⟩ := MvPolynomial.exists_coeff_ne_zero hf
  exact (Int.natAbs_pos.mpr hne).trans_le
    (Finset.le_sup (f := fun m => (f.coeff m).natAbs) (mem_support_iff.mpr hne))

end
end CCDN
