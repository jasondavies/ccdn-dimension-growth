module

public import CCDN.IntegerHilbertElimination
public import CCDN.IntegerLinearForms
public import CCDN.FilteredHilbertEquiv

/-! One bounded integer-matrix elimination step on the standard Fin-indexed
polynomial rings, ready for iteration. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def finEliminationMatrix {n : ℕ} (b : Option (Fin n) → ℤ) :
    Fin n → Fin (n + 1) → ℤ :=
  fun i => Fin.cases (-b (some i)) (fun j => if j = i then b none else 0)

lemma integerLinearForm_finEliminationMatrix {n : ℕ}
    (b : Option (Fin n) → ℤ) (i : Fin n) :
    integerLinearForm (finEliminationMatrix b i) =
      C (b none : ℚ) * X i.succ - C (b (some i) : ℚ) * X 0 := by
  rw [integerLinearForm, Fin.sum_univ_succ]
  simp [finEliminationMatrix, apply_ite, ite_mul, sub_eq_add_neg, add_comm]

lemma finEliminationMatrix_height {n d : ℕ} (b : Option (Fin n) → ℤ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d + 1) (i : Fin n) (j : Fin (n + 1)) :
    |finEliminationMatrix b i j| ≤ d + 1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [finEliminationMatrix, Fin.cases_zero, abs_neg,
      abs_of_nonneg (hb (some i)).1] using (hb (some i)).2
  · by_cases he : j = i
    · simpa only [finEliminationMatrix, Fin.cases_succ, he, ite_true,
        abs_of_nonneg (hb none).1] using (hb none).2
    · simp only [finEliminationMatrix, Fin.cases_succ, ite_eq_right he, abs_zero]
      positivity

end
end CCDN
