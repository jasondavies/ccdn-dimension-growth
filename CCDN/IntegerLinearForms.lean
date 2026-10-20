module

public import CCDN.LinearProjectionFiltration

/-! Integer matrices give linear forms. Composition is matrix
multiplication, with an explicit coefficient-height bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def integerLinearForm {σ : Type*} [Fintype σ] (a : σ → ℤ) : MvPolynomial σ ℚ :=
  ∑ i, C (a i : ℚ) * X i

lemma integerLinearForm_degree {σ : Type*} [Fintype σ] (a : σ → ℤ) :
    (integerLinearForm a).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, totalDegree_X]

lemma integerLinearForm_identity {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    integerLinearForm (fun j => if j = i then 1 else 0) = X i := by
  simp [integerLinearForm]

lemma integerLinearForm_comp {σ τ : Type*} [Fintype σ] [Fintype τ]
    (a : σ → ℤ) (b : σ → τ → ℤ) :
    aeval (fun i => integerLinearForm (b i)) (integerLinearForm a) =
      integerLinearForm (fun j => ∑ i, a i * b i j) := by
  simp only [integerLinearForm, map_sum, map_mul, aeval_C, aeval_X,
    Finset.mul_sum, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [algebraMap_eq, mul_assoc]

lemma integerLinearForm_matrix_height {σ τ : Type*} [Fintype σ]
    (a : σ → ℤ) (b : σ → τ → ℤ) (H T : ℕ)
    (ha : ∀ i, |a i| ≤ H) (hb : ∀ i j, |b i j| ≤ T) (j : τ) :
    |∑ i, a i * b i j| ≤ Fintype.card σ * H * T := by
  calc
    _ ≤ ∑ i, |a i * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (H : ℤ) * T := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (hb i j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [mul_assoc]

end
end CCDN
