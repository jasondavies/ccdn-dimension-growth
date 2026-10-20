module

public import CCDN.ChowRowSymmetry

/-! Total degree is the sum of the hyperplane block degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma sum_chow_row_weight {r s : ℕ} (e : (Fin r × Fin s) →₀ ℕ) :
    ∑ i, Finsupp.weight (chowRowWeight i) e = e.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp [chowRowWeight]

theorem chow_rows_homogeneous_total_degree
    {K : Type*} [CommRing K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (δ : Fin r → ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) :
    F.IsHomogeneous (∑ i, δ i) := by
  intro e he
  have hw : Finsupp.weight (1 : Fin r × Fin s → ℕ) e = e.degree := by
    simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
  rw [hw, ← sum_chow_row_weight e]
  exact Finset.sum_congr rfl (fun i _ => hδ i he)

theorem chow_uniform_row_degree_totalDegree
    {K : Type*} [CommRing K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (hF : F ≠ 0) (d : ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) :
    F.totalDegree = r * d := by
  have hh := chow_rows_homogeneous_total_degree F (fun _ => d) hδ
  simpa using hh.totalDegree hF

end
end CCDN
