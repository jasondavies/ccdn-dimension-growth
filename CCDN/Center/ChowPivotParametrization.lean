module

public import CCDN.Center.ChowIncidenceLocus
/-! A denominator-free parametrization of hyperplane tuples through a
cone point, using an arbitrary nonzero pivot coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def chowPivotCoefficients {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K)
    (v : Fin r × Fin (n + 1) → K) : Fin r × Fin (n + 1) → K :=
  fun q => if q.2 = j then -(∑ k ∈ Finset.univ.erase j, v (q.1,k) * x k)
    else v q * x j

def chowPivotPolynomials {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K) :
    Fin r × Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  fun q => if q.2 = j then -(∑ k ∈ Finset.univ.erase j, C (v (q.1,k)) * X k)
    else C (v q) * X j

lemma chowPivotPolynomials_eval {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K)
    (x : Fin (n + 1) → K) (q : Fin r × Fin (n + 1)) :
    eval x (chowPivotPolynomials j v q) = chowPivotCoefficients j x v q := by
  simp only [chowPivotPolynomials, chowPivotCoefficients]
  split_ifs <;> simp

lemma chowPivotCoefficients_relation {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K)
    (v : Fin r × Fin (n + 1) → K) (i : Fin r) :
    ∑ k, chowPivotCoefficients j x v (i,k) * x k = 0 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ k ∈ Finset.univ.erase j, chowPivotCoefficients j x v (i,k) * x k) =
      (∑ k ∈ Finset.univ.erase j, v (i,k) * x k) * x j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [chowPivotCoefficients, ite_eq_right (Finset.mem_erase.mp hk).1]
    ring
  rw [he, chowPivotCoefficients, ite_eq_left rfl]
  ring

lemma chowPivotCoefficients_reconstruct {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K) (hx : x j ≠ 0)
    (U : Fin r × Fin (n + 1) → K)
    (hU : ∀ i, ∑ k, U (i,k) * x k = 0) :
    chowPivotCoefficients j x (fun q => U q / x j) = U := by
  classical
  funext q
  rcases q with ⟨i,k⟩
  by_cases hk : k = j
  · subst k
    rw [chowPivotCoefficients, ite_eq_left rfl]
    apply mul_right_cancel₀ hx
    have he : (∑ k ∈ Finset.univ.erase j, U (i,k) / x j * x k) * x j =
        ∑ k ∈ Finset.univ.erase j, U (i,k) * x k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    rw [neg_mul, he]
    have hh := hU i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hh
    exact (eq_neg_of_add_eq_zero_right hh).symm
  · rw [chowPivotCoefficients, ite_eq_right hk, div_mul_cancel₀ _ hx]

end
end CCDN
