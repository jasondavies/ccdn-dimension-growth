module

public import CCDN.EulerSparseMatrix
public import CCDN.IntegerPolynomialL1

/-! The sharp printed coefficient-sum bound for the plane Noether minors:
each entry has l1 norm at most d, hence the order d²−1 determinant has
l1 norm at most d^(3d²−3). -/

@[expose] public section
namespace CCDN
noncomputable section

theorem universalEulerMatrix_coefficientL1_le (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    coefficientL1 (universalEulerMatrix k row col) ≤ k + 2 := by
  obtain hz | ⟨i, c, hc, he⟩ := universalEulerMatrix_sparse k row col
  · rw [hz, coefficientL1_zero]
    omega
  · rw [he, coefficientL1_C_mul_X]
    have hh : (c.natAbs : ℤ) ≤ ((k + 2 : ℕ) : ℤ) := by simpa only [Int.natCast_natAbs] using hc
    exact_mod_cast hh

lemma factorial_mul_degree_pow_le (d r : ℕ) (hr : r ≤ d ^ 2) :
    r.factorial * d ^ r ≤ d ^ (3 * r) := by
  calc
    r.factorial * d ^ r ≤ r ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
    _ ≤ (d ^ 2) ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr r)
    _ = d ^ (3 * r) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- The integer coefficient forms have the exact coefficient-sum
bound in the plane case, with no unspecified constant. -/
theorem universalEulerMinor_coefficientL1_le (k : ℕ)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    coefficientL1 (universalEulerMinor k rows cols) ≤
      (k + 2) ^ (3 * (k + 2) ^ 2 - 3) := by
  have hh := coefficientL1_det_le
    ((universalEulerMatrix k).submatrix rows cols) (k + 2)
    (fun i j => universalEulerMatrix_coefficientL1_le k (rows i) (cols j))
  rw [Fintype.card_fin] at hh
  have hfin := factorial_mul_degree_pow_le (k + 2) ((k + 2) ^ 2 - 1) (by omega)
  have he : 3 * ((k + 2) ^ 2 - 1) = 3 * (k + 2) ^ 2 - 3 := by omega
  rw [he] at hfin
  exact hh.trans hfin

end
end CCDN
