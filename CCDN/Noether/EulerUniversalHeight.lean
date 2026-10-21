/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerSparseMatrix
public import CCDN.ForMathlib.IntegerPolynomialL1
/-! The sharp printed coefficient-sum bound for the plane Noether minors:
each entry has l1 norm at most d, hence the order d²−1 determinant has
l1 norm at most d^(3d²−3). -/

@[expose] public section
namespace CCDN
noncomputable section

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

end
end CCDN
