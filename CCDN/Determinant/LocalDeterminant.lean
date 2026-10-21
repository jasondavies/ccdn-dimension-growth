/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import all ArithmeticHeights.BombieriVaaler
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CCDN.Determinant.GramDeterminant

/-!
# Determinant divisibility from filtered factorizations

Cauchy–Binet turns a weighted factorization into a determinant valuation bound. The
univariate specialization gives the quadratic exponent `s*(s-1)/2` for polynomial
evaluations in one residue class. The passage from a curve's local ring to such a
factorization is proved in `FilteredDeterminant` in arbitrary ambient dimension.
`HypersurfaceResidue` supplies the sharp singular hypersurface bound.
-/

@[expose] public section

namespace CCDN

open Matrix

theorem pow_dvd_det_of_weighted_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (weight : Fin N → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j)
    (he : ∀ t : Fin s ↪o Fin N, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  classical
  rw [Matrix.det_mul_eq_sum_det_submatrix]
  apply Finset.dvd_sum
  intro S _
  let t := (S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S)
  have hminor := prod_row_factors_dvd_det (V.submatrix t id)
    (fun i => p ^ weight (t i)) (fun i j => hV (t i) j)
  rw [Finset.prod_pow_eq_pow_sum] at hminor
  exact dvd_mul_of_dvd_right ((pow_dvd_pow p (he t)).trans hminor) _

private theorem orderEmbedding_value_ge {s N : ℕ} (t : Fin s ↪o Fin N) (i : Fin s) :
    i.val ≤ (t i).val := by
  have hpoint : ∀ j : ℕ, ∀ hj : j < s, j ≤ (t ⟨j, hj⟩).val := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj
      have hj' : j < s := by omega
      have hprev := ih hj'
      have hlt := t.strictMono (show (⟨j, hj'⟩ : Fin s) < ⟨j + 1, hj⟩ from by
        change j < j + 1
        omega)
      change (t ⟨j, hj'⟩).val < (t ⟨j + 1, hj⟩).val at hlt
      omega
  exact hpoint i i.isLt

/-- The sequence of weights in which each nonnegative integer occurs `μ` times. -/
def multiplicityExponent (s μ : ℕ) : ℕ := ∑ i : Fin s, i.val / μ

theorem multiplicity_pow_dvd_det_of_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (μ : ℕ) (hV : ∀ i j, p ^ (i.val / μ) ∣ V i j) :
    p ^ multiplicityExponent s μ ∣ (U * V).det := by
  apply pow_dvd_det_of_weighted_factorization U V p (fun i => i.val / μ) _ hV
  intro t
  exact Finset.sum_le_sum fun i _ => Nat.div_le_div_right (orderEmbedding_value_ge t i)

/-- An explicit quadratic lower estimate for the repeated-weight exponent. -/
theorem multiplicityExponent_lower_bound (s μ : ℕ) (hμ : 0 < μ) :
    s ^ 2 ≤ 2 * μ * (multiplicityExponent s μ + s) := by
  have hi : ∀ i : Fin s, i.val ≤ μ * (i.val / μ) + (μ - 1) := by
    intro i
    have hmod := Nat.mod_lt i.val hμ
    have hdiv := Nat.mod_add_div i.val μ
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hid : (∑ i : Fin s, i.val) * 2 = s * (s - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id_mul_two]
  have hμsub : μ - 1 + 1 = μ := by omega
  have hs : s * (s - 1) + s = s ^ 2 := by
    cases s with
    | zero => simp
    | succ s => simp; ring
  unfold multiplicityExponent
  nlinarith

end CCDN
