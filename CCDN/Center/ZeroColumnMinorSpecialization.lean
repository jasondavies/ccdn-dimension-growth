/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.ForMathlib.MvPolynomial
import CCDN.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import CCDN.Height.ProjectiveZeroLocus

/-!
Sharp bounded specialization of maximal-minor conditions while keeping
prescribed matrix columns equal to zero. The distinguished zero column is
the center-at-infinity case in Section 5.3. The nonvanishing rational
witness is an explicit hypothesis.

The sharp numerical specialization in CCDN Lemma 5.3. A
nonvanishing homogeneous condition on Plücker coordinates has a full-rank
integer witness with entries at most max(1, deg F), without a factor from
the number of rows. Every maximal minor has the stated factorial height
bound. The construction of the geometric bad-center polynomial is separate.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private theorem homogeneous_minor_nonvanishing_implies_independent
    {r n : ℕ} (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree) (hdeg : 0 < F.totalDegree)
    (A : Matrix (Fin r) (Fin n) ℚ)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    LinearIndependent ℚ A.row := by
  classical
  by_contra hli
  have hz (c : Fin r ↪ Fin n) : (A.submatrix id c).det = 0 := by
    by_contra hd
    apply hli
    apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ c)
    exact Matrix.linearIndependent_rows_of_det_ne_zero hd
  apply hF
  have he : (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) = fun _ => 0 := funext hz
  rw [he]
  change eval (0 : (Fin r ↪ Fin n) → ℚ) F = 0
  simpa only [zero_smul, zero_pow hdeg.ne', zero_mul] using
    homogeneous_eval_smul hhom (0 : ℚ) (fun _ => 0)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Universal maximal minor on matrices with the specified columns zero. -/
private def zeroColumnUniversalMinor {r n : ℕ} (Z : Finset (Fin n))
    (c : Fin r ↪ Fin n) : MvPolynomial (Fin r × Fin n) ℚ :=
  (Matrix.of fun i j : Fin r => if c j ∈ Z then 0 else X (i, c j)).det

private lemma zeroColumnUniversalMinor_eval {r n : ℕ} (Z : Finset (Fin n))
    (c : Fin r ↪ Fin n) (A : Matrix (Fin r) (Fin n) ℚ) :
    eval (fun p => A p.1 p.2) (zeroColumnUniversalMinor Z c) =
      ((Matrix.of fun i j => if j ∈ Z then 0 else A i j).submatrix id c).det := by
  classical
  rw [zeroColumnUniversalMinor, RingHom.map_det]
  congr 1
  ext i j
  change eval (fun p => A p.1 p.2) (if c j ∈ Z then 0 else X (i, c j)) =
    if c j ∈ Z then 0 else A i (c j)
  by_cases hz : c j ∈ Z <;> simp [hz]

private lemma eval_zero_column_minor_substitution {r n : ℕ} (Z : Finset (Fin n))
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ) (A : Matrix (Fin r) (Fin n) ℚ) :
    eval (fun p => A p.1 p.2) (aeval (zeroColumnUniversalMinor Z) F) =
      eval (fun c : Fin r ↪ Fin n =>
        ((Matrix.of fun i j => if j ∈ Z then 0 else A i j).submatrix id c).det) F := by
  have hh : (aeval (fun p => A p.1 p.2)).comp (aeval (zeroColumnUniversalMinor Z)) =
      aeval (fun c : Fin r ↪ Fin n =>
        ((Matrix.of fun i j => if j ∈ Z then 0 else A i j).submatrix id c).det) := by
    ext c
    simp only [AlgHom.comp_apply, aeval_X]
    exact zeroColumnUniversalMinor_eval Z c A
  exact congrArg (fun φ => φ F) hh

private lemma zeroColumnUniversalMinor_degreeOf {r n : ℕ} (Z : Finset (Fin n))
    (c : Fin r ↪ Fin n) (p : Fin r × Fin n) :
    (zeroColumnUniversalMinor Z c).degreeOf p ≤ 1 := by
  classical
  rw [zeroColumnUniversalMinor, Matrix.det_apply']
  apply (degreeOf_sum_le p _ _).trans
  apply Finset.sup_le
  intro σ _
  have hcast : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin r × Fin n) ℚ)) =
      C ((Equiv.Perm.sign σ : ℤ) : ℚ) := by simp
  rw [hcast]
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le p _ _).trans
  calc
    _ ≤ ∑ j : Fin r, if σ j = p.1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Matrix.of_apply]
      by_cases hz : c j ∈ Z
      · simp only [hz, ite_true, degreeOf_zero]
        positivity
      · simp only [hz, ite_false]
        by_cases hrow : σ j = p.1
        · simp only [hrow, ite_true, degreeOf_X]
          split_ifs <;> omega
        · have hp : p ≠ (σ j, c j) := by
            intro he
            exact hrow (congrArg Prod.fst he).symm
          simp only [hrow, ite_false, degreeOf_X_of_ne hp]
          exact le_rfl
    _ = 1 := by simp only [← σ.eq_symm_apply]; simp

private lemma zero_column_minor_substitution_degreeOf_le {r n : ℕ} (Z : Finset (Fin n))
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ) (p : Fin r × Fin n) :
    (aeval (zeroColumnUniversalMinor Z) F).degreeOf p ≤ F.totalDegree := by
  simpa only [one_mul] using MvPolynomial.degreeOf_aeval_le (zeroColumnUniversalMinor Z) p 1
    (fun c => zeroColumnUniversalMinor_degreeOf Z c p) F

/-- Constant case of the zero-column specialization: a nonzero maximal minor of `A` avoids the
zero columns, and the corresponding `0/1` selection matrix specializes it. -/
private theorem exists_integer_minor_specialization_zero_columns_of_totalDegree_eq_zero {r n : ℕ}
    (Z : Finset (Fin n)) (F : MvPolynomial (Fin r ↪ Fin n) ℚ) (hdeg : F.totalDegree = 0)
    (A : Matrix (Fin r) (Fin n) ℚ) (hli : LinearIndependent ℚ A.row)
    (hzero : ∀ i j, j ∈ Z → A i j = 0)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      (∀ i j, j ∈ Z → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 := by
  classical
  obtain ⟨c, hc, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row A hli
  have hcZ (i : Fin r) : c i ∉ Z := by
    intro hz
    apply hdet
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro j
    exact hzero j (c i) hz
  let M : Matrix (Fin r) (Fin n) ℤ := fun i j => if c i = j then 1 else 0
  have hm : (M.map (Int.castRingHom ℚ)).submatrix id c = 1 := by
    ext i j
    change (((if c i = c j then 1 else 0) : ℤ) : ℚ) = if i = j then 1 else 0
    simp only [hc.eq_iff]
    split_ifs <;> simp
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [M, hdeg]
    split_ifs <;> norm_num
  · intro i j hj
    have hne : c i ≠ j := by intro he; exact hcZ i (he.symm ▸ hj)
    simp only [M, hne, ite_false]
  · apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ c)
    have hd : ((M.map (Int.castRingHom ℚ)).submatrix id c).det ≠ 0 := by
      rw [hm, Matrix.det_one]
      exact one_ne_zero
    exact Matrix.linearIndependent_rows_of_det_ne_zero hd
  · have hconst := totalDegree_eq_zero_iff_eq_C.mp hdeg
    rw [hconst] at hF ⊢
    simpa only [eval_C] using hF

/-- Positive-degree case of the zero-column specialization: the minor substitution of `F`,
restricted to matrices with the prescribed zero columns, is nonzero, so it has a nonvanishing
integer point of the degree grid. -/
private theorem exists_integer_minor_specialization_zero_columns_of_totalDegree_ne_zero {r n : ℕ}
    (Z : Finset (Fin n)) (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree) (hdeg : F.totalDegree ≠ 0)
    (A : Matrix (Fin r) (Fin n) ℚ) (hzero : ∀ i j, j ∈ Z → A i j = 0)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      (∀ i j, j ∈ Z → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 := by
  classical
  let U := aeval (zeroColumnUniversalMinor Z) F
  have hU : U ≠ 0 := by
    intro hz
    apply hF
    have hAz : (Matrix.of fun i j => if j ∈ Z then 0 else A i j) = A := by
      ext i j
      by_cases hj : j ∈ Z
      · simp only [Matrix.of_apply, hj, ite_true, hzero i j hj]
      · simp only [Matrix.of_apply, hj, ite_false]
    rw [← hAz, ← eval_zero_column_minor_substitution]
    change eval (fun p => A p.1 p.2) U = 0
    rw [hz, map_zero]
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero_of_degreeOf U hU
    F.totalDegree (zero_column_minor_substitution_degreeOf_le Z F)
  let M : Matrix (Fin r) (Fin n) ℤ := Matrix.of fun i j => if j ∈ Z then 0 else v (i, j)
  have hvalue' : eval (fun c : Fin r ↪ Fin n =>
      ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 := by
    have he : M.map (Int.castRingHom ℚ) =
        (Matrix.of fun i j => if j ∈ Z then 0 else (v (i, j) : ℚ)) := by
      ext i j
      change ((if j ∈ Z then 0 else v (i, j) : ℤ) : ℚ) = _
      simp only [Matrix.of_apply]
      split_ifs <;> simp
    have heval := eval_zero_column_minor_substitution Z F
      (Matrix.of fun i j => (v (i, j) : ℚ))
    simp only [Matrix.of_apply] at heval
    rw [he, ← heval]
    exact hvalue
  refine ⟨M, ?_, ?_, homogeneous_minor_nonvanishing_implies_independent F hhom
    (Nat.pos_of_ne_zero hdeg) _ hvalue', hvalue'⟩
  · intro i j
    by_cases hj : j ∈ Z
    · simp only [M, Matrix.of_apply, hj, ite_true]
      constructor <;> positivity
    · simp only [M, Matrix.of_apply, hj, ite_false]
      exact ⟨(hv (i, j)).1, (hv (i, j)).2.trans
        (by exact_mod_cast le_max_right (1 : ℕ) F.totalDegree)⟩
  · intro i j hj
    simp only [M, Matrix.of_apply, hj, ite_true]

/-- Leibniz determinant bound: the maximal minors of an integer matrix with entries in
`[0, N]` are at most `r! N^r` in absolute value. -/
private theorem abs_det_submatrix_le_of_entry_bound {r n : ℕ} (M : Matrix (Fin r) (Fin n) ℤ) (N : ℕ)
    (hb : ∀ i j, 0 ≤ M i j ∧ M i j ≤ N) (c : Fin r ↪ Fin n) :
    |(M.submatrix id c).det| ≤ (r.factorial : ℤ) * (N : ℤ) ^ r := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) (A := M.submatrix id c)
    (fun i j => (abs_of_nonneg (hb i (c j)).1) ▸ (hb i (c j)).2)
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh

/-- Bounded integer specialization inside the specified coordinate linear
subspace of matrices. Zero columns, nonvanishing and full rank are all
preserved; the coordinate bound has no extra factor from the row count. -/
theorem exists_integer_minor_specialization_zero_columns {r n : ℕ}
    (Z : Finset (Fin n)) (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree)
    (A : Matrix (Fin r) (Fin n) ℚ) (hli : LinearIndependent ℚ A.row)
    (hzero : ∀ i j, j ∈ Z → A i j = 0)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      (∀ i j, j ∈ Z → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 ∧
      ∀ c : Fin r ↪ Fin n,
        |(M.submatrix id c).det| ≤ (r.factorial : ℤ) *
          ((max 1 F.totalDegree : ℕ) : ℤ) ^ r := by
  obtain ⟨M, hb, hz, hi, hv⟩ := if hdeg : F.totalDegree = 0 then
      exists_integer_minor_specialization_zero_columns_of_totalDegree_eq_zero Z F hdeg A hli
        hzero hF
    else
      exists_integer_minor_specialization_zero_columns_of_totalDegree_ne_zero Z F hhom hdeg A
        hzero hF
  exact ⟨M, hb, hz, hi, hv, abs_det_submatrix_le_of_entry_bound M _ (by exact_mod_cast hb)⟩

end
end CCDN
