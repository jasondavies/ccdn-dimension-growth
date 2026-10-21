/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Center.CoordinateGridAvoidance
import CCDN.Center.MinorCoordinateDegree
import CCDN.Center.MinorSpecialization
import CCDN.ForMathlib.MatrixRank
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
/-! Sharp bounded specialization of maximal-minor conditions while keeping
prescribed matrix columns equal to zero. The distinguished zero column is
the center-at-infinity case in Section 5.3. The nonvanishing rational
witness is an explicit hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Universal maximal minor on matrices with the specified columns zero. -/
def zeroColumnUniversalMinor {r n : ℕ} (Z : Finset (Fin n))
    (c : Fin r ↪ Fin n) : MvPolynomial (Fin r × Fin n) ℚ :=
  (Matrix.of fun i j : Fin r => if c j ∈ Z then 0 else X (i, c j)).det

lemma zeroColumnUniversalMinor_eval {r n : ℕ} (Z : Finset (Fin n))
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

lemma eval_zero_column_minor_substitution {r n : ℕ} (Z : Finset (Fin n))
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

lemma zeroColumnUniversalMinor_degreeOf {r n : ℕ} (Z : Finset (Fin n))
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

lemma zero_column_minor_substitution_degreeOf_le {r n : ℕ} (Z : Finset (Fin n))
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ) (p : Fin r × Fin n) :
    (aeval (zeroColumnUniversalMinor Z) F).degreeOf p ≤ F.totalDegree := by
  simpa only [one_mul] using aeval_degreeOf_le (zeroColumnUniversalMinor Z) p 1
    (fun c => zeroColumnUniversalMinor_degreeOf Z c p) F

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
  classical
  suffices ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      (∀ i j, j ∈ Z → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 by
    obtain ⟨M, hb, hz, hi, hv⟩ := this
    refine ⟨M, hb, hz, hi, hv, fun c => ?_⟩
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) (A := M.submatrix id c)
      (fun i j => (abs_of_nonneg (hb i (c j)).1) ▸ (hb i (c j)).2)
    simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh
  by_cases hdeg : F.totalDegree = 0
  · obtain ⟨c, hc, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row A hli
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
  · let U := aeval (zeroColumnUniversalMinor Z) F
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

end
end CCDN
