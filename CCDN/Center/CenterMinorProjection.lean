/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.MatrixRank
public import CCDN.Center.ChowLinearSpecialization
public import Mathlib.Data.Fin.Embedding
public import CCDN.Algebra.PolynomialPredicates
/-! The literal center projection from Section 5: its coordinates are the
maximal minors obtained by adjoining the point as the first row of a center
matrix. Its kernel is exactly the span of the independent center rows, and
its linear coefficients are signed Plücker coordinates of that center. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- The Plücker coordinates of a matrix: its maximal minors. They are indexed
by all ordered column injections `Fin r ↪ Fin n`, so each unordered set of
columns occurs several times, with signs; nothing depends on choosing one
representative per set. -/
def matrixPluckerCoordinates {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) : (Fin r ↪ Fin n) → K :=
  fun c => (A.submatrix id c).det

theorem matrixPluckerCoordinates_ne_zero
    {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (hA : LinearIndependent K A.row) :
    matrixPluckerCoordinates A ≠ 0 := by
  obtain ⟨c, hc, hd⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row A hA
  intro hz
  exact hd (congrFun hz ⟨c, hc⟩)

lemma matrixPluckerCoordinates_map {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin r ↪ Fin n) :
    matrixPluckerCoordinates (A.map φ) c = φ (matrixPluckerCoordinates A c) :=
  (φ.map_det (A.submatrix id c)).symm

def centerMinorProjection {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (x : Fin n → K) (c : Fin (r + 1) ↪ Fin n) : K :=
  (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c).det

/-- Laplace expansion gives the linear coordinate of the center map. -/
def centerMinorProjectionForm {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) : MvPolynomial (Fin n) K :=
  ∑ j : Fin (r + 1), C ((-1 : K) ^ (j : ℕ) * (A.submatrix id (j.succAboveEmb.trans c)).det) * X (c j)

lemma centerMinorProjectionForm_eval {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) (x : Fin n → K) :
    eval x (centerMinorProjectionForm A c) = centerMinorProjection A x c := by
  classical
  rw [centerMinorProjection, Matrix.det_succ_row_zero]
  simp only [centerMinorProjectionForm, map_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.submatrix (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c)
      Fin.succ j.succAbove = A.submatrix id (j.succAboveEmb.trans c) := by
    ext a b
    change (Fin.cons x (fun i j => A i j) : Fin (r + 1) → Fin n → K) a.succ (c (j.succAbove b)) = A a (c (j.succAbove b))
    rw [Fin.cons_succ]
  rw [he]
  change (-1 : K) ^ (j : ℕ) * _ * x (c j) = (-1 : K) ^ (j : ℕ) * x (c j) * _
  ring

/-- Vanishing of every projection coordinate is exactly membership in
the center, assuming only that the rows defining the center are independent. -/
theorem centerMinorProjection_eq_zero_iff {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (hA : LinearIndependent K A.row) (x : Fin n → K) :
    centerMinorProjection A x = 0 ↔ x ∈ Submodule.span K (Set.range A.row) := by
  classical
  constructor
  · intro hz
    by_contra hx
    have hi : LinearIndependent K (Fin.cons x (fun i j => A i j) : Fin (r + 1) → (Fin n → K)) :=
      linearIndependent_finCons.mpr ⟨hA, hx⟩
    obtain ⟨c, hc, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row
      (Fin.cons x (fun i j => A i j)) hi
    exact hdet (congrFun hz ⟨c, hc⟩)
  · intro hx
    funext c
    change (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c).det = 0
    apply Matrix.det_eq_zero_of_not_linearIndependent_rows
    intro hi
    have hh : LinearIndependent K (Fin.cons x (fun i j => A i j) : Fin (r + 1) → (Fin n → K)) :=
      LinearIndependent.of_comp (LinearMap.funLeft K K c) hi
    exact (linearIndependent_finCons.mp hh).2 hx

/-- One coefficient, as a degree-one polynomial in Plücker variables. -/
def centerPluckerCoefficient {K : Type*} [Field K] {r n : ℕ}
    (c : Fin (r + 1) ↪ Fin n) (k : Fin n) : MvPolynomial (Fin r ↪ Fin n) K :=
  ∑ j : Fin (r + 1), if c j = k then C ((-1 : K) ^ (j : ℕ)) * X (j.succAboveEmb.trans c) else 0

lemma centerPluckerCoefficient_homogeneous {K : Type*} [Field K] {r n : ℕ}
    (c : Fin (r + 1) ↪ Fin n) (k : Fin n) :
    (centerPluckerCoefficient (K := K) c k).IsHomogeneous 1 := by
  classical
  apply IsHomogeneous.sum
  intro j _
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact isHomogeneous_zero _ K 1

/-- The matrix entries of the projection are linear expressions in the
maximal minors of the center rows, exactly as in the source's Plücker map. -/
theorem centerMinorProjectionForm_eq_plucker_coefficients
    {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) :
    centerMinorProjectionForm A c =
      ∑ k, C (eval (matrixPluckerCoordinates A) (centerPluckerCoefficient c k)) * X k := by
  classical
  simp only [centerMinorProjectionForm, centerPluckerCoefficient, matrixPluckerCoordinates,
    map_sum, apply_ite, map_mul, eval_C, eval_X, map_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

end
end CCDN
