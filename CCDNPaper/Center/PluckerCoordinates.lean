/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.SubspaceQuotient
import CCDN.Height.ProjectiveZeroLocus

/-! The Plücker point of a fixed-dimensional center, with the coordinates
`matrixPluckerCoordinates`. No assertion about the dimension of the projective
target is needed. Equality of Plücker points is exactly equality of row spans. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix MvPolynomial

private theorem exists_row_matrix_of_span_le
    {K : Type*} [Field K] {r s n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin s) (Fin n) K)
    (hspan : Submodule.span K (Set.range A.row) ≤ Submodule.span K (Set.range B.row)) :
    ∃ C : Matrix (Fin r) (Fin s) K, A = C * B := by
  classical
  have hmem (i : Fin r) : A.row i ∈ Submodule.span K (Set.range B.row) :=
    hspan (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  refine ⟨c, ?_⟩
  ext i j
  change A i j = ∑ k, c i k * B k j
  have hh := congrFun (hc i) j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
    ] using hh.symm

private theorem matrixPluckerCoordinates_mul
    {K : Type*} [Field K] {r n : ℕ}
    (C : Matrix (Fin r) (Fin r) K) (A : Matrix (Fin r) (Fin n) K) :
    matrixPluckerCoordinates (C * A) = C.det • matrixPluckerCoordinates A := by
  funext c
  change ((C * A).submatrix id c).det = C.det * (A.submatrix id c).det
  rw [Matrix.submatrix_mul C A id id c Function.bijective_id]
  simp only [Matrix.submatrix_id_id, Matrix.det_mul]

private theorem matrixPluckerCoordinates_smul_of_span_eq
    {K : Type*} [Field K] {r n : ℕ}
    (A B : Matrix (Fin r) (Fin n) K) (hA : LinearIndependent K A.row)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    ∃ c : K, c ≠ 0 ∧ matrixPluckerCoordinates A = c • matrixPluckerCoordinates B := by
  obtain ⟨C, hC⟩ := exists_row_matrix_of_span_le A B hspan.le
  have he : matrixPluckerCoordinates A = C.det • matrixPluckerCoordinates B := by
    rw [hC, matrixPluckerCoordinates_mul]
  refine ⟨C.det, ?_, he⟩
  intro hc
  apply matrixPluckerCoordinates_ne_zero A hA
  rw [he, hc, zero_smul]

private theorem centerMinorProjection_smul_of_plucker
    {K : Type*} [Field K] {r n : ℕ}
    (A B : Matrix (Fin r) (Fin n) K) (c : K)
    (he : matrixPluckerCoordinates A = c • matrixPluckerCoordinates B)
    (x : Fin n → K) : centerMinorProjection A x = c • centerMinorProjection B x := by
  funext j
  change centerMinorProjection A x j = c * centerMinorProjection B x j
  rw [← centerMinorProjectionForm_eval, ← centerMinorProjectionForm_eval,
    centerMinorProjectionForm_eq_plucker_coefficients,
    centerMinorProjectionForm_eq_plucker_coefficients]
  change eval x (∑ k, C (eval (matrixPluckerCoordinates A) (centerPluckerCoefficient j k)) * X k) =
    c * eval x (∑ k, C (eval (matrixPluckerCoordinates B) (centerPluckerCoefficient j k)) * X k)
  rw [he]
  simp only [map_sum, map_mul, eval_C, eval_X,
    homogeneous_eval_smul (centerPluckerCoefficient_homogeneous j _), pow_one,
    Finset.mul_sum, mul_assoc]

private theorem matrix_span_eq_of_plucker_smul
    {K : Type*} [Field K] {r n : ℕ}
    (A B : Matrix (Fin r) (Fin n) K)
    (hA : LinearIndependent K A.row) (hB : LinearIndependent K B.row)
    (c : K) (hc : c ≠ 0)
    (he : matrixPluckerCoordinates A = c • matrixPluckerCoordinates B) :
    Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row) := by
  ext x
  rw [← centerMinorProjection_eq_zero_iff A hA, ← centerMinorProjection_eq_zero_iff B hB,
    centerMinorProjection_smul_of_plucker A B c he]
  simp only [smul_eq_zero, hc, false_or]

/-- The Plücker point of a full-row-rank `r × n` matrix: the projective point given by its
maximal minors `matrixPluckerCoordinates`, which are not all zero. -/
def independentCenterPlucker {K : Type*} [Field K] {r n : ℕ}
    (x : IndependentCenterMatrix K r n) : Projectivization K ((Fin r ↪ Fin n) → K) :=
  Projectivization.mk K (matrixPluckerCoordinates (Matrix.of fun i j => x.val (i,j)))
    (matrixPluckerCoordinates_ne_zero _ x.property)

/-- Two full-row-rank matrices have the same Plücker point if and only if they have the same
row span. -/
theorem independentCenterPlucker_eq_iff
    {K : Type*} [Field K] {r n : ℕ} (x y : IndependentCenterMatrix K r n) :
    independentCenterPlucker x = independentCenterPlucker y ↔
      centerMatrixSpan x = centerMatrixSpan y := by
  rw [independentCenterPlucker, independentCenterPlucker, Projectivization.mk_eq_mk_iff,
    centerMatrixSpan_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact matrix_span_eq_of_plucker_smul _ _ x.property y.property (c : K) c.ne_zero hc.symm
  · intro hspan
    obtain ⟨c, hc, he⟩ := matrixPluckerCoordinates_smul_of_span_eq _ _ x.property hspan
    exact ⟨Units.mk0 c hc, he.symm⟩

/-- A chosen full-row-rank matrix whose rows span the `r`-dimensional subspace `W`. -/
def centerSubspaceMatrix {K : Type*} [Field K] {r n : ℕ}
    (W : CenterSubspace K r n) : IndependentCenterMatrix K r n :=
  Classical.choose (centerMatrixSpan_surjective W)

private theorem centerSubspaceMatrix_span {K : Type*} [Field K] {r n : ℕ}
    (W : CenterSubspace K r n) : centerMatrixSpan (centerSubspaceMatrix W) = W :=
  Classical.choose_spec (centerMatrixSpan_surjective W)

/-- The Plücker point of an `r`-dimensional subspace `W` of `Fin n → K`, computed from any
matrix whose rows form a basis of `W`. -/
def centerSubspacePlucker {K : Type*} [Field K] {r n : ℕ}
    (W : CenterSubspace K r n) : Projectivization K ((Fin r ↪ Fin n) → K) :=
  independentCenterPlucker (centerSubspaceMatrix W)

/-- The Plücker point of the row span of a full-row-rank matrix `x` is the Plücker point of
`x`. -/
theorem centerSubspacePlucker_matrixSpan {K : Type*} [Field K] {r n : ℕ}
    (x : IndependentCenterMatrix K r n) :
    centerSubspacePlucker (centerMatrixSpan x) = independentCenterPlucker x := by
  apply (independentCenterPlucker_eq_iff _ _).mpr
  exact centerSubspaceMatrix_span _

/-- Distinct `r`-dimensional subspaces have distinct Plücker points. -/
theorem centerSubspacePlucker_injective {K : Type*} [Field K] {r n : ℕ} :
    Function.Injective (centerSubspacePlucker (K := K) (r := r) (n := n)) := by
  intro W V h
  have he := (independentCenterPlucker_eq_iff _ _).mp h
  simpa only [centerSubspaceMatrix_span] using he

/-- A homogeneous polynomial `f` in the Plücker coordinates vanishes at the Plücker point of a
full-row-rank matrix `x` if and only if it vanishes at the maximal minors of `x`. -/
theorem homogeneous_eval_independentCenterPlucker
    {K : Type*} [Field K] {r n d : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) (hf : f.IsHomogeneous d)
    (x : IndependentCenterMatrix K r n) :
    eval (independentCenterPlucker x).rep f = 0 ↔
      eval (matrixPluckerCoordinates (Matrix.of fun i j => x.val (i,j))) f = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K
    (matrixPluckerCoordinates (Matrix.of fun i j => x.val (i,j)))
    (matrixPluckerCoordinates_ne_zero _ x.property)
  change eval (Projectivization.mk K _ _).rep f = 0 ↔ _
  rw [← hc]
  exact homogeneous_eval_zero_iff_smul hf c.ne_zero _

end
end CCDN
