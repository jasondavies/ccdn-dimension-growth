/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.SubspaceQuotient
/-! The birational-center condition depends only on the row span, so it
defines a locus of center subspaces. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private lemma matrix_span_rows_map_le
    {K L : Type*} [Field K] [Field L] {r s n : ℕ}
    (φ : K →+* L) (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin s) (Fin n) K)
    (hspan : Submodule.span K (Set.range A.row) ≤ Submodule.span K (Set.range B.row)) :
    Submodule.span L (Set.range (A.map φ).row) ≤
      Submodule.span L (Set.range (B.map φ).row) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hi : A.row i ∈ Submodule.span K (Set.range B.row) :=
    hspan (Submodule.subset_span ⟨i,rfl⟩)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hi
  have he : (A.map φ).row i = ∑ j, φ (c j) • (B.map φ).row j := by
    funext k
    have hh := congrArg (fun v : Fin n → K => φ (v k)) hc
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,map_sum,map_mul,
      Matrix.row_apply,Matrix.map_apply] using hh.symm
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

private lemma matrix_span_rows_map_eq
    {K L : Type*} [Field K] [Field L] {r s n : ℕ}
    (φ : K →+* L) (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin s) (Fin n) K)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    Submodule.span L (Set.range (A.map φ).row) =
      Submodule.span L (Set.range (B.map φ).row) :=
  le_antisymm (matrix_span_rows_map_le φ A B hspan.le)
    (matrix_span_rows_map_le φ B A hspan.ge)

private lemma isBirationalMatrixCenter_iff_span
    {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (A B : Matrix (Fin r) (Fin (n + 1)) K)
    (hA : LinearIndependent K A.row) (hB : LinearIndependent K B.row)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    IsBirationalMatrixCenter J A ↔ IsBirationalMatrixCenter J B := by
  unfold IsBirationalMatrixCenter
  rw [matrix_span_rows_map_eq (algebraMap K (AlgebraicClosure K)) A B hspan,
    projectionImageField_centerMinorProjectionForm_eq_of_span_eq J A B hA hB hspan]

/-- Center subspaces admitting a geometrically disjoint birational
projection. The condition is independent of the representing matrix. -/
def birationalCenterSubspaceLocus
    {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] :
    Set (CenterSubspace K r (n + 1)) :=
  centerMatrixSpan '' birationalMatrixCenterLocus J

lemma birationalCenterSubspaceLocus_preimage
    {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] :
    centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus (r := r) J =
      birationalMatrixCenterLocus J := by
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact (isBirationalMatrixCenter_iff_span J
      (Matrix.of fun i j => y.val (i,j)) (Matrix.of fun i j => x.val (i,j)) y.property x.property
      ((centerMatrixSpan_eq_iff y x).mp hxy)).mp hy
  · intro hx
    exact ⟨x,hx,rfl⟩

end
end CCDN
