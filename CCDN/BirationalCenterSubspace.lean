module

public import CCDN.CenterSubspaceQuotient
public import CCDN.PolynomialPredicates

/-! The birational-center condition depends only on the row span, so it
defines a locus of center subspaces. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma matrix_span_rows_map_le
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

lemma matrix_span_rows_map_eq
    {K L : Type*} [Field K] [Field L] {r s n : ℕ}
    (φ : K →+* L) (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin s) (Fin n) K)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    Submodule.span L (Set.range (A.map φ).row) =
      Submodule.span L (Set.range (B.map φ).row) :=
  le_antisymm (matrix_span_rows_map_le φ A B hspan.le)
    (matrix_span_rows_map_le φ B A hspan.ge)

lemma isBirationalMatrixCenter_iff_span
    {K : Type*} [Field K] {n r s t u : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (e' : Fin (u + 2) ≃ (Fin (t + 1) ↪ Fin (n + 1)))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (B : Matrix (Fin t) (Fin (n + 1)) K) (hB : LinearIndependent K B.row)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    IsBirationalMatrixCenter J e A ↔ IsBirationalMatrixCenter J e' B := by
  have hgeom := matrix_span_rows_map_eq (algebraMap K (AlgebraicClosure K)) A B hspan
  have hker : (centerMinorProjectionMatrix A e).mulVecLin.ker =
      (centerMinorProjectionMatrix B e').mulVecLin.ker := by
    rw [centerMinorProjectionMatrix_ker A hA e,centerMinorProjectionMatrix_ker B hB e']
    exact hspan
  unfold IsBirationalMatrixCenter
  rw [hgeom,projectionImageField_eq_of_matrix_kernel_eq J _ _ hker]

/-- Center subspaces admitting a geometrically disjoint birational
projection. The condition is independent of the representing matrix. -/
def birationalCenterSubspaceLocus
    {K : Type*} [Field K] {n r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    Set (CenterSubspace K r (n + 1)) :=
  centerMatrixSpan '' birationalMatrixCenterLocus J e

lemma birationalCenterSubspaceLocus_preimage
    {K : Type*} [Field K] {n r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J e = birationalMatrixCenterLocus J e := by
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact (isBirationalMatrixCenter_iff_span J e e
      (Matrix.of fun i j => y.val (i,j)) y.property
      (Matrix.of fun i j => x.val (i,j)) x.property
      ((centerMatrixSpan_eq_iff y x).mp hxy)).mp hy
  · intro hx
    exact ⟨x,hx,rfl⟩

end
end CCDN
