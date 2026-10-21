/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.MinorProjection
public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Projection.ImageFractionField
public import Mathlib.Tactic.Continuity
import CCDN.Center.MatrixProjectionFields
/-! Enumerating the maximal-minor coordinates turns the source's
Plücker projection into a matrix with exactly the center as its kernel.
The Chow specialization results are stated for matrices with rows indexed by
`Fin (s + 2)`, so proofs choose such an enumeration; the statements about
centers use the forms `centerMinorProjectionForm`, indexed by the column
injections themselves, and the choice never appears in them. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma exists_center_minor_coordinate_enumeration {r n : ℕ} (hr : r + 2 ≤ n) :
    ∃ s : ℕ, Nonempty (Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin n)) := by
  classical
  let e₀ : Fin (r + 1) ↪ Fin n :=
    ⟨fun i => Fin.castLE hr i.castSucc,
      (Fin.castLE_injective hr).comp (Fin.castSucc_injective (r + 1))⟩
  let e₁ : Fin (r + 1) ↪ Fin n :=
    ⟨fun i => Fin.castLE hr i.succ,
      (Fin.castLE_injective hr).comp (Fin.succ_injective (r + 1))⟩
  have hne : e₀ ≠ e₁ := by
    intro he
    have hh := congrArg (fun e : Fin (r + 1) ↪ Fin n => (e 0).val) he
    change 0 = 1 at hh
    omega
  have hcard : 2 ≤ Fintype.card (Fin (r + 1) ↪ Fin n) :=
    Fintype.one_lt_card_iff.mpr ⟨e₀, e₁, hne⟩
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hcard
  refine ⟨s, ⟨?_⟩⟩
  have he : s + 2 = Fintype.card (Fin (r + 1) ↪ Fin n) := by omega
  exact (finCongr he).trans (Fintype.equivFin _).symm

/-- The center projection as a matrix, with rows ordered by an enumeration
of the column injections. Every entry is a degree-one polynomial in the
Plücker coordinates of the center. -/
def centerMinorProjectionMatrix {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) :
    Matrix (Fin (s + 1)) (Fin n) K :=
  fun i j => eval (matrixPluckerCoordinates A) (centerPluckerCoefficient (e i) j)

lemma centerMinorProjectionMatrix_form {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (i : Fin (s + 1)) :
    chowProjectionForms (centerMinorProjectionMatrix A e) i = centerMinorProjectionForm A (e i) :=
  (centerMinorProjectionForm_eq_plucker_coefficients A (e i)).symm

lemma chowProjectionForms_centerMinorProjectionMatrix {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    chowProjectionForms (centerMinorProjectionMatrix A e) = centerMinorProjectionForm A ∘ e :=
  funext (centerMinorProjectionMatrix_form A e)

lemma centerMinorProjectionMatrix_mulVec {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (x : Fin (n + 1) → K) :
    centerMinorProjectionMatrix A e *ᵥ x = fun i => centerMinorProjection A x (e i) := by
  funext i
  rw [← chowProjectionForms_eval, centerMinorProjectionMatrix_form,
    centerMinorProjectionForm_eval]

/-- The matrix kernel equals the linear center specified by its rows. -/
theorem centerMinorProjectionMatrix_ker {K : Type*} [Field K] {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    (centerMinorProjectionMatrix A e).mulVecLin.ker =
      Submodule.span K (Set.range A.row) := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, centerMinorProjectionMatrix_mulVec,
    ← centerMinorProjection_eq_zero_iff A hA]
  constructor
  · intro h
    funext c
    simpa only [e.apply_symm_apply, Pi.zero_apply] using congrFun h (e.symm c)
  · intro h
    funext i
    exact congrFun h (e i)

lemma centerMinorProjectionMatrix_disjoint {K : Type*} [Field K] {r n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J,
      p.rep ∉ Submodule.span K (Set.range A.row)) :
    ∀ p ∈ projectiveIdealZeroLocus J, centerMinorProjectionMatrix A e *ᵥ p.rep ≠ 0 := by
  intro p hp hz
  apply hcenter p hp
  rw [← centerMinorProjectionMatrix_ker A hA e]
  exact hz

lemma projectionImageField_centerMinorProjectionMatrix
    {K F : Type*} [Field K] [Field F] [Algebra K F] {r n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Algebra (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    [IsScalarTower K (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    projectionImageField (F := F) J (chowProjectionForms (centerMinorProjectionMatrix A e)) =
      projectionImageField (F := F) J (centerMinorProjectionForm A) := by
  rw [chowProjectionForms_centerMinorProjectionMatrix, projectionImageField_comp_equiv]

lemma centerMinorProjectionMatrix_isIntegral_iff {K : Type*} [Field K] {r n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    (projectionCoordinateMap J (chowProjectionForms (centerMinorProjectionMatrix A e))).IsIntegral ↔
      (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral := by
  rw [chowProjectionForms_centerMinorProjectionMatrix,
    projectionCoordinateMap_comp_equiv_isIntegral]

/-- The center projection generates the same field as any linear projection
with the same kernel. -/
theorem projectionImageField_centerMinorProjectionForm_of_ker
    {K F : Type*} [Field K] [Field F] [Algebra K F] {r n t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Algebra (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    [IsScalarTower K (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (hr : r + 2 ≤ n + 1) (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : B.mulVecLin.ker = Submodule.span K (Set.range A.row)) :
    projectionImageField (F := F) J (centerMinorProjectionForm A) =
      projectionImageField (F := F) J (chowProjectionForms B) := by
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  rw [← projectionImageField_centerMinorProjectionMatrix J A e]
  exact projectionImageField_eq_of_matrix_kernel_eq J _ _
    ((centerMinorProjectionMatrix_ker A hA e).trans hker.symm)

/-- The center projection is integral when a linear projection whose kernel
contains the center is. -/
theorem centerMinorProjectionForm_isIntegral_of_ker
    {K : Type*} [Field K] {r n t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (hr : r + 2 ≤ n + 1) (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : Submodule.span K (Set.range A.row) ≤ B.mulVecLin.ker)
    (hint : (projectionCoordinateMap J (chowProjectionForms B)).IsIntegral) :
    (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral := by
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  rw [← centerMinorProjectionMatrix_isIntegral_iff J A e]
  exact projection_integral_of_matrix_kernel_le J _ B
    ((centerMinorProjectionMatrix_ker A hA e).trans_le hker) hint

/-- A linear projection whose kernel is contained in the center is integral
when the center projection is. -/
theorem isIntegral_of_centerMinorProjectionForm
    {K : Type*} [Field K] {r n t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (hr : r + 2 ≤ n + 1) (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : B.mulVecLin.ker ≤ Submodule.span K (Set.range A.row))
    (hint : (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral) :
    (projectionCoordinateMap J (chowProjectionForms B)).IsIntegral := by
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  rw [← centerMinorProjectionMatrix_isIntegral_iff J A e] at hint
  exact projection_integral_of_matrix_kernel_le J B _
    (hker.trans_eq (centerMinorProjectionMatrix_ker A hA e).symm) hint

/-- Centers with the same span generate the same field. -/
theorem projectionImageField_centerMinorProjectionForm_eq_of_span_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] {r n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Algebra (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    [IsScalarTower K (MvPolynomial (Fin (n + 1)) K ⧸ J) F]
    (A B : Matrix (Fin r) (Fin (n + 1)) K)
    (hA : LinearIndependent K A.row) (hB : LinearIndependent K B.row)
    (hspan : Submodule.span K (Set.range A.row) = Submodule.span K (Set.range B.row)) :
    projectionImageField (F := F) J (centerMinorProjectionForm A) =
      projectionImageField (F := F) J (centerMinorProjectionForm B) := by
  classical
  rcases isEmpty_or_nonempty (Fin (r + 1) ↪ Fin (n + 1)) with h | h
  · congr 1
    funext c
    exact h.elim c
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero
      (Fintype.card_ne_zero (α := Fin (r + 1) ↪ Fin (n + 1)))
    let e := (finCongr hs.symm).trans (Fintype.equivFin (Fin (r + 1) ↪ Fin (n + 1))).symm
    rw [← projectionImageField_centerMinorProjectionMatrix J A e,
      ← projectionImageField_centerMinorProjectionMatrix J B e]
    apply projectionImageField_eq_of_matrix_kernel_eq J
    rw [centerMinorProjectionMatrix_ker A hA e, centerMinorProjectionMatrix_ker B hB e, hspan]

end
end CCDN
