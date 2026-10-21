/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ImageFractionField
public import CCDN.Center.ChowLinearSpecialization
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Kernel containment of matrices gives containment of their
projected-coordinate fields. Equal centers therefore give the same image
function field, for any coordinate ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private lemma matrix_row_combination_of_kernel_le
    {K α β γ : Type*} [Field K] [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α γ K) (B : Matrix β γ K)
    (hker : B.mulVecLin.ker ≤ A.mulVecLin.ker) (i : α) :
    ∃ c : β → K, ∀ j, ∑ k, c k * B k j = A i j := by
  classical
  let a : (γ → K) →ₗ[K] K := (LinearMap.proj i).comp A.mulVecLin
  let b : β → (γ → K) →ₗ[K] K := fun j => (LinearMap.proj j).comp B.mulVecLin
  have hle : (⨅ j, (b j).ker) ≤ a.ker := by
    intro x hx
    have hBx : B.mulVecLin x = 0 := by
      funext j
      exact ((Submodule.mem_iInf _).mp hx j : b j x = 0)
    have hAx : A.mulVecLin x = 0 := hker hBx
    exact congrFun hAx i
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (mem_span_of_iInf_ker_le_ker hle)
  refine ⟨c,fun j => ?_⟩
  have hh := congrArg (fun l : (γ → K) →ₗ[K] K => l (Pi.single j 1)) hc
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,Matrix.mulVecLin_apply,Matrix.mulVec_single_one,
    Matrix.col_apply,smul_eq_mul,a,b] using hh

private lemma chowProjectionForms_combination_of_kernel_le
    {K : Type*} [Field K] {n s t : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : B.mulVecLin.ker ≤ A.mulVecLin.ker) (i : Fin (s + 1)) :
    ∃ c : Fin (t + 1) → K,
      chowProjectionForms A i = ∑ j, C (c j) * chowProjectionForms B j := by
  obtain ⟨c,hc⟩ := matrix_row_combination_of_kernel_le A B hker i
  refine ⟨c,?_⟩
  symm
  simp only [linearForm]
  simp_rw [Finset.mul_sum,← mul_assoc,← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,← map_sum,hc]

private theorem projectionImageField_le_of_matrix_kernel_le
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n s t : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Algebra (MvPolynomial (Fin (n + 1)) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin (n + 1)) K ⧸ I) F]
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : B.mulVecLin.ker ≤ A.mulVecLin.ker) :
    projectionImageField (F := F) I (chowProjectionForms A) ≤
      projectionImageField (F := F) I (chowProjectionForms B) := by
  let η : MvPolynomial (Fin (n + 1)) K →ₐ[K] F :=
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K ⧸ I) F).comp
      (Ideal.Quotient.mkₐ K I)
  let E := projectionImageField (F := F) I (chowProjectionForms B)
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i,rfl⟩
  change η (chowProjectionForms A i) ∈ E
  obtain ⟨c,hc⟩ := chowProjectionForms_combination_of_kernel_le A B hker i
  rw [hc,map_sum]
  apply E.sum_mem
  intro j _
  rw [map_mul]
  apply E.mul_mem
  · change η (algebraMap K (MvPolynomial (Fin (n + 1)) K) (c j)) ∈ E
    rw [η.commutes]
    exact E.algebraMap_mem _
  · exact IntermediateField.subset_adjoin K _ ⟨j,rfl⟩

theorem projectionImageField_eq_of_matrix_kernel_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n s t : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Algebra (MvPolynomial (Fin (n + 1)) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin (n + 1)) K ⧸ I) F]
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : A.mulVecLin.ker = B.mulVecLin.ker) :
    projectionImageField (F := F) I (chowProjectionForms A) =
      projectionImageField (F := F) I (chowProjectionForms B) :=
  le_antisymm (projectionImageField_le_of_matrix_kernel_le I A B hker.ge)
    (projectionImageField_le_of_matrix_kernel_le I B A hker.le)

theorem projection_integral_of_matrix_kernel_le
    {K : Type*} [Field K] {n s t : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (B : Matrix (Fin (t + 1)) (Fin (n + 1)) K)
    (hker : A.mulVecLin.ker ≤ B.mulVecLin.ker)
    (hint : (projectionCoordinateMap I (chowProjectionForms B)).IsIntegral) :
    (projectionCoordinateMap I (chowProjectionForms A)).IsIntegral := by
  classical
  choose c hc using fun i => chowProjectionForms_combination_of_kernel_le B A hker i
  let ξ : MvPolynomial (Fin (t + 1)) K →ₐ[K] MvPolynomial (Fin (s + 1)) K :=
    aeval (fun i => ∑ j, C (c i j) * X j)
  have he : (projectionCoordinateMap I (chowProjectionForms A)).comp ξ =
      projectionCoordinateMap I (chowProjectionForms B) := by
    ext i
    simp only [AlgHom.comp_apply,ξ,aeval_X]
    change Ideal.Quotient.mk I
      (aeval (chowProjectionForms A) (∑ j, C (c i j) * X j)) =
        Ideal.Quotient.mk I (aeval (chowProjectionForms B) (X i))
    rw [aeval_X,hc i]
    congr 1
    simp only [map_sum,map_mul,aeval_C,aeval_X,MvPolynomial.algebraMap_eq]
  apply RingHom.IsIntegral.tower_top ξ.toRingHom
    (projectionCoordinateMap I (chowProjectionForms A)).toRingHom
  change ((projectionCoordinateMap I (chowProjectionForms A)).comp ξ).IsIntegral
  rwa [he]

/-- Reindexing the coordinates by an equivalence does not change the field
they generate. -/
theorem projectionImageField_comp_equiv
    {K F σ σ' τ : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial τ K))
    [Algebra (MvPolynomial τ K ⧸ I) F] [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    (a : σ → MvPolynomial τ K) (e : σ' ≃ σ) :
    projectionImageField (F := F) I (a ∘ e) = projectionImageField (F := F) I a := by
  unfold projectionImageField
  congr 1
  exact e.surjective.range_comp
    (fun i => algebraMap (MvPolynomial τ K ⧸ I) F ((Ideal.Quotient.mk I) (a i)))

/-- Reindexing the coordinates by an equivalence does not change integrality. -/
theorem projectionCoordinateMap_comp_equiv_isIntegral
    {K σ σ' τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K) (e : σ' ≃ σ) :
    (projectionCoordinateMap I (a ∘ e)).IsIntegral ↔
      (projectionCoordinateMap I a).IsIntegral := by
  have he : projectionCoordinateMap I (a ∘ e) =
      (projectionCoordinateMap I a).comp (rename e) := by
    ext i
    simp [projectionCoordinateMap]
  rw [he]
  constructor
  · intro h
    exact RingHom.IsIntegral.tower_top (rename e : MvPolynomial σ' K →ₐ[K] _).toRingHom
      (projectionCoordinateMap I a).toRingHom h
  · intro h
    exact RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _ (rename_surjective e e.surjective)) h

end
end CCDN
