/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ImageFractionField
public import Mathlib.RingTheory.MvPolynomial
import CCDN.Center.ClosureNormalizationInfinite
import CCDN.Center.FixedCoordinateGenericNormalization
import CCDN.Center.GeometricCenterRows
import CCDN.Center.HomogeneousProjectionNoBasePoint
import CCDN.Center.IndependentPrimitiveExtension
import CCDN.Hilbert.FullDimension
import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
import CCDN.Projection.IntegralProjectionHilbert
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Constructed finite birational centers at infinity. Every center row has
zero homogenizing coordinate; the construction includes affine dimension
zero. -/

@[expose] public section
namespace CCDN
noncomputable section

section

/-! A finite birational linear projection of the projective closure
that retains the homogenizing coordinate. The tuple is independent even
in degree one and in affine dimension zero. -/

open MvPolynomial

private theorem exists_independent_fixed_coordinate_closure_projection
    {K : Type*} [Field K] [CharZero K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ a : Fin (m + 2) → MvPolynomial (Fin (n + 1)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧ LinearIndependent K a ∧ a 1 = X 0 ∧
      (projectionCoordinateMap (projectiveClosureIdeal I) a).IsIntegral ∧
      projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I) a = ⊤ := by
  obtain ⟨b, hb, _, _, hcone⟩ :=
    exists_closure_normalization_infinite_of_le m n (by omega) I hdimdeg.natDegree_eq
  let J := projectiveClosureIdeal I
  have hJ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdimdeg
  have hker : RingHom.ker (projectionCoordinateMap J (closureProjectionCoordinates b)) = ⊥ :=
    ideal_eq_bot_of_full_hilbert_dimension _ (RingHom.ker_ne_top _) (by
      simpa only [Fintype.card_fin] using
        (integral_projection_hilbert_dimension_eq J _ hcone).trans hJ.natDegree_eq)
  have hinj : Function.Injective (projectionCoordinateMap J (closureProjectionCoordinates b)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hker
  obtain ⟨v, hv, hli, hint, hfield⟩ := exists_independent_linear_primitive_extension
    (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
    (closureProjectionCoordinates b) (closureProjectionCoordinates_homogeneous b hb)
    hcone hinj (by omega) d hJ
  refine ⟨Fin.cons v (closureProjectionCoordinates b), ?_, hli, ?_, hint, hfield⟩
  · intro i
    exact Fin.cases hv (closureProjectionCoordinates_homogeneous b hb) i
  · rfl

end

open MvPolynomial Matrix

theorem exists_fixed_coordinate_center_row_witness
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [Infinite L]
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ (B : Matrix (Fin (m + 2)) (Fin (n + 1)) K)
      (A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) K),
      LinearIndependent K B.row ∧ LinearIndependent K A.row ∧
      (∀ i, A i 0 = 0) ∧
      Submodule.span K (Set.range A.row) = B.mulVecLin.ker ∧
      (∀ p ∈ projectiveIdealZeroLocus ((projectiveClosureIdeal I).map (map (algebraMap K L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap K L)).row)) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I) (chowProjectionForms B)).IsIntegral ∧
      projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I) (chowProjectionForms B) = ⊤ := by
  classical
  obtain ⟨a, ha, hali, ha0, hint, hfield⟩ :=
    exists_independent_fixed_coordinate_closure_projection I hmn d hdimdeg
  obtain ⟨c, hc⟩ := homogeneous_linear_forms_coefficient_representation a ha
  let B : Matrix (Fin (m + 2)) (Fin (n + 1)) K := fun i j => c (i,j)
  have hBa : chowProjectionForms B = a := hc
  let T : (Fin (n + 1) → K) →ₗ[K] MvPolynomial (Fin (n + 1)) K :=
    (Pi.basisFun K (Fin (n + 1))).constr K X
  have hT (i) : T (B.row i) = a i := by
    simpa [T, linearForm, smul_eq_C_mul] using congrFun hBa i
  have hBli : LinearIndependent K B.row := by
    apply LinearIndependent.of_comp T
    simpa only [Function.comp_def, hT] using hali
  have hdimker : Module.finrank K B.mulVecLin.ker = n - m - 1 := by
    have hh := B.mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hBli.mulVec_surjective, finrank_top,
      Module.finrank_fin_fun, Module.finrank_fin_fun] at hh
    omega
  obtain ⟨A, hAli, hker⟩ := exists_submodule_basis_matrix B.mulVecLin.ker hdimker
  have hintB :
      (projectionCoordinateMap (projectiveClosureIdeal I) (chowProjectionForms B)).IsIntegral :=
    hBa.symm ▸ hint
  refine ⟨B, A, hBli, hAli, ?_, hker, ?_, hintB, hBa.symm ▸ hfield⟩
  · intro i
    have hz : B *ᵥ A.row i = 0 :=
      hker.le (Submodule.subset_span (Set.mem_range_self i))
    have hh : eval (A.row i) (a 1) = 0 := by
      rw [← hBa, chowProjectionForms_eval]
      exact congrFun hz 1
    rw [ha0, eval_X] at hh
    exact hh
  · have hkerL := matrix_rows_map_span_le_kernel (algebraMap K L) A B hker.le
    intro p hp hmem
    have hnon := homogeneous_integral_projection_geometric_no_base_point
      (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I)
      (chowProjectionForms B) (chowProjectionForms_homogeneous B) hintB p hp
    apply hnon
    have hz : (B.map (algebraMap K L)) *ᵥ p.rep = 0 := hkerL hmem
    funext i
    have hh := congrFun hz i
    simpa only [linearForm, map_sum, map_mul, aeval_C, aeval_X,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] using hh

end
end CCDN
