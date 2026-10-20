module

public import CCDN.FixedCoordinateBirationalProjection
public import CCDN.FixedCoordinateGenericNormalization
public import CCDN.GeometricCenterRows

/-! Constructed finite birational centers at infinity. Every center row has
zero homogenizing coordinate; the construction includes affine dimension
zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_fixed_coordinate_center_row_witness
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [Infinite L]
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
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
    exists_independent_fixed_coordinate_closure_projection I hmn d hdim hdegree
  obtain ⟨c, hc⟩ := homogeneous_linear_forms_coefficient_representation a ha
  let B : Matrix (Fin (m + 2)) (Fin (n + 1)) K := fun i j => c (i,j)
  have hBa : chowProjectionForms B = a := hc
  let T : (Fin (n + 1) → K) →ₗ[K] MvPolynomial (Fin (n + 1)) K :=
    (Pi.basisFun K (Fin (n + 1))).constr K X
  have hT (i) : T (B.row i) = a i := by
    simpa [T, chowProjectionForms, smul_eq_C_mul] using congrFun hBa i
  have hBli : LinearIndependent K B.row := by
    apply LinearIndependent.of_comp T
    simpa only [Function.comp_def, hT] using hali
  have hdimker : Module.finrank K B.mulVecLin.ker = n - m - 1 := by
    have hh := B.mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hBli.mulVec_surjective, finrank_top,
      Module.finrank_fin_fun, Module.finrank_fin_fun] at hh
    omega
  obtain ⟨A, hAli, hker⟩ := exists_submodule_basis_matrix B.mulVecLin.ker hdimker
  have hintB : (projectionCoordinateMap (projectiveClosureIdeal I) (chowProjectionForms B)).IsIntegral :=
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
    simpa only [chowProjectionForms, map_sum, map_mul, aeval_C, aeval_X,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] using hh

end
end CCDN
