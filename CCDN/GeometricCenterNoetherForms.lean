module

public import CCDN.CenterChowDetector
public import CCDN.ChowProjectionBaseChange
public import CCDN.GeometricProjectiveChow
public import CCDN.PolynomialPredicates

/-! The geometric center detector is defined over the original field.
Its evaluations on rational center matrices detect the actual restrictions
over algebraic closure, including all projective points at infinity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_geometric_center_noether_forms
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hr : r + 2 ≤ n + 2) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (s : ℕ)
      (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      Irreducible (map (algebraMap K (AlgebraicClosure K)) F) ∧
      (∀ U, eval U (map (algebraMap K (AlgebraicClosure K)) F) = 0 ↔
        U ∈ projectiveChowIncidenceLocus (m + 1)
          (J.map (map (algebraMap K (AlgebraicClosure K))))) ∧
      (∀ g ∈ Φ, g.IsHomogeneous (F.totalDegree * max 1 (F.totalDegree ^ 2 - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ F.totalDegree * max 1 (F.totalDegree ^ 2 - 1)) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 2)) K, LinearIndependent K A.row →
        let good := ∃ g ∈ Φ,
          eval (fun c : Fin r ↪ Fin (n + 2) => (A.submatrix id c).det) g ≠ 0
        let AL := A.map (algebraMap K (AlgebraicClosure K))
        let JL := J.map (map (algebraMap K (AlgebraicClosure K)))
        (good ↔ Irreducible (chowLinearSubstitution (centerMinorProjectionMatrix AL e)
          (map (algebraMap K (AlgebraicClosure K)) F))) ∧
        (good → ∀ p ∈ projectiveIdealZeroLocus JL,
          p.rep ∉ Submodule.span (AlgebraicClosure K) (Set.range AL.row)) ∧
        ((∀ p ∈ projectiveIdealZeroLocus JL,
          p.rep ∉ Submodule.span (AlgebraicClosure K) (Set.range AL.row)) →
          ∃ G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) (AlgebraicClosure K),
            Irreducible G ∧
            (∀ U, eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1)
              (chowProjectionImageIdeal JL (centerMinorProjectionMatrix AL e))) ∧
            (good ↔ F.totalDegree = G.totalDegree)) := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := AlgebraicClosure K) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  obtain ⟨F, δ, hF, hFL, hδ, hFzero⟩ :=
    exists_geometric_projective_chow_without_chart (L := AlgebraicClosure K) J hJ hdim
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  have hFhom : F.IsHomogeneous F.totalDegree := by
    have hh := chow_rows_homogeneous_total_degree F δ hδ
    rw [hh.totalDegree hF.ne_zero]
    exact hh
  have hD := mv_totalDegree_pos_of_nonzero_nonunit F hF.ne_zero hF.not_isUnit
  obtain ⟨Φ, hΦhom, hΦdegree, hΦ⟩ := exists_center_noether_forms e F hD hFhom
  refine ⟨F, s, e, Φ, hFL, hFzero, hΦhom, hΦdegree, ?_⟩
  intro A hA
  dsimp only
  let AL := A.map φ
  let M := centerMinorProjectionMatrix AL e
  let R := chowLinearSubstitution M (map φ F)
  have hAL : LinearIndependent (AlgebraicClosure K) AL.row :=
    linearIndependent_matrix_rows_map φ A hA
  have hdet := hΦ A
  rw [centerChowRestriction_map] at hdet
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span (AlgebraicClosure K) (Set.range AL.row) := by
    have hh := chowLinearSubstitution_ne_zero_iff_center_disjoint JL hJL hJLdim M
      (map φ F) hFzero
    refine hh.trans ⟨?_, centerMinorProjectionMatrix_disjoint JL AL hAL e⟩
    intro h p hp hspan
    apply h p hp
    change p.rep ∈ M.mulVecLin.ker
    rwa [centerMinorProjectionMatrix_ker AL hAL e]
  refine ⟨hdet, fun hg => hcenteriff.mp (hdet.mp hg).ne_zero, ?_⟩
  intro hdisjoint
  have hdisjoint' := centerMinorProjectionMatrix_disjoint JL AL hAL e hdisjoint
  let P := chowProjectionImageIdeal JL M
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap JL (chowProjectionForms M)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint JL hJL M hdisjoint'
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq JL _ hint).trans hJLdim
  obtain ⟨G, _, hG, _, hGzero⟩ := exists_projective_chow_equation_without_chart P
    (chowProjectionImageIdeal_homogeneous JL hJL M) hPdim
  have hzero := chowLinearSubstitution_same_zeros_as_image JL hJL M hdisjoint'
    (map φ F) G hFzero hGzero
  have hRhom : R.IsHomogeneous F.totalDegree := by
    have hh := ((universalCenterChowMap_homogeneous e F hFhom).map
      (eval (fun c : Fin r ↪ Fin (n + 2) => (A.submatrix id c).det))).map φ
    rw [universalCenterChowMap_specialize, centerChowRestriction_map] at hh
    exact hh
  have hRdeg := hRhom.totalDegree (hcenteriff.mpr hdisjoint)
  refine ⟨G, hG, hGzero, hdet.trans ?_⟩
  have hh := irreducible_iff_degree_eq_of_same_zeros G R hG hzero
  rwa [hRdeg] at hh

end
end CCDN
