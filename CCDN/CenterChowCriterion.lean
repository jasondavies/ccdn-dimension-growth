module

public import CCDN.UniversalCenterChowRestriction
public import CCDN.ChowProjectionCriterion

/-! The actual Chow restriction for centers represented by independent rows.
A source equation and its universal Plücker coefficient family are constructed
before the center is selected. Nonzero specialization detects disjointness;
for disjoint centers it is a scalar power of the actual image's equation.
The identification of Chow degree with geometric degree is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Source Chow data, minor enumeration, coefficient homogeneity and the
actual geometric restriction criterion are constructed from the source ideal.
Neither an image equation, a chart, nor an equality of zero loci is supplied. -/
theorem exists_center_chow_restriction
    {K : Type*} [Field K] [IsAlgClosed K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hr : r + 2 ≤ n + 2) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
      (δ : Fin (m + 1) → ℕ) (s : ℕ)
      (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2))),
      Irreducible F ∧ (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      (∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) ∧
      (∀ a, ((universalCenterChowMap e F).coeff a).IsHomogeneous F.totalDegree) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 2)) K, LinearIndependent K A.row →
        let R := map (eval (fun c : Fin r ↪ Fin (n + 2) => (A.submatrix id c).det))
          (universalCenterChowMap e F)
        (R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus J,
          p.rep ∉ Submodule.span K (Set.range A.row)) ∧
        ((∀ p ∈ projectiveIdealZeroLocus J,
          p.rep ∉ Submodule.span K (Set.range A.row)) →
          ∃ (G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) K)
            (ε : Fin (m + 1) → ℕ) (c : K) (k : ℕ),
            Irreducible G ∧ c ≠ 0 ∧ 0 < k ∧
            (∀ i, G.IsWeightedHomogeneous (chowRowWeight i) (ε i)) ∧
            (∀ U, eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1)
              (chowProjectionImageIdeal J (centerMinorProjectionMatrix A e))) ∧
            R = C c * G ^ k ∧ R.totalDegree = F.totalDegree ∧
            (Irreducible R ↔ F.totalDegree = G.totalDegree)) := by
  classical
  obtain ⟨F, δ, hF, hδ, hFzero⟩ := exists_projective_chow_equation_without_chart J hJ hdim
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  have hhom : F.IsHomogeneous F.totalDegree := by
    have hh := chow_rows_homogeneous_total_degree F δ hδ
    rw [hh.totalDegree hF.ne_zero]
    exact hh
  refine ⟨F, δ, s, e, hF, hδ, hFzero,
    universalCenterChowMap_coefficient_homogeneous e F hhom, ?_⟩
  intro A hA
  dsimp only
  rw [universalCenterChowMap_specialize]
  have hcenteriff : (∀ p ∈ projectiveIdealZeroLocus J,
      centerMinorProjectionMatrix A e *ᵥ p.rep ≠ 0) ↔
      ∀ p ∈ projectiveIdealZeroLocus J, p.rep ∉ Submodule.span K (Set.range A.row) := by
    constructor
    · intro h p hp hspan
      apply h p hp
      change p.rep ∈ (centerMinorProjectionMatrix A e).mulVecLin.ker
      rwa [centerMinorProjectionMatrix_ker A hA e]
    · exact centerMinorProjectionMatrix_disjoint J A hA e
  refine ⟨(chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdim _ F hFzero).trans
    hcenteriff, ?_⟩
  intro hcenter
  have hdisjoint := hcenteriff.mpr hcenter
  let P := chowProjectionImageIdeal J (centerMinorProjectionMatrix A e)
  have : P.IsPrime := RingHom.ker_isPrime
    (projectionCoordinateMap J (chowProjectionForms (centerMinorProjectionMatrix A e))).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ _ hdisjoint
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨G, ε, hG, hε, hGzero⟩ := exists_projective_chow_equation_without_chart P
    (chowProjectionImageIdeal_homogeneous J hJ _) hPdim
  have hzero := chowLinearSubstitution_same_zeros_as_image J hJ _ hdisjoint F G hFzero hGzero
  obtain ⟨c, k, hc, hk, hpow⟩ := polynomial_eq_scalar_pow_of_same_zeros G
    (chowLinearSubstitution (centerMinorProjectionMatrix A e) F) hG hzero
  have hR : chowLinearSubstitution (centerMinorProjectionMatrix A e) F ≠ 0 := by
    rw [hpow]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero k hG.ne_zero)
  have hdegree := chowLinearSubstitution_totalDegree_of_ne_zero _ F hF.ne_zero δ hδ hR
  refine ⟨G, ε, c, k, hG, hc, hk, hε, hGzero, hpow, hdegree, ?_⟩
  rw [← hdegree]
  exact irreducible_iff_degree_eq_of_same_zeros G _ hG hzero

end
end CCDN
