module

public import CCDN.ChowProjectionPower
public import CCDN.ProjectiveChowWithoutChart
public import CCDN.ChowTotalDegree
public import CCDN.WeightedHomogeneousEvaluation
public import CCDN.PolynomialPredicates

/-! Projection restrictions without chosen charts. A disjoint center preserves
every block degree of the source equation; its restriction is a scalar power
of the constructed image equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem chowLinearSubstitution_row_homogeneous
    {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin r)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    (chowLinearSubstitution A F).IsWeightedHomogeneous (chowRowWeight i) d := by
  have ha (q : Fin r × Fin (n + 1)) :
      (∑ k, C (A k q.2) * X (q.1,k) : MvPolynomial (Fin r × Fin (s + 1)) K).IsWeightedHomogeneous
        (chowRowWeight i) (chowRowWeight i q) := by
    apply IsWeightedHomogeneous.sum
    intro k _
    exact (isWeightedHomogeneous_X K (chowRowWeight i) (q.1,k)).C_mul (A k q.2)
  exact weighted_homogeneous_aeval (chowRowWeight i) (chowRowWeight i) _ ha F d hF

theorem chowLinearSubstitution_totalDegree_of_ne_zero
    {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : F ≠ 0)
    (δ : Fin r → ℕ) (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i))
    (hR : chowLinearSubstitution A F ≠ 0) :
    (chowLinearSubstitution A F).totalDegree = F.totalDegree := by
  have hRhom := chow_rows_homogeneous_total_degree (chowLinearSubstitution A F) δ
    (fun i => chowLinearSubstitution_row_homogeneous A i F (δ i) (hδ i))
  exact (hRhom.totalDegree hR).trans ((chow_rows_homogeneous_total_degree F δ hδ).totalDegree hF).symm

theorem chowLinearSubstitution_ne_zero_iff_center_disjoint
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hF : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) :
    chowLinearSubstitution A F ≠ 0 ↔
      ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0 := by
  constructor
  · exact center_disjoint_of_chowLinearSubstitution_ne_zero J A F hF
  · intro hcenter
    let P := chowProjectionImageIdeal J A
    let : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
    have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
    have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
      (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
    obtain ⟨G,_,hG,_,hGzero⟩ := exists_projective_chow_equation_without_chart P
      (chowProjectionImageIdeal_homogeneous J hJ A) hPdim
    obtain ⟨c,k,hc,_,he⟩ := polynomial_eq_scalar_pow_of_same_zeros G
      (chowLinearSubstitution A F) hG
      (chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hF hGzero)
    rw [he]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero k hG.ne_zero)

/-- Both equations and their scalar-power relation are constructed from the
actual source and matrix. No source or image chart is part of the hypotheses. -/
theorem exists_chow_projection_power
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
      (G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) K)
      (δ ε : Fin (m + 1) → ℕ) (c : K) (k : ℕ),
      Irreducible F ∧ Irreducible G ∧ c ≠ 0 ∧ 0 < k ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      (∀ i, G.IsWeightedHomogeneous (chowRowWeight i) (ε i)) ∧
      (∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) ∧
      (∀ U, eval U G = 0 ↔
        U ∈ projectiveChowIncidenceLocus (m + 1) (chowProjectionImageIdeal J A)) ∧
      chowLinearSubstitution A F = C c * G ^ k ∧
      (chowLinearSubstitution A F).totalDegree = F.totalDegree ∧
      (Irreducible (chowLinearSubstitution A F) ↔ F.totalDegree = G.totalDegree) := by
  let P := chowProjectionImageIdeal J A
  let : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨F,δ,hF,hδ,hFzero⟩ := exists_projective_chow_equation_without_chart J hJ hdim
  obtain ⟨G,ε,hG,hε,hGzero⟩ := exists_projective_chow_equation_without_chart P
    (chowProjectionImageIdeal_homogeneous J hJ A) hPdim
  have hzero := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hFzero hGzero
  obtain ⟨c,k,hc,hk,hpow⟩ := polynomial_eq_scalar_pow_of_same_zeros G
    (chowLinearSubstitution A F) hG hzero
  have hR : chowLinearSubstitution A F ≠ 0 := by
    rw [hpow]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero k hG.ne_zero)
  have hdegree := chowLinearSubstitution_totalDegree_of_ne_zero A F hF.ne_zero δ hδ hR
  refine ⟨F,G,δ,ε,c,k,hF,hG,hc,hk,hδ,hε,hFzero,hGzero,hpow,hdegree,?_⟩
  rw [← hdegree]
  exact irreducible_iff_degree_eq_of_same_zeros G _ hG hzero

end
end CCDN
