module

public import CCDN.ChowLinearSpecialization
public import CCDN.ChowPolynomialPower
public import CCDN.IntegralProjectionHilbert

/-! The geometric power criterion for the actual restriction of a Chow
incidence equation along a linear projection. Meeting the center forces the
restriction to vanish identically; a disjoint center gives precisely a scalar
power of an actual image equation. Exact Chow block degrees are not assumed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- A center point on the source lies on every pulled-back hyperplane, so the
restricted Chow polynomial is identically zero. -/
theorem chowLinearSubstitution_eq_zero_of_center_meets
    {K : Type*} [Field K] [Infinite K] {n s r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K)
    (hF : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J)
    (hcenter : ∃ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep = 0) :
    chowLinearSubstitution A F = 0 := by
  obtain ⟨p, hp, hAp⟩ := hcenter
  apply MvPolynomial.funext
  intro U
  rw [map_zero, chowLinearSubstitution_eval]
  apply (hF _).mpr
  refine ⟨p, hp, ?_⟩
  intro i
  rw [chowPullbackCoefficients_relation, hAp]
  simp

lemma center_disjoint_of_chowLinearSubstitution_ne_zero
    {K : Type*} [Field K] [Infinite K] {n s r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K)
    (hF : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J)
    (hne : chowLinearSubstitution A F ≠ 0) :
    ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0 := by
  intro p hp hAp
  exact hne (chowLinearSubstitution_eq_zero_of_center_meets J A F hF ⟨p, hp, hAp⟩)

/-- The image incidence criterion is derived from the actual linear map and
its disjoint center, rather than supplied as an equality of zero loci. -/
theorem chowLinearSubstitution_same_zeros_as_image
    {K : Type*} [Field K] [IsAlgClosed K] {n s r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K)
    (G : MvPolynomial (Fin r × Fin (s + 1)) K)
    (hF : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J)
    (hG : ∀ U, eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus r (chowProjectionImageIdeal J A)) :
    ∀ U, eval U (chowLinearSubstitution A F) = 0 ↔ eval U G = 0 := by
  intro U
  rw [chowLinearSubstitution_eval, hF, hG]
  exact chow_projection_incidence_iff J hJ A hcenter U

/-- With explicit nonempty source and image charts, both Chow equations are
constructed internally. The restricted source equation is a positive scalar
power of the image equation. No Chow equations or equal-zero-set premise are
supplied. The absence of a degree formula is intentional at this stage. -/
theorem exists_chow_projection_power_with_charts
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (hX : X 0 ∉ J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hA : chowProjectionForms A 0 ∉ J)
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
      (Irreducible (chowLinearSubstitution A F) ↔
        (chowLinearSubstitution A F).totalDegree = G.totalDegree) := by
  let P := chowProjectionImageIdeal J A
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hPhom := chowProjectionImageIdeal_homogeneous J hJ A
  have hPX : X 0 ∉ P := by
    intro h
    apply hA
    have hh := (mem_projectionCoordinateMap_ker J (chowProjectionForms A) (X 0)).mp h
    simpa only [aeval_X] using hh
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨d, _, _, hd⟩ := filteredHilbertPolynomial_positive_multiplicity J
    (Ideal.IsPrime.ne_top ‹J.IsPrime›)
  obtain ⟨e, _, _, he⟩ := filteredHilbertPolynomial_positive_multiplicity P
    (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  obtain ⟨F, δ, hF, hδ, hFzero⟩ := exists_homogeneous_prime_projective_chow_equation
    J hJ hX hdim (by simpa only [hdim] using hd)
  obtain ⟨G, ε, hG, hε, hGzero⟩ := exists_homogeneous_prime_projective_chow_equation
    P hPhom hPX hPdim (by simpa only [hPdim] using he)
  have hzero := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hFzero hGzero
  obtain ⟨c, k, hc, hk, hpow⟩ := polynomial_eq_scalar_pow_of_same_zeros G
    (chowLinearSubstitution A F) hG hzero
  exact ⟨F, G, δ, ε, c, k, hF, hG, hc, hk, hδ, hε, hFzero, hGzero, hpow,
    irreducible_iff_degree_eq_of_same_zeros G _ hG hzero⟩

end
end CCDN
