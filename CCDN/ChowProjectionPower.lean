module

public import CCDN.ChowLinearSpecialization
public import CCDN.ChowPolynomialPower
public import CCDN.IntegralProjectionHilbert
public import CCDN.PolynomialPredicates

/-! The geometric power criterion for the restriction of a Chow
incidence equation along a linear projection. Meeting the center forces the
restriction to vanish identically; a disjoint center gives precisely a scalar
power of an image equation. -/

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

/-- The image incidence criterion is derived from the linear map and
its disjoint center. -/
theorem chowLinearSubstitution_same_zeros_as_image
    {K : Type*} [Field K] [IsAlgClosed K] {n s r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
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

end
end CCDN
