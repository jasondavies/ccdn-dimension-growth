/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Center.ProjectionImageFractionField
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ChowPolynomialPower
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowProjectionPower
import CCDN.Center.ChowRowSymmetry
import CCDN.Center.HomogeneousProjectionBirational
import CCDN.Center.ProjectiveChowExactDegree
import CCDN.Projection.IntegralProjectionHilbert
/-! The Chow restriction and function-field birationality criterion
over an algebraically closed field, allowing arbitrary geometric centers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem chow_restriction_irreducible_iff_birational_over_closed_field
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hF : Irreducible F) (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d)
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    Irreducible (chowLinearSubstitution A F) ↔
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J))
        J (chowProjectionForms A) = ⊤ := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let P := chowProjectionImageIdeal J A
  let R := chowLinearSubstitution A F
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨e,_,_,he⟩ := filteredHilbertPolynomial_positive_multiplicity P
    (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  have hedegree : (filteredHilbertPolynomial P).leadingCoeff = (e : ℚ) / (m + 1).factorial := by
    simpa only [hPdim] using he
  obtain ⟨G,hG,_,hGdegree,hGzero⟩ := exists_projective_chow_exact_degree P
    (chowProjectionImageIdeal_homogeneous J hJ A) e ⟨hPdim, hedegree⟩
  have hRne : R ≠ 0 :=
    (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdim A F hzero).mpr hcenter
  have hRdegree : R.totalDegree = (m + 1) * d :=
    (chowLinearSubstitution_totalDegree_of_ne_zero A F hF.ne_zero (fun _ => d) hδ hRne).trans
      (chow_uniform_row_degree_totalDegree F hF.ne_zero d hδ)
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hzero hGzero
  have hir := irreducible_iff_degree_eq_of_same_zeros G R hG hsame
  rw [hRdegree,hGdegree,Nat.mul_left_cancel_iff (by omega : 0 < m + 1)] at hir
  have hfield := homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J))
    J hJ (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint
  change (filteredHilbertPolynomial P).leadingCoeff =
    (filteredHilbertPolynomial J).leadingCoeff ↔ _ at hfield
  have hcoeff : (filteredHilbertPolynomial P).leadingCoeff =
      (filteredHilbertPolynomial J).leadingCoeff ↔ e = d := by
    rw [hedegree,hdegree,div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)]
    exact Nat.cast_inj
  exact hir.trans ((eq_comm.trans hcoeff.symm).trans hfield)

end
end CCDN
