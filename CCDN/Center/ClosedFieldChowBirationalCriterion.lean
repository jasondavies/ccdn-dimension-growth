/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ImageFractionField
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
    (hF : IsProjectiveChowEquation J F (fun _ => d))
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    Irreducible (chowLinearSubstitution A F) ↔
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J))
        J (chowProjectionForms A) = ⊤ := by
  let P := chowProjectionImageIdeal J A
  let R := chowLinearSubstitution A F
  have : P.IsPrime :=
    RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdimdeg.natDegree_eq
  obtain ⟨e,_,hPdimdeg⟩ :=
    exists_hasAffineDimensionDegree P (Ideal.IsPrime.ne_top ‹P.IsPrime›) hPdim
  obtain ⟨G,⟨hG,_,hGzero⟩,hGdegree⟩ := exists_projective_chow_exact_degree P
    (chowProjectionImageIdeal_homogeneous J hJ A) e hPdimdeg
  have hRne : R ≠ 0 :=
    (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdimdeg.natDegree_eq A F
      hF.eval_eq_zero_iff).mpr hcenter
  have hRdegree : R.totalDegree = (m + 1) * d :=
    (chowLinearSubstitution_totalDegree_of_ne_zero A F hF.irreducible.ne_zero (fun _ => d)
      hF.row_homogeneous hRne).trans
      (chow_uniform_row_degree_totalDegree F hF.irreducible.ne_zero d hF.row_homogeneous)
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G
    hF.eval_eq_zero_iff hGzero
  have hir := irreducible_iff_degree_eq_of_same_zeros G R hG hsame
  rw [hRdegree,hGdegree,Nat.mul_left_cancel_iff (by omega : 0 < m + 1)] at hir
  have hfield := homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J))
    J hJ (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint
  change (filteredHilbertPolynomial P).leadingCoeff =
    (filteredHilbertPolynomial J).leadingCoeff ↔ _ at hfield
  have hcoeff : (filteredHilbertPolynomial P).leadingCoeff =
      (filteredHilbertPolynomial J).leadingCoeff ↔ e = d := by
    rw [hPdimdeg.leadingCoeff_eq,hdimdeg.leadingCoeff_eq,
      div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)]
    exact Nat.cast_inj
  exact hir.trans ((eq_comm.trans hcoeff.symm).trans hfield)

end
end CCDN
