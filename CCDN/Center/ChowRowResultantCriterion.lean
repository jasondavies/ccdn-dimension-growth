/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.CenterResultantForms
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.BlockResultantIrreducibility
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowProjectionPower
import CCDN.Center.ProjectiveChowWithoutChart
import CCDN.Projection.IntegralProjectionHilbert
/-! The selected-row derivative resultant detects irreducibility of a
Chow restriction. A nonzero restriction is a power of the constructed image
Chow equation, so separability is exactly the absence of a repeated power. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem chowRowResultant_ne_zero_iff_irreducible
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J)
    (i : Fin (m + 1)) (d : ℕ) (hd : 0 < d)
    (hrow : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    derivativeResultant (genericBlockLine (chowRowBlock i) (chowLinearSubstitution A F)) d ≠ 0 ↔
      Irreducible (chowLinearSubstitution A F) := by
  let R := chowLinearSubstitution A F
  by_cases hR : R = 0
  · change derivativeResultant (genericBlockLine (chowRowBlock i) R) d ≠ 0 ↔ Irreducible R
    rw [hR,map_zero,derivativeResultant_zero d hd]
    simp
  have hcenter := (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdim A F hzero).mp hR
  let P := chowProjectionImageIdeal J A
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨G,_,hG,_,hGzero⟩ := exists_projective_chow_equation_without_chart P
    (chowProjectionImageIdeal_homogeneous J hJ A) hPdim
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hzero hGzero
  have hdeg : R.weightedTotalDegree (genericBlockWeight (chowRowBlock i)) = d := by
    rw [genericBlockWeight_chowRowBlock]
    exact weightedTotalDegree_of_nonzero_homogeneous _ _ d
      (chowLinearSubstitution_row_homogeneous A i F d hrow) hR
  exact genericBlockLine_derivativeResultant_irreducible_iff
    (chowRowBlock i) G R hG hsame d hd hdeg

end
end CCDN
