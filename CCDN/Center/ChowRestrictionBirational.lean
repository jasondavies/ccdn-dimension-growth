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
import CCDN.Center.GeometricProjectionHilbert
import CCDN.Center.HomogeneousProjectionBirational
import CCDN.Center.ProjectiveChowExactDegree
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDN.Hilbert.ScalarExtension
import CCDN.Projection.IntegralProjectionHilbert

/-! A disjoint projection center gives an irreducible Chow restriction
exactly when its coordinate-field extension is birational. Source
and image degrees are the proved Hilbert multiplicities. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem geometric_chow_restriction_irreducible_iff_birational
    {K : Type*} [Field K] [CharZero K] {n s m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hF : IsProjectiveChowEquation (I.map (map (algebraMap K (AlgebraicClosure K))))
      (map (algebraMap K (AlgebraicClosure K)) F) (fun _ => d))
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap K (AlgebraicClosure K)))),
      (A.map (algebraMap K (AlgebraicClosure K))) *ᵥ p.rep ≠ 0) :
    Irreducible (chowLinearSubstitution (A.map (algebraMap K (AlgebraicClosure K)))
      (map (algebraMap K (AlgebraicClosure K)) F)) ↔
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ I))
        I (chowProjectionForms A) = ⊤ := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  let J := I.map (map φ)
  let AL := A.map φ
  let FL := map φ F
  let P := chowProjectionImageIdeal J AL
  let R := chowLinearSubstitution AL FL
  have hJ := homogeneous_ideal_scalar_extension (L := L) I hI
  have hJdim : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (hasProjectiveDimensionDegree_scalar_extension hdimdeg).natDegree_eq
  have hint := projection_integral_of_geometric_center_disjoint I hI A hcenter
  have hintL := chow_projection_integral_of_center_disjoint J hJ AL hcenter
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms AL)).toRingHom
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hintL).trans hJdim
  obtain ⟨e, _, hPdimdeg⟩ :=
    exists_hasAffineDimensionDegree P (Ideal.IsPrime.ne_top ‹P.IsPrime›) hPdim
  obtain ⟨G, ⟨hG, _, hGzero⟩, hGdegree⟩ := exists_projective_chow_exact_degree P
    (chowProjectionImageIdeal_homogeneous J hJ AL) e hPdimdeg
  have hRne : R ≠ 0 :=
    (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hJdim AL FL
      hF.eval_eq_zero_iff).mpr hcenter
  have hRdegree : R.totalDegree = (m + 1) * d :=
    (chowLinearSubstitution_totalDegree_of_ne_zero AL FL hF.irreducible.ne_zero (fun _ => d)
      hF.row_homogeneous hRne).trans
      (chow_uniform_row_degree_totalDegree FL hF.irreducible.ne_zero d hF.row_homogeneous)
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ AL hcenter FL G
    hF.eval_eq_zero_iff hGzero
  have hir := irreducible_iff_degree_eq_of_same_zeros G R hG hsame
  rw [hRdegree, hGdegree, Nat.mul_left_cancel_iff (by omega : 0 < m + 1)] at hir
  have hfield := homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ I))
    I hI (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint
  change (filteredHilbertPolynomial (chowProjectionImageIdeal I A)).leadingCoeff =
    (filteredHilbertPolynomial I).leadingCoeff ↔ _ at hfield
  rw [← chowProjectionImageIdeal_hilbertPolynomial_scalar_extension (L := L) I A] at hfield
  have hcoeff : (filteredHilbertPolynomial P).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff ↔ e = d := by
    rw [hPdimdeg.leadingCoeff_eq, hdimdeg.leadingCoeff_eq,
      div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)]
    exact Nat.cast_inj
  exact hir.trans ((eq_comm.trans hcoeff.symm).trans hfield)

end
end CCDN
