/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Center.GeometricProjectiveCurveProjection
import CCDN.Center.HomogeneousPermutationBaseChange
import CCDN.Center.ProjectiveChowEquation
import CCDN.Center.ProjectiveClosureRecovery
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Center.WeightedHomogeneousTransform
import CCDN.Hilbert.HomogeneousPrimeComponents
/-! A geometrically integral homogeneous prime ideal has an incidence equation
defined over its original coefficient field, without a prescribed chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_geometric_projective_chow_without_chart
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {n m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ),
      Irreducible F ∧ Irreducible (map (algebraMap K L) F) ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      ∀ U, eval U (map (algebraMap K L) F) = 0 ↔
        U ∈ projectiveChowIncidenceLocus (m + 1) (J.map (map (algebraMap K L))) := by
  classical
  obtain ⟨e, hJ', hX, hp⟩ := exists_projectivePermutedIdeal_chart J hJ (by omega)
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  let : (J'.map (map (algebraMap K L))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime J e
  have hdim' : (filteredHilbertPolynomial J').natDegree = m + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  obtain ⟨d,_,_,hdegree⟩ := filteredHilbertPolynomial_positive_multiplicity J'
    (Ideal.IsPrime.ne_top ‹J'.IsPrime›)
  obtain ⟨hm,_⟩ := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX m d
    ⟨hdim', by simpa only [hdim'] using hdegree⟩
  let : ((projectiveChartIdeal J').map (map (algebraMap K L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime J' hX
  obtain ⟨F,δ,hF,_,hδ,hFL,hzero⟩ := exists_geometric_projective_chow_incidence_equation
    (L := L) (projectiveChartIdeal J') hm
  let ρ := chowColumnPermutation (r := m + 1) e
  refine ⟨rename ρ F,δ,?_,?_,?_,?_⟩
  · exact (MulEquiv.irreducible_iff (renameEquiv K ρ)).mpr hF
  · rw [map_rename]
    exact (MulEquiv.irreducible_iff (renameEquiv L ρ)).mpr hFL
  · intro i
    apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight i) ρ _ F (δ i) (hδ i)
    intro q
    rfl
  · intro U
    rw [map_rename, eval_rename, hzero, projectiveClosureIdeal_chartIdeal_eq J' hJ' hX]
    change U ∘ chowColumnPermutation e ∈ projectiveChowIncidenceLocus (m + 1)
      ((projectivePermutedIdeal J e).map (map (algebraMap K L))) ↔ _
    rw [projectivePermutedIdeal_scalar_extension]
    exact projectiveChowIncidenceLocus_permuted (J.map (map (algebraMap K L)))
      (homogeneous_ideal_scalar_extension J hJ) e U

end
end CCDN
