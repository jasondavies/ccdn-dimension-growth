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
import CCDN.Center.GeometricProjectiveCurveProjection
import CCDN.Center.ProjectiveChowEquation
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Algebra.WeightedHomogeneousTransform
/-! A positive-dimensional affine cone has a nonempty coordinate chart.
The projective incidence equation is constructed without a prescribed chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_projective_chow_equation_without_chart
    {K : Type*} [Field K] [IsAlgClosed K] {n m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ),
      IsProjectiveChowEquation J F δ := by
  classical
  obtain ⟨e, hJ', hX, hp⟩ := exists_projectivePermutedIdeal_chart J hJ (by omega)
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  obtain ⟨d,_,hdimdeg⟩ := exists_hasAffineDimensionDegree J' (Ideal.IsPrime.ne_top ‹J'.IsPrime›)
    ((congrArg Polynomial.natDegree hp).trans hdim)
  obtain ⟨F,δ,⟨hF,hδ,hzero⟩⟩ :=
    exists_homogeneous_prime_projective_chow_equation J' hJ' hX hdimdeg
  let ρ := chowColumnPermutation (r := m + 1) e
  refine ⟨rename ρ F, δ, ?_, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff (renameEquiv K ρ)).mpr hF
  · intro i
    apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight i) ρ _ F (δ i) (hδ i)
    intro q
    rfl
  · intro U
    rw [eval_rename, hzero]
    exact projectiveChowIncidenceLocus_permuted J hJ e U

end
end CCDN
