/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.GeometricProjectiveCurveProjection
public import CCDN.Center.ProjectiveChowEquation
public import CCDN.Center.ProjectiveIncidencePermutation
public import CCDN.Counterexample.OriginProjectivePoint
public import CCDN.Center.WeightedHomogeneousTransform
public import CCDN.Algebra.PolynomialPredicates
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
      Irreducible F ∧ (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J := by
  classical
  obtain ⟨j,hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J (by omega)
  let e := Equiv.swap 0 j
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  have hJ' := projectivePermutedIdeal_homogeneous J hJ e
  have hp := projectivePermutedIdeal_filteredHilbertPolynomial J e
  have hX : X 0 ∉ J' := by
    change X 0 ∉ projectivePermutedIdeal J e
    rw [mem_projectivePermutedIdeal, rename_X]
    simpa only [e, Equiv.swap_apply_left] using hj
  obtain ⟨d,_,_,hdegree⟩ := filteredHilbertPolynomial_positive_multiplicity J'
    (Ideal.IsPrime.ne_top ‹J'.IsPrime›)
  have hdim' : (filteredHilbertPolynomial J').natDegree = m + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  obtain ⟨F,δ,hF,hδ,hzero⟩ := exists_homogeneous_prime_projective_chow_equation
    J' hJ' hX ⟨hdim', by simpa only [hdim'] using hdegree⟩
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
