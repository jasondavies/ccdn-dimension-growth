module

public import CCDN.Center.ProjectiveChowWithoutChart
public import CCDN.Center.HomogeneousPermutationBaseChange
public import CCDN.Algebra.PolynomialPredicates
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
  obtain ⟨j,hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J (by omega)
  let e := Equiv.swap 0 j
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  let : (J'.map (map (algebraMap K L))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime J e
  have hJ' := projectivePermutedIdeal_homogeneous J hJ e
  have hX : X 0 ∉ J' := by
    change X 0 ∉ projectivePermutedIdeal J e
    rw [mem_projectivePermutedIdeal, rename_X]
    simpa only [e, Equiv.swap_apply_left] using hj
  have hp := projectivePermutedIdeal_filteredHilbertPolynomial J e
  have hdim' : (filteredHilbertPolynomial J').natDegree = m + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  obtain ⟨d,_,_,hdegree⟩ := filteredHilbertPolynomial_positive_multiplicity J'
    (Ideal.IsPrime.ne_top ‹J'.IsPrime›)
  obtain ⟨hm,_⟩ := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX m d hdim'
    (by simpa only [hdim'] using hdegree)
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
