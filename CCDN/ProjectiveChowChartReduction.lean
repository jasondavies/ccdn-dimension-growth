module

public import CCDN.ProjectiveChowGenerator
public import CCDN.ProjectiveChowWithoutChart

/-! Any projective Chow equation can be moved to a nonempty affine chart
without changing its block degrees or total degree. The chart has the
actual dimension and multiplicity of the projective source. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projective_chow_chart_reduction
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (hF : Irreducible F)
    (δ : Fin (m + 1) → ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i))
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) :
    ∃ (I : Ideal (MvPolynomial (Fin (n + 1)) K))
      (G : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K),
      I.IsPrime ∧ (filteredHilbertPolynomial I).natDegree = m ∧
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial ∧
      Irreducible G ∧ chowIncidenceIdeal (m + 1) I = Ideal.span {G} ∧
      (∀ i, G.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      G.totalDegree = F.totalDegree := by
  classical
  obtain ⟨j,hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J (by omega)
  let e := Equiv.swap 0 j
  let J' := projectivePermutedIdeal J e
  let : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  have hJ' := projectivePermutedIdeal_homogeneous J hJ e
  have hp := projectivePermutedIdeal_filteredHilbertPolynomial J e
  have hX : X 0 ∉ J' := by
    change X 0 ∉ projectivePermutedIdeal J e
    rw [mem_projectivePermutedIdeal,rename_X]
    simpa only [e,Equiv.swap_apply_left] using hj
  have hm' : (filteredHilbertPolynomial J').natDegree = m + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  have hd' : (filteredHilbertPolynomial J').leadingCoeff = (d : ℚ) / (m + 1).factorial :=
    (congrArg Polynomial.leadingCoeff hp).trans hdegree
  obtain ⟨hmI,hdI⟩ := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX m d hm' hd'
  let ρ := chowColumnPermutation (r := m + 1) e
  let G := rename ρ.symm F
  have hG : Irreducible G :=
    (MulEquiv.irreducible_iff (renameEquiv K ρ.symm)).mpr hF
  have hzG (U) : eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J' := by
    rw [show G = rename ρ.symm F from rfl,eval_rename,hzero]
    have hh := projectiveChowIncidenceLocus_permuted J hJ e (U ∘ ρ.symm)
    have he : (U ∘ ρ.symm) ∘ chowColumnPermutation e = U := by
      funext q
      exact congrArg U (ρ.symm_apply_apply q)
    rw [he] at hh
    exact hh.symm
  refine ⟨projectiveChartIdeal J',G,inferInstance,hmI,hdI,hG,
    chowIncidenceIdeal_chart_eq_span_of_projective_equation J' hJ' hX G hG hzG,?_,?_⟩
  · intro i
    apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight i) ρ.symm _ F (δ i) (hδ i)
    intro q
    rfl
  · exact totalDegree_renameEquiv ρ.symm F

end
end CCDN
