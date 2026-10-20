module

public import CCDN.IncidenceDeterminantCertificate
public import CCDN.IrrelevantPowerCertificate
public import CCDN.ProjectiveChowIncidence

/-! Closedness of the actual projective hyperplane incidence image, proved by
finite homogeneous coefficient matrices. Empty fibers produce a determinant
which is nonzero there and vanishes at every tuple with a projective intersection.
No closed-image or geometric projection hypothesis is supplied. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma projectiveChowIncidenceLocus_iff_cone {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (U : Fin r × Fin (n + 1) → K) :
    U ∈ projectiveChowIncidenceLocus r J ↔
      ∃ x : Fin (n + 1) → K, x ≠ 0 ∧ (∀ f ∈ J, eval x f = 0) ∧
        ∀ i, ∑ j, U (i,j) * x j = 0 := by
  classical
  constructor
  · rintro ⟨p, hp, hrel⟩
    exact ⟨p.rep, p.rep_nonzero, projectiveIdealZeroLocus_rep hp, hrel⟩
  · rintro ⟨x, hx, hxJ, hrel⟩
    let p := Projectivization.mk K x hx
    refine ⟨p, ?_, ?_⟩
    · intro v hv he f hf
      conv_lhs => rw [← sum_homogeneousComponent f]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro M _
      exact (homogeneous_eval_zero_iff_projective_eq
        (homogeneousComponent_isHomogeneous M f) hv hx he).mpr (hxJ _ (hJ f hf M))
    · intro i
      rw [← incidenceLinearForm_eval]
      exact (homogeneous_eval_zero_iff_projective_eq
        (incidenceLinearForm_homogeneous U i) p.rep_nonzero hx p.mk_rep).mpr
        ((incidenceLinearForm_eval U i x).trans (hrel i))

/-- Every tuple outside the actual projective incidence image has a polynomial
separator which is normalized to one there. -/
theorem exists_polynomial_separator_of_not_projective_incidence
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (U : Fin r × Fin (n + 1) → K) (hU : U ∉ projectiveChowIncidenceLocus r J) :
    ∃ D : MvPolynomial (Fin r × Fin (n + 1)) K,
      eval U D = 1 ∧ D ∈ vanishingIdeal K (projectiveChowIncidenceLocus r J) := by
  classical
  let A := J ⊔ Ideal.span (Set.range (incidenceLinearForm U))
  have hzero : ∀ x ∈ MvPolynomial.zeroLocus K A, x = 0 := by
    intro x hx
    by_contra hx0
    apply hU
    apply (projectiveChowIncidenceLocus_iff_cone J hJ U).mpr
    refine ⟨x, hx0, ?_, ?_⟩
    · intro f hf
      simpa only [aeval_eq_eval] using hx f ((le_sup_left : J ≤ A) hf)
    · intro i
      have hmem : incidenceLinearForm U i ∈ A :=
        (le_sup_right : Ideal.span (Set.range (incidenceLinearForm U)) ≤ A)
          (Ideal.subset_span ⟨i, rfl⟩)
      simpa only [aeval_eq_eval, incidenceLinearForm_eval] using hx _ hmem
  obtain ⟨M, hM, hpower⟩ :=
    exists_positive_irrelevant_power_le_of_zero_locus_subset_origin A hzero
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  obtain ⟨D, hDU, hD⟩ := exists_incidence_determinant_certificate J hJ U (t := t) (by
    intro e
    apply hpower
    apply (monomial_mem_pow_idealOfVars_iff (t + 1) _ (one_ne_zero : (1 : K) ≠ 0)).mpr
    exact (homogeneousMonomials_degree n (t + 1) e).ge)
  refine ⟨D, hDU, ?_⟩
  intro V hV
  exact hD V ((projectiveChowIncidenceLocus_iff_cone J hJ V).mp hV)

/-- The incidence image is closed: every point annihilating its vanishing ideal
is represented by an actual nonzero intersection vector. -/
theorem projectiveChowIncidenceLocus_zeroLocus_vanishingIdeal
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J) :
    MvPolynomial.zeroLocus K (vanishingIdeal K (projectiveChowIncidenceLocus r J)) =
      projectiveChowIncidenceLocus r J := by
  ext U
  constructor
  · intro hU
    by_contra hnot
    obtain ⟨D, hDU, hD⟩ := exists_polynomial_separator_of_not_projective_incidence J hJ U hnot
    have hz := hU D hD
    rw [aeval_eq_eval, hDU] at hz
    exact one_ne_zero hz
  · intro hU f hf
    exact hf U hU

/-- Exact projective incidence, including infinity points, is the zero locus
of the actual affine elimination ideal. -/
theorem chowIncidenceIdeal_zeroLocus_eq_projective_incidence
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    MvPolynomial.zeroLocus K (chowIncidenceIdeal r I) =
      projectiveChowIncidenceLocus r (projectiveClosureIdeal I) := by
  rw [chowIncidenceIdeal_eq_projective_vanishingIdeal]
  exact projectiveChowIncidenceLocus_zeroLocus_vanishingIdeal _
    (projectiveClosureIdeal_homogeneous I)

end
end CCDN
