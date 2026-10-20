module

public import AffineCurveCounting.ProjectiveChowEquation
public import AffineCurveCounting.ProjectiveClosureRecovery

/-! An irreducible equation with the exact projective incidence criterion
is a generator of the actual chart incidence ideal. This lets degree
computations apply to any constructed projective Chow equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem chowIncidenceIdeal_eq_span_of_projective_equation
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : Irreducible F)
    (hzero : ∀ U, eval U F = 0 ↔
      U ∈ projectiveChowIncidenceLocus r (projectiveClosureIdeal I)) :
    chowIncidenceIdeal r I = Ideal.span {F} := by
  have he : projectiveChowIncidenceLocus r (projectiveClosureIdeal I) =
      MvPolynomial.zeroLocus K (Ideal.span {F}) := by
    ext U
    rw [← hzero U,zeroLocus_span]
    simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,forall_eq,aeval_eq_eval]
  rw [chowIncidenceIdeal_eq_projective_vanishingIdeal,he,
    vanishingIdeal_zeroLocus_eq_radical]
  exact ((Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime).radical

theorem chowIncidenceIdeal_chart_eq_span_of_projective_equation
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (hX : X 0 ∉ J)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : Irreducible F)
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J) :
    chowIncidenceIdeal r (projectiveChartIdeal J) = Ideal.span {F} := by
  apply chowIncidenceIdeal_eq_span_of_projective_equation (projectiveChartIdeal J) F hF
  intro U
  rw [projectiveClosureIdeal_chartIdeal_eq J hJ hX]
  exact hzero U

end
end AffineCurveCounting
