/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.GeometricProjectiveCurveProjection
import CCDN.Center.ProjectiveClosureRecovery
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Algebra.WeightedHomogeneousTransform
/-! Any projective Chow equation can be moved to a nonempty affine chart
without changing its block degrees or total degree. The chart has the
dimension and multiplicity of the projective source. -/

@[expose] public section
namespace CCDN
noncomputable section

section

/-! An irreducible equation with the exact projective incidence criterion
is a generator of the chart incidence ideal. This lets degree
computations apply to any constructed projective Chow equation. -/

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
    (hJ : IsHomogeneousIdeal J)
    (hX : X 0 ∉ J)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : Irreducible F)
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J) :
    chowIncidenceIdeal r (projectiveChartIdeal J) = Ideal.span {F} := by
  apply chowIncidenceIdeal_eq_span_of_projective_equation (projectiveChartIdeal J) F hF
  intro U
  rw [projectiveClosureIdeal_chartIdeal_eq J hJ hX]
  exact hzero U

end

open MvPolynomial

theorem projective_chow_chart_reduction
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ)
    (hF : IsProjectiveChowEquation J F δ) :
    ∃ (I : Ideal (MvPolynomial (Fin (n + 1)) K))
      (G : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K),
      I.IsPrime ∧ HasAffineDimensionDegree I m d ∧
      Irreducible G ∧ chowIncidenceIdeal (m + 1) I = Ideal.span {G} ∧
      (∀ i, G.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      G.totalDegree = F.totalDegree := by
  classical
  obtain ⟨e, hJ', hX, hp⟩ :=
    exists_projectivePermutedIdeal_chart J hJ (by simp [hdimdeg.natDegree_eq])
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  have hI := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX m d
    (hdimdeg.of_filteredHilbertPolynomial_eq hp)
  let ρ := chowColumnPermutation (r := m + 1) e
  let G := rename ρ.symm F
  have hG : Irreducible G :=
    (MulEquiv.irreducible_iff (renameEquiv K ρ.symm)).mpr hF.irreducible
  have hzG (U) : eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J' := by
    rw [show G = rename ρ.symm F from rfl,eval_rename,hF.eval_eq_zero_iff]
    have hh := projectiveChowIncidenceLocus_permuted J hJ e (U ∘ ρ.symm)
    have he : (U ∘ ρ.symm) ∘ chowColumnPermutation e = U := by
      funext q
      exact congrArg U (ρ.symm_apply_apply q)
    rw [he] at hh
    exact hh.symm
  refine ⟨projectiveChartIdeal J',G,inferInstance,hI,hG,
    chowIncidenceIdeal_chart_eq_span_of_projective_equation J' hJ' hX G hG hzG,?_,?_⟩
  · intro i
    apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight i) ρ.symm _ F (δ i)
      (hF.row_homogeneous i)
    intro q
    rfl
  · exact totalDegree_renameEquiv ρ.symm F

end
end CCDN
