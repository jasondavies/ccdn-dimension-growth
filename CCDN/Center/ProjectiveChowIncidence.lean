/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowPivotParametrization
public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Center.ChowIncidenceLocus
import CCDN.Algebra.LinearForm
import CCDN.Algebra.ProjectiveClosureDegree
import CCDN.Center.PrimeOpenVanishing
/-! The affine incidence elimination ideal is the vanishing ideal of the
full projective hyperplane incidence locus, including points at
infinity. This asserts equality of vanishing ideals, not closedness of the
incidence image. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def projectiveChowIncidenceLocus {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Set (Fin r × Fin (n + 1) → K) :=
  {U | ∃ p ∈ projectiveIdealZeroLocus J,
    ∀ i, ∑ j, U (i,j) * p.rep j = 0}

theorem chowIncidenceLocus_subset_projectiveClosureIncidence
    {K : Type*} [Field K] {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    chowIncidenceLocus r I ⊆ projectiveChowIncidenceLocus r (projectiveClosureIdeal I) := by
  intro U hU
  obtain ⟨a, ha, hrel⟩ := hU
  let p := affineProjectivePoint a
  refine ⟨p, (projectiveClosureIdeal_chart_point I a).mpr ha, ?_⟩
  intro i
  let f : MvPolynomial (Fin (n + 1)) K := linearForm fun j => U (i,j)
  have hf : f.IsHomogeneous 1 := linearForm_isHomogeneous _
  have heval (x : Fin (n + 1) → K) : eval x f = ∑ j, U (i,j) * x j := eval_linearForm _ x
  have hz : eval (Fin.cons 1 a) f = 0 := (heval _).trans (hrel i)
  have hpz := (homogeneous_eval_zero_iff_projective_eq hf p.rep_nonzero
    (affineCoordinateVector_ne_zero a) p.mk_rep).mpr hz
  rwa [heval] at hpz

lemma eval_chowPivot_substitution {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K)
    (R : MvPolynomial (Fin r × Fin (n + 1)) K) (x : Fin (n + 1) → K) :
    eval x (aeval (chowPivotPolynomials j v) R) =
      eval (chowPivotCoefficients j x v) R := by
  change eval x (eval₂ C (chowPivotPolynomials j v) R) = _
  rw [← eval_assoc]
  congr 1
  congr 1
  funext q
  exact chowPivotPolynomials_eval j v x q

/-- Clearing a pivot coordinate gives an equation in the closure
ideal. Density is proved using its nonzero standard coordinate and primeness. -/
theorem chowPivot_substitution_mem_projectiveClosure
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (R : MvPolynomial (Fin r × Fin (n + 1)) K) (hR : R ∈ chowIncidenceIdeal r I)
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K) :
    aeval (chowPivotPolynomials j v) R ∈ projectiveClosureIdeal I := by
  apply mem_prime_ideal_of_vanishing_on_principal_open
    (projectiveClosureIdeal I) (X 0) _ (projectiveClosureIdeal_not_X_zero I)
  intro x hx hx0
  rw [eval_X] at hx0
  rw [eval_chowPivot_substitution]
  let a : Fin n → K := fun k => x k.succ / x 0
  have ha : ∀ f ∈ I, eval a f = 0 := projectiveClosure_cone_chart_zero I x hx hx0
  have hinc (i : Fin r) :
      ∑ k, chowPivotCoefficients j x v (i,k) * (Fin.cons 1 a : Fin (n + 1) → K) k = 0 := by
    have hrel := chowPivotCoefficients_relation j x v i
    apply (mul_right_cancel₀ hx0)
    rw [zero_mul, Finset.sum_mul]
    convert hrel using 1
    apply Finset.sum_congr rfl
    intro k _
    refine Fin.cases ?_ (fun t => ?_) k
    · simp
    · simp only [Fin.cons_succ, a]
      field_simp
  rw [← chowIncidentCoefficients_reconstruct a _ hinc]
  exact (mem_chowIncidenceIdeal_iff I R).mp hR a ha _

/-- The full projective incidence has exactly the constructed affine
elimination ideal as vanishing ideal. No exclusion of infinity points is made. -/
theorem chowIncidenceIdeal_eq_projective_vanishingIdeal
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    chowIncidenceIdeal r I = vanishingIdeal K
      (projectiveChowIncidenceLocus r (projectiveClosureIdeal I)) := by
  apply le_antisymm
  · intro R hR U hU
    obtain ⟨p, hp, hrel⟩ := hU
    obtain ⟨j, hj⟩ : ∃ j, p.rep j ≠ 0 := by
      by_contra! h
      exact p.rep_nonzero (funext h)
    let v : Fin r × Fin (n + 1) → K := fun q => U q / p.rep j
    have hmem := chowPivot_substitution_mem_projectiveClosure I R hR j v
    have hz := projectiveIdealZeroLocus_rep hp _ hmem
    rw [eval_chowPivot_substitution, chowPivotCoefficients_reconstruct j p.rep hj U hrel] at hz
    simpa only [aeval_eq_eval] using hz
  · rw [chowIncidenceIdeal_eq_vanishingIdeal]
    exact MvPolynomial.vanishingIdeal_anti_mono
      (chowIncidenceLocus_subset_projectiveClosureIncidence I)

end
end CCDN
