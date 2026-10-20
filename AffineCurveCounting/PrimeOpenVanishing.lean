module

public import AffineCurveCounting.ProjectiveClosureDegree
public import Mathlib.RingTheory.Nullstellensatz

/-! Polynomial vanishing on a nonempty principal open subset of an
integral affine variety extends to the entire variety. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem mem_prime_ideal_of_vanishing_on_principal_open
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (g f : MvPolynomial σ K) (hg : g ∉ I)
    (hvan : ∀ x : σ → K, (∀ p ∈ I, eval x p = 0) →
      eval x g ≠ 0 → eval x f = 0) : f ∈ I := by
  have hmul : g * f ∈ I := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
    intro x hx
    rw [aeval_eq_eval, eval_mul]
    by_cases hzero : eval x g = 0
    · rw [hzero, zero_mul]
    · rw [hvan x (fun p hp => by simpa only [aeval_eq_eval] using hx p hp) hzero, mul_zero]
  exact (Ideal.IsPrime.mem_or_mem ‹I.IsPrime› hmul).resolve_left hg

/-- The standard chart of the actual closure cone recovers the affine
zero locus, before passing to projective equivalence classes. -/
theorem projectiveClosure_cone_chart_zero
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (x : Fin (n + 1) → K)
    (hx : ∀ p ∈ projectiveClosureIdeal I, eval x p = 0) (hx0 : x 0 ≠ 0) :
    ∀ f ∈ I, eval (fun i => x i.succ / x 0) f = 0 := by
  intro f hf
  let F := boundedHomogenize f.totalDegree f
  have hFhom : F.IsHomogeneous f.totalDegree := boundedHomogenize_homogeneous f le_rfl
  have hFmem : F ∈ projectiveClosureIdeal I := by
    rw [homogeneous_mem_projectiveClosureIdeal_iff I _ hFhom,
      affineChart_boundedHomogenize]
    exact hf
  have hvec : Fin.cons 1 (fun i => x i.succ / x 0) = (x 0)⁻¹ • x := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [hx0]
    · simp [div_eq_mul_inv, mul_comm]
  rw [← affineChart_boundedHomogenize f.totalDegree f, affineChart_eval,
    hvec, homogeneous_eval_smul hFhom, hx F hFmem, mul_zero]

end
end AffineCurveCounting
