/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowPivotParametrization
public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Algebra.IdealZeroLocus
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import CCDN.Center.ChowIncidenceIdeal
import CCDN.Algebra.LinearForm
import CCDN.Algebra.ProjectiveClosureDegree
import CCDN.Height.ProjectiveZeroLocus

/-!
The affine incidence elimination ideal is the vanishing ideal of the
full projective hyperplane incidence locus, including points at
infinity. This asserts equality of vanishing ideals, not closedness of the
incidence image.

Polynomial vanishing on a nonempty principal open subset of an
integral affine variety extends to the entire variety.

The constructed elimination ideal is the vanishing ideal of
hyperplane tuples having a common point on the chosen affine chart.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma chowIncidentCoefficients_relation {K : Type*} [Field K] {n r : ℕ}
    (a : Fin n → K) (u : Fin r × Fin n → K) (i : Fin r) :
    ∑ j : Fin (n + 1), chowIncidentCoefficients a u (i,j) * (Fin.cons 1 a : Fin (n + 1) → K) j = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [chowIncidentCoefficients, Fin.cases_zero, Fin.cases_succ,
    Fin.cons_zero, Fin.cons_succ, mul_one, neg_add_cancel]

lemma chowIncidentCoefficients_reconstruct {K : Type*} [Field K] {n r : ℕ}
    (a : Fin n → K) (U : Fin r × Fin (n + 1) → K)
    (hU : ∀ i, ∑ j, U (i,j) * (Fin.cons 1 a : Fin (n + 1) → K) j = 0) :
    chowIncidentCoefficients a (fun q => U (q.1,q.2.succ)) = U := by
  funext q
  rcases q with ⟨i,j⟩
  refine Fin.cases ?_ (fun _ => rfl) j
  have hh := hU i
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one] at hh
  exact (eq_neg_of_add_eq_zero_left hh).symm

/-- Hyperplane tuples whose intersection contains a point of the
affine variety represented in the projective chart x₀=1. -/
def chowIncidenceLocus {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) : Set (Fin r × Fin (n + 1) → K) :=
  {U | ∃ a : Fin n → K, a ∈ idealZeroLocus I ∧
    ∀ i, ∑ j, U (i,j) * (Fin.cons 1 a : Fin (n + 1) → K) j = 0}

theorem chowIncidenceIdeal_eq_vanishingIdeal {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    chowIncidenceIdeal r I = vanishingIdeal K (chowIncidenceLocus r I) := by
  ext R
  rw [mem_chowIncidenceIdeal_iff]
  constructor
  · intro h U hU
    obtain ⟨a,ha,he⟩ := hU
    rw [aeval_eq_eval,← chowIncidentCoefficients_reconstruct a U he]
    exact h a ha _
  · intro h a ha u
    have hh := h (chowIncidentCoefficients a u)
      ⟨a,ha,chowIncidentCoefficients_relation a u⟩
    simpa only [aeval_eq_eval] using hh

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

theorem mem_prime_ideal_of_vanishing_on_principal_open
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (g f : MvPolynomial σ K) (hg : g ∉ I)
    (hvan : ∀ x : σ → K, x ∈ idealZeroLocus I →
      eval x g ≠ 0 → eval x f = 0) : f ∈ I := by
  have hmul : g * f ∈ I := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
    intro x hx
    rw [aeval_eq_eval, eval_mul]
    by_cases hzero : eval x g = 0
    · rw [hzero, zero_mul]
    · rw [hvan x (fun p hp => by simpa only [aeval_eq_eval] using hx p hp) hzero, mul_zero]
  exact (Ideal.IsPrime.mem_or_mem ‹I.IsPrime› hmul).resolve_left hg

/-- The standard chart of the closure cone recovers the affine
zero locus, before passing to projective equivalence classes. -/
theorem projectiveClosure_cone_chart_zero
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (x : Fin (n + 1) → K)
    (hx : ∀ p ∈ projectiveClosureIdeal I, eval x p = 0) (hx0 : x 0 ≠ 0) :
    (fun i => x i.succ / x 0) ∈ idealZeroLocus I := by
  intro f hf
  let F := scaledHomogenize f.totalDegree 1 f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous 1 f le_rfl
  have hFmem : F ∈ projectiveClosureIdeal I := by
    rw [homogeneous_mem_projectiveClosureIdeal_iff I _ hFhom,
      affineChart_scaledHomogenize_one]
    exact hf
  have hvec : Fin.cons 1 (fun i => x i.succ / x 0) = (x 0)⁻¹ • x := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [hx0]
    · simp [div_eq_mul_inv, mul_comm]
  rw [← affineChart_scaledHomogenize_one f.totalDegree f, affineChart_eval,
    hvec, homogeneous_eval_smul hFhom, hx F hFmem, mul_zero]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

def projectiveChowIncidenceLocus {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Set (Fin r × Fin (n + 1) → K) :=
  {U | ∃ p ∈ projectiveIdealZeroLocus J,
    ∀ i, ∑ j, U (i,j) * p.rep j = 0}

/-- Weighted homogeneity is preserved and reflected by an injective coefficient map. -/
theorem isWeightedHomogeneous_map_iff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] {φ : R →+* S} (hφ : Function.Injective φ) (w : σ → M)
    (p : MvPolynomial σ R) (m : M) :
    (map φ p).IsWeightedHomogeneous w m ↔ p.IsWeightedHomogeneous w m := by
  simp only [IsWeightedHomogeneous, coeff_map, ne_eq, map_eq_zero_iff φ hφ]

/-- `F` is a projective Chow equation of the homogeneous ideal `J` with row degrees `δ`: it is
irreducible, weighted homogeneous of degree `δ i` in the `i`-th row of hyperplane coefficients,
and vanishes exactly at the hyperplane tuples meeting the projective variety of `J`. -/
structure IsProjectiveChowEquation {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (F : MvPolynomial (Fin r × Fin (n + 1)) K)
    (δ : Fin r → ℕ) : Prop where
  irreducible : Irreducible F
  row_homogeneous : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)
  eval_eq_zero_iff : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus r J

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
  have ha : a ∈ idealZeroLocus I := projectiveClosure_cone_chart_zero I x hx hx0
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
