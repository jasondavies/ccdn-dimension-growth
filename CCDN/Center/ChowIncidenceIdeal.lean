/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Nullstellensatz
import CCDN.Algebra.WeightedPolynomialSubstitution

/-!
Hyperplane incidence on an affine chart. The eliminated ideal is
constructed by substitution in the coordinate domain, and its geometric
zero equations are proved to be precisely the equations vanishing on all
incident hyperplane tuples.

The incidence elimination ideal is homogeneous separately in
each block of hyperplane coefficients.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Hyperplane coefficient tuples through an affine point, parametrized by
their freely chosen nonconstant coefficients. -/
def chowIncidentCoefficients {K : Type*} [Field K] {n r : ℕ}
    (a : Fin n → K) (u : Fin r × Fin n → K) : Fin r × Fin (n + 1) → K :=
  fun q => Fin.cases (-(∑ j, u (q.1,j) * a j)) (fun j => u (q.1,j)) q.2

/-- Universal substitution of the constant coefficient in each hyperplane
by the incidence equation at the generic point of the affine variety. -/
def chowIncidenceMap {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :
    MvPolynomial (Fin r × Fin (n + 1)) K →ₐ[K]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin n) K ⧸ I) :=
  aeval (fun q => Fin.cases
    (-(∑ j, X (q.1,j) * C (Ideal.Quotient.mk I (X j))))
    (fun j => X (q.1,j)) q.2)

def chowIncidenceIdeal {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin r × Fin (n + 1)) K) :=
  RingHom.ker (chowIncidenceMap r I)

instance chowIncidenceIdeal_isPrime {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    (chowIncidenceIdeal r I).IsPrime := RingHom.ker_isPrime _

private def chowPointEvaluation {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin n → K)
    (ha : ∀ f ∈ I, eval a f = 0) : (MvPolynomial (Fin n) K ⧸ I) →+* K :=
  Ideal.Quotient.lift I (eval a) ha

private lemma chowIncidenceMap_evaluate {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin n → K)
    (ha : ∀ f ∈ I, eval a f = 0) (u : Fin r × Fin n → K)
    (R : MvPolynomial (Fin r × Fin (n + 1)) K) :
    eval₂ (chowPointEvaluation I a ha) u (chowIncidenceMap r I R) =
      eval (chowIncidentCoefficients a u) R := by
  have he : (eval₂Hom (chowPointEvaluation I a ha) u).comp
      (chowIncidenceMap r I).toRingHom = eval (chowIncidentCoefficients a u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chowIncidenceMap,chowPointEvaluation]
      change Ideal.Quotient.lift I (eval a) ha (Ideal.Quotient.mk I (C c)) = c
      simp
    · intro q
      rcases q with ⟨i,j⟩
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [chowIncidenceMap,chowPointEvaluation,chowIncidentCoefficients]
      · simp [chowIncidenceMap,chowPointEvaluation,chowIncidentCoefficients]
  exact RingHom.congr_fun he R

/-- Exact vanishing characterization of the constructed elimination ideal. -/
theorem mem_chowIncidenceIdeal_iff {K : Type*} [Field K] [IsAlgClosed K]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (R : MvPolynomial (Fin r × Fin (n + 1)) K) :
    R ∈ chowIncidenceIdeal r I ↔
      ∀ (a : Fin n → K), (∀ f ∈ I, eval a f = 0) →
        ∀ u : Fin r × Fin n → K, eval (chowIncidentCoefficients a u) R = 0 := by
  classical
  constructor
  · intro h a ha u
    rw [← chowIncidenceMap_evaluate I a ha]
    change chowIncidenceMap r I R = 0 at h
    rw [h,eval₂_zero]
  · intro h
    change chowIncidenceMap r I R = 0
    by_contra hne
    obtain ⟨e,he⟩ := exists_coeff_ne_zero hne
    obtain ⟨f,hf⟩ := Ideal.Quotient.mk_surjective ((chowIncidenceMap r I R).coeff e)
    have hfI : f ∉ I := by
      intro hmem
      exact he (hf ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    have hex : ∃ a : Fin n → K, (∀ p ∈ I, eval a p = 0) ∧ eval a f ≠ 0 := by
      by_contra! hh
      apply hfI
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
      intro a ha
      rw [aeval_eq_eval]
      exact hh a (fun p hp => by simpa only [aeval_eq_eval] using ha p hp)
    obtain ⟨a,ha,haf⟩ := hex
    have hpzero : map (chowPointEvaluation I a ha) (chowIncidenceMap r I R) = 0 := by
      apply MvPolynomial.funext
      intro u
      rw [eval_map, chowIncidenceMap_evaluate]
      simpa only [map_zero] using h a ha u
    have hc := congrArg (fun p : MvPolynomial (Fin r × Fin n) K => p.coeff e) hpzero
    rw [coeff_map,AddMonoidAlgebra.coeff_zero,← hf] at hc
    exact haf hc

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Degree in a specified hyperplane-coefficient block. -/
def chowRowWeight {r s : ℕ} (i : Fin r) (q : Fin r × Fin s) : ℕ :=
  if q.1 = i then 1 else 0

private lemma chowIncidence_variable_weight {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (i : Fin r)
    (q : Fin r × Fin (n + 1)) :
    (chowIncidenceMap r I (X q)).IsWeightedHomogeneous
      (chowRowWeight (s := n) i) (chowRowWeight i q) := by
  classical
  rcases q with ⟨k,j⟩
  rw [chowIncidenceMap,aeval_X]
  refine Fin.cases ?_ (fun l => ?_) j
  · dsimp only [Fin.cases_zero]
    apply IsWeightedHomogeneous.neg
    apply IsWeightedHomogeneous.sum
    intro l _
    rw [mul_comm]
    exact (isWeightedHomogeneous_X (MvPolynomial (Fin n) K ⧸ I)
      (chowRowWeight i) (k,l)).C_mul (Ideal.Quotient.mk I (X l))
  · exact isWeightedHomogeneous_X (MvPolynomial (Fin n) K ⧸ I) (chowRowWeight i) (k,l)

private lemma chowIncidenceMap_weightedComponent {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (i : Fin r)
    (R : MvPolynomial (Fin r × Fin (n + 1)) K) (M : ℕ) :
    chowIncidenceMap r I (weightedHomogeneousComponent (chowRowWeight i) M R) =
      weightedHomogeneousComponent (chowRowWeight i) M (chowIncidenceMap r I R) := by
  apply weighted_component_substitution (algebraMap K (MvPolynomial (Fin n) K ⧸ I))
    (chowRowWeight i) (chowRowWeight i) _ _ R M
  intro q
  simpa only [chowIncidenceMap,aeval_X] using chowIncidence_variable_weight I i q

theorem chowIncidenceIdeal_multihomogeneous {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (R : MvPolynomial (Fin r × Fin (n + 1)) K)
    (hR : R ∈ chowIncidenceIdeal r I) (i : Fin r) (M : ℕ) :
    weightedHomogeneousComponent (chowRowWeight i) M R ∈ chowIncidenceIdeal r I := by
  change chowIncidenceMap r I R = 0 at hR
  change chowIncidenceMap r I (weightedHomogeneousComponent _ _ R) = 0
  rw [chowIncidenceMap_weightedComponent,hR,map_zero]

end
end CCDN
