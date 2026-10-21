/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceIdeal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import CCDN.Center.WeightedPolynomialSubstitution
/-! The incidence elimination ideal is homogeneous separately in
each block of hyperplane coefficients. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Degree in a specified hyperplane-coefficient block. -/
def chowRowWeight {r s : ℕ} (i : Fin r) (q : Fin r × Fin s) : ℕ :=
  if q.1 = i then 1 else 0

lemma chowIncidence_variable_weight {K : Type*} [Field K] {n r : ℕ}
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

lemma chowIncidenceMap_weightedComponent {K : Type*} [Field K] {n r : ℕ}
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
