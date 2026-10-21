/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceIdeal
public import Mathlib.RingTheory.Nullstellensatz
/-! The constructed elimination ideal is the vanishing ideal of
hyperplane tuples having a common point on the chosen affine chart. -/

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
  {U | ∃ a : Fin n → K, (∀ f ∈ I, eval a f = 0) ∧
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
