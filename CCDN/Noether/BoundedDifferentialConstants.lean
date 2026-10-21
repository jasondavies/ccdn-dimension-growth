/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Derivation.DifferentialRing
public import Mathlib.Algebra.Polynomial.Derivative
public import CCDN.Algebra.CharZeroOrGT
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus
/-! Bounded-degree differential constants, in characteristic zero or above
the degree. In positive characteristic the degree restrictions are essential. These
lemmas isolate the constant-descent step in Gao's differential criterion;
they do not supply the resultant bounds for residues or a Bertini theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- A polynomial with zero derivative is constant when its degree is below the characteristic. -/
lemma polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char
    {K : Type*} [Field K] (f : K[X]) (hchar : CharZeroOrGT K f.natDegree)
    (hder : f.derivative = 0) :
    f = C (f.coeff 0) := by
  ext i
  by_cases hi : i = 0
  · subst i; simp
  · rw [coeff_C, ite_eq_right hi]
    by_cases hlarge : f.natDegree < i
    · exact coeff_eq_zero_of_natDegree_lt hlarge
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have h := congrArg (fun q : K[X] => q.coeff j) hder
      simp only [coeff_derivative, coeff_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by
        simpa only [Nat.cast_succ] using hchar.natCast_ne_zero hi (Nat.le_of_not_gt hlarge))

end
end CCDN
