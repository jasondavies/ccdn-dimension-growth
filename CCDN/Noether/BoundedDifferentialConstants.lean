/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.RationalDifferential
/-! Bounded-degree differential constants in positive characteristic.
Unlike characteristic zero, the degree restrictions are essential. These
lemmas isolate the constant-descent step in Gao's differential criterion;
they do not supply the resultant bounds for residues or a Bertini theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

lemma polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (f : K[X]) (hdeg : f.natDegree < p) (hder : f.derivative = 0) :
    f = C (f.coeff 0) := by
  ext i
  by_cases hi : i = 0
  · subst i; simp
  · rw [coeff_C, ite_eq_right hi]
    by_cases hlarge : f.natDegree < i
    · exact coeff_eq_zero_of_natDegree_lt hlarge
    · have hip : i < p := lt_of_le_of_lt (Nat.le_of_not_gt hlarge) hdeg
      have hiK : (i : K) ≠ 0 := by
        intro h
        have hdiv := (CharP.cast_eq_zero_iff K p i).mp h
        exact hi (Nat.eq_zero_of_dvd_of_lt hdiv hip)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have h := congrArg (fun q : K[X] => q.coeff j) hder
      simp only [coeff_derivative, coeff_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by simpa only [Nat.cast_succ] using hiK)

end
end CCDN
