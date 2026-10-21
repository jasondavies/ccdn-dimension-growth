/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Predicates on polynomials and ideals

Named forms of two hypotheses that recur throughout the library: homogeneity of an ideal of a
polynomial ring, and absolute irreducibility of the top-degree homogeneous part of a
polynomial (the hypothesis of CCDN Theorem 4). Both are abbreviations, so proofs may use them
as their unfolded statements.
-/

@[expose] public section

namespace CCDN

open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

/-- An ideal of a polynomial ring is homogeneous when it contains every homogeneous
component of each of its elements. -/
abbrev IsHomogeneousIdeal (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- `IsHomogeneousIdeal` agrees with Mathlib's homogeneity for the grading by total degree. -/
theorem isHomogeneousIdeal_iff_isHomogeneous (I : Ideal (MvPolynomial σ K)) :
    IsHomogeneousIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule σ K) := by
  constructor
  · intro h i r hr
    exact (decomposition.decompose'_apply r i).symm ▸ h r hr i
  · intro h r hr i
    exact decomposition.decompose'_apply (R := K) r i ▸ h i hr

/-- The top-degree homogeneous part of an integer polynomial is irreducible over `ℚ̄`. -/
abbrev HasAbsIrreducibleTopForm (f : MvPolynomial σ ℤ) : Prop :=
  Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) (homogeneousComponent f.totalDegree f))

/-- The top-degree homogeneous part of a rational polynomial is irreducible over `ℚ̄`. -/
abbrev HasAbsIrreducibleTopFormRat (f : MvPolynomial σ ℚ) : Prop :=
  Irreducible
    (map (algebraMap ℚ (AlgebraicClosure ℚ)) (homogeneousComponent f.totalDegree f))

end CCDN
