/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! Degree bounds for integral elements: over an integrally closed base ring, the minimal
polynomial of an integral element has degree at most the degree of the fraction-field
extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

theorem integral_minpoly_natDegree_le_fraction_finrank
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E] (a : A) (ha : IsIntegral R a) :
    (minpoly R a).natDegree ≤ Module.finrank F E := by
  rw [← (minpoly.monic ha).natDegree_map (algebraMap R F),
    ← minpoly.isIntegrallyClosed_eq_field_fractions F E ha]
  exact minpoly.natDegree_le (algebraMap A E a)

end
end CCDN
