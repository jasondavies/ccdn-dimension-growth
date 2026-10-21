/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Construct the rational-function field embedding from a transcendental
coordinate, and prove the degree bound for the resulting field extension. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Send the rational-function variable to a transcendental element. -/
def transcendentalRatFuncMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : F) (hu : Transcendental K u) : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (Polynomial.aeval u)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.mp hu))

lemma transcendentalRatFuncMap_X {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : F) (hu : Transcendental K u) : transcendentalRatFuncMap u hu RatFunc.X = u := by
  change RatFunc.liftRingHom (Polynomial.aeval u).toRingHom _ RatFunc.X = u
  exact (RatFunc.liftRingHom_X (Polynomial.aeval u).toRingHom _).trans (Polynomial.aeval_X u)

end
end CCDN
