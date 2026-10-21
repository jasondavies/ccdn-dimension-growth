/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.GenericLinearParameterField
import CCDN.Center.PolynomialCoefficientBasis
import Mathlib.LinearAlgebra.FreeModule.PID
/-! The degree of a finite coefficient-field extension is unchanged by
adjoining rational parameters, measured over the parameter
intermediate field inside an arbitrary polynomial fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem polynomial_parameter_field_finrank
    {K A F σ : Type*} [Field K] [Field A] [Algebra K A]
    [Module.Finite K A] [Field F] [Algebra K F]
    [Algebra (MvPolynomial σ A) F]
    [IsFractionRing (MvPolynomial σ A) F]
    [IsScalarTower K (MvPolynomial σ A) F] :
    Module.finrank (polynomialParameterField (K := K) (A := A) (F := F) (σ := σ)) F =
      Module.finrank K A := by
  refine polynomialParameterField_rec (K := K) (A := A) (F := F) (σ := σ) ?_
  intro _ _ _ _ _
  simpa only [Fintype.card_fin] using
    polynomial_fraction_extension_finrank
      (R := polynomialParameterField (K := K) (A := A) (F := F) (σ := σ)) (F := F) (σ := σ)
      (Module.finBasis K A)

end
end CCDN
