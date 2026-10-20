module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.FractionRing

/-! Enlarging the coefficient domain to its fraction field does not change
the fraction field of a polynomial ring. The compatible polynomial map
and its fraction-field structure are constructed explicitly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extend polynomial coefficients inside the ambient fraction field. -/
def polynomialFractionCoefficientMap
    {A K F σ : Type*} [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra A F] [Algebra K F]
    [Algebra (MvPolynomial σ A) F] : MvPolynomial σ K →+* F :=
  eval₂Hom (algebraMap K F) (fun i => algebraMap (MvPolynomial σ A) F (X i))

lemma polynomialFractionCoefficientMap_comp
    {A K F σ : Type*} [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra A F] [Algebra K F]
    [IsScalarTower A K F]
    [Algebra (MvPolynomial σ A) F] [IsScalarTower A (MvPolynomial σ A) F] :
    (polynomialFractionCoefficientMap (A := A) (K := K) (F := F) (σ := σ)).comp
      (map (algebraMap A K)) = algebraMap (MvPolynomial σ A) F := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,map_C,polynomialFractionCoefficientMap,eval₂Hom_C,
      ← IsScalarTower.algebraMap_apply]
    exact IsScalarTower.algebraMap_apply A (MvPolynomial σ A) F a
  · intro i
    simp [polynomialFractionCoefficientMap]

/-- The constructed coefficient extension realizes the same
ambient field as a fraction field after coefficient localization. -/
theorem polynomial_fraction_coefficient_extension
    {A K F σ : Type*} [CommRing A] [IsDomain A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra A F] [Algebra K F] [IsScalarTower A K F]
    [Algebra (MvPolynomial σ A) F] [IsScalarTower A (MvPolynomial σ A) F]
    [IsFractionRing (MvPolynomial σ A) F] :
    let : Algebra (MvPolynomial σ K) F :=
      (polynomialFractionCoefficientMap (A := A) (K := K) (F := F) (σ := σ)).toAlgebra
    IsFractionRing (MvPolynomial σ K) F := by
  let : Algebra (MvPolynomial σ K) F :=
    (polynomialFractionCoefficientMap (A := A) (K := K) (F := F) (σ := σ)).toAlgebra
  let : IsScalarTower (MvPolynomial σ A) (MvPolynomial σ K) F :=
    IsScalarTower.of_algebraMap_eq' (polynomialFractionCoefficientMap_comp).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    ((nonZeroDivisors A).map (C (σ := σ))) (MvPolynomial σ K) F

end
end CCDN
