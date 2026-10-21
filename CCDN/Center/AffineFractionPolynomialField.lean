/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
/-! A chosen fraction field of a coefficient domain embeds canonically
in the fraction field of its polynomial ring. The embedding is compatible
with both the coefficient domain and its ground field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma polynomial_fraction_coefficient_map_injective
    {A E σ : Type*} [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [Algebra (MvPolynomial σ A) E]
    [IsScalarTower A (MvPolynomial σ A) E]
    [IsFractionRing (MvPolynomial σ A) E] :
    Function.Injective (algebraMap A E) := by
  rw [IsScalarTower.algebraMap_eq A (MvPolynomial σ A) E]
  exact (IsFractionRing.injective (MvPolynomial σ A) E).comp (C_injective σ A)

def fractionPolynomialCoefficientEmbedding
    {K A F E σ : Type*} [Field K] [CommRing A] [IsDomain A]
    [Field F] [Field E] [Algebra K A] [Algebra K F] [Algebra K E]
    [Algebra A F] [IsFractionRing A F] [IsScalarTower K A F]
    [Algebra A E] [IsScalarTower K A E]
    [Algebra (MvPolynomial σ A) E] [IsScalarTower A (MvPolynomial σ A) E]
    [IsFractionRing (MvPolynomial σ A) E] : F →ₐ[K] E :=
  IsFractionRing.liftAlgHom (g := IsScalarTower.toAlgHom K A E)
    (polynomial_fraction_coefficient_map_injective (σ := σ))

lemma fractionPolynomialCoefficientEmbedding_algebraMap
    {K A F E σ : Type*} [Field K] [CommRing A] [IsDomain A]
    [Field F] [Field E] [Algebra K A] [Algebra K F] [Algebra K E]
    [Algebra A F] [IsFractionRing A F] [IsScalarTower K A F]
    [Algebra A E] [IsScalarTower K A E]
    [Algebra (MvPolynomial σ A) E] [IsScalarTower A (MvPolynomial σ A) E]
    [IsFractionRing (MvPolynomial σ A) E] (x : A) :
    fractionPolynomialCoefficientEmbedding (K := K) (A := A) (E := E) (σ := σ)
      (algebraMap A F x) =
      algebraMap A E x :=
  IsFractionRing.lift_algebraMap
    (polynomial_fraction_coefficient_map_injective (A := A) (E := E) (σ := σ)) x

theorem fraction_polynomial_coefficient_tower
    {K A F E σ : Type*} [Field K] [CommRing A] [IsDomain A]
    [Field F] [Field E] [Algebra K A] [Algebra K F] [Algebra K E]
    [Algebra A F] [IsFractionRing A F] [IsScalarTower K A F]
    [Algebra A E] [IsScalarTower K A E]
    [Algebra (MvPolynomial σ A) E] [IsScalarTower A (MvPolynomial σ A) E]
    [IsFractionRing (MvPolynomial σ A) E] :
    let : Algebra F E :=
      (fractionPolynomialCoefficientEmbedding (K := K) (A := A) (F := F) (E := E)
        (σ := σ)).toRingHom.toAlgebra
    IsScalarTower A F E := by
  let : Algebra F E :=
    (fractionPolynomialCoefficientEmbedding (K := K) (A := A) (F := F) (E := E)
      (σ := σ)).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact (fractionPolynomialCoefficientEmbedding_algebraMap
    (K := K) (F := F) (E := E) (σ := σ) x).symm

end
end CCDN
