/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowNestedIncidence
public import CCDN.Center.PolynomialCoefficientNormalizationRank
public import CCDN.Center.ChowLastRowSplit
public import CCDN.Center.GenericLinearPowerBasis
public import CCDN.Center.PolynomialFractionCoefficientExtension
import CCDN.Center.GenericLinearParameterField
import CCDN.Center.IntermediateFieldParameterTower
import CCDN.Center.PolynomialCoordinateEmbeddings
/-! Identify the incidence minimal polynomial with the generic
primitive element of the affine normalization extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

local instance degreeComparisonCoefficientRing {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := by
  letI : CommRing (MvPolynomial σ K ⧸ I) := inferInstance
  infer_instance

local instance degreeComparisonNestedRing {K σ τ υ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    CommRing (MvPolynomial υ (MvPolynomial τ (MvPolynomial σ K ⧸ I))) := by
  let : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := inferInstance
  infer_instance

/-- The coefficient extension map sends each variable to its image under the ambient algebra
map. -/
lemma polynomialFractionCoefficientMap_X {A K F σ : Type*} [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra A F] [Algebra K F] [Algebra (MvPolynomial σ A) F] (i : σ) :
    polynomialFractionCoefficientMap (A := A) (K := K) (F := F) (σ := σ) (X i) =
      algebraMap (MvPolynomial σ A) F (X i) :=
  eval₂Hom_X' _ _ i

/-- The linear form in the negated coordinates of the first-row coordinate ring is sent
by the coefficient extension map to the split last incidence form. -/
theorem chow_polynomialFractionCoefficientMap_linearForm
    {K A F : Type*} [Field K] [Field A] [Field F] [Algebra A F] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (ChowFirstRowCoordinateRing m I) A] [Algebra (ChowFirstRowCoordinateRing m I) F]
    [IsScalarTower (ChowFirstRowCoordinateRing m I) A F]
    [Algebra (ChowNestedCoordinateRing m I) F]
    [IsScalarTower (ChowFirstRowCoordinateRing m I) (ChowNestedCoordinateRing m I) F] :
    polynomialFractionCoefficientMap (A := ChowFirstRowCoordinateRing m I) (K := A) (F := F)
      (σ := Fin n) (linearForm (fun j =>
        -algebraMap (ChowFirstRowCoordinateRing m I) A (C (Ideal.Quotient.mk I (X j))))) =
      algebraMap (ChowNestedCoordinateRing m I) F
        (chowLastRowSplit m I (chowIncidenceMap (m + 1) I (X (Fin.last m, 0)))) := by
  let T := ChowFirstRowCoordinateRing m I
  let N := ChowNestedCoordinateRing m I
  rw [chowLastRowSplit_incidence_last, linearForm, map_sum, map_neg, map_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, polynomialFractionCoefficientMap_X, map_mul]
  have hC : polynomialFractionCoefficientMap (A := T) (K := A) (F := F) (σ := Fin n)
      (C (-algebraMap T A (C (Ideal.Quotient.mk I (X j))))) =
      -algebraMap T F (C (Ideal.Quotient.mk I (X j))) := by
    rw [polynomialFractionCoefficientMap, eval₂Hom_C, map_neg]
    exact congrArg Neg.neg (IsScalarTower.algebraMap_apply T A F _).symm
  rw [hC]
  have hC' : algebraMap N F (C (C (Ideal.Quotient.mk I (X j)))) =
      algebraMap T F (C (Ideal.Quotient.mk I (X j))) :=
    (IsScalarTower.algebraMap_apply T N F _).symm
  rw [hC']
  ring

/-- The degree in the final constant coefficient of an irreducible incidence equation equals the
rank of the affine normalization extension. -/
theorem chow_univariate_degree_eq_normalization_rank
    {K A F : Type*} [Field K] [CharZero K] [Field A] [Field F]
    [Algebra K A] [Algebra K F] [Algebra A F] [IsScalarTower K A F]
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (ChowFirstRowCoordinateRing m I) A]
    [IsScalarTower K (ChowFirstRowCoordinateRing m I) A]
    [IsFractionRing (ChowFirstRowCoordinateRing m I) A]
    [Algebra (ChowFirstRowCoordinateRing m I) F]
    [IsScalarTower (ChowFirstRowCoordinateRing m I) A F]
    [Algebra (ChowNestedCoordinateRing m I) F]
    [IsScalarTower (ChowFirstRowCoordinateRing m I) (ChowNestedCoordinateRing m I) F]
    [IsScalarTower K (ChowNestedCoordinateRing m I) F]
    [IsFractionRing (ChowNestedCoordinateRing m I) F]
    (hfinite : Module.Finite (chowNormalizationParameterField (F := A) m I) A)
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (G : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hG : Irreducible G) (hmem : G ∈ chowIncidenceIdeal (m + 1) I) :
    (chowAsUnivariate K m n G).natDegree =
      Module.finrank (chowNormalizationParameterField (F := A) m I) A := by
  classical
  let T := ChowFirstRowCoordinateRing m I
  let N := ChowNestedCoordinateRing m I
  let E := chowNormalizationParameterField (F := A) m I
  let : Module.Finite E A := hfinite
  let : CharZero A := Algebra.charZero_of_charZero K A
  let : CharZero E := Algebra.charZero_of_charZero K E
  let : Algebra E F := inferInstance
  let : IsScalarTower E A F := inferInstance
  let : IsScalarTower K E F := IsScalarTower.to₁₂₄ K E A F
  let : Algebra (MvPolynomial (Fin n) A) F :=
    (polynomialFractionCoefficientMap (A := T) (K := A) (F := F) (σ := Fin n)).toAlgebra
  let : IsFractionRing (MvPolynomial (Fin n) A) F := polynomial_fraction_coefficient_extension
  let : IsScalarTower A (MvPolynomial (Fin n) A) F := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    change algebraMap A F a = polynomialFractionCoefficientMap (A := T) (K := A) (F := F)
      (C a)
    simp [polynomialFractionCoefficientMap])
  let : IsScalarTower E (MvPolynomial (Fin n) A) F := IsScalarTower.to₁₃₄ E A _ F
  let : Algebra (ChowIncidenceCoordinateRing m I) F := (chowNestedIncidenceMap I).toAlgebra
  let : IsScalarTower K (ChowIncidenceCoordinateRing m I) F :=
    IsScalarTower.of_algebraMap_eq (fun c => (chowNestedIncidenceMap_ground I c).symm)
  let : IsFractionRing (ChowIncidenceCoordinateRing m I) F := chowNestedIncidenceMap_isFractionRing I
  let x : Fin n → A := fun j => -algebraMap T A (C (Ideal.Quotient.mk I (X j)))
  have hparam (q : Fin m × Fin n) : ∃ e : E, algebraMap E A e = algebraMap T A (X q) :=
    ⟨⟨_,IntermediateField.subset_adjoin K _ (Or.inl ⟨q,rfl⟩)⟩,rfl⟩
  have hsep : Function.Injective
      (fun φ : A →ₐ[E] AlgebraicClosure E => fun j => φ (x j)) :=
    neg_polynomial_coordinate_embeddings_injective I hparam
  obtain ⟨_,hmin,_⟩ := generic_linear_parameter_field_degree (K := E) (A := A) (F := F) x hsep
  let R := polynomialParameterField (K := E) (A := A) (F := F) (σ := Fin n)
  let φ : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let S : Set A := Set.range (fun q : Fin m × Fin n => algebraMap T A (X q)) ∪
    Set.range (fun i : Fin m => algebraMap T A (chowIncidenceMap m I (X (i,0))))
  have hη (p : T) : φ (algebraMap T A p) = algebraMap T F p :=
    (IsScalarTower.algebraMap_apply T A F p).symm
  have hX (j : Fin n) : algebraMap (MvPolynomial (Fin n) A) F (X j) =
      algebraMap N F (X j) :=
    polynomialFractionCoefficientMap_X (A := T) (K := A) (F := F) j
  have hR : R.restrictScalars K = chowParameterField (E := F) m I := by
    change (IntermediateField.adjoin E
      (Set.range (fun j : Fin n => algebraMap (MvPolynomial (Fin n) A) F (X j)))).restrictScalars K = _
    change (IntermediateField.adjoin (IntermediateField.adjoin K S)
      (Set.range (fun j : Fin n => algebraMap (MvPolynomial (Fin n) A) F (X j)))).restrictScalars K = _
    rw [intermediateField_adjoin_mapped_generators φ S (fun _ => rfl)]
    rw [chow_nested_parameter_field]
    simp only [S,Set.image_union,← Set.range_comp,Function.comp_def,hη,hX]
    rfl
  have hlast : algebraMap (MvPolynomial (Fin n) A) F (linearForm x) =
      chowLastIncidenceValue (E := F) m I :=
    chow_polynomialFractionCoefficientMap_linearForm (A := A) (F := F) (m := m) I
  have hmin' : (minpoly (R.restrictScalars K)
      (chowLastIncidenceValue (E := F) m I)).natDegree = Module.finrank E A := by
    change (minpoly R _).natDegree = _
    rwa [hlast] at hmin
  rw [hR] at hmin'
  exact (chow_incidence_minpoly_natDegree (E := F) I hm G hG hmem).symm.trans hmin'

end
end CCDN
