/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Center.FixedCoordinateGenericNormalization
public import CCDN.Center.ScalarQuotientFractionField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Center.AffineNormalizationRank
import CCDN.Center.GeometricIdealPrimality
import CCDN.Center.IntermediateFieldParameterTower
import CCDN.Hilbert.ScalarExtension
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
Exact normalization degree inside the fraction field of the
polynomial coefficient extension of the original coordinate ring. The
parameter field uses the universal incidence values of the first rows.

Exact affine normalization degree for algebraically independent linear
coefficients. All fraction fields are fraction fields of the displayed affine
coordinate ring.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem generic_affine_normalization_functionField_finrank
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Field F] [Algebra L F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [hAF : Algebra (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    [IsScalarTower L (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    [IsFractionRing (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u)
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I m d) :
    Module.finrank (IntermediateField.adjoin L
      (Set.range (fun i => @algebraMap
        (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F _ _ hAF
        ((Ideal.Quotient.mk (I.map (map (algebraMap K L))))
          (genericAffineParameterForms u i))))) F = d := by
  let : CharZero L := Algebra.charZero_of_charZero K L
  let IL := I.map (map (algebraMap K L))
  have : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  exact affine_normalization_functionField_finrank (F := F) IL
    (genericAffineParameterForms u) (genericAffineParameterForms_homogeneous u)
    (generic_fixed_coordinate_projection_integral I hdimdeg.natDegree_eq u hu) d
    (hasAffineDimensionDegree_scalar_extension hdimdeg)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational function field in the variables `σ`. -/
private abbrev universalCoefficientField (K σ : Type*) [Field K] := FractionRing (MvPolynomial σ K)

/-- The variables, as an algebraically independent tuple in their rational function field. -/
private def universalCoefficient (K σ : Type*) [Field K] (i : σ) : universalCoefficientField K σ :=
  algebraMap (MvPolynomial σ K) (universalCoefficientField K σ) (X i)

private theorem universalCoefficient_algebraicIndependent (K σ : Type*) [Field K] :
    AlgebraicIndependent K (universalCoefficient K σ) :=
  (algebraicIndependent_X σ K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial σ K) (universalCoefficientField K σ))
    (IsFractionRing.injective (MvPolynomial σ K) (universalCoefficientField K σ))

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem polynomial_fraction_variables_generate
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra (MvPolynomial σ K) L] [IsScalarTower K (MvPolynomial σ K) L]
    [IsFractionRing (MvPolynomial σ K) L] :
    IntermediateField.adjoin K (Set.range (fun i : σ =>
      algebraMap (MvPolynomial σ K) L (X i))) = ⊤ := by
  let S := IntermediateField.adjoin K (Set.range (fun i : σ =>
    algebraMap (MvPolynomial σ K) L (X i)))
  have hpoly (p : MvPolynomial σ K) : algebraMap (MvPolynomial σ K) L p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        change algebraMap (MvPolynomial σ K) L (algebraMap K (MvPolynomial σ K) c) ∈ S
        rw [← IsScalarTower.algebraMap_apply K (MvPolynomial σ K) L]
        exact S.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        exact S.mul_mem hp (IntermediateField.subset_adjoin K _ ⟨i,rfl⟩)
  apply top_unique
  intro x _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ K) x
  exact S.div_mem (hpoly p) (hpoly q)

private lemma adjoin_union_range_neg
    {K F ι : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set F) (v : ι → F) :
    IntermediateField.adjoin K (S ∪ Set.range (fun i => -v i)) =
      IntermediateField.adjoin K (S ∪ Set.range v) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx | ⟨i,rfl⟩)
    · exact IntermediateField.subset_adjoin K _ (Or.inl hx)
    · exact (IntermediateField.adjoin K _).neg_mem
        (IntermediateField.subset_adjoin K _ (Or.inr ⟨i,rfl⟩))
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx | ⟨i,rfl⟩)
    · exact IntermediateField.subset_adjoin K _ (Or.inl hx)
    · change v i ∈ IntermediateField.adjoin K (S ∪ Set.range (fun i => -v i))
      simpa only [neg_neg] using (IntermediateField.adjoin K _).neg_mem
        (IntermediateField.subset_adjoin K (S ∪ Set.range (fun i => -v i)) (Or.inr ⟨i,rfl⟩))

section

variable {K L F σ τ : Type*} [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra (MvPolynomial τ K) L]
  [IsScalarTower K (MvPolynomial τ K) L] [IsFractionRing (MvPolynomial τ K) L]
  [Algebra K F] (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
  [(I.map (map (algebraMap K L))).IsPrime]
  [Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]
  [IsScalarTower K (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]
  [IsFractionRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]

private lemma scalarQuotientFractionMap_ground_field (c : K) :
    scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I
      (Ideal.Quotient.mk _ (C (algebraMap K L c))) = algebraMap K F c := by
  let T := MvPolynomial τ (MvPolynomial σ K ⧸ I)
  have h := RingHom.congr_fun (scalarQuotientFractionMap_comp (F := F) (τ := τ) (L := L) I)
    (algebraMap K T c)
  have he : scalarQuotientPolynomialMap (τ := τ) (L := L) I (algebraMap K T c) =
      Ideal.Quotient.mk _ (C (algebraMap K L c)) := by
    change scalarQuotientPolynomialMap (τ := τ) (L := L) I
      (C (Ideal.Quotient.mk I (C c))) = _
    simp [scalarQuotientPolynomialMap,scalarCoordinateQuotientMap]
  rw [RingHom.comp_apply,he,← IsScalarTower.algebraMap_apply K T F] at h
  exact h

private def scalarQuotientFractionCoefficientMap : L →ₐ[K] F where
  toRingHom := (scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I).comp
    (algebraMap L (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))))
  commutes' c := scalarQuotientFractionMap_ground_field I c

end

/-- The subfield of `F` generated over `K` by the hyperplane coefficient variables `X (i, j)` for
`i < m` together with the incidence values `-(∑ j, X (i, j) * x j)` of the first `m` hyperplanes at
the generic point `x` of the variety of `I`. Here `F` is an algebra over the polynomial ring in
these coefficients over the coordinate ring of `I`. -/
def chowNormalizationParameterField
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F] :
    IntermediateField K F :=
  IntermediateField.adjoin K
    (Set.range (fun q : Fin m × Fin n =>
      algebraMap (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F (X q)) ∪
     Set.range (fun i : Fin m =>
      algebraMap (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F
        (chowIncidenceMap m I (X (i,0)))))

/-- Exact degree over the parameter field of the first incidence
rows, in any fraction field of the coefficient polynomial extension. -/
theorem chow_incidence_parameter_field_finrank
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [Algebra (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsScalarTower K (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsFractionRing (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) F]
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I m d) :
    Module.finrank (chowNormalizationParameterField (F := F) m I) F = d := by
  let L := universalCoefficientField K (Fin m × Fin n)
  let : Field L := inferInstance
  let IL := I.map (map (algebraMap K L))
  have : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  let Q := MvPolynomial (Fin n) L ⧸ IL
  let : CommRing Q := inferInstance
  let T := MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)
  let θ : Q →+* F := scalarQuotientFractionMap (F := F) (τ := Fin m × Fin n) (L := L) I
  let coeffMap : L →ₐ[K] F := scalarQuotientFractionCoefficientMap
    (F := F) (τ := Fin m × Fin n) (L := L) I
  let : Algebra Q F := θ.toAlgebra
  let : Algebra L F := coeffMap.toRingHom.toAlgebra
  let : IsScalarTower K L F := IsScalarTower.of_algHom coeffMap
  let : IsScalarTower L Q F :=
    IsScalarTower.of_algebraMap_eq' (R := L) (S := Q) (A := F) rfl
  let : IsFractionRing Q F := scalarQuotientFractionMap_isFractionRing
    (F := F) (τ := Fin m × Fin n) (L := L) I
  let u := universalCoefficient K (Fin m × Fin n)
  let w : Fin m → F := fun i => θ ((Ideal.Quotient.mk IL) (genericAffineParameterForms u i))
  have hrank : Module.finrank (IntermediateField.adjoin L (Set.range w)) F = d :=
    generic_affine_normalization_functionField_finrank I u
      (universalCoefficient_algebraicIndependent K _) d hdimdeg
  have hgen : IntermediateField.adjoin K (Set.range u) = ⊤ :=
    polynomial_fraction_variables_generate (K := K) (L := L) (σ := Fin m × Fin n)
  have hparam (q : Fin m × Fin n) :
      θ (Ideal.Quotient.mk IL (C (u q))) = algebraMap T F (X q) :=
    scalarQuotientFractionMap_parameter (F := F) (τ := Fin m × Fin n) (L := L) I q
  have hcoeff (q : Fin m × Fin n) : algebraMap L F (u q) = algebraMap T F (X q) :=
    hparam q
  have hcoord (j : Fin n) :
      θ (Ideal.Quotient.mk IL (X j)) = algebraMap T F (C (Ideal.Quotient.mk I (X j))) :=
    scalarQuotientFractionMap_coordinate (F := F) (τ := Fin m × Fin n) (L := L) I j
  have hvalue (i : Fin m) :
      w i = -algebraMap T F (chowIncidenceMap m I (X (i,0))) := by
    have hw : w i = ∑ j, θ (Ideal.Quotient.mk IL (C (u (i,j)))) *
        θ (Ideal.Quotient.mk IL (X j)) := by
      change θ (Ideal.Quotient.mk IL (∑ j, C (u (i,j)) * X j)) = _
      rw [map_sum (Ideal.Quotient.mk IL)]
      change θ.toAddMonoidHom (∑ j, Ideal.Quotient.mk IL (C (u (i,j)) * X j)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul (Ideal.Quotient.mk IL)]
      exact θ.map_mul _ _
    rw [hw]
    simp only [hparam,hcoord,chowIncidenceMap,aeval_X,Fin.cases_zero,map_neg,neg_neg,
      map_sum (algebraMap T F),map_mul (algebraMap T F)]
  have he := intermediateField_adjoin_tower_generators (K := K) (L := L) (F := F)
    u hgen (Set.range w)
  simp only [hcoeff] at he
  have hw : w = fun i => -algebraMap T F (chowIncidenceMap m I (X (i,0))) := funext hvalue
  conv_rhs at he => rw [hw,adjoin_union_range_neg]
  change (IntermediateField.adjoin L (Set.range w)).restrictScalars K =
    chowNormalizationParameterField (F := F) m I at he
  rw [← he]
  exact hrank

end
end CCDN
