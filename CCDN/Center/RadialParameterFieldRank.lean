/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.PolynomialParameterFieldRank
/-! Adjoining a nonzero radial variable does not change the degree of
an affine parameter field. The cone parameters are the radial variable
and its products with the original parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem radial_parameter_field_eq
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {m : ℕ} (v : Fin m → F) (t : E) (ht : t ≠ 0) :
    (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range v)) {t}).restrictScalars K =
      IntermediateField.adjoin K
        (Set.range (Fin.cons t (fun i => t * algebraMap F E (v i)) : Fin (m + 1) → E)) := by
  let R := IntermediateField.adjoin K (Set.range v)
  let S := IntermediateField.adjoin K
    (Set.range (Fin.cons t (fun i => t * algebraMap F E (v i)) : Fin (m + 1) → E))
  let φ := IsScalarTower.toAlgHom K F E
  have htS : t ∈ S := IntermediateField.subset_adjoin K _ ⟨0,rfl⟩
  have hvS (i : Fin m) : φ (v i) ∈ S := by
    have hprod : t * algebraMap F E (v i) ∈ S :=
      IntermediateField.subset_adjoin K _ ⟨i.succ,rfl⟩
    change algebraMap F E (v i) ∈ S
    simpa only [mul_div_cancel_left₀ _ ht] using S.div_mem hprod htS
  have hRS : R ≤ S.comap φ := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨i,rfl⟩
    exact hvS i)
  apply le_antisymm
  · change (IntermediateField.adjoin R {t} : Set E) ⊆ S
    apply (IntermediateField.adjoin_subset_adjoin_iff R (F' := K)).mpr
    refine ⟨?_,?_⟩
    · rintro _ ⟨r,rfl⟩
      exact hRS r.property
    · intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact htS
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact IntermediateField.subset_adjoin R _ (Set.mem_singleton t)
    · apply (IntermediateField.adjoin R {t}).mul_mem
      · exact IntermediateField.subset_adjoin R _ (Set.mem_singleton t)
      · let r : R := ⟨v j,IntermediateField.subset_adjoin K _ ⟨j,rfl⟩⟩
        exact (IntermediateField.adjoin R {t}).algebraMap_mem r

theorem radial_parameter_field_finrank
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Algebra (MvPolynomial Unit F) E]
    [IsFractionRing (MvPolynomial Unit F) E]
    [IsScalarTower F (MvPolynomial Unit F) E]
    {m : ℕ} (v : Fin m → F)
    [Module.Finite (IntermediateField.adjoin K (Set.range v)) F] :
    let t := algebraMap (MvPolynomial Unit F) E (X ())
    Module.finrank (IntermediateField.adjoin K
      (Set.range (Fin.cons t (fun i => t * algebraMap F E (v i)) : Fin (m + 1) → E))) E =
        Module.finrank (IntermediateField.adjoin K (Set.range v)) F := by
  dsimp only
  let R := IntermediateField.adjoin K (Set.range v)
  let t := algebraMap (MvPolynomial Unit F) E (X ())
  have ht : t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit F) E)).mpr
    (X_ne_zero (R := F) ())
  have hgen : Set.range (fun i : Unit => algebraMap (MvPolynomial Unit F) E (X i)) = {t} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟩,rfl⟩
      rfl
    · rintro rfl
      exact ⟨(),rfl⟩
  have hrank := polynomial_parameter_field_finrank (K := R) (A := F) (F := E) (σ := Unit)
  rw [polynomialParameterField,hgen] at hrank
  have he := radial_parameter_field_eq (K := K) v t ht
  rw [← he]
  exact hrank

end
end CCDN
