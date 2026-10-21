/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! Explicit generators for intermediate fields obtained by adjoining
parameters after a coefficient-field extension. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma intermediateField_adjoin_tower_range
    {K A F : Type*} [Field K] [Field A] [Field F]
    [Algebra K A] [Algebra K F] [Algebra A F] [IsScalarTower K A F]
    (T : Set F) :
    (IntermediateField.adjoin A T).restrictScalars K =
      IntermediateField.adjoin K (Set.range (algebraMap A F) ∪ T) := by
  apply le_antisymm
  · change (IntermediateField.adjoin A T : Set F) ⊆
      IntermediateField.adjoin K (Set.range (algebraMap A F) ∪ T)
    rw [IntermediateField.adjoin_subset_adjoin_iff]
    exact ⟨fun x hx => IntermediateField.subset_adjoin K _ (Or.inl hx),
      fun x hx => IntermediateField.subset_adjoin K _ (Or.inr hx)⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx | hx)
    · obtain ⟨a,rfl⟩ := hx
      exact (IntermediateField.adjoin A T).algebraMap_mem a
    · exact IntermediateField.subset_adjoin A T hx

lemma intermediateField_adjoin_mapped_tower
    {K A F : Type*} [Field K] [Field A] [Field F]
    [Algebra K A] [Algebra K F]
    (φ : A →ₐ[K] F) (E : IntermediateField K A)
    [Algebra E F] [IsScalarTower K E F]
    (hφ : ∀ x : E, algebraMap E F x = φ x) (T : Set F) :
    (IntermediateField.adjoin E T).restrictScalars K =
      IntermediateField.adjoin K (φ '' (E : Set A) ∪ T) := by
  rw [intermediateField_adjoin_tower_range]
  congr 2
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a,a.property,(hφ a).symm⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,ha⟩,hφ ⟨a,ha⟩⟩

lemma intermediateField_adjoin_mapped_generators
    {K A F : Type*} [Field K] [Field A] [Field F]
    [Algebra K A] [Algebra K F]
    (φ : A →ₐ[K] F) (S : Set A)
    [Algebra (IntermediateField.adjoin K S) F]
    [IsScalarTower K (IntermediateField.adjoin K S) F]
    (hφ : ∀ x : IntermediateField.adjoin K S,
      algebraMap (IntermediateField.adjoin K S) F x = φ x) (T : Set F) :
    (IntermediateField.adjoin (IntermediateField.adjoin K S) T).restrictScalars K =
      IntermediateField.adjoin K (φ '' S ∪ T) := by
  rw [intermediateField_adjoin_mapped_tower φ _ hφ T]
  rw [← IntermediateField.coe_map, IntermediateField.adjoin_union,
    IntermediateField.adjoin_self, IntermediateField.adjoin_map,
    ← IntermediateField.adjoin_union]

lemma intermediateField_adjoin_tower_generators
    {K L F σ : Type*} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
    (u : σ → L) (hu : IntermediateField.adjoin K (Set.range u) = ⊤) (T : Set F) :
    (IntermediateField.adjoin L T).restrictScalars K =
      IntermediateField.adjoin K (Set.range (fun i => algebraMap L F (u i)) ∪ T) := by
  let E := IntermediateField.adjoin K (Set.range (fun i => algebraMap L F (u i)) ∪ T)
  let φ : L →ₐ[K] F := IsScalarTower.toAlgHom K L F
  have hle : IntermediateField.adjoin K (Set.range u) ≤ E.comap φ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact IntermediateField.subset_adjoin K _ (Or.inl ⟨i,rfl⟩)
  have hbase (x : L) : algebraMap L F x ∈ E := hle (by rw [hu]; trivial)
  rw [intermediateField_adjoin_tower_range]
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx | hx)
    · obtain ⟨x,rfl⟩ := hx
      exact hbase x
    · exact IntermediateField.subset_adjoin K _ (Or.inr hx)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx | hx)
    · obtain ⟨i,rfl⟩ := hx
      exact IntermediateField.subset_adjoin K _ (Or.inl ⟨u i,rfl⟩)
    · exact IntermediateField.subset_adjoin K _ (Or.inr hx)

end
end CCDN
