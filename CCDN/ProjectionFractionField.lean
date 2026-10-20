module

public import CCDN.PrimitivePairReconstruction
public import CCDN.BoundedPrimitiveElement
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! Field generation by a parameter tuple and one primitive coordinate,
and the resulting fraction-field structure on the image ring. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem primitive_parameter_tuple_adjoin_top
    {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}
    (u : Fin m → F) (v : F)
    (hprim : IntermediateField.adjoin (IntermediateField.adjoin K (Set.range u)) {v} = ⊤) :
    IntermediateField.adjoin K (Set.range (Fin.cases v u : Fin (m + 1) → F)) = ⊤ := by
  let R := IntermediateField.adjoin K (Set.range u)
  let L := IntermediateField.adjoin K (Set.range (Fin.cases v u : Fin (m + 1) → F))
  have hu (i : Fin m) : u i ∈ L :=
    IntermediateField.subset_adjoin K _ ⟨i.succ, rfl⟩
  have hv : v ∈ L := IntermediateField.subset_adjoin K _ ⟨0, rfl⟩
  have hRL : R ≤ L := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hu i)
  have hsub : (IntermediateField.adjoin R {v} : Set F) ⊆ L := by
    apply (IntermediateField.adjoin_subset_adjoin_iff R (F' := K)).mpr
    refine ⟨?_, ?_⟩
    · rintro _ ⟨r, rfl⟩
      exact hRL r.property
    · intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hv
  apply top_unique
  intro x _
  exact hsub (by rw [hprim]; trivial)

/-- An injective algebra map into a field realizes that field as the fraction
field whenever a tuple of source elements generates it as a field. -/
theorem isFractionRing_of_generating_tuple
    {K A F σ : Type*} [Field K] [CommRing A] [Field F]
    [Algebra K A] [Algebra K F]
    (φ : A →ₐ[K] F) (hφ : Function.Injective φ) (a : σ → A)
    (ha : IntermediateField.adjoin K (Set.range (fun i => φ (a i))) = ⊤) :
    let : Algebra A F := φ.toRingHom.toAlgebra
    IsFractionRing A F := by
  let : Algebra A F := φ.toRingHom.toAlgebra
  let : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hφ
  apply IsFractionRing.of_field
  intro x
  obtain ⟨p, q, _, he⟩ := adjoin_top_polynomial_fraction (fun i => φ (a i)) ha x
  refine ⟨aeval a p, aeval a q, ?_⟩
  change x = φ (aeval a p) / φ (aeval a q)
  simpa only [comp_aeval_apply] using he

end
end CCDN
