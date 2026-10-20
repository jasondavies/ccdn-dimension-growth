module

public import AffineCurveCounting.FiniteGroupPowerTorsion

/-! A subgroup covered by finitely many cosets of a homomorphic image
has power torsion bounded by the source torsion times the cover size. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

theorem power_torsion_card_le_of_coset_cover
    {A G ι : Type*} [CommGroup A] [CommGroup G] [Finite A] [Finite G] [Fintype ι]
    (φ : A →* G) (S : Subgroup G) (c : ι → G)
    (hcover : ∀ x : S, ∃ a : A, ∃ i : ι, x.val = φ a * c i)
    (m : ℕ) :
    Nat.card (powMonoidHom m : S →* S).ker ≤
      Nat.card (powMonoidHom m : A →* A).ker * Fintype.card ι := by
  let π := QuotientGroup.mk' φ.range
  let ψ : S →* G ⧸ φ.range := π.comp S.subtype
  let δ := ψ.rangeRestrict
  have hφ (a : A) : π (φ a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hex (r : ψ.range) : ∃ i : ι, r.val = π (c i) := by
    obtain ⟨x, hx⟩ := r.property
    obtain ⟨a, i, he⟩ := hcover x
    refine ⟨i, ?_⟩
    rw [← hx]
    change π x.val = _
    rw [he, map_mul, hφ, one_mul]
  choose i hi using hex
  have hinj : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    rw [hi x, hi y, h]
  have hrange : Nat.card ψ.range ≤ Fintype.card ι := by
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective i hinj
  let j : δ.ker →* φ.range :=
    { toFun := fun x ↦ ⟨x.val.val, by
        have hh := congrArg Subtype.val x.property
        change QuotientGroup.mk x.val.val = 1 at hh
        exact (QuotientGroup.eq_one_iff _).mp hh⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : φ.range ↦ z.val) h
  have hjtor : Function.Injective (powerTorsionMap j m) := by
    intro x y h
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val h
  have hker :
      Nat.card (powMonoidHom m : δ.ker →* δ.ker).ker ≤
        Nat.card (powMonoidHom m : A →* A).ker :=
    (Nat.card_le_card_of_injective _ hjtor).trans
      (power_torsion_card_le_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective m)
  have hr : Nat.card (powMonoidHom m : ψ.range →* ψ.range).ker ≤ Fintype.card ι :=
    (Subgroup.card_le_card_group _).trans hrange
  exact (power_torsion_card_le_kernel_mul_target δ m).trans (Nat.mul_le_mul hker hr)

end
end AffineCurveCounting
