module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-! Cardinal bounds for power torsion in finite abelian groups.
These are the exact-sequence inequalities used in quadratic descent. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Power torsion maps functorially under a group homomorphism. -/
def powerTorsionMap (φ : G →* H) (n : ℕ) :
    (powMonoidHom n : G →* G).ker →* (powMonoidHom n : H →* H).ker where
  toFun x := ⟨φ x, by
    change (φ x.val) ^ n = 1
    rw [← map_pow, show x.val ^ n = 1 from x.property, map_one]⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' x y := Subtype.ext (map_mul φ _ _)

theorem power_torsion_card_le_of_surjective [Finite G] [Finite H]
    (φ : G →* H) (hφ : Function.Surjective φ) (n : ℕ) :
    Nat.card (powMonoidHom n : H →* H).ker ≤
      Nat.card (powMonoidHom n : G →* G).ker := by
  have hpow : (powMonoidHom n : G →* G).range ≤
      ((powMonoidHom n : H →* H).range).comap φ := by
    rintro x ⟨y, rfl⟩
    exact ⟨φ y, (map_pow φ y n).symm⟩
  have hq := QuotientGroup.map_surjective_of_surjective
    (powMonoidHom n : G →* G).range (powMonoidHom n : H →* H).range φ
    (QuotientGroup.mk_surjective.comp hφ) hpow
  have hc := Nat.card_le_card_of_surjective _ hq
  simpa only [← Subgroup.index_eq_card, Subgroup.index_range] using hc

/-- The torsion of the middle group is bounded by the torsion of a
homomorphism's kernel and the torsion of its target. -/
theorem power_torsion_card_le_kernel_mul_target [Finite G] [Finite H]
    (φ : G →* H) (n : ℕ) :
    Nat.card (powMonoidHom n : G →* G).ker ≤
      Nat.card (powMonoidHom n : φ.ker →* φ.ker).ker *
        Nat.card (powMonoidHom n : H →* H).ker := by
  let ψ := powerTorsionMap φ n
  let j : ψ.ker → (powMonoidHom n : φ.ker →* φ.ker).ker :=
    fun x ↦ ⟨⟨x.val.val, by
      have hx := congrArg Subtype.val x.property
      exact hx⟩, by
        apply Subtype.ext
        exact x.val.property⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (powMonoidHom n : φ.ker →* φ.ker).ker ↦ z.val.val) h
  have hk := Nat.card_le_card_of_injective j hj
  have hr := Subgroup.card_le_card_group ψ.range
  calc
    Nat.card (powMonoidHom n : G →* G).ker = Nat.card ψ.ker * Nat.card ψ.range :=
      (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ _ := Nat.mul_le_mul hk hr

end
end AffineCurveCounting
