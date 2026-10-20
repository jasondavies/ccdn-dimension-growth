module

public import CCDN.ClassGroupTwoTorsion
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.GroupTheory.Index

/-! The group-theoretic part of quadratic class-group descent. An
involution on an elementary abelian two-group has at least the square
root of the group's cardinality in fixed points. This is applied to the
action of a field involution on two-torsion ideal classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

theorem two_torsion_card_le_involution_fixed_square
    {G : Type*} [CommGroup G] [Finite G]
    (σ : G →* G) (hσ : Function.Involutive σ) (hG : ∀ x : G, x ^ 2 = 1) :
    Nat.card G ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := by
  let τ : G →* G := (MonoidHom.id G) * σ
  have hker : τ.ker ≤ σ.eqLocus (MonoidHom.id G) := by
    intro x hx
    change x * σ x = 1 at hx
    change σ x = x
    apply mul_left_cancel (a := x)
    exact hx.trans (by simpa only [pow_two] using (hG x).symm)
  have hrange : τ.range ≤ σ.eqLocus (MonoidHom.id G) := by
    rintro x ⟨y, rfl⟩
    change σ (y * σ y) = y * σ y
    rw [map_mul, hσ, mul_comm]
  have hk := Nat.card_le_card_of_injective (Subgroup.inclusion hker)
    (Subgroup.inclusion_injective hker)
  have hr := Nat.card_le_card_of_injective (Subgroup.inclusion hrange)
    (Subgroup.inclusion_injective hrange)
  calc
    Nat.card G = Nat.card τ.ker * Nat.card τ.range :=
      (Subgroup.card_ker_mul_card_range τ).symm
    _ ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) *
        Nat.card (σ.eqLocus (MonoidHom.id G)) := Nat.mul_le_mul hk hr
    _ = Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := (pow_two _).symm

theorem classGroup_mulEquiv_involutive
    {R : Type*} [CommRing R] [IsDomain R]
    (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (ClassGroup.mulEquiv σ) := by
  intro c
  change ClassGroup.map (σ : R →+* R)
    (show Function.Injective (σ : R →+* R) from σ.injective)
    (ClassGroup.map (σ : R →+* R)
      (show Function.Injective (σ : R →+* R) from σ.injective) c) = c
  rw [ClassGroup.map_map]
  have hh : (σ : R →+* R).comp (σ : R →+* R) = RingHom.id R :=
    RingHom.ext hσ
  simpa only [hh] using ClassGroup.map_id c

variable (K : Type*) [Field K]

/-- The action of a field automorphism on two-torsion ideal classes. -/
def classGroupTwoTorsionAction (σ : K ≃+* K) :
    classGroupTwoTorsion K →* classGroupTwoTorsion K where
  toFun c := ⟨ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c, by
    change (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val) ^ 2 = 1
    rw [← map_pow, show c.val ^ 2 = 1 from c.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)

theorem classGroupTwoTorsionAction_involutive (σ : K ≃+* K)
    (hσ : Function.Involutive σ) :
    Function.Involutive (classGroupTwoTorsionAction K σ) := by
  have hσO : Function.Involutive (RingOfIntegers.mapRingEquiv σ) := by
    intro x
    exact RingOfIntegers.ext (hσ x)
  intro c
  apply Subtype.ext
  exact classGroup_mulEquiv_involutive _ hσO c

/-- Two-torsion classes fixed by the specified field automorphism. -/
def fixedClassGroupTwoTorsion (σ : K ≃+* K) : Subgroup (classGroupTwoTorsion K) :=
  (classGroupTwoTorsionAction K σ).eqLocus (MonoidHom.id _)

@[simp]
theorem mem_fixedClassGroupTwoTorsion (σ : K ≃+* K) (c : classGroupTwoTorsion K) :
    c ∈ fixedClassGroupTwoTorsion K σ ↔
      ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val = c.val :=
  Subtype.ext_iff

variable [NumberField K]

/-- The factor of two in the quadratic rank estimate is proved here for
the class-group action. Bounding the fixed subgroup arithmetically
is a separate genus-theory step. -/
theorem classGroupTwoTorsionCard_le_fixed_square (σ : K ≃+* K)
    (hσ : Function.Involutive σ) :
    classGroupTwoTorsionCard K ≤ Nat.card (fixedClassGroupTwoTorsion K σ) ^ 2 := by
  apply two_torsion_card_le_involution_fixed_square
    (classGroupTwoTorsionAction K σ) (classGroupTwoTorsionAction_involutive K σ hσ)
  intro c
  exact Subtype.ext c.property

end
end CCDN
