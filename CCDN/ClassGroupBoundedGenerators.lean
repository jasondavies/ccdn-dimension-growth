module

public import CCDN.ClassGroupBalancedGenerator
public import Mathlib.Data.Set.Card

/-! The first counting reduction for two-torsion ideal classes:
inject them into the finite set of bounded algebraic integers whose absolute
norm is a square. Both possible signs of the signed norm are retained. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

def boundedSquareNormIntegers (B : ℝ) : Set (𝓞 K) :=
  {β | β ≠ 0 ∧ (∀ w : InfinitePlace K, w (β : K) ≤ B) ∧
    ∃ m : ℕ, (Algebra.norm ℤ β).natAbs = m ^ 2}

lemma boundedSquareNormIntegers_finite (B : ℝ) :
    (boundedSquareNormIntegers K B).Finite := by
  apply Set.Finite.of_injOn (f := fun β : 𝓞 K ↦ (β : K))
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
  · intro β hβ
    exact ⟨β.isIntegral_coe, fun φ ↦ hβ.2.1 (InfinitePlace.mk φ)⟩
  · exact RingOfIntegers.coe_injective.injOn
  · exact Embeddings.finite_of_norm_le K ℂ B

/-- The bounded-integer reduction has no hypothesis supplying representatives
or a counting family: the injection comes from the proved Minkowski step. -/
theorem classGroupTwoTorsionCard_le_boundedSquareNormIntegers :
    classGroupTwoTorsionCard K ≤
      (boundedSquareNormIntegers K
        (9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard := by
  obtain ⟨β, hinj, hβ⟩ := exists_injective_balanced_two_torsion_generators K
  rw [classGroupTwoTorsionCard, ← Set.ncard_range_of_injective hinj]
  apply Set.ncard_le_ncard _ (boundedSquareNormIntegers_finite K _)
  rintro _ ⟨c, rfl⟩
  obtain ⟨h0, hw, J, _, _, hnorm⟩ := hβ c
  exact ⟨h0, fun w ↦ (hw w).le, Ideal.absNorm (J : Ideal (𝓞 K)), hnorm⟩

omit [NumberField K] in
end
end CCDN
