module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

/-! Uniform control of the unit contribution to quadratic descent.
Dirichlet's theorem and cyclicity of roots of unity give at most one
binary choice per free unit and one further binary choice for torsion.
The endpoint concerns the unit group modulo squares. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

def integerParityIndex (e : ℤ) : Fin 2 :=
  ⟨(e % 2).toNat, by omega⟩

theorem zpow_eq_parity_pow {G : Type*} [Group G] (x : G)
    (hx : x ^ 2 = 1) (e : ℤ) :
    x ^ e = x ^ (integerParityIndex e).val := by
  rw [zpow_eq_zpow_emod' e hx, ← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg (Int.emod_nonneg e (by norm_num))).symm

variable (K : Type*) [Field K] [NumberField K]

/-- Every exponent-two quotient of the unit group has cardinality
at most `2^(unit rank + 1)`. The finite parametrization is constructed
from a torsion generator and a fundamental system of units. -/
theorem numberFieldUnit_exponent_two_quotient
    {G : Type*} [CommGroup G] (φ : (𝓞 K)ˣ →* G)
    (hφ : Function.Surjective φ) (hG : ∀ x : G, x ^ 2 = 1) :
    Finite G ∧ Nat.card G ≤ 2 ^ (NumberField.Units.rank K + 1) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_zpow_surjective (NumberField.Units.torsion K)
  let code : Fin 2 × (Fin (NumberField.Units.rank K) → Fin 2) → G :=
    fun e ↦ φ (ζ : (𝓞 K)ˣ) ^ e.1.val *
      ∏ i, φ (NumberField.Units.fundSystem K i) ^ (e.2 i).val
  have hcode : Function.Surjective code := by
    intro y
    obtain ⟨u, rfl⟩ := hφ y
    obtain ⟨⟨η, e⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
    obtain ⟨k, hk⟩ := hζ η
    refine ⟨(integerParityIndex k, fun i ↦ integerParityIndex (e i)), ?_⟩
    change φ (ζ : (𝓞 K)ˣ) ^ (integerParityIndex k).val *
      ∏ i, φ (NumberField.Units.fundSystem K i) ^ (integerParityIndex (e i)).val = φ u
    rw [hu, map_mul, map_prod]
    congr 1
    · rw [← hk, Subgroup.coe_zpow, map_zpow]
      exact (zpow_eq_parity_pow _ (hG _) k).symm
    · apply Finset.prod_congr rfl
      intro i _
      rw [map_zpow]
      exact (zpow_eq_parity_pow _ (hG _) (e i)).symm
  refine ⟨Finite.of_surjective code hcode, ?_⟩
  have hc := Nat.card_le_card_of_surjective code hcode
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, pow_succ, mul_comm] using hc

/-- Square classes of units of the ring of integers. -/
abbrev numberFieldUnitSquareClasses :=
  (𝓞 K)ˣ ⧸ (powMonoidHom 2 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range

omit [NumberField K] in
theorem numberFieldUnitSquareClasses_square (x : numberFieldUnitSquareClasses K) :
    x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

instance : Finite (numberFieldUnitSquareClasses K) :=
  (numberFieldUnit_exponent_two_quotient K
    (QuotientGroup.mk' (powMonoidHom 2 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range)
    (QuotientGroup.mk'_surjective _) (numberFieldUnitSquareClasses_square K)).1

theorem numberFieldUnitSquareClasses_card_le_rank :
    Nat.card (numberFieldUnitSquareClasses K) ≤
      2 ^ (NumberField.Units.rank K + 1) :=
  (numberFieldUnit_exponent_two_quotient K
    (QuotientGroup.mk' (powMonoidHom 2 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range)
    (QuotientGroup.mk'_surjective _) (numberFieldUnitSquareClasses_square K)).2

theorem numberField_unit_rank_add_one_le_degree :
    NumberField.Units.rank K + 1 ≤ Module.finrank ℚ K := by
  have hpos := Fintype.card_pos (α := InfinitePlace K)
  have hcard := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hrank := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  unfold NumberField.Units.rank
  omega

/-- The unit square-class contribution is bounded solely by the number
field degree, as needed in a uniform quadratic-tower estimate. -/
theorem numberFieldUnitSquareClasses_card_le_degree :
    Nat.card (numberFieldUnitSquareClasses K) ≤ 2 ^ Module.finrank ℚ K := by
  apply (numberFieldUnitSquareClasses_card_le_rank K).trans
  exact Nat.pow_le_pow_right (by norm_num) (numberField_unit_rank_add_one_le_degree K)

end
end CCDN
