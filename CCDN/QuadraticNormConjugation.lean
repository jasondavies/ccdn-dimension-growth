module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Tactic

/-! Explicit quadratic conjugation formulas. These identify the
two-element Galois group, the field norm, and its fixed field; they
connect the unit-norm obstruction with the involution formulation. -/

@[expose] public section
namespace CCDN
noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]

theorem quadratic_automorphism_eq_one_or
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (τ : K ≃ₐ[F] K) : τ = 1 ∨ τ = σ := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hc : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
  by_cases hτ : τ = 1
  · exact Or.inl hτ
  · right
    have he : (Finset.univ.erase (1 : K ≃ₐ[F] K)).card ≤ 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc]
    exact Finset.card_le_one.mp he _ (by simp [hτ]) _ (by simp [hσ])

theorem quadratic_automorphism_involutive
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) :
    Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hs : σ ^ 2 = 1 := by
    simpa only [IsGalois.card_aut_eq_finrank, hd] using
      (pow_card_eq_one' (x := σ))
  intro x
  simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using
    congrArg (fun τ : K ≃ₐ[F] K ↦ τ x) hs

theorem quadratic_norm_eq_mul_conjugate
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * σ x := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  rw [Algebra.norm_eq_prod_automorphisms]
  have hp := Fintype.prod_eq_mul (f := fun τ : K ≃ₐ[F] K ↦ τ x)
    1 σ hσ.symm (fun τ hτ ↦
      False.elim ((quadratic_automorphism_eq_one_or F K hd σ hσ τ).elim hτ.1 hτ.2))
  simpa only [AlgEquiv.one_apply] using hp

theorem quadratic_fixed_iff_mem_base
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (x : K) :
    σ x = x ↔ x ∈ Set.range (algebraMap F K) := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro hx τ
    rcases quadratic_automorphism_eq_one_or F K hd σ hσ τ with rfl | rfl
    · exact AlgEquiv.one_apply x
    · exact hx
  · exact fun hx ↦ hx σ

end
end CCDN
