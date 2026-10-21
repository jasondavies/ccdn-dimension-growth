/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Auxiliary.HypersurfaceBadPrimeFactor
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
/-! The literal affine bad-prime factor in CCDN Definition 3.2.1.
Only failure of geometric irreducibility is counted. A reduction which loses
degree but remains geometrically irreducible is good. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def LiteralAffineBadReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

lemma LiteralAffineBadReduction.hypersurfaceBadReduction {σ : Type*}
    {f : MvPolynomial σ ℤ} {p : ℕ} (h : LiteralAffineBadReduction f p) :
    HypersurfaceBadReduction f p := ⟨h.1, Or.inr h.2⟩

lemma finite_literal_affine_bad_primes {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    {p : ℕ | 27 * f.totalDegree ^ 4 < p ∧ LiteralAffineBadReduction f p}.Finite := by
  apply (finite_fin_hypersurface_bad_primes f hf
    (absolute_integer_polynomial_totalDegree_pos f hf)).subset
  intro p hp
  exact ⟨hp.1, hp.2.hypersurfaceBadReduction⟩

def literalAffineBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ := by
  classical
  exact if h : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f) then
    Real.exp (∑ p ∈ (finite_literal_affine_bad_primes f h).toFinset, Real.log p / p)
  else 0

lemma literalAffineBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ literalAffineBadPrimeFactor f := by
  unfold literalAffineBadPrimeFactor
  split <;> positivity

lemma literalAffineBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    literalAffineBadPrimeFactor f = 0 := by
  simp only [literalAffineBadPrimeFactor, dite_eq_right hf]

lemma literalAffineBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ 27 * d ^ 4 < p ∧ LiteralAffineBadReduction f p) :
    literalAffineBadPrimeFactor f = primeSetFactor bad := by
  classical
  unfold literalAffineBadPrimeFactor
  rw [dite_eq_left hf]
  congr 1
  have he : (finite_literal_affine_bad_primes f hf).toFinset = bad := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hd, hbad]
  rw [he]

lemma literalAffineBadPrimeFactor_le_inclusive {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    literalAffineBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor f := by
  classical
  by_cases hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)
  · unfold literalAffineBadPrimeFactor hypersurfaceBadPrimeFactor
    rw [dite_eq_left hf, dite_eq_left hf]
    apply Real.exp_le_exp.mpr
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨hp.1, hp.2.hypersurfaceBadReduction⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  · rw [literalAffineBadPrimeFactor_eq_zero f hf, hypersurfaceBadPrimeFactor_eq_zero f hf]

lemma literalAffineBadReduction_affineTranslation {n : ℕ}
    (a : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ) (p : ℕ) :
    LiteralAffineBadReduction (affineTranslation ℤ a f) p ↔ LiteralAffineBadReduction f p := by
  unfold LiteralAffineBadReduction
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  rw [affineTranslation_map, affineTranslation_irreducible_iff]

theorem literalAffineBadPrimeFactor_affineTranslation {n : ℕ}
    (a : Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    literalAffineBadPrimeFactor (affineTranslation ℤ a f) = literalAffineBadPrimeFactor f := by
  classical
  have hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) (affineTranslation ℤ a f)) ↔
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f) := by
    rw [affineTranslation_map, affineTranslation_irreducible_iff]
  by_cases hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)
  · let bad := (finite_literal_affine_bad_primes f hf).toFinset
    have hbad (p) : p ∈ bad ↔ 27 * f.totalDegree ^ 4 < p ∧ LiteralAffineBadReduction f p := by
      simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [literalAffineBadPrimeFactor_eq_exp f hf rfl bad hbad]
    exact literalAffineBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad (by intro p; rw [hbad, literalAffineBadReduction_affineTranslation])
  · rw [literalAffineBadPrimeFactor_eq_zero f hf,
      literalAffineBadPrimeFactor_eq_zero _ (fun h => hf (hir.mp h))]

end
end CCDN
