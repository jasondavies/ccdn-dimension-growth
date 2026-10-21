/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Auxiliary.HypersurfaceBadPrimeFactor
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
/-!
# The literal affine bad-prime factor

`literalAffineBadPrimeFactor f` is the factor `b(f)` of CCDN Definition 3.2.1 applied verbatim
to an affine integer polynomial `f`: it sums `log p / p` over the primes `p > 27 d⁴` at which the
reduction of `f` is not absolutely irreducible (`LiteralAffineBadReduction`). A reduction that
loses degree but remains absolutely irreducible is good, so primes at which `f` drops degree are
not counted.

This is in contrast with `hypersurfaceBadPrimeFactor` (`HypersurfaceBadReduction`), which also
counts primes at which the degree drops, and is the factor used for homogeneous equations; the
literal factor is at most it (`literalAffineBadPrimeFactor_le_inclusive`). The printed proof of
Proposition 4.2.1 passes to the homogenization `F₁` of `f` and uses `b(F₁) = b(f)`, which fails
(`Counterexample/HomogenizedBadPrimeFactor.lean`). The `LiteralAffine*` modules therefore prove
Proposition 4.2.1 and Corollary 4.2.4 with the literal factor, working in the affine chart.
-/

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
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ LiteralAffineBadReduction f p}.Finite := by
  apply (finite_fin_hypersurface_bad_primes f hf
    (absolute_integer_polynomial_totalDegree_pos f hf)).subset
  intro p hp
  exact ⟨hp.1, hp.2.hypersurfaceBadReduction⟩

/-- The literal affine bad-prime factor of CCDN Definition 3.2.1: `badPrimeFactor` for
`LiteralAffineBadReduction`, which counts only failure of absolute irreducibility. -/
def literalAffineBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ :=
  badPrimeFactor LiteralAffineBadReduction finite_literal_affine_bad_primes f

lemma literalAffineBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ literalAffineBadPrimeFactor f :=
  badPrimeFactor_nonneg f

lemma literalAffineBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    literalAffineBadPrimeFactor f = 0 :=
  badPrimeFactor_eq_zero hf

lemma literalAffineBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ LiteralAffineBadReduction f p) :
    literalAffineBadPrimeFactor f = primeSetFactor bad :=
  badPrimeFactor_eq_primeSetFactor hf hd bad hbad

lemma literalAffineBadPrimeFactor_le_inclusive {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    literalAffineBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor f :=
  badPrimeFactor_mono f fun _ h => h.hypersurfaceBadReduction

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
    have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
        LiteralAffineBadReduction f p := by
      simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [literalAffineBadPrimeFactor_eq_exp f hf rfl bad hbad]
    exact literalAffineBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad (by intro p; rw [hbad, literalAffineBadReduction_affineTranslation])
  · rw [literalAffineBadPrimeFactor_eq_zero f hf,
      literalAffineBadPrimeFactor_eq_zero _ (fun h => hf (hir.mp h))]

end
end CCDN
