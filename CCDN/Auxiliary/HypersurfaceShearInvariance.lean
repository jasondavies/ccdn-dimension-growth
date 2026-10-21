/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Auxiliary.HypersurfaceBadPrimes
import CCDN.Algebra.ProjectiveTranslation
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
/-! The geometric bad-prime predicate is invariant under integral shears. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma hypersurfaceBadReduction_homogeneousTranslation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (a : Fin n → ℤ) (p : ℕ) :
    HypersurfaceBadReduction (homogeneousTranslation ℤ a f) p ↔ HypersurfaceBadReduction f p := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    have hg0 : homogeneousTranslation ℤ a f ≠ 0 := by
      exact (homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)
    rw [homogeneous_hypersurfaceBadReduction_iff _ (homogeneousTranslation_homogeneous a hf) hg0,
      homogeneous_hypersurfaceBadReduction_iff _ hf hf0, homogeneousTranslation_map]
    exact not_congr (MulEquiv.irreducible_iff
      (f := homogeneousTranslation (AlgebraicClosure (ZMod p)) ((Int.castRingHom _) ∘ a)))
  · constructor <;> intro h <;> exact (hp h.1).elim

end
end CCDN
