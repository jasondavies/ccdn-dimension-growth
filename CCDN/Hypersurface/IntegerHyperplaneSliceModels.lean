/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
import CCDN.Hypersurface.GoodHyperplane
import CCDN.Hypersurface.IntegerGoodHyperplaneSlices
/-! Integer equations for every parallel level of a good hyperplane whose
normal has cubic degree height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_good_integer_hyperplane_slices {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ) (g : ℤ → MvPolynomial (Fin (3 + n)) ℤ),
      D ≠ 0 ∧ |D| ≤ (f.totalDegree ^ 3 : ℕ) ∧
      (∀ i, |a i| ≤ (f.totalDegree ^ 3 : ℕ)) ∧
      ∀ k : ℤ, (g k).totalDegree = f.totalDegree ∧
        HasAbsIrreducibleTopForm (g k) ∧
        ∀ x : Option (Fin (3 + n)) → ℤ,
          D * x none - ∑ i, a i * x (some i) = k →
          eval x f = 0 → eval (fun i => x (some i)) (g k) = 0 := by
  obtain ⟨D, a, hD, hDb, hab, _, hgood⟩ := exists_geometrically_good_hyperplane
    (homogeneousComponent f.totalDegree f) f.totalDegree hd
    (homogeneousComponent_isHomogeneous _ _) hir
  obtain ⟨g, hg⟩ := exists_integer_hyperplane_slice_models f D a hD hgood
  exact ⟨D, a, g, hD, hDb, hab, hg⟩

end
end CCDN
