/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Auxiliary.AuxiliaryNonmultiple
public import CCDN.Auxiliary.HypersurfaceBadPrimeFactor
public import CCDN.Height.Box
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
import CCDN.Height.AffineTranslationCount
/-! Integral translations preserve the affine bad-prime factor, including
degree-dropping reductions and the nonabsolute zero convention. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma hypersurfaceBadReduction_affineTranslation {n : ℕ}
    (a : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ) (p : ℕ) :
    HypersurfaceBadReduction (affineTranslation ℤ a f) p ↔ HypersurfaceBadReduction f p := by
  unfold HypersurfaceBadReduction
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  rw [affineTranslation_map, affineTranslation_totalDegree, affineTranslation_totalDegree,
    affineTranslation_irreducible_iff]

theorem hypersurfaceBadPrimeFactor_affineTranslation {n : ℕ}
    (a : Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    hypersurfaceBadPrimeFactor (affineTranslation ℤ a f) = hypersurfaceBadPrimeFactor f := by
  classical
  have hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) (affineTranslation ℤ a f)) ↔
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f) := by
    rw [affineTranslation_map, affineTranslation_irreducible_iff]
  by_cases hf : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)
  · let bad := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
        HypersurfaceBadReduction f p := by
      simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    exact hypersurfaceBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad (by intro p; rw [hbad, hypersurfaceBadReduction_affineTranslation])
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf,
      hypersurfaceBadPrimeFactor_eq_zero _ (fun h => hf (hir.mp h))]

/-- Pull an auxiliary equation back through a bounded translation. -/
theorem affine_auxiliary_translation_transport {n : ℕ}
    (f g : MvPolynomial (Fin n) ℤ) (a : Fin n → ℤ) {B D : ℝ}
    (hg : IsBoxAuxiliary (affineTranslation ℤ a f) g (B + D)) (ha : ∀ j, |(a j : ℝ)| ≤ D) :
    ∃ G, IsBoxAuxiliary f G B ∧ G.totalDegree = g.totalDegree := by
  let G := (affineTranslation ℤ a).symm g
  have hG0 : G ≠ 0 := (affineTranslation ℤ a).symm.injective.ne (by simpa using hg.ne_zero)
  have hGnd : ¬ f ∣ G := by
    intro hd
    apply hg.not_dvd
    have hh := map_dvd (affineTranslation ℤ a).toRingHom hd
    change affineTranslation ℤ a f ∣ affineTranslation ℤ a ((affineTranslation ℤ a).symm g) at hh
    simpa only [AlgEquiv.apply_symm_apply] using hh
  refine ⟨G, ⟨hG0, hGnd, ?_⟩, affineTranslation_totalDegree (-a) g⟩
  intro x hx hxf
  have hx' (j) : |((x - a) j : ℝ)| ≤ B + D := by
    change |((x j - a j : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    exact (abs_sub _ _).trans (add_le_add (hx j) (ha j))
  have hf' : eval (x - a) (affineTranslation ℤ a f) = 0 := by
    rw [affineTranslation_eval, sub_add_cancel, hxf]
  change eval x (affineTranslation ℤ (-a) g) = 0
  rw [affineTranslation_eval]
  exact hg.vanishes (x - a) hx' hf'

end
end CCDN
