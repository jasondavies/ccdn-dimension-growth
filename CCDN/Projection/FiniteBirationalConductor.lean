/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-! A finite extension of domains with a common fraction field has a
nonzero conductor. Clearing the denominators of finite module
generators supplies one multiplier valid for every element. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A common nonzero denominator for a finite birational extension. -/
theorem exists_nonzero_finite_birational_conductor
    (R A F : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Field F]
    [Algebra R A] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [IsFractionRing R F] [IsFractionRing A F] [Module.Finite R A] :
    ∃ c : R, c ≠ 0 ∧ ∀ a : A, ∃ r : R,
      algebraMap R A r = algebraMap R A c * a := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  let φ : A →ₐ[R] F := IsScalarTower.toAlgHom R A F
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors R) s (fun a => φ a)
  let N : Submodule R A :=
    Submodule.comap ((c : R) • φ.toLinearMap) (LinearMap.range (Algebra.linearMap R F))
  have hspan : Submodule.span R (s : Set A) ≤ N := by
    apply Submodule.span_le.mpr
    intro a ha
    exact hc a ha
  have hall (a : A) : a ∈ N := by
    apply hspan
    rw [hs]
    trivial
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.2, ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hall a
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective A F
  change algebraMap A F (algebraMap R A r) =
    algebraMap A F (algebraMap R A (c : R) * a)
  rw [map_mul, ← IsScalarTower.algebraMap_apply R A F,
    ← IsScalarTower.algebraMap_apply R A F]
  simpa only [LinearMap.smul_apply, Algebra.smul_def, Algebra.linearMap_apply,
    AlgHom.toLinearMap_apply, φ, IsScalarTower.toAlgHom_apply] using hr

end
end CCDN
