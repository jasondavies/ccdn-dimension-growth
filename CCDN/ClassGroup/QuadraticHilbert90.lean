/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Echelon.Zsqrtd

/-! The degree-two multiplicative Hilbert 90 argument, stated directly
for a nontrivial field involution. This form is suited to the scalar
obstruction for ambiguous ideal classes. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K : Type*} [Field K]

/-- A norm-one scalar for a nontrivial involution is a multiplicative
coboundary. The explicit construction also works in characteristic two. -/
theorem quadratic_hilbert90 (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) {a : K} (ha : a * σ a = 1) :
    ∃ b : K, b ≠ 0 ∧ a * σ b = b := by
  by_cases h : 1 + a = 0
  · have ha' : a = -1 := by linear_combination h
    obtain ⟨z, hz⟩ : ∃ z : K, σ z ≠ z := by
      by_contra hn
      push Not at hn
      exact hσne (RingEquiv.ext hn)
    refine ⟨z - σ z, sub_ne_zero.mpr hz.symm, ?_⟩
    rw [ha', map_sub]
    change -1 * (σ z - σ (σ z)) = z - σ z
    rw [hσ]
    ring
  · refine ⟨1 + a, h, ?_⟩
    rw [map_add, map_one, mul_add, mul_one, ha, add_comm]

/-- The same construction in the multiplicative group. -/
theorem quadratic_hilbert90_units (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) (a : Kˣ)
    (ha : (a : K) * σ (a : K) = 1) :
    ∃ b : Kˣ, a * Units.map σ.toMonoidHom b = b := by
  obtain ⟨b, hb, hab⟩ := quadratic_hilbert90 σ hσ hσne ha
  exact ⟨Units.mk0 b hb, Units.ext hab⟩

/-- If the scalar comparison of an element with its conjugate has norm
one, multiplication by a principal element produces an invariant
representative. Here the principal map is a homomorphism. -/
theorem quadratic_invariant_representative
    {A : Type*} [CommGroup A]
    (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) (τ : A →* A) (P : Kˣ →* A)
    (hcompat : ∀ b : Kˣ, τ (P b) = P (Units.map σ.toMonoidHom b))
    (I : A) (a : Kˣ) (hI : τ I = P a * I)
    (ha : (a : K) * σ (a : K) = 1) :
    ∃ b : Kˣ, τ (P b * I) = P b * I := by
  obtain ⟨b, hb⟩ := quadratic_hilbert90_units σ hσ hσne a ha
  refine ⟨b, ?_⟩
  rw [map_mul, hcompat, hI, ← mul_assoc, mul_comm (P _), ← map_mul, hb]

end
end CCDN
