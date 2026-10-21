/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD

/-! A nonzero height-one prime in an integral extension of a normal unique
factorization domain contracts to a principal height-one prime. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem integral_prime_under_height_one
    (R A : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥) (hheight : Q.height ≤ 1) :
    (Q.under R).height = 1 := by
  have hne : Q.under R ≠ ⊥ := fun h => hQ (Ideal.eq_bot_of_under_eq_bot h)
  have hupper : (Q.under R).height ≤ 1 := by
    have he := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
    exact (le_self_add.trans he.symm.le).trans hheight
  apply le_antisymm hupper
  by_contra! h
  have hz : (Q.under R).height = 0 := Order.lt_one_iff.mp h
  exact hne (Ideal.height_eq_zero_iff_eq_bot.mp hz)

theorem integral_prime_under_isPrincipal
    (R A : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [UniqueFactorizationMonoid R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥) (hheight : Q.height ≤ 1) :
    (Q.under R).IsPrincipal :=
  UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    (integral_prime_under_height_one R A Q hQ hheight)

end
end CCDN
