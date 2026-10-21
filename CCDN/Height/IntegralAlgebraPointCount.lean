/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! Uniform counts for coordinate tuples obtained from integral
algebra homomorphisms. A normal base ring bounds every integral generator's
minimal polynomial by the degree of the fraction-field extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

theorem integral_coordinate_tuple_count
    {R A k ι : Type*} [CommRing R] [CommRing A] [Field k]
    [Algebra R A] [Algebra R k] [Fintype ι]
    (a : ι → A) (ha : ∀ i, IsIntegral R (a i))
    (s : Finset (ι → k))
    (hs : ∀ x ∈ s, ∃ φ : A →ₐ[R] k, ∀ i, φ (a i) = x i) :
    s.card ≤ ∏ i, (minpoly R (a i)).natDegree := by
  classical
  let p : ι → k[X] := fun i => (minpoly R (a i)).map (algebraMap R k)
  have hp (i) : (p i).Monic := (minpoly.monic (ha i)).map _
  have hroot {x : ι → k} (hx : x ∈ s) (i) : x i ∈ (p i).roots := by
    obtain ⟨φ, hφ⟩ := hs x hx
    apply Polynomial.mem_roots (hp i).ne_zero |>.mpr
    change (p i).eval (x i) = 0
    rw [← hφ i]
    dsimp only [p]
    rw [Polynomial.eval_map_algebraMap]
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hsub : s ⊆ Fintype.piFinset (fun i => (p i).roots.toFinset) := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun i => Multiset.mem_toFinset.mpr (hroot hx i))
  apply (Finset.card_le_card hsub).trans
  rw [Fintype.card_piFinset]
  apply Finset.prod_le_prod
  intro i _
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' (p i)).trans (Polynomial.natDegree_map_le))

theorem integral_minpoly_natDegree_le_fraction_finrank
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E] (a : A) (ha : IsIntegral R a) :
    (minpoly R a).natDegree ≤ Module.finrank F E := by
  rw [← (minpoly.monic ha).natDegree_map (algebraMap R F),
    ← minpoly.isIntegrallyClosed_eq_field_fractions F E ha]
  exact minpoly.natDegree_le (algebraMap A E a)

/-- A polynomial degree bound for every finite set of specialization
tuples. -/
theorem integral_coordinate_tuple_count_le_finrank_pow
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E]
    {k ι : Type*} [Field k] [Algebra R k] [Fintype ι]
    (a : ι → A) (ha : ∀ i, IsIntegral R (a i))
    (s : Finset (ι → k))
    (hs : ∀ x ∈ s, ∃ φ : A →ₐ[R] k, ∀ i, φ (a i) = x i) :
    s.card ≤ (Module.finrank F E) ^ Fintype.card ι := by
  apply (integral_coordinate_tuple_count a ha s hs).trans
  calc
    (∏ i, (minpoly R (a i)).natDegree) ≤ ∏ _i : ι, Module.finrank F E := by
      apply Finset.prod_le_prod
      intro i _
      exact integral_minpoly_natDegree_le_fraction_finrank R A F E (a i) (ha i)
    _ = _ := by simp

end
end CCDN
