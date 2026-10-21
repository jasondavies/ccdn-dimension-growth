/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! Finite prime decomposition and codimension two for an intersection
 of two equations. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A nontrivial two-equation intersection with prime first equation is purely
of codimension two: all its minimal primes have height two. -/
theorem minimalPrime_pair_height_two {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {f g : R} (hf : Prime f) (hfg : ¬ f ∣ g)
    {p : Ideal R} (hp : p ∈ (Ideal.span ({f, g} : Set R)).minimalPrimes) :
    p.height = 2 := by
  classical
  have : p.IsPrime := hp.isPrime
  let : (Ideal.span ({f} : Set R)).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hpf : Ideal.span ({f} : Set R) ≤ p :=
    (Ideal.span_mono (by simp : ({f} : Set R) ⊆ {f, g})).trans hp.le
  have hpg : g ∈ p := hp.le (Ideal.subset_span (by simp))
  have hlt : Ideal.span ({f} : Set R) < p := by
    apply lt_of_le_of_ne hpf
    intro he
    exact hfg (Ideal.mem_span_singleton.mp (he ▸ hpg))
  have h1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  have hlo := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [h1] at hlo
  have hhi : p.height ≤ 2 := by
    have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := ({f, g} : Finset R)) (by simpa using hp)
    exact h.trans (by exact_mod_cast (Finset.card_le_two : ({f, g} : Finset R).card ≤ 2))
  norm_num at hlo
  exact le_antisymm hhi hlo

end
end CCDN
