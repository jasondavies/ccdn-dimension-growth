/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Nonvanishing of natural number casts

## Main results

* `natCast_ne_zero_of_algebra`: a natural number that is nonzero in a field is nonzero in every
  nontrivial algebra over it. This is the `≠` form of the instance
  `NeZero.nat_of_injective (algebraMap F R).injective`.
* `CharP.natCast_ne_zero_of_lt`: a positive natural number below the characteristic is nonzero.
-/

@[expose] public section

/-- A natural number that is nonzero in a field is nonzero in every nontrivial algebra. -/
theorem natCast_ne_zero_of_algebra {F R : Type*} [Field F] [Semiring R] [Nontrivial R]
    [Algebra F R] {n : ℕ} (h : (n : F) ≠ 0) : (n : R) ≠ 0 := by
  rw [← map_natCast (algebraMap F R)]
  exact (map_ne_zero _).mpr h

namespace CharP

/-- A positive natural number below the characteristic is nonzero. -/
theorem natCast_ne_zero_of_lt (R : Type*) [AddMonoidWithOne R] {p : ℕ} [CharP R p] {n : ℕ}
    (hn : n ≠ 0) (hnp : n < p) : (n : R) ≠ 0 := fun h =>
  Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) hnp ((cast_eq_zero_iff R p n).mp h)

end CharP
