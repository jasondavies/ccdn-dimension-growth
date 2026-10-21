/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Finiteness.Attr

/-!
# Nonvanishing of natural number casts

## Main results

* `CharP.natCast_ne_zero_of_lt`: a positive natural number below the characteristic is nonzero.
-/

@[expose] public section

namespace CharP

/-- A positive natural number below the characteristic is nonzero. -/
theorem natCast_ne_zero_of_lt (R : Type*) [AddMonoidWithOne R] {p : ℕ} [CharP R p] {n : ℕ}
    (hn : n ≠ 0) (hnp : n < p) : (n : R) ≠ 0 := fun h =>
  Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) hnp ((cast_eq_zero_iff R p n).mp h)

end CharP
