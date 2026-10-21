/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Set.Fin

/-!
# Images of initial segments under `Fin.snoc`, and counting pairs in `Fin n`

## Main results

* `Fin.snoc_image_Iio_castSucc`: `Fin.snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i`.
* `Fin.snoc_image_Iio_last`: `Fin.snoc v x '' Set.Iio (Fin.last k) = Set.range v`.
* `Fin.sum_card_Ioi`: there are `n.choose 2` pairs `i < j` in `Fin n`.
-/

@[expose] public section

namespace Fin

variable {α : Type*} {k : ℕ}

/-- Below `i.castSucc`, `Fin.snoc v x` takes the same values as `v` below `i`. -/
theorem snoc_image_Iio_castSucc (v : Fin k → α) (x : α) (i : Fin k) :
    snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i := by
  rw [← image_castSucc_Iio, Set.image_image]
  simp only [snoc_castSucc]

/-- Below `Fin.last k`, `Fin.snoc v x` takes exactly the values of `v`. -/
theorem snoc_image_Iio_last (v : Fin k → α) (x : α) :
    snoc v x '' Set.Iio (last k) = Set.range v := by
  have h : Set.Iio (last k) = Set.range castSucc := by
    ext j
    simp [range_castSucc, lt_def]
  rw [h, ← Set.range_comp, snoc_comp_castSucc]

/-- Counting the pairs `i < j` in `Fin n` by their smaller element gives `n.choose 2`. -/
theorem sum_card_Ioi (n : ℕ) : ∑ i : Fin n, (Finset.Ioi i).card = n.choose 2 := by
  have he (i : Fin n) : (Finset.Ioi i).card = i.rev.val := by
    rw [card_Ioi, val_rev]
    omega
  simp_rw [he]
  rw [show ∑ i : Fin n, i.rev.val = ∑ i : Fin n, i.val from
    Equiv.sum_comp revPerm (fun i : Fin n => i.val)]
  rw [sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id, Nat.choose_two_right]

end Fin
