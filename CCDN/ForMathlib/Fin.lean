/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Image

/-!
# Images of initial segments under `Fin.snoc`

## Main results

* `Fin.snoc_image_Iio_castSucc`: `Fin.snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i`.
* `Fin.snoc_image_Iio_last`: `Fin.snoc v x '' Set.Iio (Fin.last k) = Set.range v`.
-/

@[expose] public section

namespace Fin

variable {α : Type*} {k : ℕ}

/-- Below `i.castSucc`, `Fin.snoc v x` takes the same values as `v` below `i`. -/
theorem snoc_image_Iio_castSucc (v : Fin k → α) (x : α) (i : Fin k) :
    snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjk : j.val < k := lt_trans hj i.isLt
    let j' : Fin k := ⟨j.val, hjk⟩
    have he : j = j'.castSucc := rfl
    refine ⟨j', hj, ?_⟩
    rw [he, snoc_castSucc]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, snoc_castSucc _ _ _⟩

/-- Below `Fin.last k`, `Fin.snoc v x` takes exactly the values of `v`. -/
theorem snoc_image_Iio_last (v : Fin k → α) (x : α) :
    snoc v x '' Set.Iio (last k) = Set.range v := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    let j' : Fin k := ⟨j.val, hj⟩
    have he : j = j'.castSucc := rfl
    refine ⟨j', ?_⟩
    rw [he, snoc_castSucc]
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, snoc_castSucc _ _ _⟩

end Fin
