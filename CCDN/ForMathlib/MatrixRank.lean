/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nonzero minors of matrices with arbitrarily many rows

The row index type may be infinite, as for coefficient matrices indexed by all monomials; only
the column index type is finite.

## Main results

* `Matrix.exists_fin_linearIndependent_row_span_eq`: finitely many linearly independent rows
  span the row space.
* `Matrix.exists_rank_linearIndependent_rows`: there are `A.rank` linearly independent rows.
* `Matrix.exists_det_submatrix_ne_zero_of_le_rank`: every `r ≤ A.rank` is witnessed by a
  nonzero `r × r` minor with distinct rows and columns.
-/

@[expose] public section

namespace Matrix

/-- A finite independent family spans the rows even when their original index
set is infinite. -/
theorem exists_fin_linearIndependent_row_span_eq
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) :
    ∃ (s : ℕ) (a : Fin s → ι), Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' F A.row
  let : Finite κ := hi.finite
  let : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  have hli : LinearIndependent F (A.submatrix (a ∘ e) id).row := hi.comp e e.injective
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, hli, ?_⟩
  have hr : Set.range (A.submatrix (a ∘ e) id).row = Set.range (A.row ∘ a) := by
    change Set.range ((A.row ∘ a) ∘ e) = _
    exact e.surjective.range_comp _
  rw [hr, hs]

/-- Restriction to spanning rows preserves the exact kernel. -/
theorem ker_mulVecLin_submatrix_eq_of_span_row_eq
    {F ι κ ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) (a : κ → ι)
    (hs : Submodule.span F (Set.range (A.submatrix a id).row) =
      Submodule.span F (Set.range A.row)) :
    (A.submatrix a id).mulVecLin.ker = A.mulVecLin.ker := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    ext i
    have hm : A.row i ∈ Submodule.span F (Set.range (A.submatrix a id).row) := by
      rw [hs]
      exact Submodule.subset_span ⟨i, rfl⟩
    change A.row i ⬝ᵥ v = 0
    suffices hh : ∀ r ∈ Submodule.span F (Set.range (A.submatrix a id).row), r ⬝ᵥ v = 0 from hh _ hm
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨j, rfl⟩ := hr
      exact congrFun hv j
    | zero => simp
    | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
    | smul b x hx ih => simp [smul_dotProduct, ih]
  · intro hv
    ext i
    exact congrFun hv (a i)

/-- There are exactly rank-many independent rows. -/
theorem exists_rank_linearIndependent_rows
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) :
    ∃ a : Fin A.rank → ι, Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row := by
  obtain ⟨s, a, ha, hi, hs⟩ := exists_fin_linearIndependent_row_span_eq A
  have hk := ker_mulVecLin_submatrix_eq_of_span_row_eq A a hs
  have h₁ := (A.submatrix a id).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.mulVecLin.finrank_range_add_finrank_ker
  change (A.submatrix a id).rank + _ = _ at h₁
  change A.rank + _ = _ at h₂
  rw [hi.rank_matrix, Fintype.card_fin, hk] at h₁
  have he : s = A.rank := by omega
  subst s
  exact ⟨a, ha, hi⟩

/-- Full row rank supplies a nonzero square minor: some set of columns of the transpose is
linearly independent. -/
theorem exists_det_submatrix_ne_zero_of_linearIndependent_row
    {F ν : Type*} [Field F] [Fintype ν] {s : ℕ}
    (A : Matrix (Fin s) ν F) (hi : LinearIndependent F A.row) :
    ∃ c : Fin s → ν, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  have hr : Aᵀ.rank = s := by rw [rank_transpose, hi.rank_matrix, Fintype.card_fin]
  obtain ⟨c, hc, hli⟩ := exists_rank_linearIndependent_rows Aᵀ
  let e := finCongr hr
  refine ⟨c ∘ e.symm, hc.comp e.symm.injective, ?_⟩
  have hcol : LinearIndependent F (A.submatrix id (c ∘ e.symm)).col :=
    hli.comp e.symm e.symm.injective
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det]
  exact linearIndependent_col_iff_isUnit.mp hcol

/-- Every rank lower bound is witnessed by a nonzero minor with distinct rows
and distinct columns, without any finiteness requirement on the rows. -/
theorem exists_det_submatrix_ne_zero_of_le_rank
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F)
    (r : ℕ) (hr : r ≤ A.rank) :
    ∃ (a : Fin r → ι) (c : Fin r → ν), Function.Injective a ∧
      Function.Injective c ∧ (A.submatrix a c).det ≠ 0 := by
  obtain ⟨a, ha, hi⟩ := exists_rank_linearIndependent_rows A
  let b : Fin r → Fin A.rank := Fin.castLE hr
  have hb : Function.Injective b := Fin.castLE_injective hr
  have hli : LinearIndependent F (A.submatrix (a ∘ b) id).row := hi.comp b hb
  obtain ⟨c, hc, hd⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_row _ hli
  exact ⟨a ∘ b, c, ha.comp hb, hc, hd⟩

end Matrix
