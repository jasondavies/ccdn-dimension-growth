/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.BinomialSectionBound
import CCDN.Auxiliary.FiniteFieldInterpolation
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Bounds

/-! Finite-field point bounds for a proper section of an irreducible
hypersurface. The proof uses polynomial interpolation and the filtered
Koszul rank estimate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The product-of-degrees factor survives in every ambient dimension. -/
theorem finite_field_common_zeros_card_le_choose {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f g : MvPolynomial (Fin (n + 2)) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (z : ι → Fin (n + 2) → K) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzg : ∀ i, eval (z i) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree *
      (n + ((n + 2) * (Fintype.card K - 1) + f.totalDegree + g.totalDegree)).choose n := by
  let I : Ideal (MvPolynomial (Fin (n + 2)) K) := Ideal.span {f} ⊔ Ideal.span {g}
  let N := (n + 2) * (Fintype.card K - 1) + f.totalDegree + g.totalDegree
  have hzI (i : ι) (u : MvPolynomial (Fin (n + 2)) K) (hu : u ∈ I) : eval (z i) u = 0 := by
    obtain ⟨v, hv, w, hw, he⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hv
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hw
    rw [← he]
    simp only [eval_add, eval_mul, hzf, hzg, zero_mul, zero_add]
  have hlower := finite_field_points_filtered_lower I z hz hzI (N := N)
    (by simp only [Fintype.card_fin]; dsimp [N]; omega)
  have hIf : f ∈ I := (show Ideal.span {f} ≤ I from le_sup_left) (Ideal.subset_span (by simp))
  have hIg : g ∈ I := (show Ideal.span {g} ≤ I from le_sup_right) (Ideal.subset_span (by simp))
  exact hlower.trans (filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg (by dsimp [N]; omega))

/-- Below the field-size degree threshold, a dimension-only constant times
(degree f)(degree g) q^(ambient dimension-2) bounds the common zeros. -/
theorem finite_field_common_zeros_card_le {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f g : MvPolynomial (Fin (n + 2)) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hdegrees : f.totalDegree + g.totalDegree ≤ 2 * (Fintype.card K - 1))
    (z : ι → Fin (n + 2) → K) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzg : ∀ i, eval (z i) g = 0) :
    Fintype.card ι ≤ (n + 4) ^ n * f.totalDegree * g.totalDegree * Fintype.card K ^ n := by
  let N := (n + 2) * (Fintype.card K - 1) + f.totalDegree + g.totalDegree
  have hq : 1 ≤ Fintype.card K := Nat.succ_le_of_lt Fintype.card_pos
  have hbase : n + N ≤ (n + 4) * Fintype.card K := by
    calc
      _ ≤ n + (n + 4) * (Fintype.card K - 1) := by dsimp [N]; nlinarith
      _ ≤ (n + 4) * Fintype.card K := by
        have he := congrArg (fun a => (n + 4) * a) (Nat.sub_add_cancel hq)
        simp only [Nat.mul_add, Nat.mul_one] at he
        omega
  have hchoose : (n + N).choose n ≤ ((n + 4) * Fintype.card K) ^ n :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hbase n)
  have h := (finite_field_common_zeros_card_le_choose f g hf hfg z hz hzf hzg).trans
    (Nat.mul_le_mul_left (f.totalDegree * g.totalDegree) hchoose)
  simpa only [mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end
end CCDN
