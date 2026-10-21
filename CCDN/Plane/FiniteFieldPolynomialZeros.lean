/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalPlaneWitness
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! The polynomial zero bound on the full affine parameter space, with its
field-size saving retained in multiplicative form. This wraps Mathlib's Schwartz–Zippel
lemma `MvPolynomial.schwartz_zippel_totalDegree`, applied to the whole finite field and
restated as a cardinality bound over an arbitrary finite coordinate type. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma finite_field_polynomial_zeros_mul_card_fin {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    Nat.card {x : Fin n → K // eval x f = 0} * Fintype.card K ≤
      f.totalDegree * Fintype.card K ^ n := by
  classical
  have h := schwartz_zippel_totalDegree hf (Finset.univ : Finset K)
  have hR : (Fintype.card {x : Fin n → K // eval x f = 0} : ℚ) /
      (Fintype.card K : ℚ) ^ n ≤ f.totalDegree / (Fintype.card K : ℚ) := by
    simpa [Fintype.card_subtype] using (NNRat.cast_le (K := ℚ)).mpr h
  have hq : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hc := (div_le_div_iff₀ (pow_pos hq n) hq).mp hR
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hc

/-- Schwartz--Zippel for an arbitrary finite coordinate type. -/
theorem finite_field_polynomial_zeros_mul_card {K τ : Type*} [Field K] [Fintype K]
    [Fintype τ] (f : MvPolynomial τ K) (hf : f ≠ 0) :
    Nat.card {x : τ → K // eval x f = 0} * Fintype.card K ≤
      f.totalDegree * Fintype.card K ^ Fintype.card τ := by
  classical
  let e := Fintype.equivFin τ
  let g := rename e f
  have hg : g ≠ 0 := (map_ne_zero_iff _ (rename_injective e e.injective)).mpr hf
  let ψ : {x : τ → K // eval x f = 0} →
      {x : Fin (Fintype.card τ) → K // eval x g = 0} := fun x =>
    ⟨x.val ∘ e.symm, by simpa [g, eval_rename, Function.comp_def] using x.property⟩
  have hψ : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    funext i
    have hh := congrArg (fun z => z.val (e i)) h
    simpa [ψ] using hh
  have hcard := Fintype.card_le_of_injective ψ hψ
  have hb := finite_field_polynomial_zeros_mul_card_fin g hg
  simp only [Nat.card_eq_fintype_card] at hb ⊢
  exact ((Nat.mul_le_mul_right (Fintype.card K) hcard).trans hb).trans
    (Nat.mul_le_mul_right _ (totalDegree_rename_le e f))

end
end CCDN
