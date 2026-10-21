/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateCoefficientMatrix
public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.LinearAlgebra.Matrix.Rank
import CCDN.Noether.ClosedFormGradient

/-! The closed-form coefficient matrix has corank at most one for a monic
irreducible equation of outer degree d whose coefficients have degree at most
D, in characteristic zero or larger than 2dD. This supplies the rank input to
effective Bertini. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix Submodule

lemma bivariateGridPolynomial_natDegree_lt {R : Type*} [CommRing R] {d : ℕ}
    (hd : 0 < d) (v : BivariateGrid d → R) :
    (bivariateGridPolynomial R d v).natDegree < d := by
  by_cases h : bivariateGridPolynomial R d v = 0
  · simpa only [h, natDegree_zero] using hd
  · exact (natDegree_lt_iff_degree_lt h).mpr (bivariateGridPolynomial_degree_lt v)

lemma bivariateGridPolynomial_coefficient_natDegree_le {R : Type*} [CommRing R] {d : ℕ}
    (v : BivariateGrid d → R) (i : ℕ) :
    ((bivariateGridPolynomial R d v).coeff i).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  apply le_of_lt
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  exact bivariateGridPolynomial_coeff_zero d v i j (Or.inr hj)

/-- For a normalized irreducible equation the entire coefficient kernel
maps into the one-dimensional span of the gradient. -/
theorem closedForm_kernel_image_le_gradient
    {F : Type*} [Field F] [IsAlgClosed F]
    (d : ℕ) (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d)
    (D : ℕ) (htotal : bivariateTotalDegree f ≤ D) (hchar : CharZeroOrGT F (2 * d * D)) :
    LinearMap.range ((closedFormPair F d).domRestrict
      (closedFormCoefficientMatrix d f).mulVecLin.ker) ≤
      F ∙ (f.derivative, (bivariateCoefficientDerivative F) f) := by
  rintro u ⟨v, rfl⟩
  have hv := (closedFormCoefficientMatrix_kernel d f v.val).mp (LinearMap.mem_ker.mp v.property)
  let p := (closedFormPair F d v.val).1
  let q := (closedFormPair F d v.val).2
  have hfd : f.natDegree = d := natDegree_eq_of_degree_eq_some hdeg
  have hd : 0 < d := hfd ▸ hm.natDegree_pos.mpr hf.ne_one
  have hdD : d ≤ D := hfd ▸ (bivariate_natDegree_le_totalDegree f).trans htotal
  have hp : p.natDegree < f.natDegree := hfd ▸ bivariateGridPolynomial_natDegree_lt hd _
  have hq : q.natDegree < f.natDegree := hfd ▸ bivariateGridPolynomial_natDegree_lt hd _
  have hfD (i : ℕ) : (f.coeff i).natDegree ≤ D :=
    (bivariate_coefficient_natDegree_le_totalDegree f i).trans htotal
  have hpD (i : ℕ) : (p.coeff i).natDegree ≤ D :=
    (bivariateGridPolynomial_coefficient_natDegree_le _ i).trans hdD
  have hmchar : CharZeroOrGT F f.natDegree := hchar.mono (by rw [hfd]; nlinarith)
  have hchar' : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D) :=
    hchar.mono (by rw [hfd]; exact Nat.mul_le_mul_right D (by omega))
  have he : (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f =
      q.derivative * f - q * f.derivative := by
    change (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f -
      q.derivative * f + q * f.derivative = 0 at hv
    linear_combination hv
  obtain ⟨a, ha, hb⟩ := bivariate_closed_form_eq_gradient
    f p q hf hm hp hq D hfD hpD hmchar hchar' he
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  apply Prod.ext
  · change a • f.derivative = p
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using ha.symm
  · change a • (bivariateCoefficientDerivative F) f = q
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using hb.symm

/-- No more than one independent coefficient vector solves the closed-form
matrix for an irreducible normalized equation. -/
theorem closedForm_kernel_finrank_le_one
    {F : Type*} [Field F] [IsAlgClosed F]
    (d : ℕ) (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d)
    (D : ℕ) (htotal : bivariateTotalDegree f ≤ D) (hchar : CharZeroOrGT F (2 * d * D)) :
    Module.finrank F (closedFormCoefficientMatrix d f).mulVecLin.ker ≤ 1 := by
  let U := (closedFormCoefficientMatrix d f).mulVecLin.ker
  let ψ := (closedFormPair F d).domRestrict U
  have hi : Function.Injective ψ := (closedFormPair_injective d).comp Subtype.val_injective
  have he := LinearMap.finrank_range_of_inj hi
  have hl := Submodule.finrank_mono
    (closedForm_kernel_image_le_gradient d f hf hm hdeg D htotal hchar)
  have hs : Module.finrank F (F ∙ (f.derivative, (bivariateCoefficientDerivative F) f)) ≤ 1 := by
    simpa using finrank_span_le_card (R := F)
      ({(f.derivative, (bivariateCoefficientDerivative F) f)} : Set _)
  exact he ▸ hl.trans hs

/-- The matrix on the 2*d² unknown coefficients has rank at least 2*d²-1. -/
theorem closedForm_coefficient_rank_lower
    {F : Type*} [Field F] [IsAlgClosed F]
    (d : ℕ) (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d)
    (D : ℕ) (htotal : bivariateTotalDegree f ≤ D) (hchar : CharZeroOrGT F (2 * d * D)) :
    2 * d ^ 2 ≤ (closedFormCoefficientMatrix d f).rank + 1 := by
  have he := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  have hk := closedForm_kernel_finrank_le_one d f hf hm hdeg D htotal hchar
  have hdim : Module.finrank F (ClosedFormColumns d → F) = 2 * d ^ 2 := by
    simp [ClosedFormColumns, BivariateGrid, pow_two, two_mul]
  rw [hdim] at he
  change (closedFormCoefficientMatrix d f).rank + _ = _ at he
  omega

end
end CCDN
