/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateClosedForms
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import CCDN.Determinant.DifferentialResidue
import CCDN.Determinant.PositiveCharacteristicResidue
import CCDN.Noether.BoundedDifferentialConstants
import CCDN.Noether.SeparableRootDifferential
import Mathlib.RingTheory.Polynomial.IsIntegral
/-! The monic irreducible closed-form criterion in large characteristic.
Separability, the differential root extension and constant-residue descent
are all constructed from the polynomial and the displayed degree bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

lemma irreducible_separable_of_natDegree_lt_char
    {K : Type*} [Field K] {ell : ℕ} [CharP K ell]
    (f : K[X]) (hf : Irreducible f) (hdeg : f.natDegree < ell) :
    f.Separable := by
  apply (separable_iff_derivative_ne_zero hf).mpr
  intro h
  have he := polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char f hdeg h
  have hn : f.natDegree = 0 := by rw [he, natDegree_C]
  exact (Nat.ne_of_gt hf.natDegree_pos) hn

lemma aeval_ratFunc_variable {F L : Type*} [Field F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    (a : F[X]) :
    aeval (algebraMap (RatFunc F) L RatFunc.X) a =
      algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) a) := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | monomial n c =>
    simp only [aeval_monomial, RatFunc.algebraMap_monomial, map_mul, map_pow,
      ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

theorem bivariate_closed_form_eq_gradient_of_char
    {F : Type*} [Field F] [IsAlgClosed F] {ell : ℕ} [CharP F ell]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : f.natDegree < ell)
    (hchar : (f.natDegree + (f.natDegree - 1)) * D < ell)
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let K := RatFunc F
  let φ := algebraMap F[X] K
  let fr := f.map φ
  let gr := g.map φ
  let hr := h.map φ
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hfm : fr.Monic := hm.map φ
  have hfd : fr.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hsep : fr.Separable :=
    irreducible_separable_of_natDegree_lt_char fr hfr (hfd.trans_lt hmchar)
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let : Fact fr.Monic := ⟨hfm⟩
  let L := AdjoinRoot fr
  have : CharP L ell := charP_of_injective_algebraMap (algebraMap F L).injective ell
  let : Differential L := separableAdjoinRootDifferential fr hsep
  have : DifferentialAlgebra K L := separableAdjoinRootDifferential_algebra fr hsep
  let ψ := algebraMap K L
  let β : L := AdjoinRoot.root fr
  let t : L := ψ RatFunc.X
  have hβ : aeval β fr = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs : aeval β fr.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hβ
  have hbase (a : F) : (algebraMap F L a)′ = 0 := by
    rw [IsScalarTower.algebraMap_apply F K L, deriv_algebraMap]
    have ha : (algebraMap F K a)′ = 0 := by
      change rationalDerivative (algebraMap F K a) = 0
      rw [IsScalarTower.algebraMap_apply F F[X] K, rationalDerivative_polynomial]
      simp
    rw [ha, map_zero]
  have ht : t′ = 1 := by
    change (algebraMap K L RatFunc.X)′ = 1
    rw [deriv_algebraMap]
    have hX : (RatFunc.X : K)′ = 1 := by
      change rationalDerivative RatFunc.X = 1
      rw [← RatFunc.algebraMap_X, rationalDerivative_polynomial, derivative_X, map_one]
    rw [hX, map_one]
  have hmaps (q : F[X][X]) :
      q.map (aeval t).toRingHom = (q.map φ).map ψ := by
    ext i
    simp only [coeff_map]
    exact aeval_ratFunc_variable _
  have hclosedR : Differential.mapCoeffs gr * fr - gr * Differential.mapCoeffs fr =
      hr.derivative * fr - hr * fr.derivative := by
    dsimp only [fr, gr, hr, φ]
    rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
    simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using congrArg (Polynomial.map φ) hclosed
  have hclosedL : Differential.mapCoeffs (gr.map ψ) * fr.map ψ -
      gr.map ψ * Differential.mapCoeffs (fr.map ψ) =
      (hr.map ψ).derivative * fr.map ψ - hr.map ψ * (fr.map ψ).derivative := by
    dsimp only [ψ]
    simp only [differential_mapCoeffs_map, derivative_map]
    simpa only [ψ, Polynomial.map_sub, Polynomial.map_mul] using congrArg (Polynomial.map ψ) hclosedR
  have hrootL : (fr.map ψ).eval β = 0 := by simpa only [eval_map, aeval_def] using hβ
  have hsL : (fr.map ψ).derivative.eval β ≠ 0 := by
    simpa only [derivative_map, eval_map, aeval_def] using hs
  have hder := closed_form_residue_deriv_eq_zero (fr.map ψ) (gr.map ψ) (hr.map ψ) β
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hrootL)
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hsL) hclosedL
  have hres : aeval β gr / aeval β fr.derivative ∈ (algebraMap F L).range := by
    have hh := simple_root_ratio_mem_base_of_differential_constant (p := ell)
      hbase t β ht f g hfr hgdeg D hfD hgD hchar
      (by simpa only [hmaps] using hrootL)
      (by simpa only [hmaps] using hsL)
      (by simpa only [hmaps, aeval_def, Algebra.algebraMap_self, eval₂_id] using hder)
    simpa only [hmaps, gr, fr, ψ, derivative_map, eval_map, aeval_def] using hh
  have hgR : gr.degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show gr.natDegree < fr.natDegree by
      simpa only [gr, fr, natDegree_map_eq_of_injective hinj] using hgdeg)
  have hhR : hr.degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show hr.natDegree < fr.natDegree by
      simpa only [hr, fr, natDegree_map_eq_of_injective hinj] using hhdeg)
  obtain ⟨a, ha, hb⟩ := closed_form_eq_constant_gradient_of_residue_mem_base
    fr gr hr hfr hfm β hβ hs hgR hhR hclosedR hres
  refine ⟨a, ?_, ?_⟩
  · apply Polynomial.map_injective φ hinj
    simpa only [gr, fr, φ, K, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, derivative_map] using ha
  · apply Polynomial.map_injective φ hinj
    simpa only [hr, fr, φ, K, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map] using hb

end
end CCDN
