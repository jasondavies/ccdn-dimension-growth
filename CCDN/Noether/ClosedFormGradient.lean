/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateClosedForms
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import CCDN.Determinant.DifferentialResidue
import CCDN.Determinant.SimpleRootResidue
import CCDN.ForMathlib.Polynomial
import CCDN.Noether.SeparableRootDifferential
import Mathlib.RingTheory.Polynomial.IsIntegral
/-! The monic irreducible closed-form criterion, in characteristic zero or in
characteristic larger than the displayed degree bounds. Separability, the
differential root extension and constant-residue descent are all constructed
from the polynomial and the degree bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

/-- An irreducible polynomial of degree below the characteristic is separable. -/
lemma irreducible_separable_of_natDegree_lt_char
    {K : Type*} [Field K] (f : K[X]) (hf : Irreducible f)
    (hchar : CharZeroOrGT K f.natDegree) :
    f.Separable :=
  (separable_iff_derivative_ne_zero hf).mpr (derivative_ne_zero_of_natCast_natDegree_ne_zero
    (hchar.natCast_ne_zero hf.natDegree_pos.ne' le_rfl))

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

/-- In a differential algebra over `F(t)`, the constants of `F` have derivative zero. -/
lemma deriv_algebraMap_ratFunc_base {F L : Type*} [Field F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [DifferentialAlgebra (RatFunc F) L] (a : F) :
    (algebraMap F L a)′ = 0 := by
  rw [IsScalarTower.algebraMap_apply F (RatFunc F) L, deriv_algebraMap]
  have ha : (algebraMap F (RatFunc F) a)′ = 0 := by
    change rationalDerivative (algebraMap F (RatFunc F) a) = 0
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), rationalDerivative_polynomial]
    simp
  rw [ha, map_zero]

/-- In a differential algebra over `F(t)`, the image of `t` has derivative one. -/
lemma deriv_algebraMap_ratFunc_X {F L : Type*} [Field F] [Field L]
    [Algebra (RatFunc F) L] [Differential L] [DifferentialAlgebra (RatFunc F) L] :
    (algebraMap (RatFunc F) L RatFunc.X)′ = 1 := by
  rw [deriv_algebraMap]
  have hX : (RatFunc.X : RatFunc F)′ = 1 := by
    change rationalDerivative RatFunc.X = 1
    rw [← RatFunc.algebraMap_X, rationalDerivative_polynomial, derivative_X, map_one]
  rw [hX, map_one]

/-- The closed-form equation persists over the rational function field. -/
lemma bivariate_closed_form_map_ratFunc {F : Type*} [Field F] (f g h : F[X][X])
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    Differential.mapCoeffs (g.map (algebraMap F[X] (RatFunc F))) *
        f.map (algebraMap F[X] (RatFunc F)) -
      g.map (algebraMap F[X] (RatFunc F)) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) =
      (h.map (algebraMap F[X] (RatFunc F))).derivative * f.map (algebraMap F[X] (RatFunc F)) -
        h.map (algebraMap F[X] (RatFunc F)) * (f.map (algebraMap F[X] (RatFunc F))).derivative := by
  rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
  simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
    congrArg (Polynomial.map (algebraMap F[X] (RatFunc F))) hclosed

/-- At a simple root over `F(t)`, the residue of a closed form lies in `F`. This is
the constant-residue descent, with the characteristic bounded by the residue
eliminant's degree. -/
lemma closed_form_residue_mem_base {F L : Type*} [Field F] [IsAlgClosed F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [DifferentialAlgebra (RatFunc F) L]
    (f g h : F[X][X]) (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hgdeg : g.natDegree < f.natDegree) (D : ℕ)
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hchar : CharZeroOrGT L ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative)
    (β : L) (hβ : aeval β (f.map (algebraMap F[X] (RatFunc F))) = 0)
    (hs : aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ≠ 0) :
    aeval β (g.map (algebraMap F[X] (RatFunc F))) /
      aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ∈ (algebraMap F L).range := by
  let φ := algebraMap F[X] (RatFunc F)
  let ψ := algebraMap (RatFunc F) L
  let t : L := ψ RatFunc.X
  have hmaps (q : F[X][X]) : q.map (aeval t).toRingHom = (q.map φ).map ψ := by
    ext i
    simp only [coeff_map]
    exact aeval_ratFunc_variable _
  have hclosedL : Differential.mapCoeffs ((g.map φ).map ψ) * (f.map φ).map ψ -
      (g.map φ).map ψ * Differential.mapCoeffs ((f.map φ).map ψ) =
      ((h.map φ).map ψ).derivative * (f.map φ).map ψ -
        (h.map φ).map ψ * ((f.map φ).map ψ).derivative := by
    dsimp only [ψ]
    simp only [differential_mapCoeffs_map, derivative_map]
    simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
      congrArg (Polynomial.map (algebraMap (RatFunc F) L))
        (bivariate_closed_form_map_ratFunc f g h hclosed)
  have hrootL : ((f.map φ).map ψ).eval β = 0 := by simpa only [eval_map, aeval_def] using hβ
  have hsL : ((f.map φ).map ψ).derivative.eval β ≠ 0 := by
    simpa only [derivative_map, eval_map, aeval_def] using hs
  have hder := closed_form_residue_deriv_eq_zero ((f.map φ).map ψ) ((g.map φ).map ψ)
    ((h.map φ).map ψ) β
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hrootL)
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hsL) hclosedL
  have hh := simple_root_ratio_mem_base_of_differential_constant
    deriv_algebraMap_ratFunc_base t β deriv_algebraMap_ratFunc_X f g hf hgdeg D hfD hgD hchar
    (by simpa only [hmaps] using hrootL) (by simpa only [hmaps] using hsL)
    (by simpa only [hmaps, aeval_def, Algebra.algebraMap_self, eval₂_id] using hder)
  simpa only [hmaps, ψ, derivative_map, eval_map, aeval_def] using hh

/-- The closed-form criterion over `F(t)`: a closed form within the degree bounds
is a constant multiple of the gradient. -/
lemma ratFunc_closed_form_eq_gradient {F : Type*} [Field F] [IsAlgClosed F]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : CharZeroOrGT F f.natDegree)
    (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F,
      g.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        (f.map (algebraMap F[X] (RatFunc F))).derivative ∧
      h.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) := by
  let φ := algebraMap F[X] (RatFunc F)
  let fr := f.map φ
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hfd : fr.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hsep : fr.Separable := irreducible_separable_of_natDegree_lt_char fr hfr
    (hfd ▸ (hmchar.map (algebraMap F (RatFunc F))))
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let : Fact fr.Monic := ⟨hm.map φ⟩
  let : Differential (AdjoinRoot fr) := separableAdjoinRootDifferential fr hsep
  have : DifferentialAlgebra (RatFunc F) (AdjoinRoot fr) :=
    separableAdjoinRootDifferential_algebra fr hsep
  let β : AdjoinRoot fr := AdjoinRoot.root fr
  have hβ : aeval β fr = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs : aeval β fr.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hβ
  have hres := closed_form_residue_mem_base f g h hfr hgdeg D hfD hgD
    (hchar.map (algebraMap F (AdjoinRoot fr))) hclosed β hβ hs
  have hdeg_lt (q : F[X][X]) (hq : q.natDegree < f.natDegree) : (q.map φ).degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    exact degree_le_natDegree.trans_lt
      (by exact_mod_cast (natDegree_map_eq_of_injective hinj q).trans_lt (hfd ▸ hq))
  exact closed_form_eq_constant_gradient_of_residue_mem_base fr (g.map φ) (h.map φ) hfr
    (hm.map φ) β hβ hs (hdeg_lt g hgdeg) (hdeg_lt h hhdeg)
    (bivariate_closed_form_map_ratFunc f g h hclosed) hres

/-- Over an algebraically closed field `F` of characteristic zero or larger than the
degree bounds, a monic irreducible bivariate equation has only constant-gradient closed
forms within the strict outer-variable degree bounds. -/
theorem bivariate_closed_form_eq_gradient
    {F : Type*} [Field F] [IsAlgClosed F]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : CharZeroOrGT F f.natDegree)
    (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  obtain ⟨a, ha, hb⟩ := ratFunc_closed_form_eq_gradient f g h hf hm hgdeg hhdeg D hfD hgD
    hmchar hchar hclosed
  refine ⟨a, Polynomial.map_injective φ hinj ?_, Polynomial.map_injective φ hinj ?_⟩
  · simpa only [φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, derivative_map] using ha
  · simpa only [φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map] using hb

end
end CCDN
