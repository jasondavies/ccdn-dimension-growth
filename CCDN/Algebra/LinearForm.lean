/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The homogeneous linear form `∑ i, a i * X i` with a given coefficient vector,
and its basic API: homogeneity, degree, evaluation, coefficient maps, renaming and
linearity in the coefficient vector. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R S σ τ : Type*}

/-- The linear form `∑ i, a i * X i` with coefficient vector `a`. -/
def linearForm [CommSemiring R] [Fintype σ] (a : σ → R) : MvPolynomial σ R :=
  ∑ i, C (a i) * X i

section CommSemiring

variable [CommSemiring R] [Fintype σ]

lemma linearForm_isHomogeneous (a : σ → R) : (linearForm a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i)

lemma linearForm_totalDegree_le (a : σ → R) : (linearForm a).totalDegree ≤ 1 :=
  (linearForm_isHomogeneous a).totalDegree_le

@[simp] lemma eval_linearForm (a x : σ → R) : eval x (linearForm a) = ∑ i, a i * x i := by
  simp [linearForm]

@[simp] lemma aeval_linearForm [CommSemiring S] [Algebra R S] (a : σ → R) (x : σ → S) :
    aeval x (linearForm a) = ∑ i, algebraMap R S (a i) * x i := by
  simp [linearForm]

@[simp] lemma eval₂_linearForm [CommSemiring S] (φ : R →+* S) (a : σ → R) (x : σ → S) :
    eval₂ φ x (linearForm a) = ∑ i, φ (a i) * x i := by
  simp [linearForm]

lemma rename_linearForm [Fintype τ] (e : σ ≃ τ) (a : σ → R) :
    rename e (linearForm a) = linearForm (a ∘ e.symm) := by
  simp only [linearForm, map_sum, map_mul, rename_C, rename_X]
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    e.sum_comp (fun j => C (a (e.symm j)) * X j)

@[simp] lemma linearForm_zero : linearForm (0 : σ → R) = 0 := by
  simp [linearForm]

lemma linearForm_add (a b : σ → R) : linearForm (a + b) = linearForm a + linearForm b := by
  simp [linearForm, add_mul, Finset.sum_add_distrib]

lemma linearForm_smul (c : R) (a : σ → R) : linearForm (c • a) = c • linearForm a := by
  simp [linearForm, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

variable (R σ) in
/-- `linearForm` as a linear map from coefficient vectors to polynomials. -/
def linearFormLinearMap : (σ → R) →ₗ[R] MvPolynomial σ R where
  toFun := linearForm
  map_add' := linearForm_add
  map_smul' := linearForm_smul

@[simp] lemma linearFormLinearMap_apply (a : σ → R) :
    linearFormLinearMap R σ a = linearForm a :=
  rfl

end CommSemiring

section CommRing

variable [CommRing R] [Fintype σ]

end CommRing

end
end CCDN
