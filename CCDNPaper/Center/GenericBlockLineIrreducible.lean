/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.GenericBlockLine
public import Mathlib.FieldTheory.Separable
import CCDN.LowerBound.GridMultivariate
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! A generic affine line in a nonconstant block of an irreducible
polynomial remains irreducible over the field of its remaining parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def genericBlockShearHom (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) (a : R) :
    MvPolynomial (Option (σ ⊕ σ)) R →ₐ[R] MvPolynomial (Option (σ ⊕ σ)) R :=
  aeval (fun q => match q with
    | none => X none
    | some (Sum.inl i) => X (some (Sum.inl i)) +
        if b i then C a * X (some (Sum.inr i)) * X none else 0
    | some (Sum.inr i) => X (some (Sum.inr i)))

private lemma genericBlockShearHom_comp {R σ : Type*} [CommRing R]
    (b : σ → Bool) (a c : R) :
    (genericBlockShearHom R b a).comp (genericBlockShearHom R b c) =
      genericBlockShearHom R b (a + c) := by
  apply MvPolynomial.algHom_ext
  intro q
  rcases q with _ | (i | i)
  · simp [genericBlockShearHom]
  · by_cases hi : b i = true
    · simp [genericBlockShearHom, hi]
      ring
    · simp [genericBlockShearHom, hi]
  · simp [genericBlockShearHom]

private lemma genericBlockShearHom_zero (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) : genericBlockShearHom R b 0 = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro q
  rcases q with _ | (i | i)
  · simp [genericBlockShearHom]
  · simp [genericBlockShearHom]
  · simp [genericBlockShearHom]

private def genericBlockShear (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) :
    MvPolynomial (Option (σ ⊕ σ)) R ≃ₐ[R] MvPolynomial (Option (σ ⊕ σ)) R :=
  AlgEquiv.ofAlgHom (genericBlockShearHom R b 1) (genericBlockShearHom R b (-1))
    (by rw [genericBlockShearHom_comp, add_neg_cancel, genericBlockShearHom_zero])
    (by rw [genericBlockShearHom_comp, neg_add_cancel, genericBlockShearHom_zero])

private lemma genericBlockLine_eq_shear {R σ : Type*} [CommRing R]
    (b : σ → Bool) (f : MvPolynomial σ R) :
    genericBlockLine b f = optionEquivLeft R (σ ⊕ σ)
      (genericBlockShear R b (rename (fun i => some (Sum.inl i)) f)) := by
  have he : genericBlockLine (R := R) b =
      (optionEquivLeft R (σ ⊕ σ)).toRingHom.comp
        ((genericBlockShear R b).toRingHom.comp
          (rename (fun i => some (Sum.inl i))).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericBlockLine, genericBlockShear, genericBlockShearHom]
    · intro i
      by_cases hi : b i = true <;>
        simp [genericBlockLine, genericBlockShear, genericBlockShearHom, hi]
  exact RingHom.congr_fun he f

private theorem genericBlockLine_irreducible {K σ : Type*} [Field K]
    (b : σ → Bool) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (genericBlockLine b f) := by
  rw [genericBlockLine_eq_shear]
  apply (MulEquiv.irreducible_iff (f := optionEquivLeft K (σ ⊕ σ))).mpr
  apply (MulEquiv.irreducible_iff (f := genericBlockShear K b)).mpr
  exact irreducible_rename_of_injective (fun i => some (Sum.inl i))
    (Option.some_injective _ |>.comp Sum.inl_injective) f hf

private theorem genericBlockLine_fraction_irreducible
    {K F σ : Type*} [Field K] [Field F]
    [Algebra (MvPolynomial (σ ⊕ σ) K) F] [IsFractionRing (MvPolynomial (σ ⊕ σ) K) F]
    (b : σ → Bool) (f : MvPolynomial σ K) (hf : Irreducible f)
    (hpos : 0 < f.weightedTotalDegree (genericBlockWeight b)) :
    Irreducible ((genericBlockLine b f).map (algebraMap (MvPolynomial (σ ⊕ σ) K) F)) := by
  have hp := genericBlockLine_irreducible b f hf
  have hd : (genericBlockLine b f).natDegree ≠ 0 := by
    rw [genericBlockLine_natDegree]
    omega
  exact (hp.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map.mp hp

/-- In characteristic zero, if `f` is irreducible and of positive degree in the block selected by
`b`, then its restriction `genericBlockLine b f` to a generic line in that block is separable as a
univariate polynomial over the fraction field `F` of the line parameters. -/
theorem genericBlockLine_fraction_separable
    {K F σ : Type*} [Field K] [CharZero K] [Field F]
    [Algebra (MvPolynomial (σ ⊕ σ) K) F] [IsFractionRing (MvPolynomial (σ ⊕ σ) K) F]
    (b : σ → Bool) (f : MvPolynomial σ K) (hf : Irreducible f)
    (hpos : 0 < f.weightedTotalDegree (genericBlockWeight b)) :
    ((genericBlockLine b f).map (algebraMap (MvPolynomial (σ ⊕ σ) K) F)).Separable := by
  let : CharZero F := charZero_of_injective_algebraMap
    (IsFractionRing.injective (MvPolynomial (σ ⊕ σ) K) F)
  exact (genericBlockLine_fraction_irreducible b f hf hpos).separable

end
end CCDN
