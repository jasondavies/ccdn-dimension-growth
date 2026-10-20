module

public import CCDN.GenericBlockLine
public import CCDN.GridMultivariate
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.Separable

/-! A generic affine line in a nonconstant block of an irreducible
polynomial remains irreducible over the field of its remaining parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def genericBlockShearHom (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) (a : R) :
    MvPolynomial (Option (σ ⊕ σ)) R →ₐ[R] MvPolynomial (Option (σ ⊕ σ)) R :=
  aeval (fun q => match q with
    | none => X none
    | some (Sum.inl i) => X (some (Sum.inl i)) +
        if b i then C a * X (some (Sum.inr i)) * X none else 0
    | some (Sum.inr i) => X (some (Sum.inr i)))

lemma genericBlockShearHom_comp {R σ : Type*} [CommRing R]
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

lemma genericBlockShearHom_zero (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) : genericBlockShearHom R b 0 = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro q
  rcases q with _ | (i | i)
  · simp [genericBlockShearHom]
  · simp [genericBlockShearHom]
  · simp [genericBlockShearHom]

def genericBlockShear (R : Type*) [CommRing R] {σ : Type*}
    (b : σ → Bool) :
    MvPolynomial (Option (σ ⊕ σ)) R ≃ₐ[R] MvPolynomial (Option (σ ⊕ σ)) R :=
  AlgEquiv.ofAlgHom (genericBlockShearHom R b 1) (genericBlockShearHom R b (-1))
    (by rw [genericBlockShearHom_comp, add_neg_cancel, genericBlockShearHom_zero])
    (by rw [genericBlockShearHom_comp, neg_add_cancel, genericBlockShearHom_zero])

lemma genericBlockLine_eq_shear {R σ : Type*} [CommRing R]
    (b : σ → Bool) (f : MvPolynomial σ R) :
    genericBlockLine b f = optionEquivLeft R (σ ⊕ σ)
      (genericBlockShear R b (rename (fun i => some (Sum.inl i)) f)) := by
  have he : genericBlockLine (R := R) b =
      (optionEquivLeft R (σ ⊕ σ)).toRingHom.comp
        ((genericBlockShear R b).toRingHom.comp (rename (fun i => some (Sum.inl i))).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericBlockLine, genericBlockShear, genericBlockShearHom]
    · intro i
      by_cases hi : b i = true <;>
        simp [genericBlockLine, genericBlockShear, genericBlockShearHom, hi]
  exact RingHom.congr_fun he f

theorem genericBlockLine_irreducible {K σ : Type*} [Field K]
    (b : σ → Bool) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (genericBlockLine b f) := by
  rw [genericBlockLine_eq_shear]
  apply (MulEquiv.irreducible_iff (f := optionEquivLeft K (σ ⊕ σ))).mpr
  apply (MulEquiv.irreducible_iff (f := genericBlockShear K b)).mpr
  exact irreducible_rename_of_injective (fun i => some (Sum.inl i))
    (Option.some_injective _ |>.comp Sum.inl_injective) f hf

theorem genericBlockLine_fraction_irreducible
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
