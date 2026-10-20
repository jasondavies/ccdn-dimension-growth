module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Tactic

/-! The relative ideal norm descends to the actual ideal class group.
This supplies the norm map required for quadratic descent without assuming
a class-number or ambiguous-class estimate. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open scoped nonZeroDivisors

variable (R S : Type*) [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]

/-- Relative norm on nonzero integral ideals. -/
def nonzeroIdealRelNorm : (Ideal S)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨Ideal.relNorm R (I : Ideal S), mem_nonZeroDivisors_iff_ne_zero.mpr <| by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      (Ideal.relNorm_eq_bot_iff.mp h)⟩
  map_one' := Subtype.ext (map_one (Ideal.relNorm R))
  map_mul' I J := Subtype.ext (map_mul (Ideal.relNorm R) (I : Ideal S) (J : Ideal S))

@[simp]
theorem nonzeroIdealRelNorm_coe (I : (Ideal S)⁰) :
    (nonzeroIdealRelNorm R S I : Ideal R) = Ideal.relNorm R (I : Ideal S) := rfl

theorem nonzeroIdealRelNorm_class_eq {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (nonzeroIdealRelNorm R S I) =
      ClassGroup.mk0 (nonzeroIdealRelNorm R S J) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  refine ClassGroup.mk0_eq_mk0_iff.mpr
    ⟨Algebra.intNorm R S x, Algebra.intNorm R S y, ?_, ?_, ?_⟩
  · exact Algebra.intNorm_ne_zero.mpr hx
  · exact Algebra.intNorm_ne_zero.mpr hy
  · simpa only [map_mul, Ideal.relNorm_singleton, nonzeroIdealRelNorm_coe] using
      congrArg (Ideal.relNorm R) hxy

def classGroupRelativeNormOnClass (c : ClassGroup S) : ClassGroup R :=
  ClassGroup.mk0 (nonzeroIdealRelNorm R S (ClassGroup.mk0_surjective c).choose)

theorem classGroupRelativeNormOnClass_mk0 (I : (Ideal S)⁰) :
    classGroupRelativeNormOnClass R S (ClassGroup.mk0 I) =
      ClassGroup.mk0 (nonzeroIdealRelNorm R S I) :=
  nonzeroIdealRelNorm_class_eq R S (ClassGroup.mk0_surjective (ClassGroup.mk0 I)).choose_spec

/-- The relative norm of actual ideal classes, constructed from integral
representatives and proved independent of their choice. -/
def classGroupRelativeNorm : ClassGroup S →* ClassGroup R where
  toFun := classGroupRelativeNormOnClass R S
  map_one' := by
    rw [← (ClassGroup.mk0 (R := S)).map_one, classGroupRelativeNormOnClass_mk0,
      map_one, map_one]
  map_mul' c d := by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective d
    rw [← map_mul, classGroupRelativeNormOnClass_mk0, map_mul, map_mul,
      classGroupRelativeNormOnClass_mk0, classGroupRelativeNormOnClass_mk0]

@[simp]
theorem classGroupRelativeNorm_mk0 (I : (Ideal S)⁰) :
    classGroupRelativeNorm R S (ClassGroup.mk0 I) =
      ClassGroup.mk0 (nonzeroIdealRelNorm R S I) :=
  classGroupRelativeNormOnClass_mk0 R S I

/-- Norm after extension is multiplication by the extension degree on
the ideal class group. -/
theorem classGroupRelativeNorm_extendedHom (c : ClassGroup R) :
    classGroupRelativeNorm R S (ClassGroup.extendedHom R S c) =
      c ^ Module.finrank R S := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.extendedHom_mk0, classGroupRelativeNorm_mk0, ← map_pow]
  congr 1
  apply Subtype.ext
  exact Ideal.relNorm_algebraMap S (I : Ideal R)

theorem classGroupRelativeNorm_extendedHom_eq :
    (classGroupRelativeNorm R S).comp (ClassGroup.extendedHom R S) =
      powMonoidHom (Module.finrank R S) := by
  ext c
  exact classGroupRelativeNorm_extendedHom R S c

end
end AffineCurveCounting
