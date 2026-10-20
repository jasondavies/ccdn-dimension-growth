module

public import CCDN.QuadraticHilbert90
public import Mathlib.RingTheory.ClassGroup.Basic

/-! An actual fractional ideal with norm-one scalar comparison to its
conjugate can be replaced in its ideal class by an invariant fractional
ideal. The norm-one hypothesis isolates the unit obstruction rather than
discarding it. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
theorem fractionField_involution (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K) := by
  have hσσ : σ.trans σ = RingEquiv.refl R := RingEquiv.ext hσ
  have h := IsFractionRing.ringEquivOfRingEquiv_comp K K K σ σ
  rw [hσσ, IsFractionRing.ringEquivOfRingEquiv_refl] at h
  intro x
  exact (RingEquiv.congr_fun h x).symm

omit [IsDomain R] in
theorem fractionField_involution_ne_refl (σ : R ≃+* R)
    (hσ : σ ≠ RingEquiv.refl R) :
    (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K) ≠ RingEquiv.refl K := by
  intro h
  apply hσ
  ext x
  apply IsFractionRing.injective R K
  have hx := RingEquiv.congr_fun h (algebraMap R K x)
  simpa only [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    RingEquiv.refl_apply] using hx

/-- Conjugation of invertible fractional ideals by a ring automorphism. -/
def fractionalIdealUnitAction (σ : R ≃+* R) :
    (FractionalIdeal R⁰ K)ˣ →* (FractionalIdeal R⁰ K)ˣ :=
  Units.map (FractionalIdeal.ringEquivOfRingEquiv K K σ).toMonoidHom

theorem fractionalIdealUnitAction_principal (σ : R ≃+* R) (b : Kˣ) :
    fractionalIdealUnitAction (K := K) σ (toPrincipalIdeal R K b) =
      toPrincipalIdeal R K
        (Units.map (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K).toMonoidHom b) := by
  apply Units.ext
  simp only [fractionalIdealUnitAction, Units.coe_map, coe_toPrincipalIdeal]
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton K K σ b

theorem classGroup_mk_principal (b : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K b) = 1 := by
  apply ClassGroup.mk_eq_one_iff.mpr
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(b : K), rfl⟩⟩

/-- Trivial scalar norm obstruction gives an invariant ideal in the
same actual ideal class, by the explicit quadratic Hilbert 90 argument. -/
theorem exists_invariant_ideal_of_scalar_norm_one
    (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl R)
    (I : (FractionalIdeal R⁰ K)ˣ) (a : Kˣ)
    (hI : fractionalIdealUnitAction (K := K) σ I = toPrincipalIdeal R K a * I)
    (ha : (a : K) *
      (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K) (a : K) = 1) :
    ∃ J : (FractionalIdeal R⁰ K)ˣ,
      ClassGroup.mk K J = ClassGroup.mk K I ∧
      fractionalIdealUnitAction (K := K) σ J = J := by
  obtain ⟨b, hb⟩ := quadratic_invariant_representative
    (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K)
    (fractionField_involution σ hσ) (fractionField_involution_ne_refl σ hσne)
    (fractionalIdealUnitAction (K := K) σ) (toPrincipalIdeal R K)
    (fractionalIdealUnitAction_principal σ) I a hI ha
  refine ⟨toPrincipalIdeal R K b * I, ?_, hb⟩
  rw [map_mul, classGroup_mk_principal, one_mul]

end
end CCDN
