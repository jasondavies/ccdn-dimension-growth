module

public import CCDN.QuadraticHilbert90
public import Mathlib.RingTheory.ClassGroup.Basic

/-! A fractional ideal with norm-one scalar comparison to its
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
omit [IsDomain R] in
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

end
end CCDN
