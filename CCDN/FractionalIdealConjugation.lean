module

public import CCDN.QuadraticInvariantIdeal

/-! Compatibility of conjugation with integral representatives and with
the scalar comparisons used in the definition of an ideal class. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem fractionalIdeal_conjugate_coeIdeal (σ : R ≃+* R) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      (I.map σ.toRingHom : FractionalIdeal R⁰ K) := by
  let : RingHomInvPair (σ : R →+* R) σ.symm := RingHomInvPair.of_ringEquiv σ
  let : RingHomInvPair (σ.symm : R →+* R) σ := RingHomInvPair.of_ringEquiv σ.symm
  ext x
  change x ∈ (Submodule.map
    (IsFractionRing.semilinearEquivOfRingEquiv K K σ).toLinearMap
      (I : FractionalIdeal R⁰ K).val) ↔
    x ∈ (I.map σ.toRingHom : FractionalIdeal R⁰ K)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    apply (FractionalIdeal.mem_coeIdeal R⁰).mpr
    refine ⟨σ r, Ideal.mem_map_of_mem _ hr, ?_⟩
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ r).symm
  · intro hx
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hx
    obtain ⟨s, hs, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mp hr
    refine ⟨algebraMap R K s, (FractionalIdeal.mem_coeIdeal R⁰).mpr
      ⟨s, hs, rfl⟩, ?_⟩
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap σ s

theorem fractionalIdealUnitAction_mk0 (σ : R ≃+* R) (I : (Ideal R)⁰) :
    fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K
        ⟨(I : Ideal R).map σ.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            intro h
            have hh := Ideal.map_eq_bot_iff_of_injective (I := (I : Ideal R))
              (f := σ.toRingHom) σ.injective
            exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property) (hh.mp h))⟩ := by
  apply Units.ext
  exact fractionalIdeal_conjugate_coeIdeal σ I

theorem integral_ideal_scalar_fractional_comparison
    (σ : R ≃+* R) (I : (Ideal R)⁰) (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Ideal.span {x} * (I : Ideal R).map σ.toRingHom =
      Ideal.span {y} * (I : Ideal R)) :
    fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
      toPrincipalIdeal R K
        (Units.mk0 (algebraMap R K y) (by
          simpa only [map_zero] using (IsFractionRing.injective R K).ne hy) /
        Units.mk0 (algebraMap R K x) (by
          simpa only [map_zero] using (IsFractionRing.injective R K).ne hx)) *
      FractionalIdeal.mk0 K I := by
  let a : Kˣ := Units.mk0 (algebraMap R K x) (by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hx)
  let b : Kˣ := Units.mk0 (algebraMap R K y) (by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hy)
  have h : toPrincipalIdeal R K a *
      fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
      toPrincipalIdeal R K b * FractionalIdeal.mk0 K I := by
    apply Units.ext
    have hh := congrArg (fun J : Ideal R => (J : FractionalIdeal R⁰ K)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hh
    simp only [Units.val_mul, coe_toPrincipalIdeal, fractionalIdealUnitAction,
      Units.coe_map, FractionalIdeal.coe_mk0]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K x) *
      FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K y) * (I : FractionalIdeal R⁰ K)
    rw [fractionalIdeal_conjugate_coeIdeal]
    exact hh
  change fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
    toPrincipalIdeal R K (b / a) * FractionalIdeal.mk0 K I
  rw [map_div]
  apply mul_left_cancel (a := toPrincipalIdeal R K a)
  rw [h]
  symm
  calc
    _ = (toPrincipalIdeal R K a * (toPrincipalIdeal R K a)⁻¹) *
        (toPrincipalIdeal R K b * FractionalIdeal.mk0 K I) := by
      rw [div_eq_mul_inv]
      ac_rfl
    _ = _ := by rw [mul_inv_cancel, one_mul]

end
end CCDN
