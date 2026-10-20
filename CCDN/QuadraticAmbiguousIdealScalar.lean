module

public import CCDN.ClassGroupQuadraticInvolution

/-! An ideal class fixed by a quadratic involution has a scalar
comparison with its conjugate. Applying the involution twice shows that
the scalar norm is an invariant unit. This is the concrete unit
obstruction in the passage from ambiguous classes to invariant ideals. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

omit [IsDedekindDomain R] in
theorem ideal_map_involutive (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (I : Ideal R) : (I.map (σ : R →+* R)).map (σ : R →+* R) = I := by
  rw [Ideal.map_map]
  have hh : (σ : R →+* R).comp (σ : R →+* R) = RingHom.id R :=
    RingHom.ext hσ
  rw [hh, Ideal.map_id]

/-- The norm obstruction is represented by an actual invariant unit of
the ring. The equation uses integral numerators and denominators, so
there is no choice of a fraction field in the statement. -/
theorem ambiguous_ideal_scalar_invariant_unit
    (σ : R ≃+* R) (hσ : Function.Involutive σ) (I : (Ideal R)⁰)
    (hI : ClassGroup.mulEquiv σ (ClassGroup.mk0 I) = ClassGroup.mk0 I) :
    ∃ x y : R, ∃ u : Rˣ, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * (I : Ideal R).map (σ : R →+* R) =
        Ideal.span {y} * (I : Ideal R) ∧
      (x * σ x) * (u : R) = y * σ y ∧ σ (u : R) = (u : R) := by
  rw [ClassGroup.mulEquiv_mk0] at hI
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hI
  change Ideal.span {x} * (I : Ideal R).map (σ : R →+* R) =
    Ideal.span {y} * (I : Ideal R) at hxy
  have hσxy := congrArg (fun J : Ideal R ↦ J.map (σ : R →+* R)) hxy
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    ideal_map_involutive σ hσ] at hσxy
  change Ideal.span {σ x} * (I : Ideal R) =
    Ideal.span {σ y} * (I : Ideal R).map (σ : R →+* R) at hσxy
  have hn : Ideal.span {x * σ x} * (I : Ideal R) =
      Ideal.span {y * σ y} * (I : Ideal R) := by
    calc
      Ideal.span {x * σ x} * (I : Ideal R) =
          Ideal.span {x} * (Ideal.span {σ x} * (I : Ideal R)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc]
      _ = Ideal.span {x} *
          (Ideal.span {σ y} * (I : Ideal R).map (σ : R →+* R)) := by rw [hσxy]
      _ = Ideal.span {σ y} *
          (Ideal.span {x} * (I : Ideal R).map (σ : R →+* R)) := by ac_rfl
      _ = Ideal.span {σ y} * (Ideal.span {y} * (I : Ideal R)) := by rw [hxy]
      _ = Ideal.span {y * σ y} * (I : Ideal R) := by
        rw [← Ideal.span_singleton_mul_span_singleton]
        ac_rfl
  have hn' : Ideal.span {x * σ x} = Ideal.span {y * σ y} :=
    mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp I.property) hn
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hn'
  refine ⟨x, y, u, hx, hy, hxy, hu, ?_⟩
  have hσu := congrArg σ hu
  simp only [map_mul] at hσu
  change (σ x * σ (σ x)) * σ (u : R) = σ y * σ (σ y) at hσu
  rw [hσ, hσ] at hσu
  have hsx : σ x ≠ 0 := by simpa only [map_zero] using σ.injective.ne hx
  apply mul_left_cancel₀ (mul_ne_zero hx hsx)
  calc
    (x * σ x) * σ (u : R) = (σ x * x) * σ (u : R) := by ac_rfl
    _ = σ y * y := hσu
    _ = y * σ y := mul_comm _ _
    _ = (x * σ x) * (u : R) := hu.symm

end
end CCDN
