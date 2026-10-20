module

public import CCDN.CenterProjectionHeight

/-! Coordinate forms for the projection in CCDN (5-4), and the fixed
coordinate at infinity used to clear denominators in the affine case. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix LinearMap Module

/-- A projection along independent center rows admits dual linear
forms, normalized to take value one on the corresponding row. Their common
zero space is exactly the complementary image, and their expansion is the
projection formula (5-4). -/
theorem exists_center_projection_coordinate_forms {s n : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hP : P * P = D • P)
    (hk : (normalizedIntegerProjection D P).ker =
      Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))) :
    ∃ L : Fin (s + 1) → ((Fin (n + 1) → ℚ) →ₗ[ℚ] ℚ),
      (∀ i j, L i (fun k => (A j k : ℚ)) = if j = i then 1 else 0) ∧
      (∀ x, normalizedIntegerProjection D P x =
        x - ∑ i, L i x • (fun j => (A i j : ℚ))) ∧
      (normalizedIntegerProjection D P).range = ⨅ i, (L i).ker := by
  classical
  let S := Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))
  let Q := normalizedIntegerProjection D P
  have hid : IsIdempotentElem Q := normalizedIntegerProjection_idempotent D hD P hP
  have hres (x : Fin (n + 1) → ℚ) : ((LinearMap.id : Module.End ℚ (Fin (n + 1) → ℚ)) - Q) x ∈ S := by
    change x - Q x ∈ Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))
    rw [← hk]
    exact normalizedIntegerProjection_sub_mem_ker D hD P hP x
  let R : (Fin (n + 1) → ℚ) →ₗ[ℚ] S := (LinearMap.id - Q).codRestrict S hres
  let b : Basis (Fin (s + 1)) ℚ S := Basis.span hli
  let L : Fin (s + 1) → ((Fin (n + 1) → ℚ) →ₗ[ℚ] ℚ) :=
    fun i => (b.coord i).comp R
  have hQrow (i : Fin (s + 1)) : Q (fun j => (A i j : ℚ)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hk]
    exact Submodule.subset_span (Set.mem_range_self i)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i j
    have hR : R (fun k => (A j k : ℚ)) = b j := by
      apply Subtype.ext
      change (fun k => (A j k : ℚ)) - Q (fun k => (A j k : ℚ)) = _
      rw [hQrow, sub_zero]
      exact (Basis.coe_span_apply hli j).symm
    change b.coord i (R (fun k => (A j k : ℚ))) = _
    rw [hR]
    simp [Basis.coord_apply, Finsupp.single_apply]
  · intro x
    have he := congrArg (fun y : S => y.val) (b.sum_repr (R x))
    have he' : ∑ i, L i x • (fun j => (A i j : ℚ)) = x - Q x := by
      have hb (i : Fin (s + 1)) : (b i : Fin (n + 1) → ℚ) =
          (fun j => (A i j : ℚ)) := Basis.coe_span_apply hli i
      simpa only [Submodule.coe_sum, Submodule.coe_smul, hb, L, LinearMap.comp_apply,
        Basis.coord_apply, R, LinearMap.codRestrict_apply, LinearMap.sub_apply,
        LinearMap.id_apply] using he
    rw [he']
    abel
  · ext x
    rw [hid.mem_range_iff, Submodule.mem_iInf]
    constructor
    · intro hx i
      change b.coord i (R x) = 0
      have hRx : R x = 0 := by
        apply Subtype.ext
        change x - Q x = 0
        exact sub_eq_zero.mpr hx.symm
      rw [hRx, map_zero]
    · intro hx
      have hRx : R x = 0 := b.forall_coord_eq_zero_iff.mp hx
      have he := congrArg (fun y : S => y.val) hRx
      change x - Q x = 0 at he
      exact (sub_eq_zero.mp he).symm

/-- If the center lies in a coordinate hyperplane, projection preserves
that coordinate, as needed for the hyperplane at infinity. -/
theorem normalizedIntegerProjection_coordinate_eq {s n : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hP : P * P = D • P)
    (hk : (normalizedIntegerProjection D P).ker =
      Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))))
    (j : Fin (n + 1)) (hj : ∀ i, A i j = 0) (x : Fin (n + 1) → ℚ) :
    normalizedIntegerProjection D P x j = x j := by
  have hspan : Submodule.span ℚ (Set.range (fun i => fun k => (A i k : ℚ))) ≤
      (LinearMap.proj j : (Fin (n + 1) → ℚ) →ₗ[ℚ] ℚ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (A i j : ℚ) = 0
    simp only [hj, Int.cast_zero]
  have hres := normalizedIntegerProjection_sub_mem_ker D hD P hP x
  rw [hk] at hres
  have hz := LinearMap.mem_ker.mp (hspan hres)
  change x j - normalizedIntegerProjection D P x j = 0 at hz
  exact (sub_eq_zero.mp hz).symm

/-- A single nonzero denominator D works for every affine input: for
integer inputs with distinguished coordinate one, the explicit integral
output has that coordinate equal to D. -/
theorem integer_center_projection_fixed_coordinate {s n : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hP : P * P = D • P)
    (hk : (normalizedIntegerProjection D P).ker =
      Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))))
    (j : Fin (n + 1)) (hj : ∀ i, A i j = 0)
    (z : IntPoint (n + 1)) : (P *ᵥ z) j = D * z j := by
  have he := normalizedIntegerProjection_coordinate_eq A D hD P hP hk j hj (rationalPoint z)
  rw [normalizedIntegerProjection_apply, ← rationalPoint_integer_mulVec] at he
  change (D : ℚ)⁻¹ * ((P *ᵥ z) j : ℚ) = (z j : ℚ) at he
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have he' : ((P *ᵥ z) j : ℚ) = (D : ℚ) * (z j : ℚ) := by
    field_simp at he
    exact he
  exact_mod_cast he'

end
end CCDN
