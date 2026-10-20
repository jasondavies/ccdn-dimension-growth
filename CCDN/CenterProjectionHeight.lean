module

public import CCDN.BoundedCenterProjection

/-! The intrinsic projective height of the genuine projection from a bounded
integer center. The common-denominator cofactor construction gives a stronger
bound than the exponent in CCDN (5-5), without the incorrect row-separation
constant printed in Lemma 5.4. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

lemma projectivization_normalizedIntegerProjection {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (x : Fin (n + 1) → ℚ) (hx : normalizedIntegerProjection D P x ≠ 0) :
    ∃ hxP : (P.map (Int.castRingHom ℚ)) *ᵥ x ≠ 0,
      Projectivization.mk ℚ (normalizedIntegerProjection D P x) hx =
        Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x) hxP := by
  have hxP : (P.map (Int.castRingHom ℚ)) *ᵥ x ≠ 0 :=
    fun h => hx ((normalizedIntegerProjection_eq_zero_iff D hD P x).mpr h)
  refine ⟨hxP, (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr ?_⟩
  exact ⟨(D : ℚ)⁻¹, rfl⟩

/-- The normalized rational projection has an explicit integral projective
representative, obtained by multiplying the primitive input by the same
integer matrix. Its coordinates satisfy the stated bound. -/
theorem normalizedIntegerProjection_integer_representative {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (x : ProjectivePoint n) (hx : normalizedIntegerProjection D P x.rep ≠ 0) :
    ∃ hw : P *ᵥ primitiveProjectiveRep x ≠ 0,
      Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx =
        Projectivization.mk ℚ (rationalPoint (P *ᵥ primitiveProjectiveRep x))
          (rationalPoint_ne_zero hw) ∧
      ∀ i, |((P *ᵥ primitiveProjectiveRep x) i : ℝ)| ≤
        (n + 1 : ℕ) * H * x.mulHeight := by
  obtain ⟨hxP, he⟩ := projectivization_normalizedIntegerProjection D hD P x.rep hx
  have hrep := (primitiveProjectiveRep_mk x).trans x.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp hrep
  have hw : rationalPoint (P *ᵥ primitiveProjectiveRep x) =
      (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) := by
    rw [rationalPoint_integer_mulVec, ← hc, Matrix.mulVec_smul]
    rfl
  have hw0 : P *ᵥ primitiveProjectiveRep x ≠ 0 := by
    intro hz
    have hzero : (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) = 0 := by
      rw [← hw, hz]
      rfl
    exact hxP ((smul_eq_zero.mp hzero).resolve_left c.ne_zero)
  refine ⟨hw0, he.trans ?_, integer_linear_map_box_bound P hH hP
    (primitiveProjectiveRep x) (primitiveProjectiveRep_bound x)⟩
  symm
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
  exact ⟨c, hw.symm⟩

lemma normalizedIntegerProjection_projective_height {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (x : ProjectivePoint n) (hx : normalizedIntegerProjection D P x.rep ≠ 0) :
    (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
      (n + 1 : ℕ) * H * x.mulHeight := by
  obtain ⟨hxP, he⟩ := projectivization_normalizedIntegerProjection D hD P x.rep hx
  rw [he]
  exact projective_linear_map_height P hH hP x hxP

/-- A dimension-only constant, independent of the degree and the center. -/
def centerProjectionHeightConstant (n : ℕ) : ℕ :=
  2 * (n + 1) * (n + 1).factorial * (n + 1) ^ (2 * (n + 1))

lemma centerProjectionHeightConstant_pos (n : ℕ) : 0 < centerProjectionHeightConstant n := by
  unfold centerProjectionHeightConstant
  positivity

lemma center_projection_source_exponent {m n r d : ℕ}
    (hr : 1 ≤ r) (hrn : r ≤ n + 1) (hmn : m + 1 ≤ n + 1) (hd : 1 ≤ d) :
    (n + 1) * (2 * r.factorial * ((m + 1) ^ 2 * d ^ 2) ^ r) ≤
      centerProjectionHeightConstant n * d ^ (2 * r ^ 2) := by
  have hf := Nat.factorial_le hrn
  have hp : (m + 1) ^ (2 * r) ≤ (n + 1) ^ (2 * (n + 1)) := by
    calc
      _ ≤ (n + 1) ^ (2 * r) := Nat.pow_le_pow_left hmn _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hrd : d ^ (2 * r) ≤ d ^ (2 * r ^ 2) := by
    apply Nat.pow_le_pow_right hd
    nlinarith
  calc
    _ = (2 * (n + 1) * r.factorial * (m + 1) ^ (2 * r)) * d ^ (2 * r) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
    _ ≤ (2 * (n + 1) * (n + 1).factorial * (n + 1) ^ (2 * (n + 1))) *
        d ^ (2 * r ^ 2) := by gcongr
    _ = _ := rfl

/-- From bounded independent rows alone, construct the rational
projection and complementary projective (m+1)-space of Section 5.1. The
exponent is exactly the exponent in (5-5); the integral matrix has the
stronger cofactor bound of degree 2r, where r is the vector dimension of
the center. Existence of a geometrically good center is separate. -/
theorem exists_center_projection_source_height {s m n d : ℕ}
    (hd : 1 ≤ d) (hdim : (s + 1) + (m + 2) = n + 1)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (hA : ∀ i j, |A i j| ≤ (((m + 1) ^ 2 * d ^ 2 : ℕ) : ℤ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      (∀ i j, |P i j| ≤ 2 * ((s + 1).factorial : ℤ) *
        (((m + 1) ^ 2 * d ^ 2 : ℕ) : ℤ) ^ (s + 1)) ∧
      P * P = D • P ∧
      IsIdempotentElem (normalizedIntegerProjection D P) ∧
      (normalizedIntegerProjection D P).ker =
        Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) ∧
      IsCompl (Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))))
        (normalizedIntegerProjection D P).range ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 ∧
      (∀ x : Fin (n + 1) → ℚ,
        x - normalizedIntegerProjection D P x ∈
          Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))) ∧
      ∀ x : ProjectivePoint n,
        x.rep ∉ Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) →
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (centerProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * (s + 1) ^ 2) *
              x.mulHeight := by
  obtain ⟨D, hD, P, hb, hPP, hi, hk, hc, hdim', hsub, _⟩ :=
    exists_bounded_rational_center_projection A hli ((m + 1) ^ 2 * d ^ 2) hA
  refine ⟨D, hD, P, hb, hPP, hi, hk, hc, by omega, hsub, ?_⟩
  intro x hx
  have hx' : normalizedIntegerProjection D P x.rep ≠ 0 := by
    intro hz
    apply hx
    rw [← hk, LinearMap.mem_ker]
    exact hz
  refine ⟨hx', ?_⟩
  have hbR : ∀ i j, |(P i j : ℝ)| ≤
      2 * ((s + 1).factorial : ℝ) * (((m + 1) ^ 2 * d ^ 2 : ℕ) : ℝ) ^ (s + 1) := by
    intro i j
    exact_mod_cast hb i j
  apply (normalizedIntegerProjection_projective_height D hD P (by positivity) hbR x hx').trans
  apply mul_le_mul_of_nonneg_right _ x.mulHeight_pos.le
  exact_mod_cast center_projection_source_exponent (m := m) (n := n) (r := s + 1)
    (d := d) (by omega) (by omega) (by omega) hd

end
end CCDN
