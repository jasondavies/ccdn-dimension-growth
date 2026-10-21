/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.BoundedCenterProjection
/-! The intrinsic projective height of the projection from a bounded
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

end
end CCDN
