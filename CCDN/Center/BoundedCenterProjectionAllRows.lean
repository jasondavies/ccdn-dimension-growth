module

public import CCDN.Center.CenterProjectionHeight
/-! The complementary projection construction also covers the empty
projective center, represented by a matrix with zero rows. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix LinearMap

theorem exists_bounded_rational_center_projection_all_rows {r n : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (T : ℕ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      (∀ i j, |P i j| ≤ 2 * (r.factorial : ℤ) * (T : ℤ) ^ r) ∧
      P * P = D • P ∧
      IsIdempotentElem (normalizedIntegerProjection D P) ∧
      (normalizedIntegerProjection D P).ker =
        Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) ∧
      IsCompl (Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))))
        (normalizedIntegerProjection D P).range ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range + r = n + 1 ∧
      (∀ x : Fin (n + 1) → ℚ,
        x - normalizedIntegerProjection D P x ∈
          Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))) ∧
      ∀ x : Fin (n + 1) → ℚ, ∀ y : (normalizedIntegerProjection D P).range,
        x - y.val ∈ Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) →
          normalizedIntegerProjection D P x = y.val := by
  cases r with
  | succ r => exact exists_bounded_rational_center_projection A hli T hA
  | zero =>
    have hz : Submodule.span ℚ (Set.range (fun i : Fin 0 => fun j => (A i j : ℚ))) = ⊥ := by
      simp
    have hi : normalizedIntegerProjection 1 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) =
        LinearMap.id := by
      ext x j
      simp [normalizedIntegerProjection, Matrix.map_one]
    refine ⟨1,one_ne_zero,1,?_,by simp,?_,?_,?_,?_,?_,?_⟩
    · intro i j
      simp only [Matrix.one_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
      split_ifs <;> norm_num
    · rw [hi]
      exact IsIdempotentElem.one
    · simp only [hi, LinearMap.ker_id, hz]
    · simp only [hz, hi, LinearMap.range_id]
      exact isCompl_bot_top
    · rw [hi, LinearMap.range_id]
      simp
    · intro x
      simp [hi]
    · intro x y hxy
      simp only [hz, Submodule.mem_bot, sub_eq_zero] at hxy
      simpa only [hi, LinearMap.id_apply] using hxy

lemma normalizedIntegerProjection_matrix_ker {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin n) (Fin n) ℤ) :
    (P.map (Int.castRingHom ℚ)).mulVecLin.ker = (normalizedIntegerProjection D P).ker := by
  ext x
  exact (normalizedIntegerProjection_eq_zero_iff D hD P x).symm

end
end CCDN
