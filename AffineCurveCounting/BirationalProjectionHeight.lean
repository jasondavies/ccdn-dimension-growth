module

public import AffineCurveCounting.BoundedBirationalHypersurfaceProjection

/-! The constructed projection has a coefficient bound polynomial in
the actual degree, with exponent and constant depending only on ambient
dimension. -/

@[expose] public section
namespace AffineCurveCounting

def birationalProjectionHeightConstant (n : ℕ) : ℕ :=
  n.factorial * 2 ^ n + (n + 1) ^ n

lemma birationalProjectionHeightConstant_pos (n : ℕ) :
    0 < birationalProjectionHeightConstant n := by
  dsimp [birationalProjectionHeightConstant]
  positivity

theorem integerBirationalProjectionHeight_le (n d : ℕ) (hd : 1 ≤ d) :
    integerBirationalProjectionHeight n d ≤
      birationalProjectionHeightConstant n * d ^ (2 * n) := by
  have hpow : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  have hfirst : integerNormalizationHeight n d ≤
      (n.factorial * 2 ^ n) * d ^ (2 * n) := by
    dsimp only [integerNormalizationHeight]
    calc
      _ ≤ n.factorial * (2 * d) ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n.factorial * 2 ^ n) * d ^ n := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd (by omega))
  have hsecond : (n * d ^ 2 + 1) ^ n ≤ (n + 1) ^ n * d ^ (2 * n) := by
    calc
      _ ≤ ((n + 1) * d ^ 2) ^ n :=
        Nat.pow_le_pow_left (by nlinarith) _
      _ = _ := by rw [Nat.mul_pow, ← pow_mul]
  apply max_le
  · exact hfirst.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact hsecond.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

end AffineCurveCounting
