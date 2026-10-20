module

public import AffineCurveCounting.HypersurfacePositionedProjectiveAuxiliary
public import AffineCurveCounting.DistinguishedCoefficientOrder

/-! Source-shaped versions of CCDN Lemmas 3.3.2 and 3.3.3. Positioning is
assumed for an actual pure-power coefficient, including the last variable.
The constant `C` is any positive real number, as in the paper. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The logarithmic position parameter associated to the paper's constant. -/
def hypersurfaceSourcePositionParameter (n : ℕ) (C : ℝ) : ℝ :=
  (n + 1 : ℝ) * Real.log (max 1 C)

lemma hypersurfaceSourcePositionParameter_nonneg (n : ℕ) (C : ℝ) :
    0 ≤ hypersurfaceSourcePositionParameter n C := by
  exact mul_nonneg (by positivity) (Real.log_nonneg (le_max_left 1 C))

/-- The paper's positive pure-power coefficient gives the required monomial
order positioning without altering the equation, its height, or its zero set. -/
lemma hypersurface_pure_coefficient_log_position {n d : ℕ}
    (i : Fin (n + 3)) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    {C : ℝ} (hC : 0 < C)
    (hposition : (integerCoefficientHeight f : ℝ) *
      C ^ (-((n + 1 : ℝ) * (d : ℝ) ^ (1 + 1 / (n + 1 : ℝ)))) ≤
        (f.coeff (Finsupp.single i d) : ℝ)) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      Real.log |(((distinguishedCoefficientOrder i).leadingCoeff f : ℤ) : ℝ)| +
        hypersurfaceSourcePositionParameter n C * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
  have hH : 0 < (integerCoefficientHeight f : ℝ) := by
    exact_mod_cast integerCoefficientHeight_pos f hf0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 < C ^ (-((n + 1 : ℝ) * (d : ℝ) ^ (1 + 1 / (n + 1 : ℝ)))) :=
    Real.rpow_pos_of_pos hC _
  have hc : 0 < (f.coeff (Finsupp.single i d) : ℝ) := (mul_pos hH hp).trans_le hposition
  have hci : f.coeff (Finsupp.single i d) ≠ 0 := by
    exact_mod_cast ne_of_gt hc
  rw [distinguishedCoefficientOrder_leadingCoeff i f hf.totalDegree_le hci,
    abs_of_pos hc]
  have hh := Real.log_le_log (mul_pos hH hp) hposition
  rw [Real.log_mul hH.ne' hp.ne', Real.log_rpow hC,
    Real.rpow_add hd0, Real.rpow_one] at hh
  have hlog : Real.log C ≤ Real.log (max 1 C) := Real.log_le_log hC (le_max_right 1 C)
  have hcost := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) by positivity)
  unfold hypersurfaceSourcePositionParameter
  nlinarith

/-- CCDN Lemma 3.3.2, including its exact coefficient-one logarithmic term.
Take `i = Fin.last (n+2)` for the distinguished coefficient printed in the
paper. The remainder `4*d` is stronger than the printed `O_n(d^2)`. -/
theorem hypersurface_small_height_pure_coefficient_auxiliary
    {n d : ℕ} (i : Fin (n + 3)) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 < C)
    (hheight : (integerCoefficientHeight f : ℝ) ≤ B ^ (2 * d * (n + 2)))
    (hposition : (integerCoefficientHeight f : ℝ) *
      C ^ (-((n + 1 : ℝ) * (d : ℝ) ^ (1 + 1 / (n + 1 : ℝ)))) ≤
        (f.coeff (Finsupp.single i d) : ℝ)) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceSmallProjectiveConstant n (hypersurfaceSourcePositionParameter n C) *
        ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f *
          B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
          (integerCoefficientHeight f : ℝ) ^
            (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))))) +
        (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + 4 * d ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hH : 0 < (integerCoefficientHeight f : ℝ) := by
    exact_mod_cast integerCoefficientHeight_pos f hf0
  have hh := Real.log_le_log hH hheight
  rw [Real.log_pow] at hh
  push_cast at hh
  exact hypersurface_small_height_projective_auxiliary (distinguishedCoefficientOrder i)
    f hf hd hir hB (hypersurfaceSourcePositionParameter n C) hh
    (hypersurface_pure_coefficient_log_position i f hf hf0 hd hC hposition)

/-- CCDN Lemma 3.3.3 on the whole bounded projective zero set. Its explicit
constant depends on dimension and `C` alone, independently of `B`, `d`, and
coefficient height. The chosen monomial order requires no coordinate change. -/
theorem hypersurface_large_height_pure_coefficient_auxiliary
    {n d : ℕ} (i : Fin (n + 3)) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 < C)
    (hheight : B ^ (2 * d * (n + 2)) ≤ (integerCoefficientHeight f : ℝ))
    (hposition : (integerCoefficientHeight f : ℝ) *
      C ^ (-((n + 1 : ℝ) * (d : ℝ) ^ (1 + 1 / (n + 1 : ℝ)))) ≤
        (f.coeff (Finsupp.single i d) : ℝ)) :
    ∃ M : ℕ, (M : ℝ) ≤
        hypersurfaceLargeProjectiveConstant n (hypersurfaceSourcePositionParameter n C) *
          (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hh := Real.log_le_log (pow_pos (by linarith : 0 < B) _) hheight
  rw [Real.log_pow] at hh
  push_cast at hh
  exact hypersurface_large_height_projective_auxiliary (distinguishedCoefficientOrder i)
    f hf hd hir hB (hypersurfaceSourcePositionParameter n C)
    (hypersurfaceSourcePositionParameter_nonneg n C) hh
    (hypersurface_pure_coefficient_log_position i f hf hf0 hd hC hposition)

end
end AffineCurveCounting
