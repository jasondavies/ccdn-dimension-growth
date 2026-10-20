module

public import AffineCurveCounting.AffineHypersurfaceAuxiliary

/-! The coefficient-sensitive affine plane count obtained from the full
auxiliary theorem and Bezout. The bad-prime factor is the defined geometric
factor, including degree-dropping reductions; the literal printed affine
factor in CCDN has a separate statement issue. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The complete minimum expression in the affine plane count. -/
def affinePlaneCoefficientCountExpression (d : ℕ) (B L b : ℝ) : ℝ :=
  B ^ (1 / (d : ℝ)) *
      min ((d : ℝ) ^ 2 * Real.log L + (d : ℝ) ^ 3 * Real.log B + (d : ℝ) ^ 4)
        ((d : ℝ) ^ 4 * b) / L ^ (1 / (d : ℝ) ^ 2) +
    d * Real.log B + (d : ℝ) ^ 4

theorem degree_mul_affineAuxiliaryDegreeExpression (d : ℕ) (B L b : ℝ) :
    (d : ℝ) * affineAuxiliaryDegreeExpression 0 d B L b =
      affinePlaneCoefficientCountExpression d B L b := by
  have hmin :
      min ((d : ℝ) ^ 2 * Real.log L + (d : ℝ) ^ 3 * Real.log B + (d : ℝ) ^ 4)
        ((d : ℝ) ^ 4 * b) =
      (d : ℝ) ^ 2 *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
    rw [mul_min_of_nonneg _ _ (sq_nonneg (d : ℝ))]
    congr 1 <;> ring
  unfold affineAuxiliaryDegreeExpression affinePlaneCoefficientCountExpression
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero,
    one_mul, sub_self, mul_one, show (2 - 1 : ℝ) = 1 by norm_num,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [hmin]
  ring_nf

/-- Actual integral points satisfy the complete coefficient-sensitive
bound, with the original leading homogeneous coefficient height and a
single absolute constant. No geometric irreducibility is assumed. -/
theorem affine_plane_coefficient_count
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 *
        affinePlaneCoefficientCountExpression f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  obtain ⟨g, _, hfg, hgdeg, hgz⟩ :=
    affine_hypersurface_auxiliary f hprim (hprim.irreducible_of_rational_map hir) hd hB
  have hfgQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
    fun h => hfg (hprim.rational_map_dvd_iff.mp h)
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hzf hbox
  have hzQ : Function.Injective (fun i => rationalPoint (z i)) := by
    intro i j h
    apply hinj
    funext k
    exact Int.cast_injective (congrFun h k)
  have hmapzero (p : MvPolynomial (Fin 2) ℤ) (i : Fin t) (hp : eval (z i) p = 0) :
      eval (rationalPoint (z i)) (map (Int.castRingHom ℚ) p) = 0 := by
    have hh := congrArg (Int.castRingHom ℚ) hp
    rw [map_eval, map_zero] at hh
    exact hh
  have hbezout := plane_common_zeros_card_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hir hfgQ (fun i => rationalPoint (z i)) hzQ
    (fun i => hmapzero f i (hzf i)) (fun i => hmapzero g i (hgz (z i) (hbox i) (hzf i)))
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree] at hbezout
  have hcount : (t : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree := by exact_mod_cast hbezout
  apply hcount.trans
  have hh := mul_le_mul_of_nonneg_left hgdeg (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  rw [mul_left_comm, degree_mul_affineAuxiliaryDegreeExpression] at hh
  exact hh

/-- A declaration with the universal constant quantified before the
equation, degree and box, matching the uniformity in Corollary 4.2.4. -/
theorem affine_plane_coefficient_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 2) ℤ,
      PrimitiveIntegerPolynomial f → Irreducible f → 0 < f.totalDegree →
      ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * affinePlaneCoefficientCountExpression f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  refine ⟨affineHypersurfaceAuxiliaryConstant 0,
    affineHypersurfaceAuxiliaryConstant_pos 0, ?_⟩
  intro f hprim hir hd B hB
  exact affine_plane_coefficient_count f hprim
    (rational_map_irreducible_of_integer f hir hd) hd hB

end
end AffineCurveCounting
