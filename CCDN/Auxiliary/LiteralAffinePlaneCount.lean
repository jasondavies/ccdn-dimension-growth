/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.LiteralAffineAuxiliaryTheorem
public import CCDN.Plane.AffinePlaneCoefficientCount
/-! CCDN Corollary 4.2.4 with the literal affine bad-prime factor and the
original coefficient-sensitive minimum. The auxiliary equation
and Bezout supply the count for every primitive irreducible plane equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Integral points satisfy the complete coefficient-sensitive
bound, with the original leading homogeneous coefficient height and a
single absolute constant. The equation need not be geometrically irreducible. -/
theorem literal_affine_plane_coefficient_count
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 *
        affinePlaneCoefficientCountExpression f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (literalAffineBadPrimeFactor f) := by
  obtain ⟨g, _, hfg, hgdeg, hgz⟩ :=
    literal_affine_hypersurface_auxiliary f hprim (hprim.irreducible_of_rational_map hir) hd hB
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

/-- The same bound with the universal constant quantified before the
equation, degree and box, matching the uniformity in Corollary 4.2.4. -/
theorem literal_affine_plane_coefficient_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 2) ℤ,
      PrimitiveIntegerPolynomial f → Irreducible f → 0 < f.totalDegree →
      ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * affinePlaneCoefficientCountExpression f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (literalAffineBadPrimeFactor f) := by
  refine ⟨affineHypersurfaceAuxiliaryConstant 0,
    affineHypersurfaceAuxiliaryConstant_pos 0, ?_⟩
  intro f hprim hir hd B hB
  exact literal_affine_plane_coefficient_count f hprim
    (rational_map_irreducible_of_integer f hir hd) hd hB

end
end CCDN
