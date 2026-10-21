module

public import CCDN.HypersurfaceAuxiliaryTheorem
public import CCDN.ProjectivePlaneBezout

/-! The coefficient-sensitive first inequality in CCDN Corollary 3.1.2,
from the full auxiliary theorem and projective Bezout. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projective_plane_coefficient_count {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant 0 *
        ((d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * B ^ (2 / (d : ℝ)) /
            (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) +
          d * Real.log B + (d : ℝ) ^ 4) := by
  classical
  obtain ⟨M, hdegree, g, hg0, hgh, hzero, hgnd⟩ := hypersurface_projective_auxiliary f hf hd hir hB
  dsimp only [hypersurfaceAuxiliaryDegreeBound, auxDegreeBound, auxMainTerm, boxExponent,
    heightExponent, degreeRoot] at hdegree
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  have hQ := rational_map_irreducible_of_integer f hir (by rw [hf.totalDegree hir.ne_zero]; exact hd)
  have hnd : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g := by
    rwa [hprim.rational_map_dvd_iff]
  have hc := projective_plane_common_zeros_card_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) (hf.map _) hQ (hgh.map _) hnd
    (fun x : S => x.val) Subtype.val_injective
    (fun x => (mem_projectivePoints.mp x.property).2)
    (fun x => hzero x.val (mem_projectivePoints.mp x.property).1 (mem_projectivePoints.mp x.property).2)
  have hcR : (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (d : ℝ) * M := by
    have hh : projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B ≤ d * M := by
      simpa only [Fintype.card_coe, S, projectiveCount] using hc
    exact_mod_cast hh
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hh := mul_le_mul_of_nonneg_left hdegree hd0
  norm_num only [Nat.cast_zero, zero_add, div_one, one_mul, Real.rpow_one,
    sub_self, Real.rpow_zero, mul_one] at hh
  norm_num at hh
  apply hcR.trans
  convert hh using 1
  ring_nf

end
end CCDN
