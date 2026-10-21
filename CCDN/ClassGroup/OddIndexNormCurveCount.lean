/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineNonzeroConstant
public import CCDN.ClassGroup.ClassGroupNormPolynomial
import CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import CCDN.ClassGroup.SquareNormCurveIrreducibility
import CCDN.Plane.PlaneCount
/-! Uniform counts for signed norm curves whose parameter generates a
subfield of odd index. The ambient field degree may be even. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField IntermediateField

def oddIndexNormCurveCountConstant : ℝ :=
  2 * Real.exp 1 * affineNonzeroConstantBound 161

lemma oddIndexNormCurveCountConstant_pos : 0 < oddIndexNormCurveCountConstant :=
  mul_pos (by positivity) (affineNonzeroConstantBound_pos 161)

theorem signed_norm_curve_count_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      oddIndexNormCurveCountConstant * (Module.finrank ℚ K : ℝ) ^ 3 *
        B ^ (1 / (Module.finrank ℚ K : ℝ)) *
          (Real.log B + Module.finrank ℚ K) := by
  have hεQ : (ε : ℚ) ≠ 0 := by exact_mod_cast hε
  have hd := signedNormCurvePolynomial_map_totalDegree K ℚ β hεQ hn
  have hir : Irreducible (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε))) := by
    have hcomp : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AlgebraicClosure ℚ) := by ext; simp
    rw [MvPolynomial.map_map, hcomp]
    exact signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
      K β hε hindex
  have h := count_rational_plane_of_residue_bound _ hir (by omega) hB
    (by norm_num : (0 : ℝ) ≤ 161) planeResidueBound
  rw [hd] at h
  simpa only [curveBound, oddIndexNormCurveCountConstant, mul_assoc] using h

end
end CCDN
