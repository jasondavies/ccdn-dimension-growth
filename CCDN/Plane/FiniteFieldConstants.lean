/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! The prime cutoff `27 d⁴` and the absolute constants of the finite-field point counts.

Every count below holds for primes `p > stepanovThreshold d = 27 d⁴` and has the shape
`main term + C d² √p · (lower-order power of p)`. The constants are derived from the plane
constant `planeResidueConstant = 161` by explicit additive corrections, recorded here with
the lemmas where they arise. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The prime cutoff `27 d⁴` of the Stepanov method. For `p > 27 d⁴` the integer Stepanov
parameters `A = ⌊√p / d⌋`, `D = ⌊(p - 1) / d⌋`, `N = d A - 4 d²` exist with `N > 0`
(`exists_stepanov_integer_parameters`), the Hilbert-dimension inequality holds
(`stepanov_numeric_dimension`), and `√p < 32 N` (`stepanov_real_bound`), since
`31² · 27 > 160²`. Bad primes are only counted above this cutoff; below it the trivial
bounds are used. The definition is polymorphic so that it reads the same over `ℕ` and `ℝ`. -/
def stepanovThreshold {R : Type*} [Semiring R] (d : R) : R := 27 * d ^ 4

@[simp, norm_cast]
lemma Nat.cast_stepanovThreshold {R : Type*} [Semiring R] (d : ℕ) :
    ((stepanovThreshold d : ℕ) : R) = stepanovThreshold (d : R) := by
  simp [stepanovThreshold]

@[gcongr]
lemma stepanovThreshold_le_stepanovThreshold {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) :
    stepanovThreshold a ≤ stepanovThreshold b := by
  unfold stepanovThreshold
  have : (0 : R) ≤ 27 := Nat.ofNat_nonneg 27
  gcongr

/-- The constant `161` of the affine plane-curve count `#C(𝔽_p) ≤ p + 161 d² √p`
(`plane_finite_field_card_bound`). In `stepanov_real_bound` the Stepanov count
`t N ≤ d D + p (N + 4 d²) + d² N` is bounded using `d D < p`, `(4 d² + 1) p ≤ 5 d² p`,
`p ≤ 32 N √p` and `1 ≤ √p`, giving `t ≤ p + (5 · 32 + 1) d² √p`. -/
def planeResidueConstant : ℝ := 161

/-- The constant `162 = 161 + 1` of the projective plane-curve count
(`projective_plane_finite_field_card_bound`): the affine chart contributes
`p + 161 d² √p` and the line at infinity at most `d ≤ d² √p` further points. -/
def projectivePlaneResidueConstant : ℝ := planeResidueConstant + 1

/-- The constant `C = 164 = 162 + 2` for which the projective plane total multiplicity is
at most `p + (C + 1) d² √p` (`projectivePlaneTotalMultiplicity_le`). The singular
correction `3 d² (d - 1) ≤ 3 d² √p` adds `3` to `162`; the shift by one matches the affine
convention of `degreeFourDeterminantError`, whose singular correction `d² (d - 1)` costs `1`. -/
def projectivePlaneDeterminantConstant : ℝ := projectivePlaneResidueConstant + 2

/-- The constant `164 = 161 + 3` of the affine hypersurface count
`#X(𝔽_p) ≤ p^(m-1) + 164 d² p^(m-2) √p` (`affine_hypersurface_finite_field_bound`). Averaging
the plane count over plane sections gives `161`; bad and zero plane sections cost at most
`3 d² p √p` (`hypersurface_bad_section_error`). -/
def hypersurfaceResidueConstant : ℝ := planeResidueConstant + 3

/-- The constant `330 = 2 (164 + 1)` of the projective hypersurface count
(`projective_hypersurface_finite_field_bound`). Applied to the affine cone count with error
`H = 164 d² √p`, `homogeneous_projective_count_of_cone_bound` gives the projective error
`2 (H + 1) p^(m-2)`, and `1 ≤ d² √p`. -/
def projectiveHypersurfaceResidueConstant : ℝ := 2 * (hypersurfaceResidueConstant + 1)

lemma planeResidueConstant_eq : planeResidueConstant = 161 := rfl

lemma projectivePlaneResidueConstant_eq : projectivePlaneResidueConstant = 162 := by
  norm_num [projectivePlaneResidueConstant, planeResidueConstant]

lemma projectivePlaneDeterminantConstant_eq : projectivePlaneDeterminantConstant = 164 := by
  norm_num [projectivePlaneDeterminantConstant, projectivePlaneResidueConstant_eq]

lemma hypersurfaceResidueConstant_eq : hypersurfaceResidueConstant = 164 := by
  norm_num [hypersurfaceResidueConstant, planeResidueConstant]

lemma projectiveHypersurfaceResidueConstant_eq : projectiveHypersurfaceResidueConstant = 330 := by
  norm_num [projectiveHypersurfaceResidueConstant, hypersurfaceResidueConstant_eq]

lemma planeResidueConstant_pos : 0 < planeResidueConstant := by
  norm_num [planeResidueConstant]

lemma projectivePlaneDeterminantConstant_pos : 0 < projectivePlaneDeterminantConstant := by
  norm_num [projectivePlaneDeterminantConstant_eq]

lemma hypersurfaceResidueConstant_pos : 0 < hypersurfaceResidueConstant := by
  norm_num [hypersurfaceResidueConstant_eq]

lemma projectiveHypersurfaceResidueConstant_pos : 0 < projectiveHypersurfaceResidueConstant := by
  norm_num [projectiveHypersurfaceResidueConstant_eq]

end
end CCDN
