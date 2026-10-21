/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectiveProjectionGrowth
import CCDN.Projection.LinearNormalizationFiberCount
/-! Dimension growth for homogeneous prime ideals of positive
projective dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The general projective-variety bound, with dimension and codimension
displayed separately. The hypotheses use the Hilbert polynomial of
the coordinate ring. -/
theorem projective_variety_dimension_growth (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I (m + 1) d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_projection_dimension_growth m k
  refine ⟨C, hC, ?_⟩
  intro I hprime hI d hd hdimdeg B hB
  have : I.IsPrime := hprime
  obtain ⟨b, hb, hnorm, hinj, _, _, f, hf, hfhom, hfdeg, hker⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le (m + 1) (m + k + 2)
      (by omega) I hI d hdimdeg
  have hrel : aeval (fun i => integerLinearForm (b i)) f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f ∈ RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i)))
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton f)
  apply hcount I d hd b hb f hf hfhom hfdeg hrel _ B hB
  intro z s hzero hproj
  exact linear_normalization_fiber_card_le I
    (fun i : Fin (m + 2) => integerLinearForm (b i.succ))
    (fun i => integerLinearForm_degree (b i.succ)) hinj hnorm d hdimdeg
    (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)

end
end CCDN
