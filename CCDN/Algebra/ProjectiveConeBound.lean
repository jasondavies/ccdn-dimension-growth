module

public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Plane.Plane
/-! A projective point count is bounded by the integer count on its
affine cone at the same height. Chosen primitive representatives give a
height-preserving injection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Height-preserving comparison with the affine cone, for every real radius. -/
theorem projective_count_le_affine_cone_count {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f.IsHomogeneous d) (B : ℝ) :
    projectiveCount (projectiveZeroLocus f) B ≤ count (zeroLocus f) B := by
  classical
  let S := projectivePoints (projectiveZeroLocus f) B
  have hsub : S.image primitiveProjectiveRep ⊆ integralPoints (zeroLocus f) B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hheight, hzero⟩ := mem_projectivePoints.mp hx
    apply mem_integralPoints.mpr
    refine ⟨fun i => (primitiveProjectiveRep_bound x i).trans hheight, ?_⟩
    exact (mem_projectiveZeroLocus_primitive hf x).mp hzero
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S primitiveProjectiveRep_injective] at hc
  exact hc

end
end CCDN
