module

public import CCDN.ProjectiveProjectionGrowth
public import CCDN.LinearNormalizationFiberCount
public import CCDN.PolynomialPredicates

/-! Dimension growth for actual homogeneous prime ideals of positive
projective dimension. Normalization, primitive projection, exact image degree,
finite fibers and height control are all constructed in the proof. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The general projective-variety bound, with dimension and codimension
displayed separately. The hypotheses use the actual Hilbert polynomial of
the coordinate ring and contain no supplied projection or counting theorem. -/
theorem projective_variety_dimension_growth (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).natDegree = m + 2 →
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 2).factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectiveProjectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_projection_dimension_growth m k
  refine ⟨C, hC, ?_⟩
  intro I hprime hI d hd hdim hdegree B hB
  let : I.IsPrime := hprime
  obtain ⟨b, hb, hnorm, hinj, _, _, f, hf, hfhom, hfdeg, hker⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le (m + 1) (m + k + 2)
      (by omega) I hI d hdim hdegree
  have hrel : aeval (fun i => integerLinearForm (b i)) f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f ∈ RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i)))
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton f)
  apply hcount I d hd b hb f hf hfhom hfdeg hrel _ B hB
  intro z s hzero hproj
  exact linear_normalization_fiber_card_le I
    (fun i : Fin (m + 2) => integerLinearForm (b i.succ))
    (fun i => integerLinearForm_degree (b i.succ)) hinj hnorm d hdim hdegree
    (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)

end
end CCDN
