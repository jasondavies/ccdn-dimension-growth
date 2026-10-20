module

public import AffineCurveCounting.HilbertBoundedElimination
public import AffineCurveCounting.IntegralProjectionHilbert

/-! A complete bounded elimination step: the actual contraction stays prime,
retains dimension, and has no larger Hilbert multiplicity. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def eliminationLinearCoordinates {σ : Type*} (b : Option σ → ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  fun i => X (some i) - C (b (some i) / b none) * X none

lemma eliminationLinearCoordinates_degree {σ : Type*} (b : Option σ → ℚ) (i : σ) :
    (eliminationLinearCoordinates b i).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

lemma coordinateEliminationMap_eq_projection {σ : Type*}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) (b : Option σ → ℚ) (hb : b none ≠ 0) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) =
      projectionCoordinateMap I (eliminationLinearCoordinates b) := by
  ext i
  rw [coordinateEliminationMap_direction_X]
  simp [projectionCoordinateMap, eliminationLinearCoordinates]

/-- Construct a bounded integral projection and its actual prime
contraction with the same Hilbert dimension and multiplicity at most d.
This is the induction step for bounded linear normalization. -/
theorem exists_multiplicity_bounded_elimination_step
    {σ : Type*} [Fintype σ] [LinearOrder σ] [LinearOrder (Option σ)] {m : ℕ}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hcodim : m < Fintype.card σ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial) :
    ∃ (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0) (e : ℕ),
      (∀ i, 0 ≤ b i ∧ b i ≤ d + 1) ∧ 0 < e ∧ e ≤ d ∧
      let ψ := coordinateEliminationMap I
        (hypersurfaceAffineCoordinates 0 (fun i => (b i : ℚ)) hb)
      ψ.IsIntegral ∧ (RingHom.ker ψ).IsPrime ∧
      (filteredHilbertPolynomial (RingHom.ker ψ)).natDegree = m + 1 ∧
      (filteredHilbertPolynomial (RingHom.ker ψ)).leadingCoeff =
        (e : ℚ) / (m + 1).factorial := by
  obtain ⟨b, hb, hbound, hint⟩ :=
    exists_multiplicity_bounded_integral_linear_elimination I d hdim hcodim hdegree
  rw [coordinateEliminationMap_eq_projection] at hint
  obtain ⟨hprojdim, e, he, hed, hprojdegree⟩ :=
    integral_linear_projection_multiplicity I
      (eliminationLinearCoordinates (fun i => (b i : ℚ)))
      (eliminationLinearCoordinates_degree _) hint d (by simpa only [hdim] using hdegree)
  refine ⟨b, hb, e, hbound, he, hed, ?_⟩
  dsimp only
  rw [coordinateEliminationMap_eq_projection]
  exact ⟨hint, RingHom.ker_isPrime _, hprojdim.trans hdim, by
    simpa only [hdim] using hprojdegree⟩

end
end AffineCurveCounting
