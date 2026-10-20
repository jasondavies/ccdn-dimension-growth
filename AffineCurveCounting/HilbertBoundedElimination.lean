module

public import AffineCurveCounting.HilbertLowDegreeEquation
public import AffineCurveCounting.BoundedLinearElimination

/-! One actual bounded integral linear elimination, with the bound controlled
by geometric Hilbert multiplicity rather than a supplied ideal equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Every positive-dimensional prime ideal of positive codimension admits
an integral linear projection eliminating one variable, with integer
direction coordinates between zero and d+1. -/
theorem exists_multiplicity_bounded_integral_linear_elimination
    {σ : Type*} [Fintype σ] [LinearOrder (Option σ)] {m : ℕ}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hcodim : m < Fintype.card σ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial) :
    ∃ (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0),
      (∀ i, 0 ≤ b i ∧ b i ≤ d + 1) ∧
      (coordinateEliminationMap I
        (hypersurfaceAffineCoordinates 0 (fun i => (b i : ℚ)) hb)).IsIntegral := by
  obtain ⟨f, hf, hfi, hfd⟩ := exists_mem_ideal_degree_le_multiplicity I d hdim
    (by simpa only [Fintype.card_option] using Nat.add_lt_add_right hcodim 1) hdegree
  obtain ⟨b, hb, hbound, hint⟩ :=
    exists_bounded_integral_linear_elimination I f hf hfi
  refine ⟨b, hb, fun i => ⟨(hbound i).1, ?_⟩, hint⟩
  have hh : (f.totalDegree : ℤ) ≤ d := by exact_mod_cast hfd
  exact (hbound i).2.trans (by omega)

end
end AffineCurveCounting
