module

public import CCDN.FilteredHilbertLinearity
public import CCDN.CoordinatePowerGeneration
public import CCDN.PlaneProjectionDegree
public import CCDN.BinomialSectionBound

/-! An eventual linear upper bound gives an eventual linear Hilbert
formula, with its slope bounded by the original coefficient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem filteredCoordinateSpace_eventually_linear_of_eventual_bound
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (C T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d ≤ C, ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c := by
  have hglobal (N : ℕ) (_hN : 14 ≤ N) :
      Module.finrank K (filteredCoordinateSpace I N) ≤ (C * (T + 2)) * (N + 2) := by
    by_cases hTN : T ≤ N
    · apply (hbound N hTN).trans
      exact Nat.mul_le_mul_right (N + 2) (Nat.le_mul_of_pos_right C (by omega))
    · have hNT : N ≤ T := by omega
      have hh := Submodule.finrank_mono (filteredCoordinateSpace_mono I hNT)
      exact (hh.trans (hbound T le_rfl)).trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨d, _, N, c, hlinear⟩ := filteredCoordinateSpace_eventually_linear I (C * (T + 2)) hglobal
  refine ⟨d, ?_, N, c, hlinear⟩
  apply eventual_linear_slope_le
    (fun k => Module.finrank K (filteredCoordinateSpace I (k + T)))
    (fun k => C * (k + T + 2)) d C
  · refine ⟨N, c + (d : ℤ) * T, ?_⟩
    intro k hk
    rw [hlinear (k + T) (by omega)]
    push_cast
    ring
  · refine ⟨0, (C : ℤ) * (T + 2), ?_⟩
    intro k _
    push_cast
    ring
  · intro k
    exact hbound (k + T) (by omega)

/-- A proper intersection of two equations in affine three-space has an
eventually linear Hilbert function with slope at most the product of degrees.
This holds for every ideal containing the equations, not just prime ideals. -/
theorem proper_intersection_eventual_linear_degree {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 3) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin 3) K)) (hIf : f ∈ I) (hIg : g ∈ I) :
    ∃ d ≤ f.totalDegree * g.totalDegree, ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c := by
  apply filteredCoordinateSpace_eventually_linear_of_eventual_bound I
    (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
  intro N hN
  have hh := filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg hN
  simp only [Nat.choose_one_right] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (by omega))

end
end CCDN
