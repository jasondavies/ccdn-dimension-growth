module

public import CCDN.ProjectiveFiniteFibers
public import CCDN.FilteredHilbertPolynomial
public import CCDN.GridPointInterpolation

/-! A coordinate ring with constant filtered Hilbert polynomial has
finitely many rational affine zeros. Its projective zero locus is empty,
since every nonzero representative would produce arbitrarily many affine
zeros by scaling. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem finite_point_bound_of_hilbert_dimension_zero
    {σ : Type*} [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ ℚ)) (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ M : ℕ, ∀ s : Finset (σ → ℚ),
      (∀ x ∈ s, ∀ f ∈ I, eval x f = 0) → s.card ≤ M := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  refine ⟨Module.finrank ℚ (filteredCoordinateSpace I N₀), ?_⟩
  intro s hs
  let S : Finset ℚ := s.biUnion (fun x => Finset.univ.image x)
  let N := max N₀ (Fintype.card σ * (S.card - 1))
  have hdimN : Module.finrank ℚ (filteredCoordinateSpace I N) =
      Module.finrank ℚ (filteredCoordinateSpace I N₀) := by
    have h₁ := hN₀ N (le_max_left _ _)
    have h₂ := hN₀ N₀ le_rfl
    rw [hP, Polynomial.eval_C] at h₁ h₂
    exact_mod_cast h₁.symm.trans h₂
  have hh := grid_points_filtered_lower I S (fun x : s => x.val)
    Subtype.val_injective (fun x j => by
      apply Finset.mem_biUnion.mpr
      exact ⟨x.val, x.property, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    (fun x f hf => hs x.val x.property f hf) (le_max_right _ _ : _ ≤ N)
  have hh' : s.card ≤ Module.finrank ℚ (filteredCoordinateSpace I N) := by
    simpa only [Fintype.card_coe] using hh
  exact hh'.trans_eq hdimN

theorem projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ := by
  obtain ⟨M, hM⟩ := finite_point_bound_of_hilbert_dimension_zero I hdim
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := projective_linear_image_ne_zero_of_finite_zero_fiber I
    (0 : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) M
    (fun s hs _ => hM s hs) x hx
  exact hh rfl

end
end CCDN
