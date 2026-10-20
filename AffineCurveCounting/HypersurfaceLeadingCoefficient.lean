module

public import AffineCurveCounting.HomogeneousLeadingCoefficient
public import AffineCurveCounting.MultivariateGridHeight

/-! Bounded integer shears placing a large coefficient first, in all dimensions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The large leading-coefficient witness in arbitrary projective dimension.
Every original coefficient is controlled by one bounded grid evaluation. -/
theorem exists_hypersurface_leading_coefficient_translation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) ≠ 0 ∧
      ∀ m, |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) *
        |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| := by
  have hc0 : affineChart n f ≠ 0 := by
    intro hz
    exact hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
      (by simpa only [map_zero] using hz))
  obtain ⟨a, ha, hval, hcoeff⟩ := exists_integer_multivariate_grid_height_witness (affineChart n f)
    hc0 ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  have he : (homogeneousTranslation ℤ a f).coeff (Finsupp.single 0 d) =
      eval a (affineChart n f) := by
    rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
  have hlc := lex_leadingCoeff_eq_pure_first (homogeneousTranslation ℤ a f)
    (homogeneousTranslation_homogeneous a hf).totalDegree_le (he ▸ hval)
  refine ⟨a, ha, by rw [hlc, he]; exact hval, ?_⟩
  intro m
  by_cases hm : m.sum (fun _ e => e) = d
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
    rw [← affineChart_homogeneous_coefficient f hf j, hlc, he]
    exact hcoeff _
  · rw [hf.coeff_eq_zero hm, Int.cast_zero, abs_zero]
    positivity

end
end AffineCurveCounting
