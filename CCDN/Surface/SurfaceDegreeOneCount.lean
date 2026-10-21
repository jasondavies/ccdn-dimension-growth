module

public import CCDN.Hilbert.DegreeOneComponentLines
public import CCDN.Surface.SurfaceLineContribution
public import CCDN.Algebra.PolynomialPredicates
/-! The proved line contribution applies to degree-one prime
components, with the original number of components as the additive cost. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem surface_degree_one_component_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree → ∀ B : ℝ, 0 ≤ B →
      ∀ S : Finset (Ideal (CoordinatePolynomial 3)),
      (∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) →
      (∀ P ∈ S, map (Int.castRingHom ℚ) f ∈ P) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 6 * B + S.card := by
  obtain ⟨C, hC, hline⟩ := surface_line_contribution
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB S hcurve hSf
  obtain ⟨lines, hcover, hcard, hlines⟩ := degree_one_components_line_cover S hcurve
  have hh := (hline f hir hd B hB lines (by
    intro L hL
    obtain ⟨a, v, _, he⟩ := (hlines L hL).2
    exact ⟨a, v, he⟩) (by
      intro L hL x hx
      obtain ⟨P, hPS, rfl⟩ := (hlines L hL).1
      exact hx _ (hSf P hPS))).2
  rw [← hcover] at hh
  have hcardR : (lines.card : ℝ) ≤ S.card := by exact_mod_cast hcard
  exact hh.trans (add_le_add le_rfl hcardR)

end
end CCDN
