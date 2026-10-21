module

public import CCDN.Center.ChowExactDegree
public import CCDN.Center.ProjectiveChowChartReduction
public import CCDN.Center.GeometricProjectiveChow
public import CCDN.Center.GeometricIdealPrimality
public import CCDN.Algebra.PolynomialPredicates
/-! The constructed projective Chow equation has degree exactly d in every
hyperplane block, where d is the Hilbert multiplicity. This includes
forms over the original field for geometrically integral sources. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projective_chow_row_degree_eq_multiplicity
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (hF : Irreducible F)
    (δ : Fin (m + 1) → ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i))
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) :
    ∀ i, δ i = d := by
  obtain ⟨I,G,hI,hmI,hdI,hG,hgen,hδG,_⟩ :=
    projective_chow_chart_reduction J hJ d hdimdeg F hF δ hδ hzero
  have : I.IsPrime := hI
  let : (I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    prime_ideal_scalar_extension_of_isAlgClosed I
  exact chow_generator_row_degree_eq_multiplicity I hmI d hdI G hG hgen δ hδG

theorem exists_projective_chow_exact_degree
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K,
      Irreducible F ∧ (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) ∧
      F.totalDegree = (m + 1) * d ∧
      ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  obtain ⟨F,δ,hF,hδ,hzero⟩ := exists_projective_chow_equation_without_chart J hJ hdim
  have he := projective_chow_row_degree_eq_multiplicity J hJ d ⟨hdim, hdegree⟩ F hF δ hδ hzero
  have hd := fun i => he i ▸ hδ i
  exact ⟨F,hF,hd,chow_uniform_row_degree_totalDegree F hF.ne_zero d hd,hzero⟩

theorem exists_geometric_projective_chow_exact_degree
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K,
      Irreducible F ∧ Irreducible (map (algebraMap K L) F) ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) ∧
      F.totalDegree = (m + 1) * d ∧
      ∀ U, eval U (map (algebraMap K L) F) = 0 ↔
        U ∈ projectiveChowIncidenceLocus (m + 1) (J.map (map (algebraMap K L))) := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨F,δ,hF,hFL,hδ,hzero⟩ := exists_geometric_projective_chow_without_chart (L := L) J hJ hdim
  have hδL (i) : (map (algebraMap K L) F).IsWeightedHomogeneous (chowRowWeight i) (δ i) := by
    intro e he
    apply hδ i
    intro hz
    apply he
    rw [coeff_map,hz,map_zero]
  have hmL : (filteredHilbertPolynomial (J.map (map (algebraMap K L)))).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  have hdL : (filteredHilbertPolynomial (J.map (map (algebraMap K L)))).leadingCoeff =
      (d : ℚ) / (m + 1).factorial := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdegree
  have he := projective_chow_row_degree_eq_multiplicity _
    (homogeneous_ideal_scalar_extension J hJ) d ⟨hmL, hdL⟩ (map (algebraMap K L) F)
    hFL δ hδL hzero
  have hd := fun i => he i ▸ hδ i
  exact ⟨F,hF,hFL,hd,chow_uniform_row_degree_totalDegree F hF.ne_zero d hd,hzero⟩

end
end CCDN
