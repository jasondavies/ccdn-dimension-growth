/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ChowExactDegree
import CCDN.Center.ChowRowSymmetry
import CCDN.Center.GeometricIdealPrimality
import CCDN.Center.GeometricProjectiveChow
import CCDN.Center.ProjectiveChowChartReduction
import CCDN.Center.ProjectiveChowWithoutChart
import CCDN.Hilbert.HilbertScalarExtension
import CCDN.Hilbert.HomogeneousPrimeComponents
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
  obtain ⟨I,G,hI,hdimdegI,hG,hgen,hδG,_⟩ :=
    projective_chow_chart_reduction J hJ d hdimdeg F hF δ hδ hzero
  have : I.IsPrime := hI
  let : (I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    prime_ideal_scalar_extension_of_isAlgClosed I
  exact chow_generator_row_degree_eq_multiplicity I d hdimdegI G hG hgen δ hδG

theorem exists_projective_chow_exact_degree
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K,
      Irreducible F ∧ (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) ∧
      F.totalDegree = (m + 1) * d ∧
      ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J := by
  obtain ⟨F,δ,hF,hδ,hzero⟩ :=
    exists_projective_chow_equation_without_chart J hJ hdimdeg.natDegree_eq
  have he := projective_chow_row_degree_eq_multiplicity J hJ d hdimdeg F hF δ hδ hzero
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
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨F,δ,hF,hFL,hδ,hzero⟩ :=
    exists_geometric_projective_chow_without_chart (L := L) J hJ hdimdeg.natDegree_eq
  have hδL (i) : (map (algebraMap K L) F).IsWeightedHomogeneous (chowRowWeight i) (δ i) := by
    intro e he
    apply hδ i
    intro hz
    apply he
    rw [coeff_map,hz,map_zero]
  have he := projective_chow_row_degree_eq_multiplicity _
    (homogeneous_ideal_scalar_extension J hJ) d
    (hasProjectiveDimensionDegree_scalar_extension hdimdeg) (map (algebraMap K L) F)
    hFL δ hδL hzero
  have hd := fun i => he i ▸ hδ i
  exact ⟨F,hF,hFL,hd,chow_uniform_row_degree_totalDegree F hF.ne_zero d hd,hzero⟩

end
end CCDN
