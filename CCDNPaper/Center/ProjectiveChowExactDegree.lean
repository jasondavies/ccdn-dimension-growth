/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDNPaper.Center.ProjectiveChowIncidence
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDN.Hilbert.ScalarExtension
import CCDNPaper.Center.ChowExactDegree
import CCDNPaper.Center.ChowRowSymmetry
import CCDNPaper.Center.GeometricIdealPrimality
import CCDNPaper.Center.GeometricProjectiveChow
import CCDNPaper.Center.ProjectiveChowChartReduction
import CCDNPaper.Center.ProjectiveChowWithoutChart

/-! The constructed projective Chow equation has degree exactly d in every
hyperplane block, where d is the Hilbert multiplicity. This includes
forms over the original field for geometrically integral sources. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem projective_chow_row_degree_eq_multiplicity
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ)
    (hF : IsProjectiveChowEquation J F δ) :
    ∀ i, δ i = d := by
  obtain ⟨I,G,hI,hdimdegI,hG,hgen,hδG,_⟩ :=
    projective_chow_chart_reduction J hJ d hdimdeg F δ hF
  have : I.IsPrime := hI
  let : (I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    prime_ideal_scalar_extension_of_isAlgClosed I
  exact chow_generator_row_degree_eq_multiplicity I d hdimdegI G hG hgen δ hδG

/-- Over an algebraically closed field of characteristic zero, a homogeneous prime ideal `J`
defining a projective variety of dimension `m` and degree `d` has a projective Chow equation that
is homogeneous of degree exactly `d` in each of the `m + 1` hyperplane rows, hence of total
degree `(m + 1) * d`. -/
theorem exists_projective_chow_exact_degree
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K,
      IsProjectiveChowEquation J F (fun _ => d) ∧ F.totalDegree = (m + 1) * d := by
  obtain ⟨F,δ,hF⟩ := exists_projective_chow_equation_without_chart J hJ hdimdeg.natDegree_eq
  have he := projective_chow_row_degree_eq_multiplicity J hJ d hdimdeg F δ hF
  have hd := fun i => he i ▸ hF.row_homogeneous i
  exact ⟨F,⟨hF.irreducible,hd,hF.eval_eq_zero_iff⟩,
    chow_uniform_row_degree_totalDegree F hF.irreducible.ne_zero d hd⟩

/-- Let `J` be a homogeneous prime ideal over a field `K` of characteristic zero that stays prime
over an algebraically closed extension `L`, defining a projective variety of dimension `m` and
degree `d`. Then there is a polynomial `F` over `K`, irreducible over both `K` and `L`, homogeneous
of degree `d` in each hyperplane row and of total degree `(m + 1) * d`, whose image over `L`
vanishes exactly on the hyperplane tuples meeting the variety. -/
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
  obtain ⟨F,δ,hF,hFL⟩ :=
    exists_geometric_projective_chow_without_chart (L := L) J hJ hdimdeg.natDegree_eq
  have he := projective_chow_row_degree_eq_multiplicity _
    (homogeneous_ideal_scalar_extension J hJ) d
    (hasProjectiveDimensionDegree_scalar_extension hdimdeg) (map (algebraMap K L) F)
    δ hFL
  have hd (i) : F.IsWeightedHomogeneous (chowRowWeight i) d :=
    he i ▸ (isWeightedHomogeneous_map_iff (algebraMap K L).injective _ _ _).mp
      (hFL.row_homogeneous i)
  exact ⟨F,hF,hFL.irreducible,hd,chow_uniform_row_degree_totalDegree F hF.ne_zero d hd,
    hFL.eval_eq_zero_iff⟩

end
end CCDN
