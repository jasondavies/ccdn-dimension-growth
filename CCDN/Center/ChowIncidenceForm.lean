/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ChowIncidenceBaseChange
import CCDN.Center.ChowIncidencePrincipal
import CCDN.Center.PrincipalWeightedHomogeneous
/-! Constructed incidence equations with separate homogeneity and
geometric irreducibility. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_multihomogeneous_chow_incidence_generator
    {K : Type*} [Field K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ),
      Irreducible F ∧ chowIncidenceIdeal (m + 1) I = Ideal.span {F} ∧
      ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i) := by
  obtain ⟨F,hF,hgen⟩ := exists_chow_incidence_generator_of_dimension I hm
  obtain ⟨δ,hδ⟩ := chow_incidence_generator_multihomogeneous I F hF.ne_zero hgen
  exact ⟨F,δ,hF,hgen,hδ⟩

theorem exists_geometric_chow_incidence_generator
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ),
      Irreducible F ∧ chowIncidenceIdeal (m + 1) I = Ideal.span {F} ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      Irreducible (map (algebraMap K L) F) := by
  obtain ⟨F,δ,hF,hgen,hδ⟩ := exists_multihomogeneous_chow_incidence_generator I hm
  exact ⟨F,δ,hF,hgen,hδ,
    chow_incidence_equation_irreducible_map (m + 1) I F hF.ne_zero hgen⟩

end
end CCDN
