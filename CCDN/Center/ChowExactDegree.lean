/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowDistinguishedVariable
public import CCDN.Center.ChowIncidenceIdeal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Center.ChowAxisEvaluation
import CCDN.Center.ChowIncidenceBaseChange
import CCDN.Center.ChowNormalizationDegreeComparison
import CCDN.Center.ChowRowSymmetry
import CCDN.Hilbert.ScalarExtension
/-! The Chow incidence equation has one block degree equal to the
source Hilbert multiplicity in every row, and total degree (m+1)d.
The generic normalization and primitive-element fields are constructed
from the source. -/

@[expose] public section
namespace CCDN
noncomputable section

section

/-! The distinguished coordinate computes the Chow block degree over the
original field whenever the source stays prime over an algebraically
closed extension. -/

open MvPolynomial

private theorem chow_generator_last_coordinate_degree_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {F})
    (d : ℕ) (hd : F.IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d) :
    F.degreeOf (Fin.last m,0) = d := by
  let J := I.map (map (algebraMap K L))
  have hmJ : (filteredHilbertPolynomial J).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hm
  have hgenJ : chowIncidenceIdeal (m + 1) J = Ideal.span {map (algebraMap K L) F} := by
    rw [← chowIncidenceIdeal_scalar_extension, hgen, Ideal.map_span, Set.image_singleton]
  have hdJ : (map (algebraMap K L) F).IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d := by
    intro e he
    apply hd
    intro hz
    apply he
    rw [coeff_map, hz, map_zero]
  have hh := chow_generator_last_coordinate_degree J hmJ
    (map (algebraMap K L) F) hgenJ d hdJ
  simpa only [degreeOf, degrees_map_of_injective F (algebraMap K L).injective] using hh

private theorem chow_generator_univariate_degree_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {F})
    (d : ℕ) (hd : F.IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d) :
    (chowAsUnivariate K m n F).natDegree = d := by
  rw [chowAsUnivariate_natDegree]
  exact chow_generator_last_coordinate_degree_of_geometric_prime (L := L) I hm F hgen d hd

end

open MvPolynomial

local instance exactDegreeCoefficientRing {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := by
  letI : CommRing (MvPolynomial σ K ⧸ I) := inferInstance
  infer_instance

local instance exactDegreeNestedRing {K σ τ υ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    CommRing (MvPolynomial υ (MvPolynomial τ (MvPolynomial σ K ⧸ I))) := by
  let : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := inferInstance
  infer_instance

private theorem chow_univariate_degree_eq_multiplicity
    {K : Type*} [Field K] [CharZero K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I m d)
    (G : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hG : Irreducible G) (hmem : G ∈ chowIncidenceIdeal (m + 1) I) :
    (chowAsUnivariate K m n G).natDegree = d := by
  classical
  let T := ChowFirstRowCoordinateRing m I
  let N := ChowNestedCoordinateRing m I
  let : CommRing T := inferInstance
  let : IsDomain T := inferInstance
  let : CommRing N := inferInstance
  let : IsDomain N := inferInstance
  let A := FractionRing T
  let F := FractionRing N
  let : Field A := inferInstance
  let : Field F := inferInstance
  let : Algebra T F := inferInstance
  let : FaithfulSMul T F := inferInstance
  let aAF : Algebra A F := FractionRing.liftAlgebra T F
  let : SMul A F := aAF.toSMul
  let : Algebra A F := aAF
  let : IsScalarTower T A F := FractionRing.isScalarTower_liftAlgebra T F
  let : IsScalarTower K A F := IsScalarTower.to₁₃₄ K T A F
  have hrank := chow_incidence_parameter_field_finrank (F := A) I d hdimdeg
  have hd : 0 < d := by
    obtain ⟨e,he,_,heq⟩ := filteredHilbertPolynomial_positive_multiplicity I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›)
    rw [hdimdeg.natDegree_eq, hdimdeg.leadingCoeff_eq] at heq
    have hfac : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hde : (d : ℚ) = e := (div_left_inj' hfac).mp heq
    have hde' : d = e := Nat.cast_injective hde
    exact hde'.symm ▸ he
  have hfinite : Module.Finite (chowNormalizationParameterField (F := A) m I) A :=
    Module.finite_of_finrank_pos (by rwa [hrank])
  exact (chow_univariate_degree_eq_normalization_rank (A := A) (F := F)
    I hfinite hdimdeg.natDegree_eq G hG hmem).trans hrank

theorem chow_generator_row_degree_eq_multiplicity
    {K : Type*} [Field K] [CharZero K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I m d)
    (G : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hG : Irreducible G) (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {G})
    (δ : Fin (m + 1) → ℕ)
    (hδ : ∀ i, G.IsWeightedHomogeneous (chowRowWeight i) (δ i)) :
    ∀ i, δ i = d := by
  have hmem : G ∈ chowIncidenceIdeal (m + 1) I := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton G)
  have hu := chow_univariate_degree_eq_multiplicity I d hdimdeg G hG hmem
  have hl := chow_generator_univariate_degree_of_geometric_prime
    (L := AlgebraicClosure K) I hdimdeg.natDegree_eq G hgen (δ (Fin.last m)) (hδ _)
  intro i
  exact (chow_generator_row_degrees_equal I G hG.ne_zero hgen δ hδ i (Fin.last m)).trans
    (hl.symm.trans hu)

end
end CCDN
