/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import CCDN.Center.ChowPolynomialPower
import CCDN.Center.ChowProjectionPower
import CCDN.Center.ChowRowSymmetry
import CCDN.Center.ProjectiveChowWithoutChart
import CCDN.Projection.IntegralProjectionHilbert
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
Projection restrictions without chosen charts. A disjoint center preserves
every block degree of the source equation; its restriction is a scalar power
of the constructed image equation.

Weighted homogeneity under polynomial evaluation over the same field.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem weighted_homogeneous_aeval
    {K σ τ : Type*} [Field K] (w : σ → ℕ) (v : τ → ℕ)
    (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).IsWeightedHomogeneous v (w i))
    (f : MvPolynomial σ K) (d : ℕ) (hf : f.IsWeightedHomogeneous w d) :
    (aeval a f).IsWeightedHomogeneous v d := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  rw [aeval_monomial, algebraMap_eq]
  have hh := IsWeightedHomogeneous.prod e.support (fun i => (a i) ^ e i)
    (fun i => e i • w i) (fun i _ => (ha i).pow (e i))
  have hw := hf (mem_support_iff.mp he)
  change ∑ i ∈ e.support, e i • w i = d at hw
  simpa only [Finsupp.prod, hw] using hh.C_mul (f.coeff e)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem chowLinearSubstitution_row_homogeneous
    {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin r)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    (chowLinearSubstitution A F).IsWeightedHomogeneous (chowRowWeight i) d := by
  have ha (q : Fin r × Fin (n + 1)) :
      (∑ k, C (A k q.2) * X (q.1,k) : MvPolynomial (Fin r × Fin (s + 1)) K).IsWeightedHomogeneous
        (chowRowWeight i) (chowRowWeight i q) := by
    apply IsWeightedHomogeneous.sum
    intro k _
    exact (isWeightedHomogeneous_X K (chowRowWeight i) (q.1,k)).C_mul (A k q.2)
  exact weighted_homogeneous_aeval (chowRowWeight i) (chowRowWeight i) _ ha F d hF

theorem chowLinearSubstitution_totalDegree_of_ne_zero
    {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : F ≠ 0)
    (δ : Fin r → ℕ) (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i))
    (hR : chowLinearSubstitution A F ≠ 0) :
    (chowLinearSubstitution A F).totalDegree = F.totalDegree := by
  have hRhom := chow_rows_homogeneous_total_degree (chowLinearSubstitution A F) δ
    (fun i => chowLinearSubstitution_row_homogeneous A i F (δ i) (hδ i))
  exact (hRhom.totalDegree hR).trans ((chow_rows_homogeneous_total_degree F δ hδ).totalDegree hF).symm

/-- For a center disjoint from the projective variety of `J`, the image ideal of the
projection has the same dimension, so it has a projective Chow equation without charts. -/
theorem exists_chow_projection_image_equation
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    ∃ (G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) K) (ε : Fin (m + 1) → ℕ),
      IsProjectiveChowEquation (chowProjectionImageIdeal J A) G ε := by
  have : (chowProjectionImageIdeal J A).IsPrime :=
    RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  exact exists_projective_chow_equation_without_chart _
    (chowProjectionImageIdeal_homogeneous J hJ A)
    ((integral_projection_hilbert_dimension_eq J _ hint).trans hdim)

theorem chowLinearSubstitution_ne_zero_iff_center_disjoint
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hF : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) :
    chowLinearSubstitution A F ≠ 0 ↔
      ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0 := by
  constructor
  · exact center_disjoint_of_chowLinearSubstitution_ne_zero J A F hF
  · intro hcenter
    obtain ⟨G,_,hG⟩ := exists_chow_projection_image_equation J hJ hdim A hcenter
    obtain ⟨c,k,hc,_,he⟩ := polynomial_eq_scalar_pow_of_same_zeros G
      (chowLinearSubstitution A F) hG.irreducible
      (chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hF hG.eval_eq_zero_iff)
    rw [he]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero k hG.irreducible.ne_zero)

/-- Both equations and their scalar-power relation are constructed from the
source and matrix. No source or image chart is part of the hypotheses. -/
theorem exists_chow_projection_power
    {K : Type*} [Field K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
      (G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) K)
      (δ ε : Fin (m + 1) → ℕ) (c : K) (k : ℕ),
      IsProjectiveChowEquation J F δ ∧
      IsProjectiveChowEquation (chowProjectionImageIdeal J A) G ε ∧ c ≠ 0 ∧ 0 < k ∧
      chowLinearSubstitution A F = C c * G ^ k ∧
      (chowLinearSubstitution A F).totalDegree = F.totalDegree ∧
      (Irreducible (chowLinearSubstitution A F) ↔ F.totalDegree = G.totalDegree) := by
  obtain ⟨F,δ,hF⟩ := exists_projective_chow_equation_without_chart J hJ hdim
  obtain ⟨G,ε,hG⟩ := exists_chow_projection_image_equation J hJ hdim A hcenter
  have hzero := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G
    hF.eval_eq_zero_iff hG.eval_eq_zero_iff
  obtain ⟨c,k,hc,hk,hpow⟩ := polynomial_eq_scalar_pow_of_same_zeros G
    (chowLinearSubstitution A F) hG.irreducible hzero
  have hR : chowLinearSubstitution A F ≠ 0 := by
    rw [hpow]
    exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero k hG.irreducible.ne_zero)
  have hdegree := chowLinearSubstitution_totalDegree_of_ne_zero A F hF.irreducible.ne_zero δ
    hF.row_homogeneous hR
  refine ⟨F,G,δ,ε,c,k,hF,hG,hc,hk,hpow,hdegree,?_⟩
  rw [← hdegree]
  exact irreducible_iff_degree_eq_of_same_zeros G _ hG.irreducible hzero

end
end CCDN
