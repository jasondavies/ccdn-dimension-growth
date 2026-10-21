/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.StandardMonomials

/-! Coefficient-field isomorphisms preserve the filtered Hilbert
polynomial. The standard exponent set is unchanged, so this does not need
semilinear quotient identifications. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma monomialOrder_degree_mapEquiv
    {K L σ : Type*} [Field K] [Field L] (e : K ≃+* L)
    (m : MonomialOrder σ) (f : MvPolynomial σ K) :
    m.degree (mapEquiv σ e f) = m.degree f := by
  simp only [MonomialOrder.degree, mapEquiv_apply]
  rw [support_map_of_injective f e.injective]

private theorem standardExponents_coefficientEquiv
    {K L σ : Type*} [Field K] [Field L] (I : Ideal (MvPolynomial σ K))
    (e : K ≃+* L) (m : MonomialOrder σ) :
    Ideal.standardExponents (I.map (mapEquiv σ e)) m = Ideal.standardExponents I m := by
  classical
  ext a
  constructor
  · intro ha f hf hf0
    have hm := ha (mapEquiv σ e f) (Ideal.mem_map_of_mem _ hf)
      (map_ne_zero_iff _ (mapEquiv σ e).injective |>.mpr hf0)
    simpa only [monomialOrder_degree_mapEquiv] using hm
  · intro ha f hf hf0
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (mapEquiv σ e) (mapEquiv σ e).surjective).mp hf
    have hg0 : g ≠ 0 := fun h => hf0 (by simp [h])
    simpa only [monomialOrder_degree_mapEquiv] using ha g hg hg0

private theorem filteredCoordinateSpace_finrank_coefficientEquiv
    {K L σ : Type*} [Field K] [Field L] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (e : K ≃+* L) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Module.finrank L (filteredCoordinateSpace (I.map (mapEquiv σ e)) N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  simp only [Ideal.boundedStandardExponents, standardExponents_coefficientEquiv]

/-- A ring isomorphism `K ≃+* L` of coefficient fields preserves the filtered Hilbert polynomial of
an ideal. -/
theorem filteredHilbertPolynomial_coefficientEquiv
    {K L σ : Type*} [Field K] [Field L] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (e : K ≃+* L) :
    filteredHilbertPolynomial (I.map (mapEquiv σ e)) = filteredHilbertPolynomial I := by
  apply filteredHilbertPolynomial_eq_of_eventual
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  refine ⟨N, fun M hM => ?_⟩
  rw [hN M hM, filteredCoordinateSpace_finrank_coefficientEquiv I e M]

end
end CCDN
