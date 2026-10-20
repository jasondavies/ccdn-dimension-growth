module

public import CCDN.FilteredHilbertPolynomial
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Coefficient-field isomorphisms preserve the actual filtered Hilbert
polynomial. The standard exponent set is unchanged, so this does not need
semilinear quotient identifications. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma monomialOrder_degree_mapEquiv
    {K L σ : Type*} [Field K] [Field L] (e : K ≃+* L)
    (m : MonomialOrder σ) (f : MvPolynomial σ K) :
    m.degree (mapEquiv σ e f) = m.degree f := by
  simp only [MonomialOrder.degree, mapEquiv_apply]
  rw [support_map_of_injective f e.injective]

theorem standardExponents_coefficientEquiv
    {K L σ : Type*} [Field K] [Field L] (I : Ideal (MvPolynomial σ K))
    (e : K ≃+* L) (m : MonomialOrder σ) :
    standardExponents (I.map (mapEquiv σ e)) m = standardExponents I m := by
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

theorem filteredCoordinateSpace_finrank_coefficientEquiv
    {K L σ : Type*} [Field K] [Field L] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (e : K ≃+* L) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Module.finrank L (filteredCoordinateSpace (I.map (mapEquiv σ e)) N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  simp only [boundedStandardExponents, standardExponents_coefficientEquiv]

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
