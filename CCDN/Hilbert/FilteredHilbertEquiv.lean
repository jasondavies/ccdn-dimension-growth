/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
/-! The filtered Hilbert polynomial is unchanged by an invertible
coordinate substitution preserving total degree in both directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem filteredCoordinateSpace_finrank_equiv
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (hJ : J = I.map e)
    (he : ∀ f, (e f).totalDegree ≤ f.totalDegree)
    (hei : ∀ f, (e.symm f).totalDegree ≤ f.totalDegree) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Module.finrank K (filteredCoordinateSpace J N) := by
  let φ := Ideal.quotientEquivAlg I J e hJ
  let V := filteredCoordinateSpace I N
  let W := filteredCoordinateSpace J N
  have hmem (x : V) : φ x.val ∈ W := by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    apply Submodule.mem_map.mpr
    refine ⟨e f, (mem_restrictTotalDegree _ _ _).mpr
      ((he f).trans ((mem_restrictTotalDegree _ _ _).mp hf)), ?_⟩
    change φ ((Ideal.Quotient.mk I) f) = φ x.val
    exact congrArg φ hfx
  let T : V →ₗ[K] W := (φ.toLinearMap.comp V.subtype).codRestrict W hmem
  have hinj : Function.Injective T := by
    intro x y h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective T := by
    intro y
    obtain ⟨g, hg, hgy⟩ := Submodule.mem_map.mp y.property
    refine ⟨⟨(Ideal.Quotient.mk I) (e.symm g), ?_⟩, ?_⟩
    · exact Submodule.mem_map.mpr ⟨e.symm g,
        (mem_restrictTotalDegree _ _ _).mpr
          ((hei g).trans ((mem_restrictTotalDegree _ _ _).mp hg)), rfl⟩
    · apply Subtype.ext
      change (Ideal.Quotient.mk J) (e (e.symm g)) = y.val
      rw [e.apply_symm_apply]
      exact hgy
  exact (LinearEquiv.ofBijective T ⟨hinj, hsurj⟩).finrank_eq

theorem filteredHilbertPolynomial_equiv
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (hJ : J = I.map e)
    (he : ∀ f, (e f).totalDegree ≤ f.totalDegree)
    (hei : ∀ f, (e.symm f).totalDegree ≤ f.totalDegree) :
    filteredHilbertPolynomial I = filteredHilbertPolynomial J := by
  apply filteredHilbertPolynomial_eq_of_eventual
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec J
  refine ⟨M, fun N hN => ?_⟩
  rw [hM N hN, filteredCoordinateSpace_finrank_equiv I J e hJ he hei N]

theorem filteredHilbertPolynomial_renameEquiv
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (e : σ ≃ τ) :
    filteredHilbertPolynomial I =
      filteredHilbertPolynomial (I.map (renameEquiv K e)) := by
  apply filteredHilbertPolynomial_equiv I _ (renameEquiv K e) rfl
  · intro f
    exact (totalDegree_renameEquiv e f).le
  · intro f
    exact (totalDegree_renameEquiv e.symm f).le

end
end CCDN
