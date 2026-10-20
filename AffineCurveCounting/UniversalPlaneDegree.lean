module

public import AffineCurveCounting.UniversalPlaneFamily

/-! Degree in the affine-plane parameters of every coefficient of the
universal restriction. This degree is bounded by the original equation's
actual total degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma commAlgEquiv_coeff_coeff {K σ τ : Type*} [CommRing K]
    (f : MvPolynomial σ (MvPolynomial τ K)) (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    ((commAlgEquiv K σ τ f).coeff n).coeff m = (f.coeff m).coeff n := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial a b =>
    induction b using MvPolynomial.induction_on' with
    | add b c hb hc => simp [hb, hc]
    | monomial b c =>
      simp [commAlgEquiv, monomial, AddMonoidAlgebra.commAlgEquiv_single_single,
        Finsupp.single_apply, eq_comm]
      split_ifs <;> simp_all [AddMonoidAlgebra.coeff_single]

lemma coefficient_totalDegree_le_commAlgEquiv {K σ τ : Type*} [CommRing K]
    (f : MvPolynomial σ (MvPolynomial τ K)) (m : σ →₀ ℕ) :
    (f.coeff m).totalDegree ≤ (commAlgEquiv K σ τ f).totalDegree := by
  classical
  apply Finset.sup_le
  intro n hn
  apply le_totalDegree
  rw [mem_support_iff] at hn ⊢
  intro he
  apply hn
  rw [← commAlgEquiv_coeff_coeff, he]
  rfl

lemma universalPlaneMap_comm {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    commAlgEquiv K (Fin 2) (PlaneParameters σ) (universalPlaneMap K σ f) =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin 2) K))
        (fun i => X (i,0) + X (i,1) * C (X 0) + X (i,2) * C (X 1)) f := by
  have he : (commAlgEquiv K (Fin 2) (PlaneParameters σ)).toRingHom.comp
      (universalPlaneMap K σ).toRingHom =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin 2) K))
        (fun i => X (i,0) + X (i,1) * C (X 0) + X (i,2) * C (X 1)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalPlaneMap]
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

lemma universalPlaneMap_parameterDegree_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) :
    (commAlgEquiv K (Fin 2) (PlaneParameters σ) (universalPlaneMap K σ f)).totalDegree ≤
      f.totalDegree := by
  rw [universalPlaneMap_comm]
  apply linear_eval₂_totalDegree_le
  intro i
  have hx (j : PlaneParameters σ) :
      (X j : MvPolynomial (PlaneParameters σ) (MvPolynomial (Fin 2) K)).totalDegree ≤ 1 := by
    simpa [X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : MvPolynomial (Fin 2) K)
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact hx _
    · exact (totalDegree_mul _ _).trans (by simpa using hx (i,1))
  · exact (totalDegree_mul _ _).trans (by simpa using hx (i,2))

/-- Each coefficient has degree at most d in ALL plane parameters together. -/
theorem universalPlanePolynomial_coefficient_degree {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (i j : ℕ) :
    (((universalPlanePolynomial f).coeff i).coeff j).totalDegree ≤ f.totalDegree := by
  rw [universalPlanePolynomial, bivariatePolynomialEquiv_coeff]
  exact (coefficient_totalDegree_le_commAlgEquiv _ _).trans
    (universalPlaneMap_parameterDegree_le f)

end
end AffineCurveCounting
