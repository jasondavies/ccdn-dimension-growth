module

public import CCDN.WeightedPolynomialTop
public import CCDN.AffineLineLeading

/-! Restrict a selected block of variables to a generic affine line.
The line parameter has exactly the weighted degree of the selected block. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def genericBlockWeight {σ : Type*} (b : σ → Bool) : σ → ℕ :=
  fun i => if b i then 1 else 0

def genericBlockLine {R σ : Type*} [CommRing R] (b : σ → Bool) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial (σ ⊕ σ) R) :=
  eval₂Hom (Polynomial.C.comp C) (fun i =>
    Polynomial.C (X (Sum.inl i)) +
      if b i then Polynomial.C (X (Sum.inr i)) * Polynomial.X else 0)

lemma polynomial_eval₂_natDegree_le_weight
    {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (v : σ → Polynomial S) (w : σ → ℕ)
    (hv : ∀ i, (v i).natDegree ≤ w i) (f : MvPolynomial σ R) :
    (eval₂Hom (Polynomial.C.comp φ) v f).natDegree ≤ f.weightedTotalDegree w := by
  classical
  have hm (e : σ →₀ ℕ) (c : R) :
      (eval₂Hom (Polynomial.C.comp φ) v (monomial e c)).natDegree ≤ Finsupp.weight w e := by
    rw [eval₂Hom_monomial]
    apply Polynomial.natDegree_mul_le.trans
    simp only [RingHom.comp_apply, Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_prod_le _ _).trans
    change (∑ i ∈ e.support, (v i ^ e i).natDegree) ≤ _
    rw [Finsupp.weight_apply]
    apply Finset.sum_le_sum
    intro i _
    exact Polynomial.natDegree_pow_le.trans (by simpa [smul_eq_mul] using Nat.mul_le_mul_left (e i) (hv i))
  conv_lhs => rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact (hm e _).trans (le_weightedTotalDegree w he)

lemma genericBlockLine_natDegree_le {R σ : Type*} [CommRing R]
    (b : σ → Bool) (f : MvPolynomial σ R) :
    (genericBlockLine b f).natDegree ≤ f.weightedTotalDegree (genericBlockWeight b) := by
  apply polynomial_eval₂_natDegree_le_weight
  intro i
  by_cases hi : b i = true
  · simp only [hi, genericBlockWeight, ite_true]
    exact polynomial_affine_natDegree_le _ _
  · simp [hi, genericBlockWeight]

def genericBlockLineOrigin {R σ : Type*} [CommRing R] (b : σ → Bool) :
    MvPolynomial (σ ⊕ σ) R →+* MvPolynomial σ R :=
  eval₂Hom C (Sum.elim (fun i => if b i then 0 else X i) X)

lemma genericBlockLine_origin {R σ : Type*} [CommRing R]
    (b : σ → Bool) (f : MvPolynomial σ R) :
    (genericBlockLine b f).map (genericBlockLineOrigin b) =
      weightedDegreePolynomial (genericBlockWeight b) f := by
  have he : (Polynomial.mapRingHom (genericBlockLineOrigin (R := R) b)).comp (genericBlockLine b) =
      weightedDegreePolynomial (genericBlockWeight b) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericBlockLine, genericBlockLineOrigin, weightedDegreePolynomial]
    · intro i
      by_cases hi : b i = true <;>
        simp [genericBlockLine, genericBlockLineOrigin, weightedDegreePolynomial,
          genericBlockWeight, hi, ← Polynomial.C_mul_X_pow_eq_monomial]
  exact RingHom.congr_fun he f

theorem genericBlockLine_natDegree {R σ : Type*} [CommRing R]
    (b : σ → Bool) (f : MvPolynomial σ R) :
    (genericBlockLine b f).natDegree = f.weightedTotalDegree (genericBlockWeight b) := by
  apply le_antisymm (genericBlockLine_natDegree_le b f)
  rw [← weightedDegreePolynomial_natDegree, ← genericBlockLine_origin]
  exact Polynomial.natDegree_map_le

theorem genericBlockLine_ne_zero {R σ : Type*} [CommRing R]
    (b : σ → Bool) {f : MvPolynomial σ R} (hf : f ≠ 0) :
    genericBlockLine b f ≠ 0 := by
  intro hz
  have he := genericBlockLine_origin b f
  rw [hz, Polynomial.map_zero] at he
  exact weightedDegreePolynomial_ne_zero _ hf he.symm

lemma genericBlockLine_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (b : σ → Bool) (f : MvPolynomial σ R) :
    (genericBlockLine b f).map (MvPolynomial.map φ) =
      genericBlockLine b (MvPolynomial.map φ f) := by
  have he : (Polynomial.mapRingHom (MvPolynomial.map φ)).comp (genericBlockLine b) =
      (genericBlockLine b).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericBlockLine]
    · intro i
      by_cases hi : b i = true <;> simp [genericBlockLine, hi]
  exact RingHom.congr_fun he f

end
end CCDN
