module

public import CCDN.NestedPolynomialL1
public import CCDN.AmbientNoetherVanishing
public import CCDN.EulerUniversalHeight

/-! Explicit coefficient-sum bounds for generic plane restrictions.
An original monomial of degree d contributes at most 3^d; an Euler matrix
entry contributes at most d times this quantity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientL1_pow_le {σ : Type*} (f : MvPolynomial σ ℤ) (n : ℕ) :
    coefficientL1 (f ^ n) ≤ coefficientL1 f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientL1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

lemma universalPlane_coordinate_flatten_l1_le {σ : Type*} (i : σ) :
    coefficientL1 ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
      (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1)) ≤ 3 := by
  simp only [map_add, map_mul, sumAlgEquiv_symm_C_X, sumAlgEquiv_symm_X]
  have hx (j : Fin 2 ⊕ PlaneParameters σ) :
      coefficientL1 (X j : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ) = 1 := by
    simp [X]
  apply (coefficientL1_add_le _ _).trans
  have hab := (coefficientL1_add_le
    (X (Sum.inr (i,0)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ)
      (X (Sum.inr (i,1)) * X (Sum.inl 0))).trans
      (Nat.add_le_add_left (coefficientL1_mul_le _ _) _)
  have hc := coefficientL1_mul_le
    (X (Sum.inr (i,2)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ) (X (Sum.inl 1))
  simpa only [hx] using Nat.add_le_add hab hc

theorem universalPlane_monomial_flatten_l1_le {σ : Type*} (m : σ →₀ ℕ) :
    coefficientL1 ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
      (universalPlaneMap ℤ σ (monomial m 1))) ≤ 3 ^ m.degree := by
  classical
  rw [universalPlaneMap, aeval_monomial, map_one, one_mul]
  change coefficientL1 ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
    (∏ i ∈ m.support,
      (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1) ^ m i)) ≤ _
  rw [map_prod]
  simp only [map_pow]
  calc
    _ ≤ ∏ i ∈ m.support, coefficientL1
        (((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
          (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1)) ^ m i) :=
      coefficientL1_prod_le _ _
    _ ≤ ∏ i ∈ m.support, 3 ^ m i := by
      exact Finset.prod_le_prod fun i _ =>
        (coefficientL1_pow_le _ _).trans
          (Nat.pow_le_pow_left (universalPlane_coordinate_flatten_l1_le i) _)
    _ = 3 ^ m.degree := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

theorem universalPlane_monomial_coefficient_l1_le {σ : Type*}
    (m : σ →₀ ℕ) (n : Fin 2 →₀ ℕ) :
    coefficientL1 ((universalPlaneMap ℤ σ (monomial m 1)).coeff n) ≤ 3 ^ m.degree :=
  (coefficientL1_coeff_le_flatten _ _).trans (universalPlane_monomial_flatten_l1_le m)

theorem eulerClosedForm_entry_l1_le {σ : Type*} (k H : ℕ)
    (f : Polynomial (Polynomial (MvPolynomial σ ℤ)))
    (hf : bivariateTotalDegree f ≤ k + 2)
    (hcoeff : ∀ i, coefficientL1 (eulerCoefficientData (k + 2) f i) ≤ H)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    coefficientL1 (eulerClosedFormCoefficientMatrix k f row col) ≤ (k + 2) * H := by
  have he := congrFun (congrFun (universalEulerMatrix_specialize k f hf) row) col
  change eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ))
    (eulerCoefficientData (k + 2) f) (universalEulerMatrix k row col) = _ at he
  rw [← he]
  obtain hz | ⟨i,c,hc,hm⟩ := universalEulerMatrix_sparse k row col
  · rw [hz, map_zero, coefficientL1_zero]
    exact Nat.zero_le _
  · rw [hm, map_mul, eval₂Hom_C]
    have hX : eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ))
        (eulerCoefficientData (k + 2) f) (X i) = eulerCoefficientData (k + 2) f i :=
      eval₂_X _ _ _
    rw [hX]
    change coefficientL1 (C c * eulerCoefficientData (k + 2) f i) ≤ _
    apply (coefficientL1_mul_le _ _).trans
    rw [coefficientL1_C]
    apply Nat.mul_le_mul _ (hcoeff i)
    have hh : (c.natAbs : ℤ) ≤ (k + 2 : ℕ) := by simpa only [Int.natCast_natAbs] using hc
    exact_mod_cast hh

theorem ambientEulerEntry_monomial_l1_le {σ : Type*} (k : ℕ)
    (m : σ →₀ ℕ) (hm : m.degree = k + 2) (row : ℕ × ℕ) (col : EulerColumns k) :
    coefficientL1 (ambientEulerEntryLinear ℤ σ k row col (monomial m 1)) ≤
      (k + 2) * 3 ^ (k + 2) := by
  rw [ambientEulerEntryLinear_apply]
  apply eulerClosedForm_entry_l1_le k (3 ^ (k + 2)) _
  · exact (universalPlanePolynomial_totalDegree_le _).trans
      ((totalDegree_monomial_le m (1 : ℤ)).trans (by change m.degree ≤ k + 2; omega))
  · intro i
    simpa only [eulerCoefficientData, universalPlanePolynomial,
      AlgEquiv.symm_apply_apply, hm] using
      universalPlane_monomial_coefficient_l1_le m
        ((boundedExponentEquivSym (Fin 2) (k + 2)).symm i).val

end
end CCDN
