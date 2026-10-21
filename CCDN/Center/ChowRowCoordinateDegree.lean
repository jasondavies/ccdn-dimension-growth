module

public import CCDN.Center.ChowRowSymmetry
/-! A nonzero evaluation with only one active coordinate in a hyperplane
block identifies its separate degree with the degree in that coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma chow_row_weight_eq_sum {r s : ℕ} (i : Fin r)
    (e : (Fin r × Fin s) →₀ ℕ) :
    Finsupp.weight (chowRowWeight i) e = ∑ j, e (i,j) := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  simp [chowRowWeight]

theorem chow_row_degreeOf_le
    {K : Type*} [Field K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (i : Fin r) (j : Fin s) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    F.degreeOf (i,j) ≤ d := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hh := Finsupp.le_weight (chowRowWeight (s := s) i)
    (s := (i,j)) (by simp [chowRowWeight]) e
  exact hh.trans_eq (hF (mem_support_iff.mp he))

theorem chow_row_degreeOf_eq_of_eval_ne_zero
    {K : Type*} [Field K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (i : Fin r) (j : Fin s) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d)
    (u : Fin r × Fin s → K) (hu : ∀ k, k ≠ j → u (i,k) = 0)
    (hne : eval u F ≠ 0) : F.degreeOf (i,j) = d := by
  classical
  apply le_antisymm (chow_row_degreeOf_le F i j d hF)
  rw [F.as_sum, map_sum] at hne
  obtain ⟨e,he,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [eval_monomial] at hterm
  have hprod : ∀ q ∈ e.support, u q ^ e q ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hterm)
  have hother (k : Fin s) (hk : k ≠ j) : e (i,k) = 0 := by
    by_contra hz
    have hh := hprod (i,k) (Finsupp.mem_support_iff.mpr hz)
    rw [hu k hk, zero_pow hz] at hh
    exact hh rfl
  have hw : Finsupp.weight (chowRowWeight i) e = e (i,j) := by
    rw [chow_row_weight_eq_sum]
    exact Finset.sum_eq_single j (fun k _ hk => hother k hk)
      (fun h => False.elim (h (Finset.mem_univ j)))
  calc
    d = Finsupp.weight (chowRowWeight i) e := (hF (mem_support_iff.mp he)).symm
    _ = e (i,j) := hw
    _ ≤ F.degreeOf (i,j) := monomial_le_degreeOf (i,j) he

end
end CCDN
