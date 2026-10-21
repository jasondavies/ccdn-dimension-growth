/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.LowerBound.GridPolynomialNormalization
public import CCDN.Projection.BoundedDegreeNormalizationFiber
public import CCDN.Algebra.SmallOutsidePoint
/-! The sharp grid bound for every prime affine variety. The
vanishing grid polynomials construct finite integral parameters; their
function-field rank is controlled by the Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The irreducible case of CCDN Lemma 4.1.1 over any characteristic-zero
field, including zero-dimensional varieties and empty coordinate grids. -/
theorem prime_ideal_grid_card_le
    {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d * S.card ^ (filteredHilbertPolynomial I).natDegree := by
  classical
  by_cases hdim0 : (filteredHilbertPolynomial I).natDegree = 0
  · have hh := zero_dimensional_affine_points_card_le I d hdim0
      (by simpa only [hdim0, Nat.factorial_zero, Nat.cast_one, div_one] using hdegree)
      (fun x : s => x.val) Subtype.val_injective (fun x => hzero x.val x.property)
    simpa only [Fintype.card_coe, hdim0, pow_zero, Nat.mul_one] using hh
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
    (show 1 ≤ (filteredHilbertPolynomial I).natDegree by omega)
  have hdim : (filteredHilbertPolynomial I).natDegree = m + 1 := by omega
  by_cases hS : S.Nonempty
  · obtain ⟨l, hl, hint, hinj, hvan⟩ := exists_grid_polynomial_normalization n m I hdim S hS
    have hh := bounded_degree_normalization_fiber_card_le I S.card
      (Finset.card_pos.mpr hS) l hl hinj hint d ⟨hdim, by simpa only [hdim] using hdegree⟩
      (0 : Fin (m + 1) → K) s hzero
      (fun x hx i => hvan x (hgrid x hx) i)
    simpa only [hdim] using hh
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hn : 0 < n := by
      obtain ⟨_, _, hh, _⟩ := filteredHilbertPolynomial_positive_multiplicity I
        (Ideal.IsPrime.ne_top ‹I.IsPrime›)
      simp only [Fintype.card_fin, hdim] at hh
      omega
    have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := hgrid x hx ⟨0, hn⟩
      simp only [hS0, Finset.notMem_empty] at hh
    rw [hs, Finset.card_empty]
    exact Nat.zero_le _

end
end CCDN
