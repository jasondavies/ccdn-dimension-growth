/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.HilbertPolynomialComparison
import CCDN.Hilbert.ProperSectionHilbert
import CCDN.Hypersurface.PrincipalSectionGridBound
/-! A strict containment of affine prime ideals strictly lowers the
Hilbert dimension. The proof uses a polynomial in their difference. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem prime_ideal_strict_hilbert_dimension_drop
    {K : Type*} [Field K] {n m : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hJ : J ≠ ⊤) (hIJ : I < J) :
    (filteredHilbertPolynomial J).natDegree ≤ m := by
  obtain ⟨f, hfJ, hfI⟩ := IsConcreteLE.not_le_iff_exists.mp (not_le_of_gt hIJ)
  have hsection : I ⊔ Ideal.span {f} ≤ J :=
    sup_le hIJ.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfJ))
  have hsectionproper : I ⊔ Ideal.span {f} ≠ ⊤ :=
    fun h => hJ (top_le_iff.mp (h ▸ hsection))
  have hfdeg : 0 < f.totalDegree := by
    by_contra! h
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hc : f.coeff 0 ≠ 0 := by
      intro hc
      apply hfI
      rw [he, hc, map_zero]
      exact I.zero_mem
    have hu : IsUnit f := by
      rw [he]
      exact (isUnit_iff_ne_zero.mpr hc).map C
    exact hJ (Ideal.eq_top_of_isUnit_mem J hfJ hu)
  exact (filteredHilbertPolynomial_natDegree_le J _ hJ
    (filteredCoordinateSpace_finrank_antitone_ideal _ _ hsection)).trans
      (proper_section_hilbert_dimension_leadingCoeff I m hdim f hfI hfdeg hsectionproper).1

theorem prime_ideal_not_le_of_same_positive_dimension
    {K : Type*} [Field K] {n m : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [J.IsPrime]
    (hI : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hJ : (filteredHilbertPolynomial J).natDegree = m + 1) (hne : I ≠ J) :
    ¬ I ≤ J := by
  intro h
  have hh := prime_ideal_strict_hilbert_dimension_drop I J hI
    (Ideal.IsPrime.ne_top ‹J.IsPrime›) (lt_of_le_of_ne h hne)
  omega

end
end CCDN
