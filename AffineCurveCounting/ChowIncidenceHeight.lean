module

public import AffineCurveCounting.ChowIncidencePrincipal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! The constructed incidence elimination ideal has height exactly one. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem chowIncidenceIdeal_height_one {K : Type*} [Field K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    (chowIncidenceIdeal (m + 1) I).height = 1 := by
  obtain ⟨F,hF,hgen⟩ := exists_chow_incidence_generator_of_dimension I hm
  rw [hgen]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hF.ne_zero) hF.not_isUnit

end
end AffineCurveCounting
