module

public import AffineCurveCounting.RationalDifferential
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Degree bounds for polynomial determinants and Sylvester resultants.
The degree refers to the coefficient parameter, independently of the
eliminated polynomial variable. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

theorem polynomial_det_natDegree_le {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X]) (D : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = _ := by simp

theorem polynomial_resultant_natDegree_le {R : Type*} [CommRing R]
    (f g : R[X][X]) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g m n).natDegree ≤ (m + n) * D := by
  have hM : ∀ i j, (f.sylvester g m n i j).natDegree ≤ D := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp
  simpa only [Fintype.card_fin, resultant] using polynomial_det_natDegree_le (f.sylvester g m n) D hM

/-- Padding the second Sylvester degree preserves nonvanishing when the
first polynomial is irreducible and the second is nonzero of smaller degree. -/
theorem resultant_ne_zero_of_irreducible_of_natDegree_lt
    {K : Type*} [Field K] (f g : K[X]) (hf : Irreducible f) (hg : g ≠ 0)
    (hdeg : g.natDegree < f.natDegree) (n : ℕ) (hn : g.natDegree ≤ n) :
    f.resultant g f.natDegree n ≠ 0 := by
  have hcop : IsCoprime f g := hf.coprime_iff_not_dvd.mpr fun h =>
    (not_le_of_gt hdeg) (natDegree_le_of_dvd h hg)
  have he : n = g.natDegree + (n - g.natDegree) := by omega
  rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))
    (resultant_ne_zero f g hcop)

end
end AffineCurveCounting
