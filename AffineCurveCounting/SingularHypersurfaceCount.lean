module

public import AffineCurveCounting.NonabsoluteHypersurfaceCount
public import AffineCurveCounting.HypersurfacePositioningCharZero

/-! The singular locus of an irreducible rational hypersurface has a
coefficient-uniform codimension-two integer point bound. A nonzero partial
derivative gives the actual proper intersection used in the count. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def singularHypersurfaceLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    Set (RatPoint n) :=
  {x | eval x f = 0 ∧ ∀ j, eval x (pderiv j f) = 0}

theorem exists_proper_partial_derivative {K σ : Type*}
    [Field K] [CharZero K] [Fintype σ]
    (f : MvPolynomial σ K) (hir : Irreducible f) :
    ∃ j, pderiv j f ≠ 0 ∧ ¬ f ∣ pderiv j f ∧
      (pderiv j f).totalDegree < f.totalDegree := by
  have hd := irreducible_mvPolynomial_totalDegree_pos hir
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_charZero f hd
  have hdeg : (pderiv j f).totalDegree < f.totalDegree := by
    have := pderiv_totalDegree_le f j
    omega
  refine ⟨j, hj, ?_, hdeg⟩
  rintro ⟨g, he⟩
  have hg : g ≠ 0 := by intro hz; exact hj (by rw [he, hz, mul_zero])
  have hm := totalDegree_mul_of_isDomain hir.ne_zero hg
  rw [← he] at hm
  omega

theorem singular_hypersurface_count_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨j, _, hproper, hdeg⟩ := exists_proper_partial_derivative f hir
  have hsub : singularHypersurfaceLocus f ⊆ zeroLocus f ∩ zeroLocus (pderiv j f) :=
    fun x hx => ⟨hx.1, hx.2 j⟩
  exact (Nat.cast_le.mpr (count_mono hsub le_rfl)).trans
    (proper_intersection_count_le_box f (pderiv j f) hir.prime hproper le_rfl hdeg.le hB)

theorem singular_hypersurface_dimension_growth {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  calc
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n :=
      singular_hypersurface_count_le f hir (by linarith)
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (3 * B) ^ n := by
      gcongr
      linarith
    _ = _ := by simp only [mul_pow]; ring

end
end AffineCurveCounting
