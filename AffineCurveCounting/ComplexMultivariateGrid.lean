module

public import AffineCurveCounting.ComplexGridInterpolation
public import AffineCurveCounting.HomogeneousLeadingCoefficient
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Sharp complex integer-grid bounds in any number of variables. Iteration
of the univariate bound proves the exact coefficient-positioning constant
in CCDN Lemma 3.4.2. The distinguished homogeneous coordinate is indexed first. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem complex_multivariate_coefficient_bound_of_integer_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → ‖eval (fun i => (a i : ℂ)) f‖ ≤ H)
    (m : Fin n →₀ ℕ) :
    ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) * H := by
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    have hh := heval (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rw [eq_C_of_isEmpty f] at hh
    simpa [hm] using hh
  | succ n ih =>
    let g := (finSuccEquiv ℂ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      · simp [hzero]
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        dsimp only [g]
        omega
    have hvalues (a : Fin n → ℕ) (ha : ∀ i, a i ≤ d) :
        ‖eval (fun i => (a i : ℂ)) g‖ ≤ (3 : ℝ) ^ d * H := by
      have hh := complex_polynomial_coefficient_bound_of_integer_grid
        (Polynomial.map (eval (fun i => (a i : ℂ))) (finSuccEquiv ℂ n f))
        (Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))) hH
        (fun x hx => ?_) (m 0)
      · simpa only [g, Polynomial.coeff_map] using hh
      · rw [← eval_eq_eval_mv_eval']
        have hcons : (Fin.cons (x : ℂ) (fun i => (a i : ℂ))) =
            (fun i => (((Fin.cons x a : Fin (n + 1) → ℕ) i) : ℂ)) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [hcons]
        exact heval (Fin.cons x a) (fun i => Fin.cases hx ha i)
    have hh := ih g hg (show 0 ≤ (3 : ℝ) ^ d * H by positivity) hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    rw [show (n + 1) * d = n * d + d by ring, pow_add]
    ring

/-- The same grid point works for all coefficients of a complex polynomial. -/
theorem exists_complex_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧ ∀ m,
      ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) * ‖eval (fun i => (a i : ℂ)) f‖ := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))
  have hS : S.Nonempty := ⟨fun _ => 0, by simp [S]⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image
    (fun a => ‖eval (fun i => (a i : ℂ)) f‖) hS
  have hb : ∀ i, a i ≤ d := by
    simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using ha
  refine ⟨a, hb, complex_multivariate_coefficient_bound_of_integer_grid f hd (norm_nonneg _) ?_⟩
  intro b hb
  exact hmax b (by simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using hb)

/-- CCDN Lemma 3.4.2, with the fixed homogeneous coordinate placed first.
The bound is simultaneous for all coefficients and has the exact factor 3^(nd). -/
theorem exists_complex_homogeneous_grid_height_witness {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℂ) (hf : f.IsHomogeneous d) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧ ∀ m,
      ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) *
        ‖eval (Fin.cons 1 (fun i => (a i : ℂ))) f‖ := by
  obtain ⟨a, ha, hcoeff⟩ := exists_complex_multivariate_grid_height_witness (affineChart n f)
    ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  refine ⟨a, ha, ?_⟩
  intro m
  by_cases hm : m.sum (fun _ e => e) = d
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
    rw [← affineChart_homogeneous_coefficient f hf j, ← affineChart_eval]
    exact hcoeff _
  · rw [hf.coeff_eq_zero hm, norm_zero]
    positivity


/-- A bounded integer shear places the sharp complex grid witness in the
leading coefficient, without changing homogeneous degree. -/
theorem exists_complex_bounded_leading_coefficient_translation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℂ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f) ≠ 0 ∧
      ∀ m, ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) *
        ‖MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f)‖ := by
  obtain ⟨a, ha, hcoeff⟩ := exists_complex_homogeneous_grid_height_witness f hf
  have hval : eval (Fin.cons 1 (fun i => (a i : ℂ))) f ≠ 0 := by
    intro hz
    apply hf0
    apply MvPolynomial.ext
    intro m
    have hh := hcoeff m
    rw [hz, norm_zero, mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  have he := homogeneousTranslation_pure_first (fun i => (a i : ℂ)) f hf
  have hlc := lex_leadingCoeff_eq_pure_first
    (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f)
    (homogeneousTranslation_homogeneous _ hf).totalDegree_le (he ▸ hval)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hlc, he]
    exact hval
  · intro m
    rw [hlc, he]
    exact hcoeff m

end
end AffineCurveCounting
