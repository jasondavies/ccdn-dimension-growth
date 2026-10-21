module

public import CCDN.Counterexample.GridVandermondeCounterexample
public import CCDN.Auxiliary.HypersurfaceBadPrimeFactor
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The differing-degree global determinant lower bound cannot hold with
a dimension-only error. A grid of primitive points on a single fixed line
has a nonzero determinant whose logarithm is too small. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset
open scoped BigOperators

lemma log_factorial_le_mul_log {N : ℕ} (_hN : 0 < N) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
  have h : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < N.factorial) h
  simpa only [Real.log_pow] using hh

lemma globalMixedDegreeMatrix_log_det_le {N : ℕ} (hN : 2 ≤ N) :
    Real.log (|(globalMixedDegreeMatrix N).det| : ℝ) ≤
      (3 / 4 : ℝ) * (N : ℝ) ^ 4 * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hQpos : (0 : ℝ) < N.factorial := by positivity
  obtain ⟨hDpos, hDle⟩ := globalMixedDegreeMatrix_det_pos_le N
  have hDposR : (0 : ℝ) < (globalMixedDegreeMatrix N).det := by exact_mod_cast hDpos
  have hDleR : ((globalMixedDegreeMatrix N).det : ℝ) ≤
      ((N : ℝ) * N.factorial) ^ (N.choose 2 * N) * (N : ℝ) ^ (N.choose 2 * N) := by
    exact_mod_cast hDle
  have hlogD := Real.log_le_log hDposR hDleR
  rw [Real.log_mul (pow_ne_zero _ (mul_pos hNpos hQpos).ne') (pow_ne_zero _ hNpos.ne'),
    Real.log_pow, Real.log_pow, Real.log_mul hNpos.ne' hQpos.ne'] at hlogD
  have hQ := log_factorial_le_mul_log (by omega : 0 < N)
  have hE : (0 : ℝ) ≤ (N.choose 2 * N : ℕ) := by positivity
  have hQmul := mul_le_mul_of_nonneg_left hQ hE
  have hsum : Real.log (|(globalMixedDegreeMatrix N).det| : ℝ) ≤
      (N.choose 2 * N : ℕ) * ((N : ℝ) + 2) * Real.log N := by
    rw [abs_of_pos hDposR]
    nlinarith only [hlogD, hQmul]
  have he : ((N.choose 2 * N : ℕ) : ℝ) = (N : ℝ) ^ 2 * (N - 1) / 2 := by
    rw [Nat.cast_mul, Nat.cast_choose_two]
    ring
  rw [he] at hsum
  have hbase : ((N : ℝ) - 1) * (N + 2) ≤ 3 / 2 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hprod := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ (N : ℝ) ^ 2 / 2)
  have hpoly : (N : ℝ) ^ 2 * (N - 1) / 2 * (N + 2) ≤ (3 / 4 : ℝ) * (N : ℝ) ^ 4 := by
    nlinarith only [hprod]
  exact hsum.trans (mul_le_mul_of_nonneg_right hpoly hlog)

/-- For every proposed absolute error constant, a nonzero evaluation
determinant violates the n=1,d=1,b=1 specialization of the printed bound. -/
theorem global_mixed_degree_det_violates_bound (C : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ (globalMixedDegreeMatrix N).det ≠ 0 ∧
      Real.log (|(globalMixedDegreeMatrix N).det| : ℝ) <
        ((N : ℝ) ^ 2) ^ 2 / 2 * (Real.log ((N : ℝ) ^ 2) - C) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 2 (Real.exp (2 * C + 1)))
  have hN2 : (2 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNat : 2 ≤ N := by exact_mod_cast hN2.le
  have hNpos : (0 : ℝ) < N := by linarith
  have hExp : Real.exp (2 * C + 1) < N := (le_max_right _ _).trans_lt hN
  have hlog : 2 * C < Real.log (N : ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos _) hExp
    rw [Real.log_exp] at hh
    linarith
  refine ⟨N, hNat, (globalMixedDegreeMatrix_det_pos_le N).1.ne', ?_⟩
  have hup := globalMixedDegreeMatrix_log_det_le hNat
  rw [Real.log_pow]
  have hgap := mul_pos (pow_pos hNpos 4) (sub_pos.mpr hlog)
  nlinarith only [hup, hgap]

/-- The single-determinant specialization of Proposition 3.2.6 on the fixed
primitive absolutely irreducible line X₂=0 is false when its homogeneous
polynomials may have different degrees. The tuple indexing and evaluation
matrix orientation here match the printed statement. -/
theorem no_uniform_global_mixed_degree_det_lower_bound :
    ¬ ∃ C : ℝ, ∀ (s : ℕ), 0 < s →
      ∀ (ξ : Fin s → Fin 3 → ℤ) (F : Fin s → MvPolynomial (Fin 3) ℤ),
        (∀ i, univ.gcd (ξ i) = 1) →
        (∀ i, eval (ξ i) (X (2 : Fin 3)) = 0) →
        (∀ i, ∃ d : ℕ, (F i).IsHomogeneous d) →
        (Matrix.of fun i j => eval (ξ j) (F i)).det ≠ 0 →
        (s : ℝ) ^ 2 / 2 * (Real.log (s : ℝ) - C) ≤
          Real.log (|(Matrix.of fun i j => eval (ξ j) (F i)).det| : ℝ) := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN, hD, hfail⟩ := global_mixed_degree_det_violates_bound C
  let e : Fin (N * N) ≃ Fin N × Fin N := finProdFinEquiv.symm
  let ξ : Fin (N * N) → Fin 3 → ℤ := fun i => globalMixedDegreePoint N (e i)
  let F : Fin (N * N) → MvPolynomial (Fin 3) ℤ := fun i => globalMixedDegreeForm (e i)
  have hdet : (Matrix.of fun i j => eval (ξ j) (F i)).det =
      (globalMixedDegreeMatrix N).det := by
    change ((globalMixedDegreeMatrix N).transpose.submatrix e e).det = _
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hlower := hC (N * N) (by positivity) ξ F
    (fun i => globalMixedDegreePoint_primitive N (e i))
    (fun i => globalMixedDegreePoint_zero N (e i))
    (fun i => ⟨(e i).1.val + (e i).2.val, globalMixedDegreeForm_homogeneous (e i)⟩)
    (by rwa [hdet])
  rw [hdet, Nat.cast_mul, ← pow_two] at hlower
  exact (not_lt_of_ge hlower) hfail

end
end CCDN
