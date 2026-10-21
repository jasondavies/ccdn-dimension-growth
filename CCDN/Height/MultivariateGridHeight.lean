module

public import CCDN.Auxiliary.IntegerGridInterpolation
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Coefficient control on the integer grid in every finite dimension.
The explicit interpolation factor has logarithm O_n(d log(d+1)). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Iterated one-variable interpolation controls every coefficient from the
values on the full grid, with a constant depending only on degree and dimension. -/
theorem multivariate_coefficient_bound_of_integer_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → |eval (fun i => (a i : ℝ)) f| ≤ H)
    (m : Fin n →₀ ℕ) :
    |f.coeff m| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    have hh := heval (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rw [eq_C_of_isEmpty f] at hh
    simpa [hm] using hh
  | succ n ih =>
    let g := (finSuccEquiv ℝ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      · simp [hzero]
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        dsimp only [g]
        omega
    have hvalues (a : Fin n → ℕ) (ha : ∀ i, a i ≤ d) :
        |eval (fun i => (a i : ℝ)) g| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
      have hh := polynomial_coefficient_bound_of_integer_grid
        (Polynomial.map (eval (fun i => (a i : ℝ))) (finSuccEquiv ℝ n f))
        (Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))) hH
        (fun x hx => ?_) (m 0)
      · simpa only [g, Polynomial.coeff_map] using hh
      · rw [← eval_eq_eval_mv_eval']
        have hcons : (Fin.cons (x : ℝ) (fun i => (a i : ℝ))) =
            (fun i => (((Fin.cons x a : Fin (n + 1) → ℕ) i) : ℝ)) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [hcons]
        exact heval (Fin.cons x a) (fun i => Fin.cases hx ha i)
    have hh := ih g hg (show 0 ≤ ((d : ℝ) + 1) ^ (d + 1) * H by positivity)
      hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    rw [show (n + 1) * (d + 1) = n * (d + 1) + (d + 1) by ring, pow_add]
    ring

/-- A single bounded grid value controls all coefficients simultaneously. -/
theorem exists_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧ ∀ m,
      |f.coeff m| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) *
        |eval (fun i => (a i : ℝ)) f| := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))
  have hS : S.Nonempty := ⟨fun _ => 0, by simp [S]⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image
    (fun a => |eval (fun i => (a i : ℝ)) f|) hS
  have hb : ∀ i, a i ≤ d := by
    simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using ha
  refine ⟨a, hb, multivariate_coefficient_bound_of_integer_grid f hd (abs_nonneg _) ?_⟩
  intro b hb
  exact hmax b (by simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using hb)

/-- The interpolation estimate for an integer polynomial. -/
theorem integer_multivariate_coefficient_bound_of_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) →
      |(eval (fun i => (a i : ℤ)) f : ℝ)| ≤ H) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  have hdR : (map (Int.castRingHom ℝ) f).totalDegree ≤ d := by
    unfold MvPolynomial.totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
    exact hd
  have he (a : Fin n → ℕ) : eval (fun i => (a i : ℝ)) (map (Int.castRingHom ℝ) f) =
      (eval (fun i => (a i : ℤ)) f : ℝ) := by
    have hh := map_eval (Int.castRingHom ℝ) (fun i => (a i : ℤ)) f
    change (Int.castRingHom ℝ) (eval (fun i => (a i : ℤ)) f) =
      eval (fun i => (((a i : ℤ)) : ℝ)) (map (Int.castRingHom ℝ) f) at hh
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using hh.symm
  have hh := multivariate_coefficient_bound_of_integer_grid (map (Int.castRingHom ℝ) f)
    hdR hH (fun a ha => by rw [he]; exact heval a ha) m
  simpa only [coeff_map, Int.coe_castRingHom] using hh

/-- Integer equations have the same coefficient control, with a nonzero
chosen grid value whenever the equation is nonzero. -/
theorem exists_integer_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧ eval a f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * |(eval a f : ℝ)| := by
  let fR := map (Int.castRingHom ℝ) f
  have hdR : fR.totalDegree ≤ d := by
    dsimp only [fR]
    unfold MvPolynomial.totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
    exact hd
  obtain ⟨a, ha, hc⟩ := exists_multivariate_grid_height_witness fR hdR
  have he : eval (fun i => (a i : ℝ)) fR = (eval (fun i => (a i : ℤ)) f : ℝ) := by
    have hh := map_eval (Int.castRingHom ℝ) (fun i => (a i : ℤ)) f
    change (Int.castRingHom ℝ) (eval (fun i => (a i : ℤ)) f) =
      eval (fun i => (((a i : ℤ)) : ℝ)) fR at hh
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using hh.symm
  have hb (m) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) *
      |(eval (fun i => (a i : ℤ)) f : ℝ)| := by
    simpa only [fR, coeff_map, Int.coe_castRingHom, he] using hc m
  refine ⟨fun i => (a i : ℤ), fun i => ⟨by positivity, by change (a i : ℤ) ≤ d; exact_mod_cast ha i⟩, ?_, hb⟩
  intro hz
  apply hf
  apply MvPolynomial.ext
  intro m
  have hh := hb m
  rw [hz, Int.cast_zero, abs_zero, mul_zero] at hh
  exact Int.cast_injective (α := ℝ) (by simpa using abs_nonpos_iff.mp hh)

end
end CCDN
