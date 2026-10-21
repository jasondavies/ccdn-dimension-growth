module

public import CCDN.Determinant.AmbientProjectiveDeterminant
public import CCDN.Analysis.ProjectiveCoefficientNumerics
public import CCDN.Auxiliary.HypersurfaceCoefficientDichotomy
/-! The coefficient-height dichotomy with a multiplier depending only on
the ambient dimension, uniformly in the equation's degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Exact-rank coefficient comparison for the full coefficient height. -/
theorem homogeneous_no_auxiliary_height_comparison {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (points : Fin t → IntPoint (n + 1)) (hzero : ∀ i, eval (points i) f = 0)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous d →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), s + 1 = (n + d).choose d ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n d) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      (integerCoefficientHeight f : ℝ) ≤
        Real.sqrt (((evaluationMatrix (homogeneousMonomials n d) (points ∘ a) *
          (evaluationMatrix (homogeneousMonomials n d) (points ∘ a))ᵀ).det : ℤ) : ℝ) /
          (Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n d) (points ∘ a)) : ℝ) := by
  classical
  obtain ⟨s, a, _, hli, hspan, hs⟩ :=
    homogeneous_independent_evaluation_rows f hf hf0 le_rfl points hzero
  let mon := homogeneousMonomials n d
  let A := evaluationMatrix mon (points ∘ a)
  have hr := integer_homogeneous_evaluation_rank_eq f hf hf0 le_rfl points hzero hrel
  have he : ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).rank = s := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, ← Matrix.rank_eq_finrank_span_row,
      hli.rank_matrix, Fintype.card_fin]
  rw [he] at hr
  simp only [Nat.sub_self, Nat.add_zero, Nat.choose_zero_right] at hr
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hli (by simpa using hs)
  simp only [Fintype.card_fin] at hsmall
  have hNs : (((n + d).choose d : ℝ) - s) = 1 := by
    have hh : (s : ℝ) + 1 = ((n + d).choose d : ℝ) := by exact_mod_cast hr
    linarith
  rw [hNs, inv_one, Real.rpow_one] at hsmall
  let g := polynomialOfCoefficients mon v
  have hg0 : g ≠ 0 := polynomialOfCoefficients_ne_zero mon (homogeneousMonomials_injective n d) hv
  have hgh : g.IsHomogeneous d := polynomialOfCoefficients_homogeneous n d v
  have hgz : ∀ i, eval (points i) g = 0 := by
    intro i
    apply vanishes_of_evaluation_row_mem_span mon (points ∘ a) v hAv (points i)
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hD : (0 : ℝ) < (Int.Matrix.minorGcd A : ℝ) := by
    have hh := Int.Matrix.one_le_minorGcd hli
    exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one hh)
  have hc : ∀ e, |(g.coeff e : ℝ)| ≤ Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) /
      (Int.Matrix.minorGcd A : ℝ) := by
    apply abs_coefficient_polynomialOfCoefficients_le mon (homogeneousMonomials_injective n d) v
      (div_nonneg (Real.sqrt_nonneg _) hD.le)
    intro j
    have hj : |v j| ≤ ⨆ k, |v k| := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
    have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := by exact_mod_cast hj
    exact hjR.trans hsmall
  refine ⟨s, a, hr, hli, ?_⟩
  exact integerCoefficientHeight_le f (div_nonneg (Real.sqrt_nonneg _) hD.le)
    (fun m => (homogeneous_same_degree_coefficient_le_of_dvd hf hgh hg0
      (hrel g hgh hgz) m).trans (hc m))

/-- The logarithmic multiplier is independent of the degree and coefficients.
Primitive representatives supply a universal projective determinant divisor. -/
theorem homogeneous_no_auxiliary_coefficient_height_uniform (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {d t : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ),
      f.IsHomogeneous d → f ≠ 0 →
      ∀ (z : Fin t → IntPoint (n + 2)), (∀ i, eval (z i) f = 0) →
      (∀ i, Finset.univ.gcd (z i) = 1) → ∀ {B : ℝ}, 1 ≤ B →
      (∀ i j, |(z i j : ℝ)| ≤ B) →
      (∀ g : MvPolynomial (Fin (n + 2)) ℤ, g.IsHomogeneous d →
        (∀ i, eval (z i) g = 0) → f ∣ g) →
      Real.log (integerCoefficientHeight f : ℝ) ≤
        C + ((n + 1 + d).choose d : ℝ) * d * Real.log B := by
  let c := ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ)
  let a := 1 / (n + 1 : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C, hC, hCbound⟩ := exists_determinant_factorial_absorption hc ha
    (hypersurfaceHeightDeterminantError n)
  refine ⟨C, hC, ?_⟩
  intro d t f hf hf0 z hz hprim B hB hbox hrel
  obtain ⟨s, b, hr, hi, hHb⟩ := homogeneous_no_auxiliary_height_comparison f hf hf0 z hz hrel
  let N := (n + 1 + d).choose d
  let A := evaluationMatrix (homogeneousMonomials (n + 1) d) (z ∘ b)
  let H := (integerCoefficientHeight f : ℝ)
  have hD1 : (1 : ℝ) ≤ (Int.Matrix.minorGcd A : ℝ) := by
    exact_mod_cast Int.Matrix.one_le_minorGcd hi
  have hD0 : (0 : ℝ) < (Int.Matrix.minorGcd A : ℝ) := by linarith
  have hH1 : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf0
  have hHb' : H ≤ (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) /
      (Int.Matrix.minorGcd A : ℝ)) ^ ((1 : ℝ)⁻¹) := by
    simpa only [inv_one, Real.rpow_one] using hHb
  obtain ⟨hGram, hcomp⟩ := log_gcd_le_of_coefficient_bound (by linarith : 0 < H) hD0
    zero_lt_one hHb'
  have hN : 0 < N := by dsimp [N]; omega
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogD : 0 ≤ Real.log (Int.Matrix.minorGcd A : ℝ) := Real.log_nonneg hD1
  have harch := evaluation_log_gram_le hN (homogeneousMonomials (n + 1) d) (z ∘ b)
    hB (fun i j => hbox (b i) j) (fun j => (homogeneousMonomials_degree (n + 1) d j).le) hGram
  have hsN : s ≤ N := by dsimp [N]; omega
  have hfact : (s.factorial : ℝ) ≤ (N : ℝ) ^ s := by
    exact_mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hsN s)
  have hlogfact : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast Nat.factorial_pos s) hfact
    rwa [Real.log_pow] at hh
  have hlower : c * (s : ℝ) ^ (1 + a) * (Real.log s - hypersurfaceHeightDeterminantError n) ≤
      Real.log (Int.Matrix.minorGcd A : ℝ) := by
    by_cases hs : 0 < s
    · let F := fun j => (monomial (homogeneousMonomials (n + 1) d j) 1 :
          MvPolynomial (Fin (n + 2)) ℤ)
      have he : (Matrix.of fun i j => eval ((z ∘ b) i) (F j)) = A := by
        ext i j
        simp [A, F, evaluationMatrix, eval_monomial]
      have hrows : LinearIndependent ℚ
          ((Matrix.of fun i j => eval ((z ∘ b) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
        rw [he]
        exact hi
      have hh := ambient_projective_determinant_log_lower hs F
        (fun j => isHomogeneous_monomial 1 (homogeneousMonomials_degree (n + 1) d j))
        (z ∘ b) (fun i => hprim (b i)) hrows
      simpa only [he] using hh
    · have hs0 : s = 0 := by omega
      simp only [hs0, Nat.cast_zero, Real.zero_rpow (by positivity : 1 + a ≠ 0),
        mul_zero, zero_mul]
      exact hlogD
  have habsorb := hCbound s (Real.log (Int.Matrix.minorGcd A : ℝ)) hlogD hlower
  have hNr : (N : ℝ) = (s : ℝ) + 1 := by exact_mod_cast hr.symm
  rw [← hNr] at habsorb
  have hlast := mul_le_mul_of_nonneg_right (show (s : ℝ) ≤ N by exact_mod_cast hsN)
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlogB)
  change Real.log H ≤ C + (N : ℝ) * d * Real.log B
  nlinarith

/-- CCDN Lemma 4.2.2 with a constant chosen before the degree, equation and
height. The second alternative is a nonmultiple of the same degree
vanishing on every bounded rational projective zero. -/
theorem projective_coefficient_height_dichotomy_uniform (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ),
      f.IsHomogeneous d → f ≠ 0 → ∀ {B : ℝ}, 1 ≤ B →
      (integerCoefficientHeight f : ℝ) ≤ C * B ^ (d * (n + 1 + d).choose d) ∨
      ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
        ∀ x : ProjectivePoint (n + 1), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  classical
  obtain ⟨C, _, hC⟩ := homogeneous_no_auxiliary_coefficient_height_uniform n
  refine ⟨Real.exp C, Real.exp_pos _, ?_⟩
  intro d f hf hf0 B hB
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 2) := fun i => primitiveProjectiveRep (e i).val
  have hz (i) : eval (z i) f = 0 :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hprim (i) : Finset.univ.gcd (z i) = 1 := primitiveProjectiveRep_gcd _
  have hbox (i j) : |(z i j : ℝ)| ≤ B :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  by_cases hrel : ∀ g : MvPolynomial (Fin (n + 2)) ℤ, g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g
  · left
    have hh := Real.exp_le_exp.mpr (hC f hf hf0 z hz hprim hB hbox hrel)
    rw [Real.exp_log (by exact_mod_cast integerCoefficientHeight_pos f hf0)] at hh
    have he : Real.exp (C + ((n + 1 + d).choose d : ℝ) * d * Real.log B) =
        Real.exp C * B ^ (d * (n + 1 + d).choose d) := by
      rw [Real.exp_add]
      congr 1
      rw [← Real.exp_log (pow_pos (by linarith : 0 < B) (d * (n + 1 + d).choose d))]
      congr 1
      rw [Real.log_pow]
      push_cast
      ring
    exact he ▸ hh
  · right
    push Not at hrel
    obtain ⟨g, hgh, hgz, hgnd⟩ := hrel
    refine ⟨g, fun h => hgnd (by rw [h]; exact dvd_zero _), hgh, hgnd, ?_⟩
    intro x hxB hxf
    let xS : S := ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    obtain ⟨i, hi⟩ := e.surjective xS
    have hh := hgz i
    dsimp only [z] at hh
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

end
end CCDN
