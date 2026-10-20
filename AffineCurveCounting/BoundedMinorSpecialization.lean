module

public import AffineCurveCounting.ClosedFormParameterDegree
public import AffineCurveCounting.FiniteRowMinor
public import AffineCurveCounting.IntegerPolynomialAvoidance
public import AffineCurveCounting.LinearProjectionFiltration
public import AffineCurveCounting.PrimitiveNormalization

/-! The numerical specialization step for a nonempty polynomial condition on
maximal minors. The geometric construction of a good-center condition is
separate: this module starts with a polynomial and an actual full-rank rational
matrix where it does not vanish. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

/-- Denominator clearing transfers the integer grid lemma to rational
polynomials without increasing the grid size. -/
theorem exists_integer_grid_rational_eval_ne_zero {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℚ) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧
      eval (fun i => (v i : ℚ)) f ≠ 0 := by
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model f hf
  have hg : g ≠ 0 := by
    intro hz
    have hh : C a * f = 0 := by simpa only [hz, map_zero] using he.symm
    exact mul_ne_zero (C_eq_zero.not.mpr ha) hf hh
  obtain ⟨v, hv, hvg⟩ := exists_integer_grid_eval_ne_zero g hg A
    ((rational_scalar_model_degree ha hf he).trans_le hd)
  refine ⟨v, hv, ?_⟩
  intro hz
  have hgzero := (rational_scalar_model_zero_iff ha he (fun i => (v i : ℚ))).mpr hz
  have hh : ((eval v g : ℤ) : ℚ) = 0 := by
    exact (map_eval (Int.castRingHom ℚ) v g).trans hgzero
  exact hvg (Int.cast_eq_zero.mp hh)

/-- The universal determinant in a chosen set of columns. -/
def universalMaximalMinor {r n : ℕ} (c : Fin r ↪ Fin n) :
    MvPolynomial (Fin r × Fin n) ℚ :=
  (Matrix.of fun i j : Fin r => X (i, c j)).det

lemma universalMaximalMinor_eval {r n : ℕ} (c : Fin r ↪ Fin n)
    (A : Matrix (Fin r) (Fin n) ℚ) :
    eval (fun p => A p.1 p.2) (universalMaximalMinor c) =
      (A.submatrix id c).det := by
  rw [universalMaximalMinor, RingHom.map_det]
  congr 1
  ext i j
  simp

lemma universalMaximalMinor_degree {r n : ℕ} (c : Fin r ↪ Fin n) :
    (universalMaximalMinor c).totalDegree ≤ r := by
  have hh := matrix_det_parameterDegree
    (Matrix.of fun i j : Fin r => (X (i, c j) :
      MvPolynomial (Fin r × Fin n) ℚ)) 1 (by intros; simp)
  simpa only [universalMaximalMinor, Fintype.card_fin, Nat.mul_one] using hh

lemma eval_minor_substitution {r n : ℕ}
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (A : Matrix (Fin r) (Fin n) ℚ) :
    eval (fun p => A p.1 p.2) (aeval universalMaximalMinor F) =
      eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F := by
  have hh : (aeval (fun p => A p.1 p.2)).comp (aeval universalMaximalMinor) =
      aeval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) := by
    ext c
    simp only [AlgHom.comp_apply, aeval_X]
    exact universalMaximalMinor_eval c A
  exact congrArg (fun φ => φ F) hh

/-- A nonempty polynomial condition on maximal minors has a bounded integer
specialization of full row rank. The extra minor preserving rank costs one
in the degree of the condition. -/
theorem exists_bounded_integer_minor_specialization {r n : ℕ}
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (A : Matrix (Fin r) (Fin n) ℚ)
    (hli : LinearIndependent ℚ A.row)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ r * (F.totalDegree + 1)) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 := by
  classical
  obtain ⟨c, hc, hdet⟩ := exists_nonzero_minor_of_independent_rows A hli
  let e : Fin r ↪ Fin n := ⟨c, hc⟩
  let U := aeval universalMaximalMinor F
  let V := U * universalMaximalMinor e
  have hV : V ≠ 0 := by
    intro hz
    have hh : eval (fun p => A p.1 p.2) V ≠ 0 := by
      rw [show V = U * universalMaximalMinor e from rfl, eval_mul,
        show U = aeval universalMaximalMinor F from rfl,
        eval_minor_substitution, universalMaximalMinor_eval]
      exact mul_ne_zero hF hdet
    exact hh (by rw [hz, map_zero])
  have hdeg : V.totalDegree ≤ r * (F.totalDegree + 1) := by
    calc
      V.totalDegree ≤ U.totalDegree + (universalMaximalMinor e).totalDegree :=
        totalDegree_mul _ _
      _ ≤ r * F.totalDegree + r := Nat.add_le_add
        (aeval_totalDegree_le _ universalMaximalMinor_degree F)
        (universalMaximalMinor_degree e)
      _ = _ := by ring
  obtain ⟨v, hv, hvalue⟩ :=
    exists_integer_grid_rational_eval_ne_zero V hV _ hdeg
  let M : Matrix (Fin r) (Fin n) ℤ := fun i j => v (i, j)
  have hv' : eval (fun p => ((M.map (Int.castRingHom ℚ)) p.1 p.2)) V ≠ 0 := hvalue
  rw [show V = U * universalMaximalMinor e from rfl, eval_mul,
    show U = aeval universalMaximalMinor F from rfl,
    eval_minor_substitution, universalMaximalMinor_eval] at hv'
  have hm := (mul_ne_zero_iff.mp hv').2
  have hi : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row := by
    apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ e)
    exact Matrix.linearIndependent_rows_of_det_ne_zero hm
  exact ⟨M, fun i j => hv (i, j), hi, (mul_ne_zero_iff.mp hv').1⟩

end
end AffineCurveCounting
