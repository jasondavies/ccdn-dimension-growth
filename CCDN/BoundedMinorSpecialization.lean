module

public import CCDN.ClosedFormParameterDegree
public import CCDN.FiniteRowMinor
public import CCDN.IntegerPolynomialAvoidance
public import CCDN.LinearProjectionFiltration
public import CCDN.PrimitiveNormalization

/-! The numerical specialization step for a nonempty polynomial condition on
maximal minors. The geometric construction of a good-center condition is
separate: this module starts with a polynomial and a full-rank rational
matrix where it does not vanish. -/

@[expose] public section
namespace CCDN
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

end
end CCDN
