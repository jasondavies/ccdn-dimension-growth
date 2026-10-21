module

public import CCDN.Determinant.BlockDeterminant
import all ArithmeticHeights.BombieriVaaler
public import Mathlib.Algebra.Polynomial.Derivative

/-! Divided differences of polynomials, and determinant congruence from
entrywise congruence. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Divided differences agree with the derivative modulo the argument difference. -/
lemma polynomial_divided_difference {R : Type*} [CommRing R]
    (f : R[X]) (y z : R) :
    ∃ q : R, f.eval y - f.eval z = (y - z) * q ∧
      y - z ∣ q - f.derivative.eval z := by
  have hd : X - C z ∣ f - C (f.eval z) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot]
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (Polynomial.eval y) hg
  simp only [eval_sub, eval_C, eval_mul, eval_X] at he
  have hder := congrArg (fun p : R[X] => p.derivative.eval z) hg
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul,
    derivative_X, derivative_sub, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
  refine ⟨g.eval y, he, ?_⟩
  rw [hder]
  exact Polynomial.sub_dvd_eval_sub y z g

/-- Entrywise congruence implies determinant congruence, for every modulus. -/
lemma dvd_det_sub_of_dvd_entries {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℤ)
    (m : ℤ) (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  let I : Ideal ℤ := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    ext i j
    apply sub_eq_zero.mp
    change φ (A i j) - φ (B i j) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))
  apply Ideal.mem_span_singleton.mp
  change A.det - B.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (A.det - B.det) = 0
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

end
end CCDN
