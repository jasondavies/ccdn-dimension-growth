/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceHeightDeterminant
public import CCDN.Algebra.PolynomialPredicates

/-! A universal determinant divisor for primitive projective evaluations.
Embedding the points in a coordinate hyperplane makes the established
hypersurface determinant estimate independent of any defining equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

lemma primitive_zero_cons {n : ℕ} (x : Fin n → ℤ) (hx : univ.gcd x = 1) :
    univ.gcd (Fin.cons 0 x) = 1 := by
  have h : univ.gcd (Fin.cons 0 x) ∣ univ.gcd x := by
    apply Finset.dvd_gcd
    intro i _
    simpa using (Finset.gcd_dvd (f := Fin.cons 0 x) (mem_univ i.succ))
  rw [hx] at h
  have hn := Finset.Int.finsetGcd_nonneg (f := Fin.cons 0 x) (s := univ)
  have hh := Int.isUnit_iff_abs_eq.mp (isUnit_of_dvd_one h)
  rwa [abs_of_nonneg hn] at hh

/-- All primitive projective evaluation matrices satisfy this lower bound;
its constants depend only on the number of coordinates. -/
theorem ambient_projective_determinant_log_lower {n s N M : ℕ} (hs : 0 < s)
    (F : Fin N → MvPolynomial (Fin (n + 2)) ℤ)
    (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 2)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row) :
    factorialRoot n / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - hypersurfaceHeightDeterminantError n) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  classical
  let G : Fin N → MvPolynomial (Fin (n + 3)) ℤ := fun j => rename Fin.succ (F j)
  let w : Fin s → IntPoint (n + 3) := fun i => Fin.cons 0 (z i)
  have hG : ∀ j, (G j).IsHomogeneous M := fun j => (hF j).rename_isHomogeneous
  have he : (Matrix.of fun i j => eval (w i) (G j)) =
      Matrix.of fun i j => eval (z i) (F j) := by
    ext i j
    simp [G, w, eval_rename, Function.comp_def]
  have hir : AbsolutelyIrreducible (X (0 : Fin (n + 3)) : MvPolynomial (Fin (n + 3)) ℤ) := by
    dsimp only [AbsolutelyIrreducible]
    rw [map_X]
    apply irreducible_of_totalDegree_eq_one (totalDegree_X _)
    intro x hx
    apply isUnit_of_dvd_one
    simpa using hx (Finsupp.single 0 1)
  have hcoeff : ∀ m, |(((X (0 : Fin (n + 3)) :
      MvPolynomial (Fin (n + 3)) ℤ).coeff m : ℤ) : ℝ)| ≤ 1 := by
    intro m
    rw [coeff_X]
    split <;> norm_num
  have hr : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (w i) (G j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hrows
  have h := hypersurface_determinant_log_lower_height (z := w) hs (X (0 : Fin (n + 3)))
    (isHomogeneous_X ℤ _) (by omega : 0 < 1) hir 1 le_rfl hcoeff
    ⟨hG, fun i => primitive_zero_cons _ (hprim i), fun i => by simp [w], hr⟩
  simpa only [he, Nat.cast_one, Real.log_one, mul_zero, div_one, one_pow,
    zero_div, add_zero, sub_zero] using h

end
end CCDN
