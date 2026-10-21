module

public import CCDN.HomogeneousDeterminantComparison
public import CCDN.SingularDeterminantCutoff

/-! The affine chart `z = 1` of a homogeneous plane equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Restrict a ternary homogeneous equation to the chart x₀=1. -/
def planeAffineChart : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  eval₂Hom C (Fin.cons 1 X)

lemma planeAffineChart_eval (f : MvPolynomial (Fin 3) ℤ) (z : Fin 2 → ℤ) :
    eval z (planeAffineChart f) = eval (Fin.cons 1 z) f := by
  change eval z (eval₂ C (Fin.cons 1 X) f) = _
  rw [← eval_assoc]
  have he : (eval z) ∘ Fin.cons (1 : MvPolynomial (Fin 2) ℤ) X = Fin.cons 1 z := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  rw [he]

end
end CCDN
