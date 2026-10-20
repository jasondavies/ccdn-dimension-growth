module

public import CCDN.SurfaceGeometricCurveCover
public import CCDN.HomogeneousChart
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! The affine Jacobian criterion on x₀=1 is exactly the homogeneous
projective Jacobian criterion, by Euler's identity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma affineChart_pderiv_succ {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) K) (i : Fin n) :
    affineChart n (pderiv i.succ F) = pderiv i (affineChart n F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp [affineChart]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    simp only [pderiv_mul, map_add, map_mul, hf]
    congr 1
    congr 1
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [affineChart, pderiv_X]
    · simp [affineChart, pderiv_X, Pi.single_apply]

/-- Nonsingular points of a projective hypersurface represented with first
coordinate one, using all homogeneous partial derivatives. -/
def projectiveSmoothAffineChart {n : ℕ} (F : CoordinatePolynomial (n + 1)) :
    Set (RatPoint n) :=
  {a | eval (Fin.cons 1 a) F = 0 ∧
    ∃ j, eval (Fin.cons 1 a) (pderiv j F) ≠ 0}

theorem projectiveSmoothAffineChart_eq {d : ℕ}
    (F : CoordinatePolynomial 4) (hF : F.IsHomogeneous d) :
    projectiveSmoothAffineChart F = smoothSurfaceLocus (affineChart 3 F) := by
  classical
  ext a
  have he (i : Fin 3) : eval (Fin.cons 1 a) (pderiv i.succ F) =
      eval a (pderiv i (affineChart 3 F)) := by
    rw [← affineChart_eval, affineChart_pderiv_succ]
  have hzero (hz : eval (Fin.cons 1 a) F = 0)
      (hs : ∀ i : Fin 3, eval (Fin.cons 1 a) (pderiv i.succ F) = 0) :
      eval (Fin.cons 1 a) (pderiv 0 F) = 0 := by
    have h := congrArg (eval (Fin.cons 1 a)) hF.sum_X_mul_pderiv
    change eval (Fin.cons 1 a) (∑ i : Fin 4, X i * pderiv i F) =
      eval (Fin.cons 1 a) (d • F) at h
    rw [map_sum, map_nsmul, hz, nsmul_zero, Fin.sum_univ_succ] at h
    simp only [eval_mul, eval_X, Fin.cons_zero, Fin.cons_succ, hs, mul_zero,
      Finset.sum_const_zero, one_mul, add_zero] at h
    exact h
  constructor
  · rintro ⟨hz,j,hj⟩
    refine ⟨?_,?_⟩
    · change eval a (affineChart 3 F) = 0
      rwa [affineChart_eval]
    · rintro ⟨_,hs⟩
      apply hj
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hzero hz (fun i => (he i).trans (hs i))
      · exact (he i).trans (hs i)
  · rintro ⟨hz,hns⟩
    change eval a (affineChart 3 F) = 0 at hz
    have hs : ¬ ∀ i, eval a (pderiv i (affineChart 3 F)) = 0 :=
      fun h => hns ⟨hz,h⟩
    obtain ⟨i,hi⟩ := not_forall.mp hs
    exact ⟨(affineChart_eval F a).symm.trans hz,i.succ,fun h => hi ((he i).symm.trans h)⟩

end
end CCDN
