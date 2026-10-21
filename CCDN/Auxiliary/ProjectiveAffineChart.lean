module

public import CCDN.Plane.ProjectivePlaneBezout
public import CCDN.Algebra.HomogeneousChart
/-! Affine coordinates on the standard open subset of projective space,
with injectivity and compatibility with homogeneous equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

def projectiveAffineCoordinates {n : ℕ} (x : Projectivization K (Fin (n + 1) → K)) :
    Fin n → K := fun j => x.rep j.succ / x.rep 0

lemma projectiveAffineCoordinates_normalization {n : ℕ}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0) :
    Fin.cons 1 (projectiveAffineCoordinates x) = (x.rep 0)⁻¹ • x.rep := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [hx]
  · simp [projectiveAffineCoordinates, div_eq_mul_inv, mul_comm]

lemma affineCoordinateVector_ne_zero {n : ℕ} (a : Fin n → K) :
    (Fin.cons 1 a : Fin (n + 1) → K) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp at hh

lemma projectiveAffineCoordinates_mk {n : ℕ}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0) :
    Projectivization.mk K (Fin.cons 1 (projectiveAffineCoordinates x))
      (affineCoordinateVector_ne_zero _) = x := by
  calc
    _ = Projectivization.mk K x.rep x.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨_, (projectiveAffineCoordinates_normalization x hx).symm⟩
    _ = x := x.mk_rep

theorem projectiveAffineCoordinates_injective {n : ℕ}
    {x y : Projectivization K (Fin (n + 1) → K)}
    (hx : x.rep 0 ≠ 0) (hy : y.rep 0 ≠ 0)
    (hxy : projectiveAffineCoordinates x = projectiveAffineCoordinates y) : x = y := by
  have h := congrArg (fun a : Fin n → K => Projectivization.mk K (Fin.cons 1 a : Fin (n + 1) → K)
    (affineCoordinateVector_ne_zero a)) hxy
  rwa [projectiveAffineCoordinates_mk x hx, projectiveAffineCoordinates_mk y hy] at h

theorem projectiveAffineCoordinates_zero {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0)
    (hxf : x ∈ projectiveZeroLocus f) :
    eval (projectiveAffineCoordinates x) (affineChart n f) = 0 := by
  rw [affineChart_eval, projectiveAffineCoordinates_normalization x hx,
    homogeneous_eval_smul hf, show eval x.rep f = 0 from hxf, mul_zero]

end
end CCDN
