module

public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Closure-preserving integral affine projections compose. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma aeval_closureProjectionCoordinates_rename {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    aeval (closureProjectionCoordinates a) (rename Fin.succ f) =
      rename Fin.succ (aeval a f) := by
  have h : (aeval (R := K) (closureProjectionCoordinates a)).comp (rename Fin.succ) =
      (rename Fin.succ).comp (aeval a) := by
    ext i
    simp [closureProjectionCoordinates]
  exact AlgHom.congr_fun h f

lemma closureProjectionCoordinates_comp {K : Type*} [Field K] {l m n : ℕ}
    (a : Fin l → MvPolynomial (Fin m) K)
    (b : Fin m → MvPolynomial (Fin n) K) (i : Fin (l + 1)) :
    aeval (closureProjectionCoordinates b) (closureProjectionCoordinates a i) =
      closureProjectionCoordinates (fun j => aeval b (a j)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [closureProjectionCoordinates]
  · exact aeval_closureProjectionCoordinates_rename b (a j)

theorem closure_projection_integral_comp
    {K : Type*} [Field K] {l m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (b : Fin m → MvPolynomial (Fin n) K) (hb : ∀ i, (b i).IsHomogeneous 1)
    (a : Fin l → MvPolynomial (Fin m) K)
    (hbintegral : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates b)).IsIntegral)
    (haintegral : (projectionCoordinateMap
      (projectiveClosureIdeal (RingHom.ker (projectionCoordinateMap I b)))
      (closureProjectionCoordinates a)).IsIntegral) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates (fun j => aeval b (a j)))).IsIntegral := by
  rw [projectiveClosureIdeal_projection_kernel I b hb] at haintegral
  let ψ := projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates b)
  let φ := Ideal.kerLiftAlg ψ
  have hφ : φ.IsIntegral := hbintegral.kerLift
  let χ := projectionCoordinateMap (RingHom.ker ψ) (closureProjectionCoordinates a)
  have hcomp := RingHom.IsIntegral.trans χ.toRingHom φ.toRingHom haintegral hφ
  have heq : φ.comp χ = projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates (fun j => aeval b (a j))) := by
    ext i
    simp only [AlgHom.comp_apply, χ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk (projectiveClosureIdeal I))
      (aeval (closureProjectionCoordinates b) (closureProjectionCoordinates a i)) = _
    rw [closureProjectionCoordinates_comp]
  change (φ.comp χ).IsIntegral at hcomp
  rwa [heq] at hcomp

end
end CCDN
