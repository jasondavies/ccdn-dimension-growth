/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Projection.ProjectiveClosureSpecialization
import CCDN.Auxiliary.HypersurfaceGoodDirection
import CCDN.Auxiliary.HypersurfacePositioning
import CCDN.Projection.FixedCoordinateElimination
import CCDN.Projection.HomogenizationAtInfinity
import Mathlib.Algebra.MvPolynomial.Funext
import CCDN.ForMathlib.MvPolynomial
/-! Over any infinite field a full-degree affine elimination also gives
an integral projection of the projective closure, retaining X0 exactly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def affineDirectionElimination {K : Type*} [Field K] {n : ℕ}
    (b : Fin (n + 1) → K) (i : Fin n) : MvPolynomial (Fin (n + 1)) K :=
  X i.succ - C (b i.succ / b 0) * X 0

lemma affineDirectionElimination_homogeneous {K : Type*} [Field K] {n : ℕ}
    (b : Fin (n + 1) → K) (i : Fin n) :
    (affineDirectionElimination b i).IsHomogeneous 1 :=
  (isHomogeneous_X K i.succ).sub (isHomogeneous_C_mul_X _ 0)

theorem fixed_coordinate_elimination_integral
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hfi : f ∈ I)
    (b : Fin (n + 1) → K) (hb : b 0 ≠ 0)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates (affineDirectionElimination b))).IsIntegral := by
  let H := projectiveClosureIdeal I
  let e := renameEquiv K (closurePivotEquiv n)
  let J := H.map e
  let F := e (scaledHomogenize f.totalDegree 1 f)
  let c : Option (Fin (n + 1)) → K :=
    Option.elim' (b 0) (Fin.cons 0 (fun i => b i.succ))
  have hc : c none ≠ 0 := hb
  have hFhom : F.IsHomogeneous f.totalDegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).rename_isHomogeneous
  have hF0 : F ≠ 0 := by
    intro hz
    have hh : scaledHomogenize f.totalDegree 1 f = 0 :=
      e.injective (hz.trans (map_zero e).symm)
    apply hf
    simpa only [affineChart_scaledHomogenize_one, map_zero] using
      congrArg (affineChart (n + 1)) hh
  have hcompc : c ∘ closurePivotEquiv n = Fin.cons 0 b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [c]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change c (closurePivotEquiv n (Fin.succ 0)) = b 0
        rw [closurePivotEquiv_one]
        rfl
      · simp [c]
  have hFdir : eval c (homogeneousComponent F.totalDegree F) ≠ 0 := by
    rw [hFhom.totalDegree hF0, homogeneousComponent_eq_self hFhom]
    change eval c (rename (closurePivotEquiv n) (scaledHomogenize f.totalDegree 1 f)) ≠ 0
    rw [eval_rename, hcompc, scaledHomogenize_one_eval_at_infinity f le_rfl]
    exact hdir
  have hFmem : F ∈ J := by
    apply Ideal.mem_map_of_mem
    rw [homogeneous_mem_projectiveClosureIdeal_iff I _
      (scaledHomogenize_homogeneous 1 f le_rfl), affineChart_scaledHomogenize_one]
    exact hfi
  let χ := coordinateEliminationMap J (hypersurfaceAffineCoordinates 0 c hc)
  have hraw : χ.IsIntegral := by
    apply coordinateEliminationMap_isIntegral J _
      (normalizedHypersurfaceCoordinates 0 c hc F)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFmem)
    · exact normalizedHypersurfaceCoordinates_monic 0 c hc F hFdir
  have hJ : J = H.map
      (e : MvPolynomial (Fin (n + 2)) K →+* MvPolynomial (Option (Fin (n + 1))) K) := rfl
  let φ := (Ideal.quotientEquivAlg H J e hJ).symm
  have hφ : φ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ φ.surjective
  have hint := RingHom.IsIntegral.trans χ.toRingHom φ.toRingHom hraw hφ
  have heq : φ.toAlgHom.comp χ = projectionCoordinateMap H
      (closureProjectionCoordinates (affineDirectionElimination b)) := by
    ext i
    rw [AlgHom.comp_apply]
    change φ (coordinateEliminationMap J (hypersurfaceAffineCoordinates 0 c hc) (X i)) = _
    rw [coordinateEliminationMap_direction_X]
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, c, projectionCoordinateMap, closureProjectionCoordinates]
    · simp [e, c, projectionCoordinateMap, closureProjectionCoordinates,
        affineDirectionElimination]
  change (φ.toAlgHom.comp χ).IsIntegral at hint
  rwa [heq] at hint

theorem exists_closure_integral_elimination_infinite
    {K : Type*} [Field K] [Infinite K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hfi : f ∈ I) :
    ∃ a : Fin n → MvPolynomial (Fin (n + 1)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)).IsIntegral := by
  let P := X 0 * homogeneousComponent f.totalDegree f
  have hP : P ≠ 0 := mul_ne_zero (X_ne_zero 0) (homogeneousComponent_totalDegree_ne_zero hf)
  obtain ⟨b,hb⟩ : ∃ b : Fin (n + 1) → K, eval b P ≠ 0 := by
    by_contra! hz
    apply hP
    apply MvPolynomial.funext
    intro b
    simpa only [map_zero] using hz b
  have he : b 0 * eval b (homogeneousComponent f.totalDegree f) ≠ 0 := by
    simpa only [P, map_mul, eval_X] using hb
  have hint := fixed_coordinate_elimination_integral I f hf hfi b
    (left_ne_zero_of_mul he) (right_ne_zero_of_mul he)
  exact ⟨affineDirectionElimination b, affineDirectionElimination_homogeneous b,
    affine_projection_integral_of_closure_integral I _ hint, hint⟩

end
end CCDN
