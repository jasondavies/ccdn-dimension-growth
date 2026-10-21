module

public import CCDN.Projection.HomogenizationAtInfinity
public import CCDN.Projection.ProjectiveClosureProjection
public import CCDN.Projection.FinIntegerHilbertElimination
/-! Full-degree affine elimination also gives an integral projection of the
projective closure, fixing its homogenizing coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def closurePivotEquiv (n : ℕ) : Fin (n + 2) ≃ Option (Fin (n + 1)) :=
  (Equiv.swap 0 (Fin.succ 0)).trans (finSuccEquiv (n + 1))

@[simp] lemma closurePivotEquiv_zero (n : ℕ) : closurePivotEquiv n 0 = some 0 := by
  simp [closurePivotEquiv]

@[simp] lemma closurePivotEquiv_one (n : ℕ) : closurePivotEquiv n (Fin.succ 0) = none := by
  simp [closurePivotEquiv]

@[simp] lemma closurePivotEquiv_succ_succ {n : ℕ} (i : Fin n) :
    closurePivotEquiv n i.succ.succ = some i.succ := by
  have h0 : i.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
  have h1 : i.succ.succ ≠ (Fin.succ 0 : Fin (n + 2)) := by
    intro h
    exact Fin.succ_ne_zero i (Fin.succ_injective _ h)
  simp only [closurePivotEquiv, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
  rfl

@[simp] lemma closurePivotEquiv_symm_none (n : ℕ) :
    (closurePivotEquiv n).symm none = Fin.succ 0 := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_one n).symm

@[simp] lemma closurePivotEquiv_symm_some_zero (n : ℕ) :
    (closurePivotEquiv n).symm (some 0) = 0 := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_zero n).symm

@[simp] lemma closurePivotEquiv_symm_some_succ {n : ℕ} (i : Fin n) :
    (closurePivotEquiv n).symm (some i.succ) = i.succ.succ := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_succ_succ i).symm

def closureEliminationDirection {n : ℕ} (b : Option (Fin n) → ℤ) :
    Option (Fin (n + 1)) → ℤ :=
  Option.elim' (b none) (Fin.cons 0 (fun i => b (some i)))

lemma closureEliminationDirection_comp {n : ℕ} (b : Option (Fin n) → ℤ) :
    (fun i => (closureEliminationDirection b (closurePivotEquiv n i) : ℚ)) =
      Fin.cons 0 (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [closureEliminationDirection]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [closurePivotEquiv_one]
      rfl
    · rw [closurePivotEquiv_succ_succ]
      rfl

lemma closureEliminationDirection_eval {n : ℕ} (b : Option (Fin n) → ℤ)
    (f : MvPolynomial (Fin (n + 1)) ℚ) :
    eval (fun i => (closureEliminationDirection b i : ℚ))
        (rename (closurePivotEquiv n) (boundedHomogenize f.totalDegree f)) =
      eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
        (homogeneousComponent f.totalDegree f) := by
  rw [eval_rename]
  change eval (fun i => (closureEliminationDirection b (closurePivotEquiv n i) : ℚ))
    (boundedHomogenize f.totalDegree f) = _
  rw [closureEliminationDirection_comp, boundedHomogenize_eval_at_infinity f le_rfl]

/-- A full-degree direction for an affine ideal equation gives an
integral map of projective closures whose first coordinate remains X₀. -/
theorem fixedCoordinateElimination_isIntegral {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0) (hfi : f ∈ I)
    (b : Option (Fin n) → ℤ) (hb : (b none : ℚ) ≠ 0)
    (hdir : eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
      (homogeneousComponent f.totalDegree f) ≠ 0) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates
        (fun i => integerLinearForm (finEliminationMatrix b i)))).IsIntegral := by
  let H := projectiveClosureIdeal I
  let e := renameEquiv ℚ (closurePivotEquiv n)
  let J := H.map e
  let F := e (boundedHomogenize f.totalDegree f)
  let c := closureEliminationDirection b
  have hc : (c none : ℚ) ≠ 0 := hb
  have hFhom : F.IsHomogeneous f.totalDegree :=
    (boundedHomogenize_homogeneous f le_rfl).rename_isHomogeneous
  have hF0 : F ≠ 0 := by
    intro h
    have hh : boundedHomogenize f.totalDegree f = 0 := e.injective (by
      change e (boundedHomogenize f.totalDegree f) = e 0
      rw [map_zero]
      exact h)
    apply hf
    simpa only [affineChart_boundedHomogenize, map_zero] using
      congrArg (affineChart (n + 1)) hh
  have hFdeg := hFhom.totalDegree hF0
  have hFdir : eval (fun i => (c i : ℚ))
      (homogeneousComponent F.totalDegree F) ≠ 0 := by
    rw [hFdeg, homogeneousComponent_eq_self hFhom]
    exact (closureEliminationDirection_eval b f).trans_ne hdir
  have hFmem : F ∈ J := by
    apply Ideal.mem_map_of_mem
    rw [homogeneous_mem_projectiveClosureIdeal_iff I _
      (boundedHomogenize_homogeneous f le_rfl), affineChart_boundedHomogenize]
    exact hfi
  have hraw : (coordinateEliminationMap J
      (hypersurfaceAffineCoordinates 0 (fun i => (c i : ℚ)) hc)).IsIntegral := by
    apply coordinateEliminationMap_isIntegral J _
      (normalizedHypersurfaceCoordinates 0 (fun i => (c i : ℚ)) hc F)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFmem)
    · exact normalizedHypersurfaceCoordinates_monic 0 _ hc F hFdir
  rw [coordinateEliminationMap_eq_projection] at hraw
  have hint := integerEliminationMap_isIntegral J c hc hraw
  have hJ : J = H.map
      (e : MvPolynomial (Fin (n + 2)) ℚ →+*
        MvPolynomial (Option (Fin (n + 1))) ℚ) := rfl
  let φ := (Ideal.quotientEquivAlg H J e hJ).symm
  have hφ : φ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ φ.surjective
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap J (integerEliminationCoordinates c)).toRingHom φ.toRingHom
    hint hφ
  let a := fun i => integerLinearForm (finEliminationMatrix b i)
  let ψ := projectionCoordinateMap H (closureProjectionCoordinates a)
  let χ : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin (n + 1)) ℚ :=
    aeval (Fin.cons (C (b none : ℚ) * X 0) (fun i => X i.succ))
  have heq : φ.toAlgHom.comp (projectionCoordinateMap J (integerEliminationCoordinates c)) =
      ψ.comp χ := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change φ ((Ideal.Quotient.mk J) (integerEliminationCoordinates c i)) = ψ (χ (X i))
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [integerEliminationCoordinates, c, closureEliminationDirection, e,
        ψ, χ, projectionCoordinateMap, closureProjectionCoordinates]
    · simp [integerEliminationCoordinates, c, closureEliminationDirection, e,
        ψ, χ, projectionCoordinateMap, closureProjectionCoordinates, a,
        integerLinearForm_finEliminationMatrix]
  change (φ.toAlgHom.comp
    (projectionCoordinateMap J (integerEliminationCoordinates c))).IsIntegral at hcomp
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top χ.toRingHom ψ.toRingHom hcomp

end
end CCDN
