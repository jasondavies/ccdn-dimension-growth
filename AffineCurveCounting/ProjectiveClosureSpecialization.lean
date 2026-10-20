module

public import AffineCurveCounting.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral projections of the projective closure that fix X₀ specialize
to integral affine projections on the chart X₀ = 1. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def affineChartAlgHom (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K where
  toRingHom := affineChart n
  commutes' c := by simp [affineChart]

lemma projectiveClosureIdeal_affineChart_mem {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f ∈ projectiveClosureIdeal I) : affineChart n f ∈ I := by
  have h : affineChart n
      (∑ M ∈ Finset.range (f.totalDegree + 1), homogeneousComponent M f) ∈ I := by
    rw [map_sum]
    exact I.sum_mem (fun M _ => (mem_projectiveClosureIdeal_iff I f).mp hf M)
  rwa [sum_homogeneousComponent] at h

def projectiveClosureSpecialization {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I) :=
  Ideal.Quotient.liftₐ (projectiveClosureIdeal I)
    ((Ideal.Quotient.mkₐ K I).comp (affineChartAlgHom K n))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (projectiveClosureIdeal_affineChart_mem I f hf))

@[simp] lemma projectiveClosureSpecialization_mk {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K) :
    projectiveClosureSpecialization I (Ideal.Quotient.mk (projectiveClosureIdeal I) f) =
      Ideal.Quotient.mk I (affineChart n f) := rfl

theorem projectiveClosureSpecialization_surjective {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    Function.Surjective (projectiveClosureSpecialization I) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (projectiveClosureIdeal I) (rename Fin.succ f), ?_⟩
  rw [projectiveClosureSpecialization_mk, affineChart_rename_succ]

theorem affine_projection_integral_of_closure_integral
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).IsIntegral) :
    (projectionCoordinateMap I a).IsIntegral := by
  have hspecial : (projectiveClosureSpecialization I).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (projectiveClosureSpecialization_surjective I)
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).toRingHom
    (projectiveClosureSpecialization I).toRingHom hint hspecial
  have heq : (projectiveClosureSpecialization I).comp
      (projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates a)) =
        (projectionCoordinateMap I a).comp (affineChartAlgHom K m) := by
    apply AlgHom.ext
    intro f
    change Ideal.Quotient.mk I
      (affineChart n (aeval (closureProjectionCoordinates a) f)) =
        Ideal.Quotient.mk I (aeval a (affineChart m f))
    rw [affineChart_aeval_closureProjectionCoordinates]
  change ((projectiveClosureSpecialization I).comp
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a))).IsIntegral at hcomp
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top (affineChartAlgHom K m).toRingHom
    (projectionCoordinateMap I a).toRingHom hcomp

end
end AffineCurveCounting
