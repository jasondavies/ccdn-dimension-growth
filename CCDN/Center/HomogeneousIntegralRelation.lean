/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.HomogeneousProjectionEquation
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-! A homogeneous principal relation of an integral linear projection has
full degree in the extra coordinate. Integrality supplies a monic multiple;
its leading coefficient forces the pure power of that coordinate to occur. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma homogeneous_finSucc_natDegree_of_unit_leadingCoeff
    {K : Type*} [Field K] {m d : ℕ}
    (f : MvPolynomial (Fin (m + 1)) K) (hf : f.IsHomogeneous d)
    (hu : IsUnit (finSuccEquiv K m f).leadingCoeff) :
    (finSuccEquiv K m f).natDegree = d := by
  have hc : (constantCoeff (finSuccEquiv K m f).leadingCoeff) ≠ 0 :=
    (hu.map constantCoeff).ne_zero
  have hh := hf (show f.coeff ((0 : Fin m →₀ ℕ).cons
      (finSuccEquiv K m f).natDegree) ≠ 0 from by
    rw [← finSuccEquiv_coeff_coeff]
    exact hc)
  simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons,
    Finsupp.sum_zero_index, add_zero] using hh

lemma projectionCoordinateMap_finSuccEquiv
    {K σ : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial σ K)) (a : Fin m → MvPolynomial σ K)
    (z : MvPolynomial σ K) (f : MvPolynomial (Fin (m + 1)) K) :
    (projectionCoordinateMap I (Fin.cons z a)) f =
      (finSuccEquiv K m f).eval₂ (projectionCoordinateMap I a).toRingHom
        ((Ideal.Quotient.mk I) z) := by
  let ψ := projectionCoordinateMap I a
  let e : Polynomial (MvPolynomial (Fin m) K) →+* (MvPolynomial σ K ⧸ I) :=
    Polynomial.eval₂RingHom ψ.toRingHom ((Ideal.Quotient.mk I) z)
  have he : (projectionCoordinateMap I (Fin.cons z a)).toRingHom =
      e.comp (finSuccEquiv K m).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, ψ, projectionCoordinateMap, finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, ψ, projectionCoordinateMap, finSuccEquiv_X_zero]
      · simp [e, ψ, projectionCoordinateMap, finSuccEquiv_X_succ]
  exact congrArg (fun h => h f) he

lemma projection_relation_eval₂_eq_zero
    {K σ : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial σ K)) (a : Fin m → MvPolynomial σ K)
    (z : MvPolynomial σ K) (f : MvPolynomial (Fin (m + 1)) K)
    (hker : RingHom.ker (projectionCoordinateMap I (Fin.cases z a)) = Ideal.span {f}) :
    (finSuccEquiv K m f).eval₂ (projectionCoordinateMap I a).toRingHom
      ((Ideal.Quotient.mk I) z) = 0 := by
  have hm : f ∈ RingHom.ker (projectionCoordinateMap I (Fin.cases z a)) := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton f)
  have hc : (Fin.cons z a : Fin (m + 1) → MvPolynomial σ K) = Fin.cases z a := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← projectionCoordinateMap_finSuccEquiv, hc]
  exact hm

/-- The monic relation obtained from the integral parameter map
forces every generator of the augmented kernel to have unit leading coefficient. -/
theorem integral_projection_relation_unit_leadingCoeff
    {K σ : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial σ K)) (a : Fin m → MvPolynomial σ K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : MvPolynomial σ K) (f : MvPolynomial (Fin (m + 1)) K)
    (hker : RingHom.ker (projectionCoordinateMap I (Fin.cons z a)) = Ideal.span {f}) :
    IsUnit (finSuccEquiv K m f).leadingCoeff := by
  obtain ⟨p, hp, he⟩ := hint ((Ideal.Quotient.mk I) z)
  have hm : (finSuccEquiv K m).symm p ∈
      RingHom.ker (projectionCoordinateMap I (Fin.cons z a)) := by
    change (projectionCoordinateMap I (Fin.cons z a)) ((finSuccEquiv K m).symm p) = 0
    rw [projectionCoordinateMap_finSuccEquiv, AlgEquiv.apply_symm_apply]
    exact he
  rw [hker, Ideal.mem_span_singleton] at hm
  apply hp.isUnit_leadingCoeff_of_dvd
  have hd := (finSuccEquiv K m).toRingHom.map_dvd hm
  change (finSuccEquiv K m) f ∣ (finSuccEquiv K m) ((finSuccEquiv K m).symm p) at hd
  simpa only [AlgEquiv.apply_symm_apply] using hd

/-- In a homogeneous integral projection, the principal image equation
has its full homogeneous degree in the additional primitive coordinate. -/
theorem integral_homogeneous_projection_relation_natDegree
    {K σ : Type*} [Field K] {m d : ℕ}
    (I : Ideal (MvPolynomial σ K)) (a : Fin m → MvPolynomial σ K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : MvPolynomial σ K) (f : MvPolynomial (Fin (m + 1)) K)
    (hf : f.IsHomogeneous d)
    (hker : RingHom.ker (projectionCoordinateMap I (Fin.cons z a)) = Ideal.span {f}) :
    (finSuccEquiv K m f).natDegree = d :=
  homogeneous_finSucc_natDegree_of_unit_leadingCoeff f hf
    (integral_projection_relation_unit_leadingCoeff I a hint z f hker)

end
end CCDN
