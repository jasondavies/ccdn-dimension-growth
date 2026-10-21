/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.ProjectiveChartDegree

/-!
An integral homogeneous linear projection has no nonzero geometric
point in its kernel. This gives disjointness from its projective
center over any infinite extension field.

Integrality supplies a monic equation for each coordinate of
every geometric fiber. The equation is chosen before the points of that
fiber and works over any extension of the base field.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_monic_integral_projection_fiber_equation
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (a : τ → MvPolynomial σ K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : τ → L) (i : σ) :
    ∃ p : Polynomial L, p.Monic ∧
      ∀ x : σ → L, (∀ f ∈ I, aeval x f = 0) →
        (∀ j, aeval x (a j) = z j) → p.eval (x i) = 0 := by
  let ψ := projectionCoordinateMap I a
  obtain ⟨p, hp, he⟩ := hint ((Ideal.Quotient.mk I) (X i))
  refine ⟨p.map (aeval z).toRingHom, hp.map _, ?_⟩
  intro x hx hz
  let q : (MvPolynomial σ K ⧸ I) →ₐ[K] L :=
    Ideal.Quotient.liftₐ I (aeval x) hx
  have hq (f : MvPolynomial σ K) : q ((Ideal.Quotient.mk I) f) = aeval x f := rfl
  have hcomp : q.comp ψ = aeval z := by
    ext j
    simp only [AlgHom.comp_apply, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    exact (hq (a j)).trans (hz j)
  have hh := congrArg q he
  change q.toRingHom (p.eval₂ ψ.toRingHom ((Ideal.Quotient.mk I) (X i))) =
    q.toRingHom 0 at hh
  rw [Polynomial.hom_eval₂ p ψ.toRingHom q.toRingHom, map_zero] at hh
  have hcomp' : q.toRingHom.comp ψ.toRingHom = (aeval z).toRingHom :=
    congrArg AlgHom.toRingHom hcomp
  rw [hcomp'] at hh
  change p.eval₂ (aeval z).toRingHom (aeval x (X i)) = 0 at hh
  rw [aeval_X] at hh
  simpa only [Polynomial.eval_map] using hh

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma homogeneous_ideal_aeval_smul
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (x : σ → L) (hx : ∀ f ∈ I, aeval x f = 0)
    (t : L) (f : MvPolynomial σ K) (hf : f ∈ I) :
    aeval (t • x) f = 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro N _
  rw [homogeneous_aeval_smul (homogeneousComponent_isHomogeneous _ _),
    hx _ (hI f hf N), mul_zero]

theorem homogeneous_integral_projection_zero_fiber
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (a : τ → MvPolynomial σ K) (ha : ∀ j, (a j).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (x : σ → L) (hx : ∀ f ∈ I, aeval x f = 0)
    (hzero : ∀ j, aeval x (a j) = 0) : x = 0 := by
  classical
  funext i
  by_contra hi
  obtain ⟨p, hp, he⟩ := exists_monic_integral_projection_fiber_equation
    I a hint (0 : τ → L) i
  have hroot (y : L) : p.eval y = 0 := by
    have hz (j : τ) : aeval ((y / x i) • x) (a j) = (0 : τ → L) j := by
      rw [homogeneous_aeval_smul (ha j), hzero j, mul_zero]
      rfl
    have hh := he ((y / x i) • x)
      (homogeneous_ideal_aeval_smul I hI x hx (y / x i)) hz
    simpa only [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi] using hh
  apply hp.ne_zero
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hh : {y : L | p.IsRoot y} = Set.univ :=
    Set.eq_univ_of_forall hroot
  rw [hh]
  exact Set.infinite_univ

theorem homogeneous_integral_projection_geometric_no_base_point
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Infinite L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : IsHomogeneousIdeal I)
    (a : Fin m → MvPolynomial (Fin (n + 1)) K)
    (ha : ∀ j, (a j).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (x : Projectivization L (Fin (n + 1) → L))
    (hx : x ∈ projectiveIdealZeroLocus (I.map (map (algebraMap K L)))) :
    (fun j => aeval x.rep (a j)) ≠ 0 := by
  intro hz
  apply x.rep_nonzero
  apply homogeneous_integral_projection_zero_fiber I hI a ha hint x.rep
  · intro f hf
    have hh := projectiveIdealZeroLocus_rep hx (map (algebraMap K L) f)
      (Ideal.mem_map_of_mem _ hf)
    simpa only [eval_map, aeval_def] using hh
  · intro j
    exact congrFun hz j

end
end CCDN
