/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Projection.LinearProjectionFiltration
import CCDN.Algebra.ProjectiveChartDegree
import CCDN.Center.IntegralProjectionSpecialization
/-! An integral homogeneous linear projection has no nonzero geometric
point in its kernel. This gives disjointness from its projective
center over any infinite extension field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma homogeneous_ideal_aeval_smul
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
