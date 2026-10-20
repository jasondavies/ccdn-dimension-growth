module

public import CCDN.HypersurfaceSmoothPoint
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Simultaneous avoidance of the top homogeneous form, a tangent hyperplane,
and a chosen coordinate hyperplane, by a direction over the base field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The highest homogeneous component of a nonzero polynomial is nonzero. -/
theorem top_homogeneousComponent_ne_zero {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  have hs : f.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hf (support_eq_empty.mp h))
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup f.support hs (fun s => s.sum (fun _ e => e))
  have hdeg : m.degree = f.totalDegree := hd.symm
  intro h
  have hc := congrArg (fun g : MvPolynomial σ K => g.coeff m) h
  rw [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
  exact (mem_support_iff.mp hm) hc

/-- The linear form evaluating a differential on a direction. -/
def tangentDirectionPolynomial {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial σ K) (z : σ → K) : MvPolynomial σ K :=
  ∑ i, C (eval z (pderiv i f)) * X i

lemma tangentDirectionPolynomial_coeff {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial σ K) (z : σ → K) (j : σ) :
    (tangentDirectionPolynomial f z).coeff (Finsupp.single j 1) = eval z (pderiv j f) := by
  classical
  simp [tangentDirectionPolynomial, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

lemma tangentDirectionPolynomial_eval {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial σ K) (z b : σ → K) :
    eval b (tangentDirectionPolynomial f z) = ∑ i, eval z (pderiv i f) * b i := by
  simp [tangentDirectionPolynomial]

lemma tangentDirectionPolynomial_isHomogeneous {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial σ K) (z : σ → K) :
    (tangentDirectionPolynomial f z).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i)

/-- Over an infinite field, a smooth point admits a direction with nonzero
leading form, nonzero directional derivative, and nonzero selected coordinate. -/
theorem exists_good_hypersurface_direction_with_coordinate
    {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (z : σ → K)
    (j : σ) (hj : eval z (pderiv j f) ≠ 0) (k : σ) :
    ∃ b : σ → K, b k ≠ 0 ∧
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (∑ i, eval z (pderiv i f) * b i) ≠ 0 := by
  classical
  let H := homogeneousComponent f.totalDegree f
  let T := tangentDirectionPolynomial f z
  have hH : H ≠ 0 := top_homogeneousComponent_ne_zero f hf
  have hT : T ≠ 0 := by
    intro h
    have hc := congrArg (fun g : MvPolynomial σ K => g.coeff (Finsupp.single j 1)) h
    rw [tangentDirectionPolynomial_coeff] at hc
    exact hj hc
  have hprod : H * T * X k ≠ 0 := mul_ne_zero (mul_ne_zero hH hT) (X_ne_zero k)
  have hhom : (H * T * X k).IsHomogeneous (f.totalDegree + 1 + 1) :=
    ((homogeneousComponent_isHomogeneous _ _).mul
      (tangentDirectionPolynomial_isHomogeneous f z)).mul (isHomogeneous_X K k)
  have hex : ∃ b : σ → K, eval b (H * T * X k) ≠ 0 := by
    by_contra! hn
    exact hprod (hhom.eq_zero_of_forall_eval_eq_zero hn)
  obtain ⟨b, hb⟩ := hex
  rw [map_mul, map_mul, eval_X] at hb
  refine ⟨b, right_ne_zero_of_mul hb, left_ne_zero_of_mul (left_ne_zero_of_mul hb), ?_⟩
  rw [← tangentDirectionPolynomial_eval]
  exact right_ne_zero_of_mul (left_ne_zero_of_mul hb)

/-- Choose the nonzero coordinate to be the given nonzero partial direction. -/
theorem exists_good_hypersurface_direction
    {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (z : σ → K)
    (j : σ) (hj : eval z (pderiv j f) ≠ 0) :
    ∃ b : σ → K, b j ≠ 0 ∧
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (∑ i, eval z (pderiv i f) * b i) ≠ 0 :=
  exists_good_hypersurface_direction_with_coordinate f hf z j hj j

end
end CCDN
