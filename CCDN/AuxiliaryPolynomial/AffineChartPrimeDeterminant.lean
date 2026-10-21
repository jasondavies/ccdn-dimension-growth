/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceLocalDivisor
import CCDN.Algebra.ModularPolynomialLift
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.ProjectiveOpenResidueDeterminant
import CCDN.ForMathlib.MvPolynomial
/-! The sharp prime determinant estimate from the literal affine reduction.
Loss of degree in that reduction is allowed: the extra powers of the
homogenizing coordinate are invertible at all supplied points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma homogeneous_eq_chartHomogenize_mul_X {K : Type*} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) :
    f = scaledHomogenize (affineChart n f).totalDegree 1 (affineChart n f) *
      X 0 ^ (d - (affineChart n f).totalDegree) := by
  have hdeg : (affineChart n f).totalDegree ≤ d :=
    (affineChart_totalDegree_le f).trans hf.totalDegree_le
  apply affineChart_injective_on_homogeneous hf
  · have hpow : (X (0 : Fin (n + 1)) ^ (d - (affineChart n f).totalDegree) :
        MvPolynomial (Fin (n + 1)) K).IsHomogeneous (d - (affineChart n f).totalDegree) := by
      simpa only [one_mul] using (isHomogeneous_X K (0 : Fin (n + 1))).pow
        (d - (affineChart n f).totalDegree)
    simpa only [Nat.add_sub_of_le hdeg] using
      (scaledHomogenize_homogeneous 1 (affineChart n f) le_rfl).mul hpow
  · simp only [map_mul, affineChart_scaledHomogenize_one, map_pow,
      show affineChart n (X 0 : MvPolynomial (Fin (n + 1)) K) = 1 by simp [affineChart],
      one_pow, mul_one]

/-- An affine-chart good prime for `f` and the points `z`: the reduction of the affine
chart `x₀ = 1` of `f` is absolutely irreducible and every point lies in that chart
modulo `p`. -/
abbrev AffineChartGoodPrime {n t : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ)
    (z : Fin t → IntPoint (n + 3)) (p : ℕ) [Fact p.Prime] : Prop :=
  Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
    (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
  ∀ i, IsCoprime (p : ℤ) (z i 0)

/-- An irreducible affine reduction gives the sharp prime-power
minor divisor for points whose first homogeneous coordinate is a p-adic unit.
The reduction may lose affine degree. -/
theorem affine_chart_minorGcd_dvd
    {n s N p d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0)) :
    ∃ a : ℕ,
      hypersurfaceDeterminantMain n s /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) - (n + 2 : ℝ) * s ≤ a ∧
      (p : ℤ) ^ a ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  let fbar := map (Int.castRingHom (ZMod p)) f
  let a := affineChart (n + 2) fbar
  let e := a.totalDegree
  let gbar := scaledHomogenize e 1 a
  let g := modularPolynomialLift gbar
  let h : MvPolynomial (Fin (n + 3)) ℤ := X 0 ^ (d - e)
  have hi : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) a) := by
    simpa only [a, fbar, affineChart_map] using hir
  have ha : Irreducible a := mvPolynomial_irreducible_of_field_map _ a hi
  have he : 0 < e := totalDegree_pos_of_ne_zero_of_not_isUnit ha.ne_zero ha.not_isUnit
  have hed : e ≤ d :=
    (affineChart_totalDegree_le fbar).trans (hf.map _).totalDegree_le
  have hgbar : gbar.IsHomogeneous e := scaledHomogenize_homogeneous 1 a le_rfl
  have hgreduce : map (Int.castRingHom (ZMod p)) g = gbar := map_modularPolynomialLift gbar
  have hghom : g.IsHomogeneous e := modularPolynomialLift_homogeneous gbar hgbar
  have hgabs : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) gbar) := by
    have hdeg : (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) a).totalDegree = e :=
      totalDegree_map_of_injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective a
    rw [show gbar = scaledHomogenize e 1 a from rfl, scaledHomogenize_map, map_one]
    simpa only [hdeg] using scaledHomogenize_irreducible _ hi one_ne_zero
  have hg0 : map (Int.castRingHom (ZMod p)) g ≠ 0 := by
    rw [hgreduce]
    intro hzero
    exact hgabs.ne_zero (by rw [hzero, map_zero])
  have hhhom : h.IsHomogeneous (d - e) := by
    simpa only [h, one_mul] using (isHomogeneous_X ℤ (0 : Fin (n + 3))).pow (d - e)
  have hfactor : map (Int.castRingHom (ZMod p)) f =
      map (Int.castRingHom (ZMod p)) g * map (Int.castRingHom (ZMod p)) h := by
    rw [hgreduce]
    simpa only [h, map_pow, map_X] using homogeneous_eq_chartHomogenize_mul_X fbar (hf.map _)
  simp only [← hypersurfaceDeterminantMain_div]
  apply projective_hypersurface_minorGcd_dvd_open f g h hf hghom hhhom he hed hg0
    (by rwa [hgreduce]) hfactor hsize F hF z hprim hz
  intro i
  simp only [h, map_pow, map_X, eval_X]
  apply pow_ne_zero
  intro hz0
  have hpdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0
  obtain ⟨u, v, huv⟩ := hunit i
  have hdvd : (p : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hpdiv _)
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_isUnit (isUnit_of_dvd_one hdvd)

end
end CCDN
