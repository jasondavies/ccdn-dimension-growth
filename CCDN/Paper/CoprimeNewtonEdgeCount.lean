/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.Plane.CoprimeNewtonEdgeReduction
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.Plane.AffinePlaneBadPrimeCount

/-! CCDN Corollary 4.2.5: the coprime Newton edge gives a logarithm-free
affine curve count. Geometric irreducibility, the exceptional primes,
content removal, and the point count are all proved here. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

def newtonEdgeCoefficientProduct (f : MvPolynomial (Fin 2) ℤ) (d e : ℕ) : ℤ :=
  f.coeff (Finsupp.single 0 d) * f.coeff (Finsupp.single 1 e)

lemma HasCoprimeNewtonEdge.coefficient_product_ne_zero
    {f : MvPolynomial (Fin 2) ℤ} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) :
    newtonEdgeCoefficientProduct f d e ≠ 0 := mul_ne_zero h.x_coeff h.y_coeff

lemma HasCoprimeNewtonEdge.coefficient_product_abs_one_le
    {f : MvPolynomial (Fin 2) ℤ} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) :
    1 ≤ |(newtonEdgeCoefficientProduct f d e : ℝ)| := by
  exact_mod_cast Int.one_le_abs h.coefficient_product_ne_zero

/-- The bad-prime factor depends only on the two coefficients at the
ends of the coprime edge, with an absolute multiplicative constant. -/
theorem coprime_newton_edge_bad_prime_factor
    (f : MvPolynomial (Fin 2) ℤ) {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) :
    hypersurfaceBadPrimeFactor f ≤ Real.exp (2 * mertensError + 1) *
      (Real.log |(newtonEdgeCoefficientProduct f d e : ℝ)| + 1) := by
  have hir :=
    (h.map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)) Int.cast_injective).irreducible
  have hd : 0 < f.totalDegree := by
    rw [h.totalDegree]; have := h.lower_pos; have := h.degree_gt; omega
  let P := (finite_fin_hypersurface_bad_primes f hir hd).toFinset
  have hP (p : ℕ) : p ∈ P ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
    simp only [P, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [hypersurfaceBadPrimeFactor_eq_exp f hir rfl P hP]
  let D := |newtonEdgeCoefficientProduct f d e|
  have hD : 0 < D := abs_pos.mpr h.coefficient_product_ne_zero
  have hH : 1 ≤ Real.log (D : ℝ) + 1 := by
    have hh : 1 ≤ (D : ℝ) := by
      simpa only [D, Int.cast_abs] using h.coefficient_product_abs_one_le
    linarith [Real.log_nonneg hh]
  have hh := bad_prime_factor_of_height P hD
    (fun p hp => ((hP p).mp hp).2.1)
    (fun p hp => (dvd_abs _ _).mpr (coprime_newton_edge_bad_reduction_dvd f h p ((hP p).mp hp).2))
    (show (1 : ℝ) ≤ 1 by rfl) hH
    (fun p hp => by exact_mod_cast ((hP p).mp hp).2.1.one_lt)
    (show Real.log (D : ℝ) ≤ 1 * (Real.log (D : ℝ) + 1) by linarith)
  simpa only [D, Int.cast_abs] using hh

def coprimeNewtonEdgeCountConstant : ℝ :=
  affineHypersurfaceAuxiliaryConstant 0 * (Real.exp (2 * mertensError + 1) + 2)

lemma coprimeNewtonEdgeCountConstant_pos : 0 < coprimeNewtonEdgeCountConstant := by
  unfold coprimeNewtonEdgeCountConstant
  have := affineHypersurfaceAuxiliaryConstant_pos 0
  positivity

theorem primitive_coprime_newton_edge_count
    (f : MvPolynomial (Fin 2) ℤ) {d e : ℕ} (h : HasCoprimeNewtonEdge f d e)
    (hprim : PrimitiveIntegerPolynomial f) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      coprimeNewtonEdgeCountConstant * (d : ℝ) ^ 4 *
        (Real.log |(newtonEdgeCoefficientProduct f d e : ℝ)| + 1) * B ^ (1 / (d : ℝ)) := by
  have hir := (h.map_of_injective (Int.castRingHom ℚ) Int.cast_injective).irreducible
  have hd : 0 < f.totalDegree := by
    rw [h.totalDegree]; have := h.lower_pos; have := h.degree_gt; omega
  have hb := affine_plane_count_bad_prime f hprim hir hd hB
  rw [h.totalDegree] at hb
  have hfactor := coprime_newton_edge_bad_prime_factor f h
  have hlog := Real.log_nonneg h.coefficient_product_abs_one_le
  have hfactor' : hypersurfaceBadPrimeFactor f + 2 ≤
      (Real.exp (2 * mertensError + 1) + 2) *
        (Real.log |(newtonEdgeCoefficientProduct f d e : ℝ)| + 1) := by nlinarith
  have hC := (affineHypersurfaceAuxiliaryConstant_pos 0).le
  calc
    _ ≤ affineHypersurfaceAuxiliaryConstant 0 * (d : ℝ) ^ 4 *
        (hypersurfaceBadPrimeFactor f + 2) * B ^ (1 / (d : ℝ)) := hb
    _ ≤ affineHypersurfaceAuxiliaryConstant 0 * (d : ℝ) ^ 4 *
        ((Real.exp (2 * mertensError + 1) + 2) *
          (Real.log |(newtonEdgeCoefficientProduct f d e : ℝ)| + 1)) *
          B ^ (1 / (d : ℝ)) := by gcongr
    _ = _ := by unfold coprimeNewtonEdgeCountConstant; ring

/-- The full coprime Newton-edge count for arbitrary integer equations.
The explicit positive constant is absolute, independent of both degrees,
all coefficients, and the radius. -/
theorem coprime_newton_edge_count
    (f : MvPolynomial (Fin 2) ℤ) {d e : ℕ} (h : HasCoprimeNewtonEdge f d e)
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      coprimeNewtonEdgeCountConstant * (d : ℝ) ^ 4 *
        (Real.log |(newtonEdgeCoefficientProduct f d e : ℝ)| + 1) * B ^ (1 / (d : ℝ)) := by
  obtain ⟨c, g, hc, hprim, heq⟩ := exists_primitive_integer_factor f h.ne_zero
  have hg := h.integer_scalar_factor hc heq
  have hzero : zeroLocus (map (Int.castRingHom ℚ) f) =
      zeroLocus (map (Int.castRingHom ℚ) g) := by
    ext x
    change eval x (map (Int.castRingHom ℚ) f) = 0 ↔ eval x (map (Int.castRingHom ℚ) g) = 0
    rw [heq, map_mul, map_C, eval_mul, eval_C]
    exact mul_eq_zero_iff_left (show (c : ℚ) ≠ 0 by exact_mod_cast hc)
  have hprod : |(newtonEdgeCoefficientProduct g d e : ℝ)| ≤
      |(newtonEdgeCoefficientProduct f d e : ℝ)| := by
    have hx := integer_scalar_factor_coefficient_bound hc heq (Finsupp.single 0 d)
    have hy := integer_scalar_factor_coefficient_bound hc heq (Finsupp.single 1 e)
    have hh := mul_le_mul hx hy (abs_nonneg _) (abs_nonneg _)
    simpa only [newtonEdgeCoefficientProduct, Int.cast_mul, abs_mul] using hh
  have hlog := Real.log_le_log
    (zero_lt_one.trans_le hg.coefficient_product_abs_one_le) hprod
  rw [hzero]
  apply (primitive_coprime_newton_edge_count g hg hprim hB).trans
  have hC := coprimeNewtonEdgeCountConstant_pos.le
  gcongr

/-- Corollary 4.2.5 in the paper's support form: the only monomials on
its top edge are the two specified endpoints; every other term is below.
The constant is chosen before degrees, endpoint coefficients and radius. -/
theorem coprime_newton_edge_log_free_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d e : ℕ, 0 < e → e < d → d.Coprime e →
      ∀ f : MvPolynomial (Fin 2) ℤ,
      f.coeff (Finsupp.single 0 d) ≠ 0 → f.coeff (Finsupp.single 1 e) ≠ 0 →
      (∀ m ∈ f.support, m ≠ Finsupp.single 0 d → m ≠ Finsupp.single 1 e →
        e * m 0 + d * m 1 < d * e) →
      ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (d : ℝ) ^ 4 *
          (Real.log |((f.coeff (Finsupp.single 0 d) *
            f.coeff (Finsupp.single 1 e) : ℤ) : ℝ)| + 1) * B ^ (1 / (d : ℝ)) := by
  refine ⟨coprimeNewtonEdgeCountConstant, coprimeNewtonEdgeCountConstant_pos, ?_⟩
  intro d e he hed hcop f hx hy hterms B hB
  have h : HasCoprimeNewtonEdge f d e := by
    refine ⟨hed, he, hcop, hx, hy, ?_⟩
    intro m hm
    by_cases hm0 : m = Finsupp.single 0 d
    · simp [hm0, mul_comm]
    by_cases hm1 : m = Finsupp.single 1 e
    · simp [hm1]
    exact (hterms m hm hm0 hm1).le
  exact coprime_newton_edge_count f h hB

end
end CCDN
